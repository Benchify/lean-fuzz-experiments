use std::path::PathBuf;
use std::process::Command;
use std::fs;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use core::time::Duration as CoreDuration;

use clap::Parser;
use comfy_table::{Table, Cell, Color, Attribute, presets::UTF8_FULL};
use tempfile::TempDir;
use fs_extra::dir::CopyOptions;
use libafl::corpus::{InMemoryCorpus, OnDiskCorpus};
use libafl::events::SimpleEventManager;
use libafl::executors::{ExitKind, InProcessExecutor};
use libafl::feedbacks::nautilus::{NautilusChunksMetadata, NautilusFeedback};
use libafl::feedbacks::CrashFeedback;
use libafl::HasMetadata;
use libafl::generators::nautilus::NautilusGenerator;
use libafl::inputs::nautilus::NautilusInput;
use libafl::monitors::SimpleMonitor;
use libafl::mutators::nautilus::{
    NautilusRandomMutator, NautilusRecursionMutator, NautilusSpliceMutator,
};
use libafl::mutators::HavocScheduledMutator;
use libafl::schedulers::QueueScheduler;
use libafl::stages::mutational::StdMutationalStage;
use libafl::state::StdState;
use libafl::{Fuzzer, StdFuzzer};
use libafl_bolts::current_nanos;
use libafl_bolts::rands::StdRand;
use libafl_bolts::tuples::tuple_list;

use generator::{create_context, create_prefix_context, generate_one};
use std::path::Path;

const TEMPLATE_DIR: &str = "../template";
const TARGET_FILE: &str = "../template/Solution.lean";

// ---------------------------------------------------------------------------
// Verifier statistics
// ---------------------------------------------------------------------------

#[derive(Debug)]
struct VerifierStats {
    counters: [AtomicUsize; 16],
    seen: [AtomicUsize; 16],
    last_print: Mutex<Instant>,
    start_time: Instant,
}

impl VerifierStats {
    fn new() -> Self {
        Self {
            counters: Default::default(),
            seen: Default::default(),
            last_print: Mutex::new(Instant::now()),
            start_time: Instant::now(),
        }
    }

    fn record(&self, syntax: bool, lake: bool, comp: bool, safe: bool) {
        let idx = (syntax as usize) << 3 | (lake as usize) << 2 | (comp as usize) << 1 | (safe as usize);
        let prev = self.counters[idx].fetch_add(1, Ordering::Relaxed);

        if prev == 0 && self.seen[idx].fetch_add(1, Ordering::Relaxed) == 0 {
            let (syn, l, c, s) = (
                if syntax { "PASS" } else { "FAIL" },
                if lake { "PASS" } else { "FAIL" },
                if comp { "PASS" } else { "FAIL" },
                if safe { "PASS" } else { "FAIL" },
            );
            let note = match (syntax, lake, comp, safe) {
                (true, true, true, true) => " 🎯🎯🎯 ULTIMATE!",
                (true, true, true, false) => " !!! GOLDEN",
                (true, true, false, true) => " ?! DIVERGENCE",
                _ => "",
            };
            println!("\n🔔 NEW CATEGORY: Syntax={} Lake={} Comp={} Safe={}{}", syn, l, c, s, note);
        }
    }

    fn print_if_due(&self) { self.print_table_internal(false); }
    fn print_final(&self) { self.print_table_internal(true); }

    fn print_table_internal(&self, force: bool) {
        if !force {
            let mut last = self.last_print.lock().unwrap();
            if last.elapsed() < Duration::from_secs(60) { return; }
            *last = Instant::now();
        }

        let total: usize = self.counters.iter().map(|c| c.load(Ordering::Relaxed)).sum();
        if total == 0 { return; }

        let runtime = self.start_time.elapsed();
        let mut table = Table::new();
        table.load_preset(UTF8_FULL).set_header(vec![
            Cell::new("Syntax").add_attribute(Attribute::Bold),
            Cell::new("Lake").add_attribute(Attribute::Bold),
            Cell::new("Comparator").add_attribute(Attribute::Bold),
            Cell::new("SafeVerify").add_attribute(Attribute::Bold),
            Cell::new("Count").add_attribute(Attribute::Bold),
            Cell::new("%").add_attribute(Attribute::Bold),
        ]);

        for (idx, counter) in self.counters.iter().enumerate() {
            let count = counter.load(Ordering::Relaxed);
            if count == 0 { continue; }

            let syntax = (idx >> 3) & 1 == 1;
            let lake = (idx >> 2) & 1 == 1;
            let comp = (idx >> 1) & 1 == 1;
            let safe = idx & 1 == 1;
            let pct = (count as f64 / total as f64) * 100.0;

            let pass = |b: bool| if b { Cell::new("PASS").fg(Color::Green) } else { Cell::new("FAIL").fg(Color::Red) };

            let note = match (syntax, lake, comp, safe) {
                (true, true, true, true) => " 🎯🎯🎯",
                (true, true, true, false) => " !!!",
                (true, true, false, true) => " ?!",
                _ => "",
            };

            table.add_row(vec![
                pass(syntax), pass(lake), pass(comp), pass(safe),
                Cell::new(count.to_string()),
                Cell::new(format!("{:.1}%{}", pct, note)),
            ]);
        }

        println!("\n{}", table);
        println!("📊 Total: {} executions in {:.0?}\n", total, runtime);
    }

    fn save_report(&self, artifacts_dir: &Path) -> std::io::Result<PathBuf> {
        use std::fmt::Write as FmtWrite;
        let mut report = String::new();
        let total: usize = self.counters.iter().map(|c| c.load(Ordering::Relaxed)).sum();
        let runtime = self.start_time.elapsed();

        writeln!(report, "# Fuzzer Campaign Summary\n").unwrap();
        writeln!(report, "**Total executions:** {}\n**Runtime:** {:.0?}\n", total, runtime).unwrap();
        writeln!(report, "## Verifier Results\n").unwrap();

        for (idx, counter) in self.counters.iter().enumerate() {
            let count = counter.load(Ordering::Relaxed);
            if count == 0 { continue; }
            let syntax = (idx >> 3) & 1 == 1;
            let lake = (idx >> 2) & 1 == 1;
            let comp = (idx >> 1) & 1 == 1;
            let safe = idx & 1 == 1;
            let pct = (count as f64 / total as f64) * 100.0;
            writeln!(report, "- Syntax={} Lake={} Comp={} Safe={}: {} ({:.1}%)",
                if syntax {"PASS"} else {"FAIL"},
                if lake {"PASS"} else {"FAIL"},
                if comp {"PASS"} else {"FAIL"},
                if safe {"PASS"} else {"FAIL"},
                count, pct).unwrap();
        }

        let path = artifacts_dir.join(format!("summary_{}.md", chrono::Utc::now().format("%Y%m%d_%H%M%S")));
        fs::write(&path, report)?;
        Ok(path)
    }
}

// ---------------------------------------------------------------------------
// Verifier helpers
// ---------------------------------------------------------------------------

fn setup_temp_environment(template_dir: &Path, code: &str) -> Result<(TempDir, PathBuf), String> {
    let temp_dir = TempDir::new().map_err(|e| format!("tempdir: {e}"))?;
    let temp_template = temp_dir.path().join("template");
    let mut opts = CopyOptions::new();
    opts.copy_inside = true;
    fs_extra::dir::copy(template_dir, temp_dir.path(), &opts)
        .map_err(|e| format!("copy: {e}"))?;
    // Keep .lake/ — deleting it forces full rebuild per test (very slow)
    fs::write(temp_template.join("Solution.lean"), code)
        .map_err(|e| format!("write: {e}"))?;
    Ok((temp_dir, temp_template))
}

fn run_lake_build(dir: &Path) -> (bool, String) {
    match Command::new("lake").args(["build", "Solution"])
        .current_dir(dir)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .output() {
        Ok(o) => (o.status.success(), String::from_utf8_lossy(&o.stderr).to_string()),
        Err(_) => (false, String::new()),
    }
}

fn has_parse_error(stderr: &str) -> bool {
    // Parse errors indicate syntax invalidity. Patterns from scaffold/src/scaffold/diagnostics.py
    stderr.contains("expected") ||
    stderr.contains("unexpected") ||
    stderr.contains("unknown identifier") && stderr.contains("available?") ||
    stderr.contains("invalid")
}

fn run_comparator(dir: &Path, bin: &str) -> bool {
    Command::new("lake").args(["env", bin, &dir.join("comparator_config.json").display().to_string()])
        .current_dir(dir)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .output().map_or(false, |o| o.status.success())
}

fn run_safeverify(dir: &Path, bin: &str) -> bool {
    let lib = dir.join(".lake/build/lib");
    let (ch, so) = (lib.join("Challenge.olean"), lib.join("Solution.olean"));
    [&ch, &so].iter().all(|p| p.exists())
        && Command::new("lake")
            .args(["env", bin, &ch.display().to_string(), &so.display().to_string()])
            .current_dir(dir)
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .output().map_or(false, |o| o.status.success())
}

fn categorize_and_save(syntax: bool, lake: bool, comp: bool, safe: bool, code: &str, stats: &VerifierStats) -> bool {
    stats.record(syntax, lake, comp, safe);
    stats.print_if_due();

    let cat = format!("solutions/syntax_{}_lake_{}_comp_{}_safe_{}",
        if syntax {"pass"} else {"fail"},
        if lake {"pass"} else {"fail"},
        if comp {"pass"} else {"fail"},
        if safe {"pass"} else {"fail"});
    let path = format!("{}/result_{}.lean", cat, current_nanos());
    let _ = fs::write(&path, code);

    match (syntax, lake, comp, safe) {
        (true, true, true, true) => {
            println!("\n[🎯🎯🎯] ULTIMATE: {}\n{}", path, code);
            true
        }
        (true, true, true, false) => {
            println!("\n[!!!] GOLDEN (SafeVerify blocked): {}", path);
            true
        }
        (true, true, false, true) => {
            println!("\n[?!] DIVERGENCE: {}", path);
            false
        }
        (true, true, false, false) => {
            println!("\n[*] Lake only: {}", path);
            false
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Golden suffixes (matches scaffold/src/scaffold/golden_suffixes.py)
// ---------------------------------------------------------------------------

const GOLDEN_SUFFIXES: &[(&str, &str)] = &[
    ("trivial", "\n\ntheorem soundness_check : False := by trivial\n#print axioms soundness_check\n"),
    ("simp_all", "\n\ntheorem soundness_check : False := by simp_all\n#print axioms soundness_check\n"),
    ("native_decide", "\n\ntheorem soundness_check : False := by native_decide\n#print axioms soundness_check\n"),
    ("omega", "\n\ntheorem soundness_check : (0 : Nat) = 1 := by omega\n#print axioms soundness_check\n"),
    ("decide", "\n\ntheorem soundness_check : False := by decide\n#print axioms soundness_check\n"),
    ("assumption", "\n\ntheorem soundness_check : False := by assumption\n#print axioms soundness_check\n"),
    ("inferInstance", "\n\ntheorem soundness_check : False := inferInstance\n#print axioms soundness_check\n"),
];

// ---------------------------------------------------------------------------
// CLI + main
// ---------------------------------------------------------------------------

#[derive(Parser, Debug)]
#[command(author, version, about = "Lean 4 Grammar Fuzzer (Nautilus)")]
struct Args {
    #[arg(short, long, default_value_t = 15)]
    depth: usize,

    #[arg(short = 'j', long, default_value_t = 1)]
    jobs: usize,

    #[arg(long, default_value_t = true)]
    prefix_only: bool,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::Builder::from_default_env()
        .filter_module("libafl_bolts::os::unix_shmem_server", log::LevelFilter::Off)
        .init();

    let _ = dotenvy::from_filename("../.env").or_else(|_| dotenvy::from_filename(".env"));
    let args = Args::parse();

    let template_dir = PathBuf::from(TEMPLATE_DIR).canonicalize()
        .unwrap_or_else(|_| PathBuf::from(TEMPLATE_DIR));
    let _ = PathBuf::from(TARGET_FILE).canonicalize()
        .unwrap_or_else(|_| PathBuf::from(TARGET_FILE));

    let ctx = if args.prefix_only {
        create_prefix_context(args.depth)
    } else {
        create_context(args.depth)
    };
    let rule_count = if args.prefix_only {
        generator::grammar::lean4_prefix_rules().len()
    } else {
        generator::grammar::lean4_rules().len()
    };

    println!("[*] Lean 4 Grammar Fuzzer (Nautilus)");
    println!("[*] Template: {}", template_dir.display());
    println!("[*] Depth: {}  Rules: {} (prefix_only={})", args.depth, rule_count, args.prefix_only);

    // Output directories
    let results_dir = PathBuf::from("solutions");
    let artifacts_dir = PathBuf::from("../artifacts/generator-reports");
    fs::create_dir_all(&artifacts_dir)?;
    ["pass", "fail"].iter()
        .flat_map(|syn| ["pass", "fail"].iter().map(move |l| (syn, l)))
        .flat_map(|(syn, l)| ["pass", "fail"].iter().map(move |c| (syn, l, c)))
        .flat_map(|(syn, l, c)| ["pass", "fail"].iter().map(move |s| (syn, l, c, s)))
        .try_for_each(|(syn, l, c, s)| {
            fs::create_dir_all(results_dir.join(format!("syntax_{}_lake_{}_comp_{}_safe_{}", syn, l, c, s)))
        })?;

    // LibAFL setup
    let monitor = SimpleMonitor::new(|s| println!("{s}"));
    let mut mgr = SimpleEventManager::new(monitor);
    let mut nautilus_feedback = NautilusFeedback::new(&ctx);
    let mut crash_feedback = CrashFeedback::new();
    let golden_dir = results_dir.join("syntax_pass_lake_pass_comp_pass_safe_pass");
    let mut state = StdState::new(
        StdRand::with_seed(current_nanos()),
        InMemoryCorpus::<NautilusInput>::new(),
        OnDiskCorpus::new(&golden_dir)?,
        &mut nautilus_feedback,
        &mut crash_feedback,
    )?;
    if !state.has_metadata::<NautilusChunksMetadata>() {
        state.add_metadata(NautilusChunksMetadata::new("workdir".to_string()));
    }
    let scheduler = QueueScheduler::new();
    let mut fuzzer = StdFuzzer::new(scheduler, nautilus_feedback, crash_feedback);

    // Verifier paths
    let comparator_path = std::env::var("COMPARATOR_PATH")
        .expect("COMPARATOR_PATH not set in .env");
    let safeverify_path = std::env::var("SAFEVERIFY_PATH")
        .expect("SAFEVERIFY_PATH not set in .env");

    // Stats
    let stats = Arc::new(VerifierStats::new());
    let stats_ref = Arc::clone(&stats);

    // Harness: one temp dir per prefix, try golden suffixes only if prefix compiles
    let mut harness = |input: &NautilusInput| -> ExitKind {
        let prefix = generate_one(&ctx, input);

        // Create ONE temp dir for this prefix (reused across all suffixes)
        let (_td, temp) = match setup_temp_environment(&template_dir, &prefix) {
            Ok(v) => v,
            Err(_) => return ExitKind::Ok,
        };

        // Quick check: does the prefix alone compile?
        let (prefix_builds, prefix_stderr) = run_lake_build(&temp);
        let prefix_syntax_valid = prefix_builds || !has_parse_error(&prefix_stderr);

        if !prefix_builds {
            stats_ref.record(prefix_syntax_valid, false, false, false);
            stats_ref.print_if_due();
            return ExitKind::Ok;
        }

        // Prefix compiles! Now try each golden suffix in the SAME temp dir.
        let mut best_is_crash = false;
        for &(suffix_name, golden_suffix) in GOLDEN_SUFFIXES {
            let code = format!("{}{}", prefix, golden_suffix);
            // Overwrite Solution.lean with prefix+suffix
            if fs::write(temp.join("Solution.lean"), &code).is_err() { continue; }
            let (builds, _stderr) = run_lake_build(&temp);
            if !builds { continue; }

            // This suffix compiled! Run verifiers.
            let comp = run_comparator(&temp, &comparator_path);
            let safe = run_safeverify(&temp, &safeverify_path);

            println!("[*] suffix={} syntax=PASS lake=PASS comp={} safe={}",
                suffix_name,
                if comp { "PASS" } else { "FAIL" },
                if safe { "PASS" } else { "FAIL" });

            if categorize_and_save(true, true, comp, safe, &code, &stats_ref) {
                best_is_crash = true;
            }
        }

        // Don't record prefix-only cases - only record actual test results
        // (prefix+suffix) where we ran all three verifiers.

        if best_is_crash { ExitKind::Crash } else { ExitKind::Ok }
    };

    // 120s timeout per test (7 golden suffixes × lake build can take a while)
    let mut executor = InProcessExecutor::with_timeout(
        &mut harness, (), &mut fuzzer, &mut state, &mut mgr,
        CoreDuration::from_secs(120),
    )?;
    let mut generator = NautilusGenerator::new(&ctx);

    // Single initial seed (each seed runs 7 golden suffixes × lake build, so keep it minimal)
    println!("[*] Generating initial corpus...");
    state.generate_initial_inputs_forced(&mut fuzzer, &mut executor, &mut generator, &mut mgr, 1)?;
    println!("[*] Initial corpus generated");

    let mutator = HavocScheduledMutator::new(tuple_list!(
        NautilusRandomMutator::new(&ctx),
        NautilusRandomMutator::new(&ctx),
        NautilusRandomMutator::new(&ctx),
        NautilusRandomMutator::new(&ctx),
        NautilusRandomMutator::new(&ctx),
        NautilusRandomMutator::new(&ctx),
        NautilusRecursionMutator::new(&ctx),
        NautilusSpliceMutator::new(&ctx),
        NautilusSpliceMutator::new(&ctx),
        NautilusSpliceMutator::new(&ctx),
    ));
    let mut stages = tuple_list!(StdMutationalStage::new(mutator));

    println!("[*] Starting fuzz loop...");
    let fuzz_result = fuzzer.fuzz_loop(&mut stages, &mut executor, &mut state, &mut mgr);

    // Final report (runs on normal exit)
    stats.print_final();
    if let Ok(p) = stats.save_report(&artifacts_dir) {
        println!("📄 Summary: {}", p.display());
    }
    println!("📁 Results: generator/solutions/syntax_*_lake_*_comp_*_safe_*/");

    fuzz_result?;
    Ok(())
}
