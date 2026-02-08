use std::path::PathBuf;
use std::process::Command;
use std::fs;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use clap::Parser;
use comfy_table::{Table, Cell, Color, Attribute, presets::UTF8_FULL};
use tempfile::TempDir;
use fs_extra::dir::CopyOptions;
use libafl::corpus::OnDiskCorpus;
use libafl::events::{EventConfig, llmp::setup_restarting_mgr_std};
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

use generator::{create_context, generate_one};
use std::path::Path;

/// Path to the template Lean project (relative to generator crate root).
const TEMPLATE_DIR: &str = "../template";
/// File within the template project where generated code is injected.
const TARGET_FILE: &str = "../template/Solution.lean";

/// Statistics for verifier outcomes (thread-safe)
#[derive(Debug)]
struct VerifierStats {
    counters: [AtomicUsize; 8],  // One for each (lake, comp, safe) combination
    seen: [AtomicUsize; 8],      // Track which combinations we've seen (for immediate notification)
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

    fn record(&self, lake: bool, comp: bool, safe: bool) {
        let idx = (lake as usize) << 2 | (comp as usize) << 1 | (safe as usize);
        let count = self.counters[idx].fetch_add(1, Ordering::Relaxed);

        // If this is the first time seeing this combination, notify immediately!
        if count == 0 && self.seen[idx].fetch_add(1, Ordering::Relaxed) == 0 {
            let (l, c, s) = (
                if lake { "PASS" } else { "FAIL" },
                if comp { "PASS" } else { "FAIL" },
                if safe { "PASS" } else { "FAIL" },
            );
            let note = match (lake, comp, safe) {
                (true, true, true) => " 🎯🎯🎯 ULTIMATE!",
                (true, true, false) => " !!! GOLDEN",
                (true, false, true) => " ?! DIVERGENCE",
                _ => "",
            };
            println!("\n🔔 NEW CATEGORY: Lake={} Comp={} Safe={}{}", l, c, s, note);
        }
    }

    fn print_table(&self) {
        self.print_table_internal(false);
    }

    fn print_final_summary(&self) {
        self.print_table_internal(true);
    }

    fn save_summary_report(&self, artifacts_dir: &Path) -> std::io::Result<PathBuf> {
        use std::fmt::Write as FmtWrite;

        let mut report = String::new();
        let total: usize = self.counters.iter().map(|c| c.load(Ordering::Relaxed)).sum();
        let runtime = self.start_time.elapsed();

        writeln!(report, "# Fuzzer Campaign Summary\n").unwrap();
        writeln!(report, "**Total executions:** {}", total).unwrap();
        writeln!(report, "**Runtime:** {:.0?}\n", runtime).unwrap();
        writeln!(report, "## Verifier Results\n").unwrap();

        for (idx, counter) in self.counters.iter().enumerate() {
            let count = counter.load(Ordering::Relaxed);
            if count == 0 { continue; }

            let lake = (idx >> 2) & 1 == 1;
            let comp = (idx >> 1) & 1 == 1;
            let safe = idx & 1 == 1;
            let pct = (count as f64 / total as f64) * 100.0;

            let note = match (lake, comp, safe) {
                (true, true, true) => "🎯🎯🎯 ULTIMATE - SafeVerify bypass!",
                (true, true, false) => "!!! GOLDEN - Kernel bug",
                (true, false, true) => "?! DIVERGENCE",
                _ => "",
            };

            writeln!(
                report,
                "- Lake={} Comp={} Safe={}: {} ({:.1}%) {}",
                if lake {"PASS"} else {"FAIL"},
                if comp {"PASS"} else {"FAIL"},
                if safe {"PASS"} else {"FAIL"},
                count, pct, note
            ).unwrap();
        }

        writeln!(report, "\n## Result Locations\n").unwrap();
        writeln!(report, "Results saved to: `generator/solutions/lake_*_comp_*_safe_*/`\n").unwrap();

        let summary_path = artifacts_dir.join(format!("summary_{}.md", chrono::Utc::now().format("%Y%m%d_%H%M%S")));
        fs::write(&summary_path, report)?;
        Ok(summary_path)
    }

    fn print_table_internal(&self, force: bool) {
        if !force {
            let mut last = self.last_print.lock().unwrap();
            if last.elapsed() < Duration::from_secs(60) {
                return;  // Don't print too frequently
            }
            *last = Instant::now();
        }

        let total: usize = self.counters.iter().map(|c| c.load(Ordering::Relaxed)).sum();
        if total == 0 {
            return;
        }

        let runtime = self.start_time.elapsed();

        let mut table = Table::new();
        table.load_preset(UTF8_FULL)
             .set_header(vec![
                 Cell::new("Lake").add_attribute(Attribute::Bold),
                 Cell::new("Comparator").add_attribute(Attribute::Bold),
                 Cell::new("SafeVerify").add_attribute(Attribute::Bold),
                 Cell::new("Count").add_attribute(Attribute::Bold),
                 Cell::new("%").add_attribute(Attribute::Bold),
                 Cell::new("").add_attribute(Attribute::Bold),
             ]);

        for (idx, counter) in self.counters.iter().enumerate() {
            let count = counter.load(Ordering::Relaxed);
            if count == 0 { continue; }  // Skip zeros

            let lake = (idx >> 2) & 1 == 1;
            let comp = (idx >> 1) & 1 == 1;
            let safe = idx & 1 == 1;
            let pct = (count as f64 / total as f64) * 100.0;

            let (lake_cell, comp_cell, safe_cell) = (
                if lake { Cell::new("PASS").fg(Color::Green) } else { Cell::new("FAIL").fg(Color::Red) },
                if comp { Cell::new("PASS").fg(Color::Green) } else { Cell::new("FAIL").fg(Color::Red) },
                if safe { Cell::new("PASS").fg(Color::Green) } else { Cell::new("FAIL").fg(Color::Red) },
            );

            let (note, color) = match (lake, comp, safe) {
                (true, true, true) => ("🎯🎯🎯 ULTIMATE", Color::Magenta),
                (true, true, false) => ("!!! GOLDEN", Color::Yellow),
                (true, false, true) => ("?! DIVERGE", Color::Cyan),
                _ => ("", Color::Reset),
            };

            table.add_row(vec![
                lake_cell,
                comp_cell,
                safe_cell,
                Cell::new(count.to_string()),
                Cell::new(format!("{:.1}%", pct)),
                Cell::new(note).fg(color),
            ]);
        }

        println!("\n{}", table);
        println!("📊 Total: {} executions in {:.0?}\n", total, runtime);
    }
}

/// Setup isolated temp environment for a test case
fn setup_temp_environment(
    template_dir: &Path,
    code: &str,
) -> Result<(TempDir, PathBuf), String> {
    let temp_dir = TempDir::new().map_err(|e| format!("Failed to create temp dir: {e}"))?;
    let temp_template = temp_dir.path().join("template");

    // Copy template (exclude .lake/ to save memory)
    let mut copy_options = CopyOptions::new();
    copy_options.copy_inside = true;
    fs_extra::dir::copy(template_dir, temp_dir.path(), &copy_options)
        .map_err(|e| format!("Failed to copy template: {e}"))?;

    // Remove .lake/ to save memory
    let _ = fs::remove_dir_all(temp_template.join(".lake"));

    // Write generated code
    fs::write(temp_template.join("Solution.lean"), code)
        .map_err(|e| format!("Failed to write Solution.lean: {e}"))?;

    Ok((temp_dir, temp_template))
}

/// Run lake build and return success status
fn run_lake_build(project_dir: &Path) -> bool {
    Command::new("lake")
        .arg("build")
        .arg("Solution")
        .current_dir(project_dir)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .output()
        .map(|output| output.status.success())
        .unwrap_or(false)
}

/// Run comparator and return success status
fn run_comparator(project_dir: &Path, comparator_path: &str) -> bool {
    let config = project_dir.join("comparator_config.json");
    Command::new("lake")
        .arg("env")
        .arg(comparator_path)
        .arg(config.display().to_string())
        .current_dir(project_dir)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .output()
        .map(|output| output.status.success())
        .unwrap_or(false)
}

/// Run SafeVerify on compiled .olean files and return success status
fn run_safeverify(project_dir: &Path, safeverify_path: &str) -> bool {
    let olean_dir = project_dir.join(".lake/build/lib");
    let challenge = olean_dir.join("Challenge.olean");
    let solution = olean_dir.join("Solution.olean");

    [&challenge, &solution].iter().all(|p| p.exists())
        && Command::new("lake")
            .args(["env", safeverify_path, &challenge.display().to_string(), &solution.display().to_string()])
            .current_dir(project_dir)
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .output()
            .map_or(false, |out| out.status.success())
}

/// Categorize result, save to appropriate directory, and return if it's a crash
fn categorize_and_save(
    lake: bool,
    comparator: bool,
    safeverify: bool,
    code: &str,
    stats: &VerifierStats,
) -> bool {
    // Record statistics
    stats.record(lake, comparator, safeverify);
    stats.print_table();
    let timestamp = current_nanos();
    let category = format!(
        "solutions/lake_{}_comp_{}_safe_{}",
        if lake { "pass" } else { "fail" },
        if comparator { "pass" } else { "fail" },
        if safeverify { "pass" } else { "fail" }
    );
    let save_path = format!("{}/result_{}.lean", category, timestamp);

    // Save file
    if let Err(e) = fs::write(&save_path, code) {
        log::warn!("Failed to save to {}: {e}", save_path);
    }

    // Log based on significance
    match (lake, comparator, safeverify) {
        (true, true, true) => {
            println!("\n[🎯🎯🎯] ULTIMATE GOLDEN: {}", save_path);
            println!("[🎯🎯🎯] Passes Lake + Comparator + SafeVerify!");
            println!("[🎯🎯🎯] SafeVerify failed to block this attack!");
            println!("[🎯🎯🎯] Code:\n{}", code);
            true
        }
        (true, true, false) => {
            println!("\n[!!!] GOLDEN (SafeVerify blocked): {}", save_path);
            println!("[!!!] Passes Lake + Comparator, SafeVerify blocks");
            true
        }
        (true, false, true) => {
            println!("\n[?!] DIVERGENCE: {}", save_path);
            println!("[?!] Lake + SafeVerify pass, Comparator fails");
            false
        }
        (true, false, false) => {
            println!("\n[*] Lake only: {}", save_path);
            false
        }
        _ => false, // Normal case - lake failed or other combinations
    }
}

/// Lean 4 Grammar Fuzzer (Nautilus)
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Maximum tree depth for grammar generation
    #[arg(short, long, default_value_t = 15)]
    depth: usize,

    /// Number of parallel workers (0 = number of CPUs)
    #[arg(short = 'j', long, default_value_t = 1)]
    jobs: usize,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Suppress LibAFL's "Address already in use" errors (expected when workers connect)
    env_logger::Builder::from_default_env()
        .filter_module("libafl_bolts::os::unix_shmem_server", log::LevelFilter::Off)
        .init();

    // Setup Ctrl+C handler that will run BEFORE we start fuzzing
    // (LibAFL will override this, but we can use std::panic::set_hook as alternative)

    // Load .env file for COMPARATOR_PATH
    let _ = dotenvy::from_filename("../.env").or_else(|_| dotenvy::from_filename(".env"));

    let args = Args::parse();

    // Determine number of cores
    let cores = if args.jobs == 0 {
        num_cpus::get()
    } else {
        args.jobs
    };

    println!("[*] Lean 4 Grammar Fuzzer (Nautilus)");
    println!("[*] Using {} parallel worker cores", cores);
    println!("[*] Tree depth: {}", args.depth);

    let template_dir = PathBuf::from(TEMPLATE_DIR)
        .canonicalize()
        .unwrap_or_else(|_| {
            eprintln!("warning: template dir not found at {TEMPLATE_DIR}, using relative path");
            PathBuf::from(TEMPLATE_DIR)
        });
    let _target_file = PathBuf::from(TARGET_FILE)
        .canonicalize()
        .unwrap_or_else(|_| PathBuf::from(TARGET_FILE));

    println!("[*] Lean 4 Grammar Fuzzer (Nautilus)");
    println!("[*] Template dir: {}", template_dir.display());
    println!("[*] Target file:  {}", TARGET_FILE);
    println!("[*] Tree depth:   {}", args.depth);

    // Build the Nautilus grammar context (wrap in Arc for sharing)
    let ctx = Arc::new(create_context(args.depth));
    println!(
        "[*] Grammar loaded: {} rules",
        generator::grammar::lean4_rules().len()
    );

    // Output directories for 3D categorization: Lake × Comparator × SafeVerify
    let results_dir = PathBuf::from("solutions");
    let artifacts_dir = PathBuf::from("../artifacts/generator-reports");
    fs::create_dir_all(&artifacts_dir)?;

    ["pass", "fail"].iter()
        .flat_map(|l| ["pass", "fail"].iter().map(move |c| (l, c)))
        .flat_map(|(l, c)| ["pass", "fail"].iter().map(move |s| (l, c, s)))
        .try_for_each(|(lake, comp, safe)| {
            fs::create_dir_all(results_dir.join(format!("lake_{}_comp_{}_safe_{}", lake, comp, safe)))
        })?;

    // Monitor: prints stats to stdout
    let monitor = SimpleMonitor::new(|s| println!("{s}"));

    // Event manager: multi-core with shared corpus via LLMP
    let (state_opt, mut mgr) = setup_restarting_mgr_std(monitor, 1337, EventConfig::AlwaysUnique)?;

    // Feedbacks
    let mut nautilus_feedback = NautilusFeedback::new(&ctx);
    let mut crash_feedback = CrashFeedback::new();

    // State - Use ONLY disk corpus (no in-memory) to prevent RAM exhaustion
    let golden_dir = results_dir.join("lake_pass_comp_pass_safe_pass");
    let mut state = state_opt.unwrap_or_else(|| {
        StdState::new(
            StdRand::with_seed(current_nanos()),
            OnDiskCorpus::new(&golden_dir).expect("Failed to create corpus dir"),
            OnDiskCorpus::new(&golden_dir).expect("Failed to create corpus dir"),
            &mut nautilus_feedback,
            &mut crash_feedback,
        ).expect("Failed to create state")
    });

    // Register Nautilus chunk metadata (required by NautilusFeedback and splice mutator)
    if !state.has_metadata::<NautilusChunksMetadata>() {
        state.add_metadata(NautilusChunksMetadata::new("workdir".to_string()));
    }

    // Scheduler
    let scheduler = QueueScheduler::new();

    // Fuzzer
    let mut fuzzer = StdFuzzer::new(scheduler, nautilus_feedback, crash_feedback);

    // Get verifier paths from environment (clone for move into closure)
    let comparator_path = std::env::var("COMPARATOR_PATH")
        .expect("COMPARATOR_PATH not set in .env - please configure it");
    let safeverify_path = std::env::var("SAFEVERIFY_PATH")
        .expect("SAFEVERIFY_PATH not set in .env - please configure it");

    // Statistics tracking (shared across all workers via Arc)
    let stats = Arc::new(VerifierStats::new());
    let stats_clone = Arc::clone(&stats);
    let stats_for_signal = Arc::clone(&stats);

    // Clone artifacts_dir for signal handler
    let artifacts_dir_clone = artifacts_dir.clone();

    // Register Ctrl+C handler to print stats before exit
    ctrlc::set_handler(move || {
        println!("\n\n[*] Ctrl+C received - saving reports...");
        stats_for_signal.print_final_summary();

        // Save summary report
        match stats_for_signal.save_summary_report(&artifacts_dir_clone) {
            Ok(path) => println!("\n📄 Summary saved to: {}", path.display()),
            Err(e) => eprintln!("Failed to save summary: {}", e),
        }

        println!("\n📁 Results saved to:");
        println!("   Solutions: generator/solutions/lake_*_comp_*_safe_*/");
        println!("   Reports:   artifacts/generator-reports/");
        std::process::exit(0);
    }).expect("Error setting Ctrl+C handler");

    // Clone values for move into closure
    let template_dir_clone = template_dir.clone();
    let comparator_path_clone = comparator_path.clone();
    let safeverify_path_clone = safeverify_path.clone();
    let ctx_clone = Arc::clone(&ctx);

    // Harness: unparse → write → lake build → comparator → safeverify → categorize
    let mut harness = move |input: &NautilusInput| -> ExitKind {
        let prefix = generate_one(&ctx_clone, input);
        let golden_suffix = "\n\n-- GOLDEN CHECK\ntheorem soundness_check : False := by\n  simp_all\n  omega\n  decide\n";
        let code = format!("{}{}", prefix, golden_suffix);

        // Setup isolated temp environment
        let (_temp_dir, temp_template) = match setup_temp_environment(&template_dir_clone, &code) {
            Ok(env) => env,
            Err(e) => {
                log::warn!("{}", e);
                return ExitKind::Ok;
            }
        };

        // Run verifiers
        let lake_success = run_lake_build(&temp_template);
        let comparator_success = run_comparator(&temp_template, &comparator_path_clone);
        let safeverify_success = if lake_success {
            run_safeverify(&temp_template, &safeverify_path_clone)
        } else {
            false
        };

        // Categorize and save
        let is_crash = categorize_and_save(lake_success, comparator_success, safeverify_success, &code, &stats_clone);

        // Explicit cleanup - drop temp_dir before returning
        drop(_temp_dir);
        std::thread::sleep(std::time::Duration::from_millis(10));  // Give OS time to cleanup

        if is_crash {
            ExitKind::Crash
        } else {
            ExitKind::Ok
        }
    };

    // Executor — no observers needed since we're spawning a subprocess
    let mut executor = InProcessExecutor::new(
        &mut harness,
        (),
        &mut fuzzer,
        &mut state,
        &mut mgr,
    )?;

    // Generator for initial corpus seeding
    let mut generator = NautilusGenerator::new(&ctx);

    // Generate initial corpus (reduced to 2 seeds since lake+comparator is slow)
    println!("[*] Generating initial corpus...");
    state.generate_initial_inputs_forced(
        &mut fuzzer,
        &mut executor,
        &mut generator,
        &mut mgr,
        2, // 2 initial seeds (lake+comparator is slow)
    )?;
    println!("[*] Initial corpus generated");

    // Mutators: weighted toward random mutation with some splice/recursion
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

    // Mutational stage
    let mut stages = tuple_list!(StdMutationalStage::new(mutator));

    // Run the fuzzer
    println!("[*] Starting fuzz loop...");
    println!("[*] Press Ctrl+C to stop (will save reports gracefully)");
    let fuzz_result = fuzzer.fuzz_loop(&mut stages, &mut executor, &mut state, &mut mgr);

    // Print final summary and save report (runs on normal exit)
    println!("\n[*] Fuzzing campaign ended");
    stats.print_final_summary();

    // Save summary report
    match stats.save_summary_report(&artifacts_dir) {
        Ok(path) => println!("\n📄 Summary saved to: {}", path.display()),
        Err(e) => eprintln!("Failed to save summary: {}", e),
    }

    // Show where to find results
    println!("\n📁 Results saved to:");
    println!("   Solutions: generator/solutions/lake_*_comp_*_safe_*/");
    println!("   Reports:   artifacts/generator-reports/");
    println!("\n💡 To analyze scaffold results:");
    println!("   cd scaffold && uv run scaffold report <session>.jsonl");

    fuzz_result?;
    Ok(())
}
