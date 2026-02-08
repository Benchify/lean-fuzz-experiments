use std::path::PathBuf;
use std::process::Command;
use std::fs;

use clap::Parser;
use tempfile::TempDir;
use fs_extra::dir::CopyOptions;
use libafl::corpus::{InMemoryCorpus, OnDiskCorpus};
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

/// Path to the template Lean project (relative to generator crate root).
const TEMPLATE_DIR: &str = "../template";
/// File within the template project where generated code is injected.
const TARGET_FILE: &str = "../template/Solution.lean";

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

    // Build the Nautilus grammar context
    let ctx = create_context(args.depth);
    println!(
        "[*] Grammar loaded: {} rules",
        generator::grammar::lean4_rules().len()
    );

    // Output directories for 3D categorization: Lake × Comparator × SafeVerify
    let results_dir = PathBuf::from("solutions");
    fs::create_dir_all(&results_dir)?;

    // Create all 8 possible outcome directories
    for lake in ["pass", "fail"] {
        for comp in ["pass", "fail"] {
            for safe in ["pass", "fail"] {
                let dir = results_dir.join(format!("lake_{}_comp_{}_safe_{}", lake, comp, safe));
                fs::create_dir_all(&dir)?;
            }
        }
    }

    // Monitor: prints stats to stdout
    let monitor = SimpleMonitor::new(|s| println!("{s}"));

    // Event manager: multi-core with shared corpus via LLMP
    let (state_opt, mut mgr) = setup_restarting_mgr_std(monitor, 1337, EventConfig::AlwaysUnique)?;

    // Feedbacks
    let mut nautilus_feedback = NautilusFeedback::new(&ctx);
    let mut crash_feedback = CrashFeedback::new();

    // State (use pass_pass_pass as main corpus - the ultimate golden signals!)
    // state_opt is Some(state) if we're restoring, None if first run
    let golden_dir = results_dir.join("lake_pass_comp_pass_safe_pass");
    let mut state = state_opt.unwrap_or_else(|| {
        StdState::new(
            StdRand::with_seed(current_nanos()),
            InMemoryCorpus::<NautilusInput>::new(),
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

    // Get verifier paths from environment
    let comparator_path = std::env::var("COMPARATOR_PATH")
        .expect("COMPARATOR_PATH not set in .env - please configure it");
    let safeverify_path = std::env::var("SAFEVERIFY_PATH")
        .expect("SAFEVERIFY_PATH not set in .env - please configure it");

    // Harness: unparse → write → lake build → comparator → categorize
    let mut harness = |input: &NautilusInput| -> ExitKind {
        let prefix = generate_one(&ctx, input);

        // Poisoned prefix pattern: always append a golden suffix that tries to prove False
        // This ensures every test case attempts to find a soundness bug
        let golden_suffix = "\n\n-- GOLDEN CHECK: If this succeeds, we found a soundness bug!\ntheorem soundness_check : False := by\n  simp_all\n  omega\n  decide\n";
        let code = format!("{}{}", prefix, golden_suffix);

        // Create isolated temp directory for this test case
        let temp_dir = match TempDir::new() {
            Ok(dir) => dir,
            Err(e) => {
                log::warn!("Failed to create temp dir: {e}");
                return ExitKind::Ok;
            }
        };

        // Copy template to temp (exclude .lake/ to save memory)
        let temp_template = temp_dir.path().join("template");
        let mut copy_options = CopyOptions::new();
        copy_options.copy_inside = true;

        if let Err(e) = fs_extra::dir::copy(&template_dir, temp_dir.path(), &copy_options) {
            log::warn!("Failed to copy template to temp: {e}");
            return ExitKind::Ok;
        }

        // Remove .lake/ from temp copy to save memory
        let _ = fs::remove_dir_all(temp_template.join(".lake"));

        // Write generated code to temp copy
        let temp_solution = temp_template.join("Solution.lean");
        if let Err(e) = fs::write(&temp_solution, &code) {
            log::warn!("Failed to write Solution.lean to temp: {e}");
            return ExitKind::Ok;
        }

        // Step 1: Run lake build in isolated temp directory
        let lake_result = Command::new("lake")
            .arg("build")
            .arg("Solution")
            .current_dir(&temp_template)
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .output();

        let lake_success = match lake_result {
            Ok(output) => output.status.success(),
            Err(e) => {
                log::warn!("Failed to execute lake build: {e}");
                return ExitKind::Ok;
            }
        };

        // Step 2: Run comparator (via lake env for proper environment)
        let temp_comparator_config = temp_template.join("comparator_config.json");
        let comparator_result = Command::new("lake")
            .arg("env")
            .arg(&comparator_path)
            .arg(temp_comparator_config.display().to_string())
            .current_dir(&temp_template)
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .output();

        let comparator_success = match comparator_result {
            Ok(output) => output.status.success(),
            Err(e) => {
                log::debug!("Comparator execution failed (may not have landrun on macOS): {e}");
                false
            }
        };

        // Step 3: Run SafeVerify (on .olean files)
        // First need to build .olean files if lake succeeded
        let safeverify_success = if lake_success {
            // SafeVerify expects: safe_verify Challenge.olean Solution.olean
            let challenge_olean = temp_template.join(".lake/build/lib/Challenge.olean");
            let solution_olean = temp_template.join(".lake/build/lib/Solution.olean");

            if challenge_olean.exists() && solution_olean.exists() {
                let safeverify_result = Command::new("lake")
                    .arg("env")
                    .arg(&safeverify_path)
                    .arg(challenge_olean.display().to_string())
                    .arg(solution_olean.display().to_string())
                    .current_dir(&temp_template)
                    .stdout(std::process::Stdio::piped())
                    .stderr(std::process::Stdio::piped())
                    .output();

                match safeverify_result {
                    Ok(output) => output.status.success(),
                    Err(e) => {
                        log::debug!("SafeVerify execution failed: {e}");
                        false
                    }
                }
            } else {
                false
            }
        } else {
            false
        };

        // temp_dir automatically cleaned up when dropped

        // Step 4: Categorize results (3D: Lake × Comparator × SafeVerify)
        let timestamp = current_nanos();
        let lake_str = if lake_success { "pass" } else { "fail" };
        let comp_str = if comparator_success { "pass" } else { "fail" };
        let safe_str = if safeverify_success { "pass" } else { "fail" };

        let category_dir = format!("solutions/lake_{}_comp_{}_safe_{}", lake_str, comp_str, safe_str);
        let save_path = format!("{}/result_{}.lean", category_dir, timestamp);

        // Determine significance and log appropriately
        let is_crash = match (lake_success, comparator_success, safeverify_success) {
            (true, true, true) => {
                // ULTIMATE GOLDEN SIGNAL: Passes all 3 verifiers!
                // This means SafeVerify FAILED to block an attack
                println!("\n[🎯🎯🎯] ULTIMATE GOLDEN: {}", save_path);
                println!("[🎯🎯🎯] Passes Lake + Comparator + SafeVerify!");
                println!("[🎯🎯🎯] SafeVerify failed to block this attack!");
                println!("[🎯🎯🎯] Code:\n{}", code);
                true
            }
            (true, true, false) => {
                // Kernel bug that SafeVerify correctly blocks
                println!("\n[!!!] GOLDEN (SafeVerify blocked): {}", save_path);
                println!("[!!!] Passes Lake + Comparator, SafeVerify blocks");
                true
            }
            (true, false, true) => {
                // SafeVerify passed but Comparator rejected (unusual)
                println!("\n[?!] DIVERGENCE: {}", save_path);
                println!("[?!] Lake + SafeVerify pass, Comparator fails");
                false
            }
            (true, false, false) => {
                // Lake passes but both verifiers reject
                println!("\n[*] Lake only: {}", save_path);
                false
            }
            _ => {
                // Lake failed or other combinations - normal fuzzing
                false
            }
        };

        // Save to categorized directory
        if let Err(e) = fs::write(&save_path, &code) {
            log::warn!("Failed to save to {}: {e}", save_path);
        }

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
    fuzzer.fuzz_loop(&mut stages, &mut executor, &mut state, &mut mgr)?;

    Ok(())
}
