use std::path::PathBuf;
use std::process::Command;
use std::fs;

use clap::Parser;
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

use generator::{create_context, generate_one};

/// Path to the template Lean project (relative to generator crate root).
const TEMPLATE_DIR: &str = "../template";
/// File within the template project where generated code is injected.
const TARGET_FILE: &str = "../template/Template/Basic.lean";

/// Lean 4 Grammar Fuzzer (Nautilus)
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Maximum tree depth for grammar generation
    #[arg(short, long, default_value_t = 15)]
    depth: usize,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();
    let args = Args::parse();

    let template_dir = PathBuf::from(TEMPLATE_DIR)
        .canonicalize()
        .unwrap_or_else(|_| {
            eprintln!("warning: template dir not found at {TEMPLATE_DIR}, using relative path");
            PathBuf::from(TEMPLATE_DIR)
        });
    let target_file = PathBuf::from(TARGET_FILE)
        .canonicalize()
        .unwrap_or_else(|_| PathBuf::from(TARGET_FILE));
    let template_dir_str = template_dir.display().to_string();

    println!("[*] Lean 4 Grammar Fuzzer (Nautilus)");
    println!("[*] Template dir: {}", template_dir.display());
    println!("[*] Target file:  {}", target_file.display());
    println!("[*] Tree depth:   {}", args.depth);

    // Build the Nautilus grammar context
    let ctx = create_context(args.depth);
    println!(
        "[*] Grammar loaded: {} rules",
        generator::grammar::lean4_rules().len()
    );

    // Output directories
    let solutions_dir = PathBuf::from("solutions");
    fs::create_dir_all(&solutions_dir)?;

    // Monitor: prints stats to stdout
    let monitor = SimpleMonitor::new(|s| println!("{s}"));
    let mut mgr = SimpleEventManager::new(monitor);

    // Feedbacks
    let mut nautilus_feedback = NautilusFeedback::new(&ctx);
    let mut crash_feedback = CrashFeedback::new();

    // State
    let mut state = StdState::new(
        StdRand::with_seed(current_nanos()),
        InMemoryCorpus::<NautilusInput>::new(),
        OnDiskCorpus::new(&solutions_dir)?,
        &mut nautilus_feedback,
        &mut crash_feedback,
    )?;

    // Register Nautilus chunk metadata (required by NautilusFeedback and splice mutator)
    state.add_metadata(NautilusChunksMetadata::new("workdir".to_string()));

    // Scheduler
    let scheduler = QueueScheduler::new();

    // Fuzzer
    let mut fuzzer = StdFuzzer::new(scheduler, nautilus_feedback, crash_feedback);

    // Harness: unparse → write → lake build → check
    let mut harness = |input: &NautilusInput| -> ExitKind {
        let code = generate_one(&ctx, input);

        // Write generated code to template
        if let Err(e) = fs::write(&target_file, &code) {
            log::warn!("Failed to write target file: {e}");
            return ExitKind::Ok;
        }

        // Run lake build
        let build_result = Command::new("lake")
            .arg("build")
            .current_dir(&template_dir_str)
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .output();

        match build_result {
            Ok(output) => {
                if output.status.success() {
                    // Build succeeded — check for golden signal
                    let stderr = String::from_utf8_lossy(&output.stderr);
                    if !stderr.contains("sorry") {
                        // Potential golden signal! Save the code.
                        let timestamp = current_nanos();
                        let save_path = format!("solutions/golden_{timestamp}.lean");
                        if let Err(e) = fs::write(&save_path, &code) {
                            log::warn!("Failed to save golden candidate: {e}");
                        } else {
                            println!("\n[!!!] GOLDEN SIGNAL CANDIDATE: {save_path}");
                            println!("[!!!] Code:\n{code}");
                        }
                        // Report as crash to trigger objective feedback
                        return ExitKind::Crash;
                    }
                    ExitKind::Ok
                } else {
                    // Build failed — normal case for most generated code
                    ExitKind::Ok
                }
            }
            Err(e) => {
                log::warn!("Failed to execute lake build: {e}");
                ExitKind::Ok
            }
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

    // Generate initial corpus
    println!("[*] Generating initial corpus...");
    state.generate_initial_inputs_forced(
        &mut fuzzer,
        &mut executor,
        &mut generator,
        &mut mgr,
        8, // 8 initial seeds
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
