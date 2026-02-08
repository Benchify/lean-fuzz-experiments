use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use chrono::Utc;
use clap::Parser;
use generator::{create_context, create_prefix_context, generate_one, NautilusInput};
use libafl::generators::nautilus::NautilusGenerator;
use libafl::generators::Generator;
use libafl::state::NopState;
use rayon::prelude::*;
use sha2::{Digest, Sha256};
use walkdir::WalkDir;

/// Parallel stress tester for Lean 4 grammar fuzzing.
///
/// Generates N samples sequentially, then fans out `lake build` in parallel
/// with tmpdir isolation per iteration.
#[derive(Parser)]
#[command(name = "stress", version)]
struct Cli {
    /// Number of iterations to run
    #[arg(short = 'n', long, default_value_t = 100)]
    iterations: usize,

    /// Maximum grammar tree depth
    #[arg(short, long, default_value_t = 15)]
    depth: usize,

    /// Parallel build jobs (0 = all cores)
    #[arg(short, long, default_value_t = 0)]
    jobs: usize,

    /// Timeout per `lake build` in seconds
    #[arg(long, default_value_t = 120)]
    timeout: u64,

    /// Use prefix-only grammar (no proof terms/tactics, theorems use sorry)
    #[arg(long, default_value_t = true)]
    prefix_only: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IterResult {
    Ok,
    Fail,
    Golden,
}

impl fmt::Display for IterResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IterResult::Ok => write!(f, "ok"),
            IterResult::Fail => write!(f, "FAIL"),
            IterResult::Golden => write!(f, "GOLDEN"),
        }
    }
}

// Global counters for progress reporting
static DONE_COUNT: AtomicUsize = AtomicUsize::new(0);

fn main() {
    let cli = Cli::parse();

    // Resolve monorepo root: walk up from the executable's dir looking for template/
    let monorepo = find_monorepo_root().unwrap_or_else(|| {
        eprintln!("error: could not find monorepo root (need template/ directory)");
        std::process::exit(1);
    });
    let template_dir = monorepo.join("template");
    let failures_dir = monorepo.join("artifacts/generator-failures");
    let golden_dir = monorepo.join("artifacts/golden-signals");

    fs::create_dir_all(&failures_dir).expect("failed to create failures dir");
    fs::create_dir_all(&golden_dir).expect("failed to create golden dir");

    // Configure rayon thread pool
    if cli.jobs > 0 {
        rayon::ThreadPoolBuilder::new()
            .num_threads(cli.jobs)
            .build_global()
            .expect("failed to configure rayon thread pool");
    }

    let effective_jobs = if cli.jobs == 0 {
        rayon::current_num_threads()
    } else {
        cli.jobs
    };

    println!("[stress] Lean 4 parallel stress tester");
    println!(
        "[stress] iterations={} depth={} jobs={} timeout={}s",
        cli.iterations, cli.depth, effective_jobs, cli.timeout
    );
    println!("[stress] template: {}", template_dir.display());
    println!("[stress] failures: {}", failures_dir.display());

    // Phase 1: Generate all samples sequentially
    println!("[stress] Generating {} samples... (prefix_only={})", cli.iterations, cli.prefix_only);
    let ctx = if cli.prefix_only {
        create_prefix_context(cli.depth)
    } else {
        create_context(cli.depth)
    };
    let mut generator = NautilusGenerator::new(&ctx);
    let mut state: NopState<NautilusInput> = NopState::new();

    let samples: Vec<String> = (0..cli.iterations)
        .map(|_| {
            let input = generator.generate(&mut state).expect("generation failed");
            generate_one(&ctx, &input)
        })
        .collect();
    println!("[stress] Generation complete, starting builds...");

    // Phase 2: Build in parallel
    let timeout = Duration::from_secs(cli.timeout);
    let total = samples.len();

    let results: Vec<IterResult> = samples
        .par_iter()
        .map(|code| {
            let result =
                run_one(&template_dir, code, &failures_dir, &golden_dir, timeout);
            let done = DONE_COUNT.fetch_add(1, Ordering::Relaxed) + 1;
            if done.is_multiple_of(10) || done == total {
                eprintln!("[stress] progress: {done}/{total}");
            }
            result
        })
        .collect();

    // Summary
    let ok_count = results.iter().filter(|r| **r == IterResult::Ok).count();
    let fail_count = results.iter().filter(|r| **r == IterResult::Fail).count();
    let golden_count = results.iter().filter(|r| **r == IterResult::Golden).count();

    println!();
    println!("[stress] === Results ===");
    println!("[stress] total:  {total}");
    println!("[stress] ok:     {ok_count}");
    println!("[stress] fail:   {fail_count}");
    println!("[stress] golden: {golden_count}");

    if golden_count > 0 {
        println!("[stress] !!! GOLDEN SIGNALS FOUND — check {}", golden_dir.display());
    }
}

fn run_one(
    template_dir: &Path,
    code: &str,
    failures_dir: &Path,
    golden_dir: &Path,
    timeout: Duration,
) -> IterResult {
    // Create isolated tmpdir
    let tmpdir = match tempfile::tempdir() {
        Ok(d) => d,
        Err(e) => {
            eprintln!("[stress] failed to create tmpdir: {e}");
            return IterResult::Fail;
        }
    };
    let project_dir = tmpdir.path().join("project");

    // Copy template (excluding .lake/)
    if let Err(e) = copy_template(template_dir, &project_dir) {
        eprintln!("[stress] failed to copy template: {e}");
        return IterResult::Fail;
    }

    // Inject generated code
    let target_file = project_dir.join("Template/Basic.lean");
    if let Err(e) = fs::write(&target_file, code) {
        eprintln!("[stress] failed to write Basic.lean: {e}");
        return IterResult::Fail;
    }

    // Run lake build with timeout
    let mut child = match Command::new("lake")
        .arg("build")
        .current_dir(&project_dir)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(c) => c,
        Err(e) => {
            eprintln!("[stress] failed to spawn lake: {e}");
            return IterResult::Fail;
        }
    };

    let start = Instant::now();
    let status = loop {
        match child.try_wait() {
            Ok(Some(s)) => break Some(s),
            Ok(None) => {
                if start.elapsed() > timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    break None;
                }
                std::thread::sleep(Duration::from_millis(100));
            }
            Err(e) => {
                eprintln!("[stress] wait error: {e}");
                let _ = child.kill();
                break None;
            }
        }
    };

    let Some(status) = status else {
        // Timeout — treat as failure, save artifact
        save_artifact(code, failures_dir, "timeout");
        return IterResult::Fail;
    };

    if status.success() {
        // Build succeeded — check for sorry in stderr
        let stderr = child
            .stderr
            .take()
            .and_then(|mut s| {
                let mut buf = String::new();
                std::io::Read::read_to_string(&mut s, &mut buf).ok()?;
                Some(buf)
            })
            .unwrap_or_default();

        if stderr.contains("sorry") {
            // sorry-dependent proof — not a real golden signal
            return IterResult::Ok;
        }

        // Golden signal!
        save_artifact(code, golden_dir, "golden");
        IterResult::Golden
    } else {
        // Build failed — normal case, save the failure
        save_artifact(code, failures_dir, "fail");
        IterResult::Fail
    }
}

fn copy_template(src: &Path, dest: &Path) -> std::io::Result<()> {
    for entry in WalkDir::new(src).into_iter().filter_entry(|e| {
        // Skip .lake directories
        !e.path()
            .components()
            .any(|c| c.as_os_str() == ".lake")
    }) {
        let entry = entry.map_err(std::io::Error::other)?;
        let relative = entry
            .path()
            .strip_prefix(src)
            .map_err(std::io::Error::other)?;
        let target = dest.join(relative);

        if entry.file_type().is_dir() {
            fs::create_dir_all(&target)?;
        } else {
            if let Some(parent) = target.parent() {
                fs::create_dir_all(parent)?;
            }
            fs::copy(entry.path(), &target)?;
        }
    }
    Ok(())
}

fn save_artifact(code: &str, dir: &Path, prefix: &str) -> PathBuf {
    let now = Utc::now();
    let timestamp = now.format("%Y%m%d_%H%M%S");

    let mut hasher = Sha256::new();
    hasher.update(code.as_bytes());
    let hash_bytes = hasher.finalize();
    // Manual hex for first 6 bytes (12 hex chars)
    let hash_hex: String = hash_bytes[..6]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();

    let filename = format!("{prefix}_{timestamp}_{hash_hex}.lean");
    let path = dir.join(&filename);

    if let Err(e) = fs::write(&path, code) {
        eprintln!("[stress] failed to save artifact {filename}: {e}");
    }

    path
}

fn find_monorepo_root() -> Option<PathBuf> {
    // Start from current working directory
    let mut dir = std::env::current_dir().ok()?;
    loop {
        if dir.join("template").is_dir() && dir.join("CLAUDE.md").is_file() {
            return Some(dir);
        }
        if !dir.pop() {
            return None;
        }
    }
}
