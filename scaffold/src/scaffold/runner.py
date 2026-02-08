"""CLI for the Poisoned Prefix Fuzzer.

Commands:
    fuzz        — Generate prefixes and test against golden suffixes.
    init-pool   — Create template pool without running tests.
    test-prefix — Test a single .lean file against golden suffixes.
"""

import hashlib
import logging
import subprocess
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import UTC, datetime
from pathlib import Path

import typer

from scaffold.campaign_report import generate_campaign_summary
from scaffold.corpus_tier import classify_tier, save_to_tier
from scaffold.diagnostic_log import DiagnosticLogger
from scaffold.diagnostics import summary_categories
from scaffold.executor import (
    MONOREPO,
    TemplatePool,
    execute_prefix,
    find_gen_sample,
    run_gen_sample,
)
from scaffold.golden_suffixes import SUFFIX_BY_NAME
from scaffold.models import ErrorCategory, PrefixResult, Verdict

app = typer.Typer(help="Poisoned Prefix Fuzzer for Lean 4 soundness testing.")

DEFAULT_POOL_DIR = MONOREPO / "artifacts" / "pool"
GOLDEN_SIGNALS_DIR = MONOREPO / "artifacts" / "golden-signals"


def _parse_duration(duration_str: str) -> int:
    """Parse duration string to seconds.

    Supports: '8h', '30m', '45s', '2h30m', '1h30m45s'
    """
    import re
    total_seconds = 0

    # Parse hours
    if 'h' in duration_str:
        match = re.search(r'(\d+)h', duration_str)
        if match:
            total_seconds += int(match.group(1)) * 3600

    # Parse minutes
    if 'm' in duration_str:
        match = re.search(r'(\d+)m', duration_str)
        if match:
            total_seconds += int(match.group(1)) * 60

    # Parse seconds
    if 's' in duration_str and 'h' not in duration_str and 'm' not in duration_str:
        match = re.search(r'(\d+)s', duration_str)
        if match:
            total_seconds += int(match.group(1))

    return total_seconds or 3600  # Default 1h if parse fails


def _save_checkpoint(
    campaign_dir: Path | None,
    diag_logger,
    tier_counts: Counter[str],
    tier_0_prefixes: list[tuple[str, str]],
    checkpoint_num: int,
) -> None:
    """Save intermediate checkpoint during long campaigns."""
    if not campaign_dir or not diag_logger:
        return

    checkpoint_dir = campaign_dir / "checkpoints"
    checkpoint_dir.mkdir(exist_ok=True)

    # Save intermediate summary
    summary = generate_campaign_summary(diag_logger.log_path)
    checkpoint_path = checkpoint_dir / f"checkpoint_{checkpoint_num:04d}.md"
    checkpoint_path.write_text(summary)

    # Save tier stats
    tier_stats = "\n".join(f"{tier}: {count}" for tier, count in tier_counts.items())
    (checkpoint_dir / f"tiers_{checkpoint_num:04d}.txt").write_text(tier_stats)


def _generate_near_misses(tier_0_prefixes: list[tuple[str, str]]) -> str:
    """Generate a near-misses report from Tier 0 prefixes.

    Args:
        tier_0_prefixes: List of (hash, prefix_code) tuples

    Returns:
        Markdown report of most interesting near-misses
    """
    lines = [
        "# Near-Misses Report",
        "",
        "Tier 0 prefixes that compiled successfully but failed to prove False.",
        "These are the CLOSEST to finding a soundness bug!",
        "",
        f"Total Tier 0 prefixes: {len(tier_0_prefixes)}",
        "",
    ]

    for i, (prefix_hash, prefix_code) in enumerate(tier_0_prefixes, 1):
        lines.extend([
            f"## Near-Miss #{i} - `{prefix_hash}`",
            "",
            "```lean",
            prefix_code.strip(),
            "```",
            "",
            "**Why interesting:** Prefix compiled cleanly. Golden suffix failed with",
            "'proof not found' - meaning the environment is valid but automation",
            "couldn't find a path to False. One mutation away from a potential bug!",
            "",
            "---",
            "",
        ])

    return "\n".join(lines)


def _save_golden(prefix: str, result: PrefixResult) -> Path:
    """Persist a golden signal to disk."""
    GOLDEN_SIGNALS_DIR.mkdir(parents=True, exist_ok=True)
    ts = datetime.now(tz=UTC).strftime("%Y%m%d_%H%M%S")
    h = hashlib.sha256(prefix.encode()).hexdigest()[:12]
    path = GOLDEN_SIGNALS_DIR / f"{ts}_{h}.lean"
    # Include metadata as a comment header.
    golden_suffixes = [
        r.suffix_name for r in result.results if r.verdict == Verdict.GOLDEN
    ]
    header = (
        f"-- GOLDEN SIGNAL\n"
        f"-- Timestamp: {ts}\n"
        f"-- Suffixes: {', '.join(golden_suffixes)}\n"
        f"-- Axioms: {result.results[0].axioms if result.results else []}\n"
        f"--\n"
    )
    path.write_text(header + prefix)
    return path


def _setup_logging(verbose: bool) -> None:
    level = logging.DEBUG if verbose else logging.INFO
    logging.basicConfig(
        level=level,
        format="%(asctime)s %(levelname)-8s %(name)s: %(message)s",
        datefmt="%H:%M:%S",
    )


@app.command()
def init_pool(
    pool_size: int = typer.Option(8, help="Number of template pool slots."),
    pool_dir: Path = typer.Option(DEFAULT_POOL_DIR, help="Pool directory."),
    verbose: bool = typer.Option(False, "--verbose", "-v"),
) -> None:
    """Create template pool without running tests (pre-warm cache)."""
    _setup_logging(verbose)
    pool = TemplatePool(pool_dir=pool_dir, pool_size=pool_size)
    pool.initialize()
    typer.echo(f"Initialized {pool_size} pool slots at {pool_dir}")


@app.command()
def test_prefix(
    lean_file: Path = typer.Argument(help="Path to a .lean file to use as prefix."),
    suffix: str | None = typer.Option(
        None, help="Test a single suffix by name (e.g. 'trivial'). Default: all."
    ),
    pool_size: int = typer.Option(2, help="Number of template pool slots."),
    pool_dir: Path = typer.Option(DEFAULT_POOL_DIR, help="Pool directory."),
    timeout: int = typer.Option(120, help="Build timeout per suffix (seconds)."),
    diagnostics: bool = typer.Option(True, help="Enable diagnostic logging."),
    verbose: bool = typer.Option(False, "--verbose", "-v"),
) -> None:
    """Test a single .lean file against golden suffixes."""
    _setup_logging(verbose)

    prefix = lean_file.read_text()
    typer.echo(f"Testing prefix from {lean_file} ({len(prefix)} chars)")

    pool = TemplatePool(pool_dir=pool_dir, pool_size=pool_size)
    pool.initialize()

    diag_logger = DiagnosticLogger() if diagnostics else None

    suffixes = None
    if suffix:
        if suffix not in SUFFIX_BY_NAME:
            typer.echo(
                f"Unknown suffix '{suffix}'. Available: {', '.join(SUFFIX_BY_NAME)}",
                err=True,
            )
            raise SystemExit(1)
        suffixes = [SUFFIX_BY_NAME[suffix]]

    result = execute_prefix(prefix, pool, timeout=timeout, suffixes=suffixes)

    for r in result.results:
        icon = {
            Verdict.GOLDEN: "!!!",
            Verdict.FALSE_POSITIVE: "FP ",
            Verdict.BUILD_FAILED: "  X",
            Verdict.TIMEOUT: " TO",
        }[r.verdict]
        typer.echo(f"  [{icon}] {r.suffix_name:15s} — {r.reason}")
        if r.axioms:
            typer.echo(f"        axioms: {r.axioms}")
        if r.diagnostics and verbose:
            for d in r.diagnostics:
                typer.echo(f"        L{d.line}:{d.column} [{d.category}] {d.message}")

        if diag_logger:
            diag_logger.log(prefix, r)

    if diag_logger:
        typer.echo(f"\nDiagnostics logged to {diag_logger.log_path}")

    if result.has_golden:
        saved = _save_golden(prefix, result)
        typer.echo(f"\nGOLDEN SIGNAL saved to {saved}")
    elif result.has_false_positive:
        typer.echo("\nFalse positive(s) detected — escape hatches in prefix.")
    else:
        typer.echo("\nNo golden signals (expected for benign prefixes).")


@app.command()
def fuzz(
    iterations: int = typer.Option(100, help="Number of prefixes to generate."),
    depth: int = typer.Option(15, help="Nautilus tree depth for gen-sample."),
    pool_size: int = typer.Option(8, help="Number of parallel pool slots."),
    pool_dir: Path = typer.Option(DEFAULT_POOL_DIR, help="Pool directory."),
    timeout: int = typer.Option(120, help="Build timeout per suffix (seconds)."),
    diagnostics: bool = typer.Option(True, help="Enable diagnostic logging."),
    corpus: bool = typer.Option(True, help="Save tiered corpus for reuse."),
    campaign: str | None = typer.Option(None, help="Campaign name for organized artifacts."),
    duration: str | None = typer.Option(None, help="Duration limit (e.g., '8h', '30m', '2h30m')."),
    checkpoint_every: int = typer.Option(100, help="Save checkpoint every N prefixes."),
    verbose: bool = typer.Option(False, "--verbose", "-v"),
) -> None:
    """Generate prefixes via gen-sample and test against golden suffixes."""
    import signal
    import time

    # Setup graceful shutdown on Ctrl+C
    shutdown_flag = {"triggered": False}
    tier_counts_ref = None  # Will be set later for signal handler access

    def signal_handler(sig, frame):
        if not shutdown_flag["triggered"]:
            shutdown_flag["triggered"] = True
            typer.echo("\n\n⚠️  Ctrl+C detected - saving reports...")
            # Print tier distribution if available
            if tier_counts_ref:
                typer.echo("\n📊 Current tier distribution:")
                for tier_name in ["tier-0", "tier-1", "tier-2", "discard"]:
                    count = tier_counts_ref.get(tier_name, 0)
                    if count > 0:
                        icon = "🎯" if tier_name == "tier-0" else ""
                        typer.echo(f"   {tier_name:10s} {count:4d} {icon}")
            typer.echo("\n   Finishing up... (Press Ctrl+C again to force quit)")
        else:
            typer.echo("\n\n🛑 Force quit")
            raise typer.Exit(1)

    signal.signal(signal.SIGINT, signal_handler)

    _setup_logging(verbose)

    # Parse duration if provided
    end_time = None
    if duration:
        duration_seconds = _parse_duration(duration)
        end_time = time.time() + duration_seconds
        typer.echo(f"Duration limit: {duration} ({duration_seconds}s)")

    gen_sample_bin = find_gen_sample()
    typer.echo(f"Using gen-sample: {gen_sample_bin}")

    pool = TemplatePool(pool_dir=pool_dir, pool_size=pool_size)
    pool.initialize()
    typer.echo(f"Pool ready: {pool_size} slots at {pool_dir}")

    # Setup campaign directory if named
    if campaign:
        campaign_dir = MONOREPO / "artifacts" / "campaigns" / campaign
        campaign_dir.mkdir(parents=True, exist_ok=True)
        session_id = campaign
    else:
        campaign_dir = None
        session_id = None

    diag_logger = DiagnosticLogger(session_id=session_id) if diagnostics else None
    error_counter: Counter[ErrorCategory] = Counter()
    corpus_dir = (campaign_dir / "corpus" if campaign_dir else MONOREPO / "artifacts" / "corpus") if corpus else None
    tier_counts: Counter[str] = Counter()
    tier_counts_ref = tier_counts  # Make available to signal handler
    tier_0_prefixes: list[tuple[str, str]] = []  # (prefix_hash, prefix_code) for near-misses

    # Generate prefixes incrementally (allows duration limits and checkpoints)
    typer.echo(f"Generating up to {iterations} prefixes (depth={depth})...")
    prefixes: list[str] = []
    gen_failures = 0
    checkpoint_count = 0

    for i in range(iterations):
        # Check duration limit
        if end_time and time.time() >= end_time:
            typer.echo(f"\n⏱️  Duration limit reached. Generated {len(prefixes)} prefixes.")
            break

        try:
            prefixes.append(run_gen_sample(gen_sample_bin, depth))
        except (RuntimeError, subprocess.TimeoutExpired):
            gen_failures += 1

    if gen_failures:
        typer.echo(f"  ({gen_failures} generation failures, testing {len(prefixes)})")

    # Test prefixes in parallel across pool slots.
    stats = {"golden": 0, "false_positive": 0, "build_failed": 0, "timeout": 0}
    tested_count = 0
    novel_errors: set[str] = set()  # Track unknown error patterns
    longest_surviving = {"prefix": "", "stage": 0, "hash": ""}  # Track furthest prefix

    def _test_one(idx: int, prefix: str) -> tuple[int, PrefixResult]:
        return idx, execute_prefix(prefix, pool, timeout=timeout)

    with ThreadPoolExecutor(max_workers=pool_size) as executor:
        futures = {executor.submit(_test_one, i, p): i for i, p in enumerate(prefixes)}
        for future in as_completed(futures):
            # Check for Ctrl+C
            if shutdown_flag["triggered"]:
                typer.echo("\n📊 Saving reports before exit...")
                break

            idx, result = future.result()
            tested_count += 1

            # Log diagnostics for every suffix result.
            for r in result.results:
                if diag_logger:
                    diag_logger.log(result.prefix, r)
                for cat in summary_categories(r.diagnostics):
                    error_counter[cat] += 1

                # Classify into corpus tier (use first result for classification)
                if corpus_dir and r == result.results[0]:
                    from hashlib import sha256
                    prefix_hash = sha256(result.prefix.encode()).hexdigest()[:12]
                    tier = classify_tier(r)
                    tier_counts[tier.value] += 1
                    if tier.value != "discard":
                        save_to_tier(result.prefix, tier, prefix_hash, corpus_dir)
                    # Track Tier 0 for near-misses report
                    if tier.value == "tier-0":
                        tier_0_prefixes.append((prefix_hash, result.prefix))

                # Track novel error patterns (not in known categories)
                if not r.diagnostics and r.verdict == Verdict.BUILD_FAILED:
                    # Extract unique error patterns from raw stderr
                    error_lines = [line for line in r.raw_stderr.split('\n') if 'error:' in line.lower()]
                    for error_line in error_lines[:3]:  # First 3 errors
                        novel_errors.add(error_line[:100])

            # Periodic checkpoint
            if checkpoint_every > 0 and tested_count % checkpoint_every == 0:
                checkpoint_count += 1
                _save_checkpoint(campaign_dir, diag_logger, tier_counts, tier_0_prefixes, checkpoint_count)
                typer.echo(f"\n💾 Checkpoint {checkpoint_count} saved ({tested_count} tested)")

            # Check duration limit after each test
            if end_time and time.time() >= end_time:
                typer.echo(f"\n⏱️  Duration limit reached. Tested {tested_count}/{len(prefixes)} prefixes.")
                break

            if result.has_golden:
                stats["golden"] += 1
                saved = _save_golden(result.prefix, result)
                typer.echo(f"  [{idx:4d}] !!! GOLDEN -> {saved.name}")
            elif result.has_false_positive:
                stats["false_positive"] += 1
                typer.echo(f"  [{idx:4d}] FP  (escape hatches)")
            else:
                # Count worst verdict across suffixes.
                timeouts = sum(
                    1 for r in result.results if r.verdict == Verdict.TIMEOUT
                )
                if timeouts == len(result.results):
                    stats["timeout"] += 1
                    typer.echo(f"  [{idx:4d}] TO  (all timed out)")
                else:
                    stats["build_failed"] += 1
                    typer.echo(f"  [{idx:4d}]  X  (build failed)")

    typer.echo(
        f"\nDone: {len(prefixes)} prefixes tested"
        f" | golden={stats['golden']}"
        f" | false_positive={stats['false_positive']}"
        f" | build_failed={stats['build_failed']}"
        f" | timeout={stats['timeout']}"
        f" | gen_failures={gen_failures}"
    )

    if error_counter:
        typer.echo("\nError category distribution:")
        for cat, count in error_counter.most_common():
            typer.echo(f"  {cat.value:25s} {count}")

    # Generate campaign artifacts
    if diag_logger:
        typer.echo(f"\nDiagnostics logged to {diag_logger.log_path}")

        # Generate and save campaign summary
        summary = generate_campaign_summary(diag_logger.log_path)
        if campaign_dir:
            summary_path = campaign_dir / "summary.md"
        else:
            summary_path = diag_logger.log_path.with_suffix('.md')
        summary_path.write_text(summary)
        typer.echo(f"Campaign summary saved to {summary_path}")

    # Generate near-misses report (Tier 0 prefixes that almost worked)
    if tier_0_prefixes:
        near_misses = _generate_near_misses(tier_0_prefixes[:10])  # Top 10
        if campaign_dir:
            near_misses_path = campaign_dir / "near-misses.md"
        else:
            near_misses_path = MONOREPO / "artifacts" / "near-misses.md"
        near_misses_path.write_text(near_misses)
        typer.echo(f"Near-misses report saved to {near_misses_path}")

    # Report novel error patterns
    if novel_errors:
        typer.echo(f"\n🔍 Novel error patterns detected: {len(novel_errors)}")
        if campaign_dir:
            novel_path = campaign_dir / "novel-errors.txt"
            novel_path.write_text("\n".join(sorted(novel_errors)))
            typer.echo(f"   Saved to {novel_path}")

    # Print tier distribution
    if tier_counts:
        typer.echo("\nCorpus tier distribution:")
        for tier_name in ["tier-0", "tier-1", "tier-2", "discard"]:
            count = tier_counts[tier_name]
            if count > 0:
                icon = "🎯" if tier_name == "tier-0" else ""
                typer.echo(f"  {tier_name:10s} {count:4d} {icon}")
        if corpus_dir:
            typer.echo(f"\nTiered corpus saved to {corpus_dir}")

    # Show where to find results
    typer.echo(f"\n{'='*60}")
    typer.echo(f"📁 CAMPAIGN RESULTS")
    typer.echo(f"{'='*60}")

    if campaign_dir:
        typer.echo(f"\n📂 Campaign directory: {campaign_dir}")
        typer.echo(f"   ├── summary.md       (overview and statistics)")
        typer.echo(f"   ├── near-misses.md   (top Tier 0 prefixes)")
        typer.echo(f"   ├── corpus/tier-*/   (tiered prefix corpus)")
        if checkpoint_count > 0:
            typer.echo(f"   ├── checkpoints/     ({checkpoint_count} saved)")
        if diag_logger:
            typer.echo(f"   └── {diag_logger.log_path.name}  (raw diagnostic log)")
    elif diag_logger:
        typer.echo(f"\n📄 Diagnostics: {diag_logger.log_path}")
        summary_path = diag_logger.log_path.with_suffix('.md')
        typer.echo(f"📄 Summary: {summary_path}")

    typer.echo(f"\n{'='*60}")


@app.command()
def report(
    log_file: Path = typer.Argument(..., help="Path to diagnostic .jsonl log file"),
    output: Path | None = typer.Option(None, "--output", "-o", help="Save summary to file (default: print to stdout)"),
) -> None:
    """Generate campaign summary report from diagnostic log.

    Args:
        log_file: Path to the diagnostic JSONL log
        output: Optional output file for summary (prints to stdout if not specified)
    """
    if not log_file.exists():
        typer.echo(f"Error: Log file not found: {log_file}", err=True)
        raise typer.Exit(1)

    typer.echo(f"Generating summary from {log_file}...")
    summary = generate_campaign_summary(log_file)

    if output:
        output.write_text(summary)
        typer.echo(f"Summary saved to {output}")
    else:
        typer.echo("\n" + summary)


def main() -> None:
    """Entry point for the scaffold CLI."""
    app()
