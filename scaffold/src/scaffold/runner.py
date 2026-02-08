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
    verbose: bool = typer.Option(False, "--verbose", "-v"),
) -> None:
    """Generate prefixes via gen-sample and test against golden suffixes."""
    _setup_logging(verbose)

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
    tier_0_prefixes: list[tuple[str, str]] = []  # (prefix_hash, prefix_code) for near-misses

    # Generate all prefixes upfront.
    typer.echo(f"Generating {iterations} prefixes (depth={depth})...")
    prefixes: list[str] = []
    gen_failures = 0
    for _ in range(iterations):
        try:
            prefixes.append(run_gen_sample(gen_sample_bin, depth))
        except RuntimeError:
            gen_failures += 1
        except subprocess.TimeoutExpired:
            gen_failures += 1

    if gen_failures:
        typer.echo(f"  ({gen_failures} generation failures, testing {len(prefixes)})")

    # Test prefixes in parallel across pool slots.
    stats = {"golden": 0, "false_positive": 0, "build_failed": 0, "timeout": 0}

    def _test_one(idx: int, prefix: str) -> tuple[int, PrefixResult]:
        return idx, execute_prefix(prefix, pool, timeout=timeout)

    with ThreadPoolExecutor(max_workers=pool_size) as executor:
        futures = {executor.submit(_test_one, i, p): i for i, p in enumerate(prefixes)}
        for future in as_completed(futures):
            idx, result = future.result()

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

    if campaign_dir:
        typer.echo(f"\n📁 Campaign artifacts in {campaign_dir}")


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
