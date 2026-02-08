"""CLI for the Poisoned Prefix Fuzzer.

Commands:
    fuzz        — Generate prefixes and test against golden suffixes.
    init-pool   — Create template pool without running tests.
    test-prefix — Test a single .lean file against golden suffixes.
"""

import hashlib
import logging
import subprocess
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import UTC, datetime
from pathlib import Path

import typer

from scaffold.executor import (
    MONOREPO,
    PrefixResult,
    TemplatePool,
    execute_prefix,
    find_gen_sample,
    run_gen_sample,
)
from scaffold.golden_suffixes import SUFFIX_BY_NAME
from scaffold.oracle import Verdict

app = typer.Typer(help="Poisoned Prefix Fuzzer for Lean 4 soundness testing.")

DEFAULT_POOL_DIR = MONOREPO / "artifacts" / "pool"
GOLDEN_SIGNALS_DIR = MONOREPO / "artifacts" / "golden-signals"


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
    verbose: bool = typer.Option(False, "--verbose", "-v"),
) -> None:
    """Test a single .lean file against golden suffixes."""
    _setup_logging(verbose)

    prefix = lean_file.read_text()
    typer.echo(f"Testing prefix from {lean_file} ({len(prefix)} chars)")

    pool = TemplatePool(pool_dir=pool_dir, pool_size=pool_size)
    pool.initialize()

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
    verbose: bool = typer.Option(False, "--verbose", "-v"),
) -> None:
    """Generate prefixes via gen-sample and test against golden suffixes."""
    _setup_logging(verbose)

    gen_sample_bin = find_gen_sample()
    typer.echo(f"Using gen-sample: {gen_sample_bin}")

    pool = TemplatePool(pool_dir=pool_dir, pool_size=pool_size)
    pool.initialize()
    typer.echo(f"Pool ready: {pool_size} slots at {pool_dir}")

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


def main() -> None:
    """Entry point for the scaffold CLI."""
    app()
