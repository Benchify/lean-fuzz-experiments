"""Stress-test the Lean grammar generator.

Generates random Lean code via gen-sample, injects into a template project,
runs lake build, and persists failures to artifacts/stress_gen/.
"""

import hashlib
import shutil
import subprocess
import sys
import tempfile
from datetime import UTC, datetime
from pathlib import Path

import typer
from pydantic import BaseModel

MONOREPO = Path(__file__).resolve().parents[3]


class StressResult(BaseModel):
    """Result of a single stress-test iteration."""

    code: str
    exit_code: int
    stderr: str
    timestamp: str


GENERATOR_DIR = MONOREPO / "generator"


def run_gen_sample(depth: int, *, prefix_only: bool = True) -> str:
    """Generate a Lean code sample via ``cargo run --bin gen_sample``."""
    cmd = ["cargo", "run", "--bin", "gen_sample", "--"]
    if prefix_only:
        cmd.append("--prefix-only")
    cmd.append(str(depth))
    result = subprocess.run(
        cmd,
        cwd=str(GENERATOR_DIR),
        capture_output=True,
        text=True,
        timeout=60,
    )
    if result.returncode != 0:
        typer.echo(f"gen_sample failed: {result.stderr}", err=True)
        raise SystemExit(1)
    return result.stdout


def run_lake_build(project_dir: Path) -> tuple[int, str]:
    """Run lake build in project_dir, return (exit_code, stderr)."""
    result = subprocess.run(
        ["lake", "build"],
        cwd=str(project_dir),
        capture_output=True,
        text=True,
        timeout=120,
    )
    return result.returncode, result.stderr


def save_failure(code: str, artifacts_dir: Path) -> Path:
    """Save failing Lean code to artifacts_dir with timestamp+hash filename."""
    ts = datetime.now(tz=UTC).strftime("%Y%m%d_%H%M%S")
    h = hashlib.sha256(code.encode()).hexdigest()[:12]
    path = artifacts_dir / f"{ts}_{h}.lean"
    path.write_text(code)
    return path


def _main(
    iterations: int = typer.Option(100, help="Number of iterations to run."),
    depth: int = typer.Option(15, help="Nautilus tree depth for generation."),
) -> None:
    """Stress-test the Lean grammar generator."""
    template_dir = MONOREPO / "template"
    artifacts_dir = MONOREPO / "artifacts" / "stress_gen"
    artifacts_dir.mkdir(parents=True, exist_ok=True)

    ok_count = 0
    fail_count = 0

    for i in range(iterations):
        with tempfile.TemporaryDirectory() as tmpdir:
            project_dir = Path(tmpdir) / "project"
            shutil.copytree(
                template_dir,
                project_dir,
                ignore=shutil.ignore_patterns(".lake"),
            )

            code = run_gen_sample(depth)
            (project_dir / "Template" / "Basic.lean").write_text(code)

            exit_code, _stderr = run_lake_build(project_dir)

            if exit_code != 0:
                fail_count += 1
                saved = save_failure(code, artifacts_dir)
                typer.echo(f"  [{i}] FAIL -> {saved.name}")
            else:
                ok_count += 1
                typer.echo(f"  [{i}] OK")

    typer.echo(f"\nDone: {ok_count} ok, {fail_count} failures out of {iterations}")
    if fail_count > 0:
        typer.echo(f"Failures saved to {artifacts_dir}")
    sys.exit(1 if fail_count == iterations else 0)


def main() -> None:
    """Entry point for the stress-gen CLI."""
    typer.run(_main)
