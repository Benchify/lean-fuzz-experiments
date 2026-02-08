"""Core execution engine: template pool, assembly, and prefix testing.

Manages a pool of pre-copied template projects for parallel testing.
Each prefix is assembled with golden suffixes and run through `lake build`.
"""

import logging
import re
import shutil
import subprocess
from pathlib import Path
from queue import Empty, Queue

from scaffold.golden_suffixes import GOLDEN_SUFFIXES
from scaffold.models import GoldenSuffix, OracleResult, PrefixResult, Verdict
from scaffold.oracle import judge

logger = logging.getLogger(__name__)

MONOREPO = Path(__file__).resolve().parents[3]


class TemplatePool:
    """Thread-safe pool of pre-copied template project directories.

    Each slot is a copy of `template/` including `.lake/` for warm builds.
    Workers acquire a slot, overwrite `Template/Basic.lean`, run lake build,
    and release the slot back.
    """

    def __init__(self, pool_dir: Path, pool_size: int) -> None:
        """Initialize a template pool.

        Args:
            pool_dir: Directory to create pool slots in.
            pool_size: Number of parallel slots.
        """
        self.pool_dir = pool_dir
        self.pool_size = pool_size
        self._queue: Queue[int] = Queue()

    def initialize(self, template_dir: Path | None = None) -> None:
        """Create pool slots by copying the template directory.

        Args:
            template_dir: Source template. Defaults to `<monorepo>/template`.
        """
        if template_dir is None:
            template_dir = MONOREPO / "template"

        self.pool_dir.mkdir(parents=True, exist_ok=True)

        for i in range(self.pool_size):
            slot_dir = self.pool_dir / f"slot_{i:03d}"
            if slot_dir.exists():
                shutil.rmtree(slot_dir)
            # Copy INCLUDING .lake/ for warm cache.
            shutil.copytree(template_dir, slot_dir)
            self._queue.put(i)
            logger.info("Created pool slot %d at %s", i, slot_dir)

    def acquire(self, timeout: float = 300.0) -> int:
        """Acquire a slot ID. Blocks until one is available."""
        try:
            return self._queue.get(timeout=timeout)
        except Empty:
            msg = f"No pool slot available within {timeout}s"
            raise TimeoutError(msg) from None

    def release(self, slot_id: int) -> None:
        """Release a slot back to the pool."""
        self._queue.put(slot_id)

    def slot_path(self, slot_id: int) -> Path:
        """Return the filesystem path for a slot."""
        return self.pool_dir / f"slot_{slot_id:03d}"

    def basic_lean_path(self, slot_id: int) -> Path:
        """Return the path to Template/Basic.lean in a slot."""
        return self.slot_path(slot_id) / "Template" / "Basic.lean"


def assemble(prefix: str, suffix: GoldenSuffix) -> str:
    """Concatenate a prefix with a golden suffix."""
    return f"{prefix}\n\n{suffix.code}"


def run_lake_build(project_dir: Path, timeout: int = 120) -> tuple[int, str, str, bool]:
    """Run `lake build` in project_dir.

    Returns:
        Tuple of (exit_code, stdout, stderr, timed_out).
    """
    try:
        result = subprocess.run(
            ["lake", "build", "Template"],
            cwd=str(project_dir),
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        return result.returncode, result.stdout, result.stderr, False
    except subprocess.TimeoutExpired:
        return -1, "", "Build timed out", True


def execute_prefix(
    prefix: str,
    pool: TemplatePool,
    timeout: int = 120,
    suffixes: list[GoldenSuffix] | None = None,
) -> PrefixResult:
    """Test a prefix against all golden suffixes in a single pool slot.

    Acquires a slot, tests each suffix sequentially (only Basic.lean changes
    between runs, so Lake caches everything else), and releases the slot.

    Args:
        prefix: The fuzzer-generated prefix code.
        pool: Template pool to acquire a slot from.
        timeout: Build timeout in seconds per suffix.
        suffixes: Subset of suffixes to test. Defaults to all.

    Returns:
        PrefixResult with all oracle results.
    """
    if suffixes is None:
        suffixes = GOLDEN_SUFFIXES

    slot_id = pool.acquire()
    results: list[OracleResult] = []

    try:
        for suffix in suffixes:
            code = assemble(prefix, suffix)
            pool.basic_lean_path(slot_id).write_text(code)

            exit_code, stdout, stderr, timed_out = run_lake_build(
                pool.slot_path(slot_id), timeout=timeout
            )

            output = stdout + "\n" + stderr
            result = judge(
                prefix=prefix,
                suffix_name=suffix.name,
                exit_code=exit_code,
                output=output,
                timed_out=timed_out,
                stderr=stderr,
            )
            results.append(result)

            if result.verdict == Verdict.GOLDEN:
                logger.warning(
                    "GOLDEN SIGNAL with suffix=%s in slot=%d",
                    suffix.name,
                    slot_id,
                )
    finally:
        pool.release(slot_id)

    return PrefixResult(prefix=prefix, results=results)


GENERATOR_DIR = MONOREPO / "generator"


def run_gen_sample(depth: int = 15, *, prefix_only: bool = True) -> str:
    """Generate a Lean code sample via ``cargo run --bin gen_sample``.

    Uses ``cargo run`` so the binary is automatically rebuilt when the
    Rust source changes — no stale-build issues.

    Args:
        depth: Nautilus tree depth (higher = deeper nesting).
        prefix_only: Use prefix-only grammar (no proof terms/tactics).
            Default True for the scaffold pipeline where golden suffixes
            are appended separately.
    """
    cmd = ["cargo", "+nightly", "run", "--bin", "gen_sample", "--"]
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
        msg = f"gen_sample failed: {result.stderr}"
        raise RuntimeError(msg)
    return result.stdout


# Patterns that indicate a prefix contains proof content that should have
# been stripped by the prefix-only grammar. These are warnings, not errors —
# hardcoded tactic strings in ELAB_DECL/MACRO_DECL are expected.
_PREFIX_WARN_PATTERNS = [
    (re.compile(r":=\s*by\b"), "tactic proof block (`:= by`)"),
    (
        re.compile(r"theorem\s+\w+[^:]*:\s*False\s*:=\s+(?!sorry\b)\S"),
        "non-sorry False theorem",
    ),
    (re.compile(r"#print\s+axioms\b"), "#print axioms command"),
]


def validate_prefix(prefix: str) -> list[str]:
    """Check a prefix for content that conflicts with the scaffold contract.

    Returns a list of warning strings (empty = clean prefix). These are
    advisory — some patterns (e.g. `by trivial` inside macro/elab decls)
    are harmless but flagged for visibility.
    """
    warnings: list[str] = []
    for pattern, description in _PREFIX_WARN_PATTERNS:
        if pattern.search(prefix):
            warnings.append(f"prefix contains {description}")
    return warnings
