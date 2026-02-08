"""Oracle that judges prefix+suffix execution results.

Determines whether a successful build represents a genuine soundness bug
(GOLDEN), a false positive (escape hatches like sorry/axiom), or a normal
build failure.
"""

import re

from scaffold.diagnostics import categorize_stderr, summary_categories
from scaffold.models import OracleResult, Verdict

# Patterns that indicate the prefix is "cheating" rather than exploiting a real bug.
_ESCAPE_HATCH_PATTERNS: list[tuple[str, re.Pattern[str]]] = [
    ("sorry", re.compile(r"\bsorry\b")),
    ("axiom_false", re.compile(r"\baxiom\b[^:]*:\s*(False|0\s*=\s*1)\b")),
    ("unsafe_def", re.compile(r"\bunsafe\s+def\b")),
    ("implemented_by", re.compile(r"@\[implemented_by\b")),
    ("extern", re.compile(r"@\[extern\b")),
]

# Matches the `#print axioms` output in stderr.
_AXIOMS_RE = re.compile(
    r"'soundness_check'\s+depends on axioms:\s*\[([^\]]*)\]",
)
# Fallback: sometimes Lean outputs axioms line-by-line.
_AXIOMS_LINE_RE = re.compile(
    r"'soundness_check'\s+depends on axioms:",
)

# Tainted axioms that indicate a non-genuine proof.
_TAINTED_AXIOMS = frozenset({"sorryAx"})


def check_escape_hatches(prefix: str) -> list[str]:
    """Return names of escape hatches found in the prefix.

    An empty list means the prefix appears clean.
    """
    return [name for name, pat in _ESCAPE_HATCH_PATTERNS if pat.search(prefix)]


def parse_axioms_from_output(output: str) -> list[str]:
    """Extract the axiom list from `#print axioms soundness_check` output.

    The output may appear in either stdout or stderr from `lake build`.
    Returns an empty list if no axiom info is found.
    """
    # Try bracket format first: 'soundness_check' depends on axioms: [a, b, c]
    m = _AXIOMS_RE.search(output)
    if m:
        raw = m.group(1).strip()
        if not raw:
            return []
        return [a.strip() for a in raw.split(",") if a.strip()]

    # Fallback: line-by-line format
    # 'soundness_check' depends on axioms:
    # sorryAx
    # propext
    m2 = _AXIOMS_LINE_RE.search(output)
    if m2:
        lines = output[m2.end() :].strip().splitlines()
        axioms: list[str] = []
        for line in lines:
            tok = line.strip()
            if not tok or tok.startswith("'") or tok.startswith("#"):
                break
            axioms.append(tok)
        return axioms

    return []


def judge(
    prefix: str,
    suffix_name: str,
    exit_code: int,
    output: str,
    timed_out: bool = False,
    stderr: str = "",
) -> OracleResult:
    """Judge a single prefix+suffix execution.

    Args:
        prefix: The fuzzer-generated prefix code.
        suffix_name: Which golden suffix was appended.
        exit_code: Return code from `lake build`.
        output: Combined stdout+stderr from `lake build`.
        timed_out: Whether the build timed out.
        stderr: Raw stderr from `lake build` (for diagnostics).

    Returns:
        OracleResult with the verdict.
    """
    if timed_out:
        return OracleResult(
            suffix_name=suffix_name,
            verdict=Verdict.TIMEOUT,
            exit_code=exit_code,
            reason="Build timed out.",
        )

    if exit_code != 0:
        diagnostics = categorize_stderr(stderr)
        categories = summary_categories(diagnostics)
        reason = (
            f"Build failed: {', '.join(c.value for c in categories)}"
            if categories
            else "Build failed."
        )
        return OracleResult(
            suffix_name=suffix_name,
            verdict=Verdict.BUILD_FAILED,
            exit_code=exit_code,
            reason=reason,
            diagnostics=diagnostics,
            raw_stderr=stderr,
        )

    # Build succeeded — now check if it's genuine.
    escape_hatches = check_escape_hatches(prefix)
    if escape_hatches:
        return OracleResult(
            suffix_name=suffix_name,
            verdict=Verdict.FALSE_POSITIVE,
            exit_code=exit_code,
            reason=f"Escape hatches in prefix: {', '.join(escape_hatches)}",
        )

    axioms = parse_axioms_from_output(output)
    tainted = [a for a in axioms if a in _TAINTED_AXIOMS]
    if tainted:
        return OracleResult(
            suffix_name=suffix_name,
            verdict=Verdict.FALSE_POSITIVE,
            exit_code=exit_code,
            reason=f"Tainted axioms: {', '.join(tainted)}",
            axioms=axioms,
        )

    # Build succeeded, no escape hatches, no tainted axioms → GOLDEN.
    return OracleResult(
        suffix_name=suffix_name,
        verdict=Verdict.GOLDEN,
        exit_code=exit_code,
        reason="Build succeeded with clean prefix and no tainted axioms.",
        axioms=axioms,
    )
