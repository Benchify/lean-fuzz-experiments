"""Parse Lean 4 compiler stderr into structured diagnostics.

Pure module — no I/O, no side effects.
"""

import re

from scaffold.models import DiagnosticInfo, ErrorCategory

# Lean error format: <file>:<line>:<col>: error: <message>
_ERROR_LINE_RE = re.compile(r"^(?:[^:]+):(\d+):(\d+):\s*error:\s*(.+)$", re.MULTILINE)

# Category patterns, ordered by specificity (first match wins).
_CATEGORY_PATTERNS: list[tuple[ErrorCategory, re.Pattern[str]]] = [
    (
        ErrorCategory.PARSE,
        re.compile(
            r"^expected\b|unexpected token|unknown command|unterminated", re.IGNORECASE
        ),
    ),
    (
        ErrorCategory.UNKNOWN_IDENTIFIER,
        re.compile(r"unknown identifier|unknown constant", re.IGNORECASE),
    ),
    (
        ErrorCategory.UNIVERSE,
        re.compile(r"universe level|universe constraint", re.IGNORECASE),
    ),
    (
        ErrorCategory.POSITIVITY,
        re.compile(r"positivity|negative occurrence", re.IGNORECASE),
    ),
    (
        ErrorCategory.TERMINATION,
        re.compile(
            r"structural recursion|failed to prove termination|well-founded",
            re.IGNORECASE,
        ),
    ),
    (
        ErrorCategory.TACTIC,
        re.compile(r"tactic .* failed|unsolved goals", re.IGNORECASE),
    ),
    (
        ErrorCategory.ELABORATION,
        re.compile(
            r"unsolved metavariable|don't know how to synthesize|failed to synthesize",
            re.IGNORECASE,
        ),
    ),
    (
        ErrorCategory.KERNEL,
        re.compile(
            r"\(kernel\)|declaration type mismatch|environment already contains",
            re.IGNORECASE,
        ),
    ),
    (
        ErrorCategory.DUPLICATE_DECL,
        re.compile(r"already been declared|duplicate definition", re.IGNORECASE),
    ),
    (
        ErrorCategory.TYPE_MISMATCH,
        re.compile(
            r"type mismatch|has type .* but is expected to have type", re.IGNORECASE
        ),
    ),
]


def _classify_message(message: str) -> ErrorCategory:
    """Classify an error message into a category (first match wins)."""
    for category, pattern in _CATEGORY_PATTERNS:
        if pattern.search(message):
            return category
    return ErrorCategory.OTHER


def categorize_stderr(stderr: str) -> list[DiagnosticInfo]:
    """Parse Lean compiler stderr into a list of structured diagnostics.

    Args:
        stderr: Raw stderr output from `lake build`.

    Returns:
        List of DiagnosticInfo, one per error line found.
    """
    results: list[DiagnosticInfo] = []
    for m in _ERROR_LINE_RE.finditer(stderr):
        line = int(m.group(1))
        column = int(m.group(2))
        message = m.group(3).strip()
        results.append(
            DiagnosticInfo(
                line=line,
                column=column,
                message=message,
                category=_classify_message(message),
            )
        )
    return results


def summary_categories(diagnostics: list[DiagnosticInfo]) -> list[ErrorCategory]:
    """Return a deduplicated, sorted list of error categories.

    Args:
        diagnostics: Output of categorize_stderr.

    Returns:
        Sorted list of unique ErrorCategory values.
    """
    seen: set[ErrorCategory] = set()
    ordered: list[ErrorCategory] = []
    for d in diagnostics:
        if d.category not in seen:
            seen.add(d.category)
            ordered.append(d.category)
    return sorted(ordered, key=lambda c: list(ErrorCategory).index(c))
