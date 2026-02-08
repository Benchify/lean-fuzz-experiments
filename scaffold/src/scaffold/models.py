"""Shared data structures for the poisoned prefix fuzzer."""

from datetime import datetime
from enum import StrEnum

from pydantic import BaseModel


class GoldenSuffix(BaseModel):
    """A fixed theorem claiming False (or equivalent) with a specific tactic."""

    name: str
    code: str
    description: str


class Verdict(StrEnum):
    """Outcome of judging a single prefix+suffix execution."""

    GOLDEN = "GOLDEN"
    FALSE_POSITIVE = "FALSE_POSITIVE"
    BUILD_FAILED = "BUILD_FAILED"
    TIMEOUT = "TIMEOUT"


class ErrorCategory(StrEnum):
    """Categorization of a Lean compiler error."""

    PARSE = "PARSE"
    UNKNOWN_IDENTIFIER = "UNKNOWN_IDENTIFIER"
    TYPE_MISMATCH = "TYPE_MISMATCH"
    UNIVERSE = "UNIVERSE"
    POSITIVITY = "POSITIVITY"
    TERMINATION = "TERMINATION"
    TACTIC = "TACTIC"
    ELABORATION = "ELABORATION"
    KERNEL = "KERNEL"
    DUPLICATE_DECL = "DUPLICATE_DECL"
    OTHER = "OTHER"


class DiagnosticInfo(BaseModel):
    """A single parsed error from Lean compiler output."""

    line: int
    column: int
    message: str
    category: ErrorCategory


class OracleResult(BaseModel):
    """Result of the oracle's judgement on one prefix+suffix pair."""

    suffix_name: str
    verdict: Verdict
    exit_code: int
    reason: str
    axioms: list[str] = []
    diagnostics: list[DiagnosticInfo] = []
    raw_stderr: str = ""


class DiagnosticRecord(BaseModel):
    """Schema for a single JSONL log entry."""

    timestamp: datetime
    session_id: str
    prefix_hash: str
    suffix_name: str
    verdict: Verdict
    exit_code: int
    error_categories: list[ErrorCategory]
    diagnostics: list[DiagnosticInfo]
    raw_stderr: str
    prefix_snippet: str


class PrefixResult(BaseModel):
    """Aggregated results from testing one prefix against all golden suffixes."""

    prefix: str
    results: list[OracleResult]

    @property
    def has_golden(self) -> bool:
        """Whether any suffix produced a GOLDEN verdict."""
        return any(r.verdict == Verdict.GOLDEN for r in self.results)

    @property
    def has_false_positive(self) -> bool:
        """Whether any suffix produced a FALSE_POSITIVE verdict."""
        return any(r.verdict == Verdict.FALSE_POSITIVE for r in self.results)
