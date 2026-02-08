"""Shared data structures for the poisoned prefix fuzzer."""

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


class OracleResult(BaseModel):
    """Result of the oracle's judgement on one prefix+suffix pair."""

    suffix_name: str
    verdict: Verdict
    exit_code: int
    reason: str
    axioms: list[str] = []


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
