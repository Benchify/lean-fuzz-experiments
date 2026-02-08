"""Corpus tiering: classify prefixes by how close they got to proving False."""

from enum import Enum
from pathlib import Path

from scaffold.models import DiagnosticRecord, ErrorCategory, Verdict


class CorpusTier(Enum):
    """Tiered classification of fuzzer-generated prefixes."""

    TIER_0 = "tier-0"  # Prefix compiles, proof not found (closest to success!)
    TIER_1 = "tier-1"  # Prefix compiles, type error in proof attempt
    TIER_2 = "tier-2"  # Prefix has minor errors (repairable)
    DISCARD = "discard"  # Parse failure (not useful)


def classify_tier(record: DiagnosticRecord) -> CorpusTier:
    """Classify a diagnostic record into a corpus tier.

    Args:
        record: Diagnostic record from a fuzzing execution

    Returns:
        CorpusTier classification

    Logic:
        - Tier 0: Compiled successfully but proof failed (CLOSEST to bug!)
        - Tier 1: Compiled with golden suffix having type errors
        - Tier 2: Minor errors that could be repaired
        - Discard: Parse errors or severe failures
    """
    # Golden signal - not part of corpus tiers (separate handling)
    if record.verdict == Verdict.GOLDEN:
        return CorpusTier.TIER_0  # Treat as highest tier

    # Build succeeded - check why the proof failed
    if record.verdict not in [Verdict.BUILD_FAILED, Verdict.TIMEOUT]:
        # Check error types in diagnostics
        if ErrorCategory.TACTIC in record.error_categories:
            # Tactic failed to find proof - THIS IS TIER 0!
            # The prefix compiled, environment is valid, just couldn't prove False
            return CorpusTier.TIER_0
        elif ErrorCategory.TYPE_MISMATCH in record.error_categories:
            # Type error in proof attempt - Tier 1
            return CorpusTier.TIER_1
        else:
            # Other errors after successful build - Tier 1
            return CorpusTier.TIER_1

    # Build failed - check if repairable
    error_cats = set(record.error_categories)

    # Parse errors - discard
    if ErrorCategory.PARSE in error_cats:
        return CorpusTier.DISCARD

    # Minor errors that might be fixable
    minor_errors = {
        ErrorCategory.UNKNOWN_IDENTIFIER,
        ErrorCategory.TYPE_MISMATCH,
        ErrorCategory.ELABORATION,
    }

    if error_cats.issubset(minor_errors):
        return CorpusTier.TIER_2

    # Severe errors (positivity, universe, kernel) - discard
    return CorpusTier.DISCARD


def save_to_tier(prefix: str, tier: CorpusTier, prefix_hash: str, corpus_dir: Path) -> Path:
    """Save a prefix to its tier directory.

    Args:
        prefix: The Lean code prefix
        tier: Classification tier
        prefix_hash: Hash of the prefix (for filename)
        corpus_dir: Base corpus directory

    Returns:
        Path where prefix was saved
    """
    tier_dir = corpus_dir / tier.value
    tier_dir.mkdir(parents=True, exist_ok=True)

    path = tier_dir / f"prefix_{prefix_hash}.lean"
    path.write_text(prefix)

    return path
