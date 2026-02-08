"""Fixed golden suffixes that claim False.

Each suffix is appended to a fuzzer-generated prefix. If `lake build`
succeeds on the combined file, the prefix has exploited a soundness bug.
"""

from pydantic import BaseModel


class GoldenSuffix(BaseModel):
    """A fixed theorem claiming False (or equivalent) with a specific tactic."""

    name: str
    code: str
    description: str


GOLDEN_SUFFIXES: list[GoldenSuffix] = [
    GoldenSuffix(
        name="trivial",
        code=(
            "theorem soundness_check : False := by trivial\n"
            "#print axioms soundness_check\n"
        ),
        description="Kitchen-sink tactic: tries assumption, rfl, True.intro, contradiction.",
    ),
    GoldenSuffix(
        name="simp_all",
        code=(
            "theorem soundness_check : False := by simp_all\n"
            "#print axioms soundness_check\n"
        ),
        description="Simplifier with all hypotheses and simp lemmas.",
    ),
    GoldenSuffix(
        name="native_decide",
        code=(
            "theorem soundness_check : False := by native_decide\n"
            "#print axioms soundness_check\n"
        ),
        description="Native code evaluation — bypasses kernel for some checks.",
    ),
    GoldenSuffix(
        name="omega",
        code=(
            "theorem soundness_check : (0 : Nat) = 1 := by omega\n"
            "#print axioms soundness_check\n"
        ),
        description="Integer arithmetic solver — claims 0 = 1.",
    ),
    GoldenSuffix(
        name="decide",
        code=(
            "theorem soundness_check : False := by decide\n"
            "#print axioms soundness_check\n"
        ),
        description="Decidable proposition evaluation.",
    ),
    GoldenSuffix(
        name="assumption",
        code=(
            "theorem soundness_check : False := by assumption\n"
            "#print axioms soundness_check\n"
        ),
        description="Exact match from local context — probes for False in environment.",
    ),
    GoldenSuffix(
        name="inferInstance",
        code=(
            "theorem soundness_check : False := inferInstance\n"
            "#print axioms soundness_check\n"
        ),
        description="Type class resolution — probes for False as an instance.",
    ),
]

SUFFIX_BY_NAME: dict[str, GoldenSuffix] = {s.name: s for s in GOLDEN_SUFFIXES}
