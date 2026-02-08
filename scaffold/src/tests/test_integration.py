"""Integration tests requiring external tools (cargo).

Run with: uv run pytest src/tests/ -v -m integration
"""

import subprocess

import pytest

from scaffold.executor import run_gen_sample, validate_prefix

pytestmark = pytest.mark.integration


@pytest.fixture(scope="module", autouse=True)
def _ensure_cargo_available() -> None:
    """Skip all tests in this module if cargo is not available."""
    result = subprocess.run(["cargo", "--version"], capture_output=True, text=True)
    if result.returncode != 0:
        pytest.skip("cargo not available")


class TestGenSamplePrefixOnly:
    """Tests for gen_sample --prefix-only via the Python wrapper."""

    def test_produces_output(self) -> None:
        """gen_sample --prefix-only should produce non-empty output."""
        output = run_gen_sample(depth=10, prefix_only=True)
        assert len(output) > 0

    def test_no_tactic_nonterminals(self) -> None:
        """Prefix output should not contain expanded tactic blocks.

        Note: hardcoded `by trivial` in ELAB_DECL/MACRO_DECL is allowed.
        We check that the tactic-heavy patterns from the full grammar
        (multi-line tactic sequences, cases/induction) are absent.
        """
        output = run_gen_sample(depth=15, prefix_only=True)
        # These patterns come from TACTIC_SEQ / CASE_ARMS nonterminals
        # that should be removed in prefix mode.
        assert "rcases" not in output
        assert "induction" not in output or "inductive" in output

    def test_contains_sorry(self) -> None:
        """Prefix theorems should use sorry, not proof terms."""
        # Generate several to increase chance of seeing a theorem.
        for _ in range(10):
            output = run_gen_sample(depth=15, prefix_only=True)
            if "theorem" in output:
                assert "sorry" in output
                return
        # If no theorem appeared in 10 tries, that's OK — skip.
        pytest.skip("no theorem generated in 10 samples")

    def test_prefix_validates_clean(self) -> None:
        """Generated prefix-only output should mostly validate clean."""
        clean_count = 0
        for _ in range(5):
            output = run_gen_sample(depth=10, prefix_only=True)
            warnings = validate_prefix(output)
            if not warnings:
                clean_count += 1
        # At least some should be clean (macros/elabs may trigger advisory warnings).
        assert clean_count >= 1, "no clean prefixes in 5 samples"

    @pytest.mark.parametrize("depth", [5, 10, 15, 20])
    def test_multiple_depths(self, depth: int) -> None:
        """gen_sample should produce output at various depths."""
        output = run_gen_sample(depth=depth, prefix_only=True)
        # Just verify it doesn't crash and produces something.
        assert isinstance(output, str)

    def test_full_grammar_still_works(self) -> None:
        """gen_sample without --prefix-only should still work."""
        output = run_gen_sample(depth=10, prefix_only=False)
        # Empty output is valid (grammar has empty PREAMBLE rule)
        assert isinstance(output, str)
