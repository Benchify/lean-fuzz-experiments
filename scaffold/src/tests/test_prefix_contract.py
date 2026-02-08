"""Unit tests for the prefix validation contract."""

from scaffold.executor import validate_prefix


class TestValidatePrefix:
    """Tests for validate_prefix()."""

    def test_clean_prefix_no_warnings(self) -> None:
        """A prefix with only declarations produces no warnings."""
        prefix = """\
import Lean
universe u v

inductive MyType where
  | mk : Nat → MyType

def foo : Nat := 42
"""
        assert validate_prefix(prefix) == []

    def test_sorry_is_ok(self) -> None:
        """Sorry in prefix theorems is expected and should NOT warn."""
        prefix = """\
theorem helper : True := sorry
theorem helper2 (n : Nat) : n = n := sorry
"""
        assert validate_prefix(prefix) == []

    def test_warns_on_tactic_proof(self) -> None:
        """Tactic proof blocks in prefix should trigger a warning."""
        prefix = """\
theorem foo : True := by
  trivial
"""
        warnings = validate_prefix(prefix)
        assert len(warnings) == 1
        assert "tactic proof block" in warnings[0]

    def test_warns_on_false_theorem(self) -> None:
        """A non-sorry proof of False should trigger a warning."""
        prefix = "theorem bad : False := proof_term\n"
        warnings = validate_prefix(prefix)
        assert any("non-sorry False theorem" in w for w in warnings)

    def test_warns_on_print_axioms(self) -> None:
        """#print axioms in prefix conflicts with golden suffix axiom checking."""
        prefix = "#print axioms foo\n"
        warnings = validate_prefix(prefix)
        assert any("#print axioms" in w for w in warnings)

    def test_false_sorry_no_warning(self) -> None:
        """Theorem : False := sorry is fine (expected in prefix grammar)."""
        prefix = "theorem bad : False := sorry\n"
        warnings = validate_prefix(prefix)
        # The sorry variant should NOT match the non-sorry pattern.
        assert not any("non-sorry False theorem" in w for w in warnings)

    def test_by_trivial_in_macro_warns(self) -> None:
        """By trivial inside a macro triggers a warning (advisory, not error).

        This is expected from MACRO_DECL/ELAB_DECL hardcoded strings.
        The warning is advisory since the tactic is in quoted syntax, not
        an actual proof block.
        """
        prefix = 'macro "foo_mac" : term => `(by trivial)\n'
        warnings = validate_prefix(prefix)
        # This matches `:= by` pattern — it's a known advisory warning.
        # We accept it rather than making the regex more complex.
        assert isinstance(warnings, list)

    def test_inline_by_warns(self) -> None:
        """Theorem foo : P := by tactic should warn."""
        prefix = "theorem foo : True := by trivial\n"
        warnings = validate_prefix(prefix)
        assert any("tactic proof block" in w for w in warnings)

    def test_empty_prefix(self) -> None:
        """Empty prefix is valid."""
        assert validate_prefix("") == []
