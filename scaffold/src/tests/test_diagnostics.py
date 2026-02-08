"""Tests for the Lean compiler error categorizer."""

from scaffold.diagnostics import categorize_stderr, summary_categories
from scaffold.models import ErrorCategory


class TestCategorizeStderr:
    """Tests for categorize_stderr."""

    def test_single_parse_error(self) -> None:
        """Single parse error is categorized as PARSE."""
        stderr = "Template/Basic.lean:5:0: error: expected token\n"
        diags = categorize_stderr(stderr)
        assert len(diags) == 1
        assert diags[0].category == ErrorCategory.PARSE
        assert diags[0].line == 5
        assert diags[0].column == 0
        assert "expected token" in diags[0].message

    def test_unexpected_token(self) -> None:
        """Unexpected token variant also maps to PARSE."""
        stderr = "Foo.lean:1:10: error: unexpected token 'def'\n"
        diags = categorize_stderr(stderr)
        assert len(diags) == 1
        assert diags[0].category == ErrorCategory.PARSE

    def test_unknown_command(self) -> None:
        """Unknown command maps to PARSE."""
        stderr = "Foo.lean:3:0: error: unknown command 'blah'\n"
        diags = categorize_stderr(stderr)
        assert len(diags) == 1
        assert diags[0].category == ErrorCategory.PARSE

    def test_type_mismatch(self) -> None:
        """Type mismatch is categorized correctly."""
        stderr = "Template/Basic.lean:10:4: error: type mismatch\n"
        diags = categorize_stderr(stderr)
        assert len(diags) == 1
        assert diags[0].category == ErrorCategory.TYPE_MISMATCH

    def test_type_mismatch_verbose(self) -> None:
        """Verbose type mismatch with 'has type ... but is expected' pattern."""
        stderr = "Foo.lean:7:2: error: has type Nat but is expected to have type Bool\n"
        diags = categorize_stderr(stderr)
        assert len(diags) == 1
        assert diags[0].category == ErrorCategory.TYPE_MISMATCH

    def test_unknown_identifier(self) -> None:
        """Unknown identifier is categorized correctly."""
        stderr = "Foo.lean:2:5: error: unknown identifier 'foo'\n"
        diags = categorize_stderr(stderr)
        assert len(diags) == 1
        assert diags[0].category == ErrorCategory.UNKNOWN_IDENTIFIER

    def test_unknown_constant(self) -> None:
        """Unknown constant also maps to UNKNOWN_IDENTIFIER."""
        stderr = "Foo.lean:2:5: error: unknown constant 'bar'\n"
        diags = categorize_stderr(stderr)
        assert len(diags) == 1
        assert diags[0].category == ErrorCategory.UNKNOWN_IDENTIFIER

    def test_universe_level(self) -> None:
        """Universe level error is categorized correctly."""
        stderr = "Foo.lean:1:0: error: universe level mismatch\n"
        diags = categorize_stderr(stderr)
        assert len(diags) == 1
        assert diags[0].category == ErrorCategory.UNIVERSE

    def test_positivity(self) -> None:
        """Positivity check failure is categorized correctly."""
        stderr = "Foo.lean:3:0: error: (kernel) arg #1 of 'Bad.mk' has a negative occurrence of the datatypes being declared\n"
        diags = categorize_stderr(stderr)
        assert len(diags) == 1
        # POSITIVITY should match "negative occurrence" before KERNEL matches "kernel"
        assert diags[0].category == ErrorCategory.POSITIVITY

    def test_termination(self) -> None:
        """Termination failure is categorized correctly."""
        stderr = "Foo.lean:5:0: error: failed to prove termination\n"
        diags = categorize_stderr(stderr)
        assert len(diags) == 1
        assert diags[0].category == ErrorCategory.TERMINATION

    def test_structural_recursion(self) -> None:
        """Structural recursion error maps to TERMINATION."""
        stderr = "Foo.lean:5:0: error: structural recursion cannot be used\n"
        diags = categorize_stderr(stderr)
        assert len(diags) == 1
        assert diags[0].category == ErrorCategory.TERMINATION

    def test_tactic_failed(self) -> None:
        """Tactic failure is categorized correctly."""
        stderr = "Foo.lean:8:2: error: tactic 'simp' failed\n"
        diags = categorize_stderr(stderr)
        assert len(diags) == 1
        assert diags[0].category == ErrorCategory.TACTIC

    def test_unsolved_goals(self) -> None:
        """Unsolved goals maps to TACTIC."""
        stderr = "Foo.lean:8:2: error: unsolved goals\n"
        diags = categorize_stderr(stderr)
        assert len(diags) == 1
        assert diags[0].category == ErrorCategory.TACTIC

    def test_elaboration_metavariable(self) -> None:
        """Unsolved metavariable maps to ELABORATION."""
        stderr = "Foo.lean:4:0: error: unsolved metavariable ?m_1\n"
        diags = categorize_stderr(stderr)
        assert len(diags) == 1
        assert diags[0].category == ErrorCategory.ELABORATION

    def test_elaboration_synthesize(self) -> None:
        """Failed to synthesize maps to ELABORATION."""
        stderr = "Foo.lean:4:0: error: failed to synthesize instance Add String\n"
        diags = categorize_stderr(stderr)
        assert len(diags) == 1
        assert diags[0].category == ErrorCategory.ELABORATION

    def test_kernel_error(self) -> None:
        """Kernel error is categorized correctly."""
        stderr = "Foo.lean:1:0: error: (kernel) declaration type mismatch\n"
        diags = categorize_stderr(stderr)
        assert len(diags) == 1
        assert diags[0].category == ErrorCategory.KERNEL

    def test_environment_already_contains(self) -> None:
        """Environment already contains maps to KERNEL."""
        stderr = "Foo.lean:1:0: error: environment already contains 'foo'\n"
        diags = categorize_stderr(stderr)
        assert len(diags) == 1
        assert diags[0].category == ErrorCategory.KERNEL

    def test_duplicate_decl(self) -> None:
        """Already been declared maps to DUPLICATE_DECL."""
        stderr = "Foo.lean:3:0: error: 'foo' has already been declared\n"
        diags = categorize_stderr(stderr)
        assert len(diags) == 1
        assert diags[0].category == ErrorCategory.DUPLICATE_DECL

    def test_unrecognized_error(self) -> None:
        """Unrecognized error message falls back to OTHER."""
        stderr = "Foo.lean:1:0: error: something completely novel happened\n"
        diags = categorize_stderr(stderr)
        assert len(diags) == 1
        assert diags[0].category == ErrorCategory.OTHER

    def test_multi_error_stderr(self) -> None:
        """Multiple errors are all captured."""
        stderr = (
            "Foo.lean:1:0: error: expected token\n"
            "Foo.lean:5:2: error: type mismatch\n"
            "Foo.lean:10:0: error: unknown identifier 'x'\n"
        )
        diags = categorize_stderr(stderr)
        assert len(diags) == 3
        assert diags[0].category == ErrorCategory.PARSE
        assert diags[1].category == ErrorCategory.TYPE_MISMATCH
        assert diags[2].category == ErrorCategory.UNKNOWN_IDENTIFIER

    def test_empty_stderr(self) -> None:
        """Empty stderr produces empty list."""
        assert categorize_stderr("") == []

    def test_no_error_lines(self) -> None:
        """Stderr with warnings but no errors produces empty list."""
        stderr = "Foo.lean:1:0: warning: unused variable 'x'\n"
        assert categorize_stderr(stderr) == []

    def test_line_column_extraction(self) -> None:
        """Line and column numbers are correctly extracted."""
        stderr = "Template/Basic.lean:42:17: error: type mismatch\n"
        diags = categorize_stderr(stderr)
        assert len(diags) == 1
        assert diags[0].line == 42
        assert diags[0].column == 17


class TestSummaryCategories:
    """Tests for summary_categories."""

    def test_deduplication(self) -> None:
        """Duplicate categories are removed."""
        stderr = (
            "Foo.lean:1:0: error: expected token\n"
            "Foo.lean:2:0: error: unexpected token 'x'\n"
        )
        diags = categorize_stderr(stderr)
        cats = summary_categories(diags)
        assert cats == [ErrorCategory.PARSE]

    def test_sorted_by_enum_order(self) -> None:
        """Categories are sorted by enum declaration order."""
        stderr = (
            "Foo.lean:1:0: error: type mismatch\nFoo.lean:2:0: error: expected token\n"
        )
        diags = categorize_stderr(stderr)
        cats = summary_categories(diags)
        # PARSE comes before TYPE_MISMATCH in the enum
        assert cats == [ErrorCategory.PARSE, ErrorCategory.TYPE_MISMATCH]

    def test_empty_input(self) -> None:
        """Empty diagnostics produce empty categories."""
        assert summary_categories([]) == []
