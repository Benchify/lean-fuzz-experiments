pub mod grammar;
pub mod rule_coverage;

pub use libafl::generators::nautilus::NautilusContext;
pub use libafl::inputs::nautilus::NautilusInput;
pub use rule_coverage::{RuleCoverage, Outcome};

/// Build a `NautilusContext` from the complete Lean 4 grammar.
///
/// `tree_depth` controls maximum recursion depth for generated syntax trees.
/// Values around 15 produce moderately complex programs; higher values produce
/// deeper nesting (useful for stress-testing the kernel).
pub fn create_context(tree_depth: usize) -> NautilusContext {
    NautilusContext::new(tree_depth, &grammar::lean4_rules())
}

/// Build a `NautilusContext` from the prefix-only Lean 4 grammar.
///
/// The prefix grammar omits proof terms, tactics, and tactic sequences.
/// Theorems use `sorry` as placeholder proofs. Designed for the scaffold's
/// "poisoned prefix" pipeline where golden suffixes are appended separately.
pub fn create_prefix_context(tree_depth: usize) -> NautilusContext {
    NautilusContext::new(tree_depth, &grammar::lean4_prefix_rules())
}

/// Unparse a `NautilusInput` into a UTF-8 Lean 4 program string.
pub fn generate_one(ctx: &NautilusContext, input: &NautilusInput) -> String {
    let mut bytes = Vec::new();
    input.unparse(ctx, &mut bytes);
    String::from_utf8_lossy(&bytes).into_owned()
}

/// Extract which grammar rules were used to generate this input.
///
/// Returns a list of rule names (nonterminals) that appear in the input's
/// syntax tree. This is used for coverage-guided fuzzing to identify which
/// rules produce interesting outcomes.
///
/// Note: Since NautilusInput's tree structure is internal to LibAFL,
/// we approximate rule usage by extracting nonterminals from the generated
/// code using pattern matching. This is a heuristic but works well in practice.
pub fn extract_rules_used(code: &str) -> Vec<String> {
    use std::collections::HashSet;
    let mut rules = HashSet::new();

    // Detect rules by looking for characteristic patterns in generated code
    if code.contains("theorem ") || code.contains("lemma ") {
        rules.insert("THEOREM_DECL".to_string());
    }
    if code.contains("def ") {
        rules.insert("DEF_DECL".to_string());
    }
    if code.contains("inductive ") {
        rules.insert("INDUCTIVE_DECL".to_string());
    }
    if code.contains("structure ") {
        rules.insert("STRUCTURE_DECL".to_string());
    }
    if code.contains("class ") {
        rules.insert("CLASS_DECL".to_string());
    }
    if code.contains("instance ") {
        rules.insert("INSTANCE_DECL".to_string());
    }
    if code.contains("macro ") {
        rules.insert("MACRO_DECL".to_string());
    }
    if code.contains("syntax ") {
        rules.insert("SYNTAX_DECL".to_string());
    }
    if code.contains("elab ") {
        rules.insert("ELAB_DECL".to_string());
    }
    if code.contains("mutual") {
        rules.insert("MUTUAL_BLOCK".to_string());
    }
    if code.contains("import ") {
        rules.insert("IMPORTS".to_string());
    }
    if code.contains("universe ") {
        rules.insert("UNIVERSE_DECLS".to_string());
    }
    if code.contains("open ") {
        rules.insert("OPEN_DECLS".to_string());
    }
    if code.contains("set_option ") {
        rules.insert("OPTIONS".to_string());
    }
    if code.contains("@[") {
        rules.insert("ATTRIBUTES".to_string());
    }
    if code.contains("where") {
        rules.insert("WHERE_CLAUSE".to_string());
    }
    if code.contains("deriving ") {
        rules.insert("DERIVING".to_string());
    }

    rules.into_iter().collect()
}
