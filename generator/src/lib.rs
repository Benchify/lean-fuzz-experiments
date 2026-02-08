pub mod grammar;

pub use libafl::generators::nautilus::NautilusContext;
pub use libafl::inputs::nautilus::NautilusInput;

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
