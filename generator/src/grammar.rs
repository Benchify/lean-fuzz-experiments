/// Lean 4 grammar for LibAFL Nautilus grammar-based mutation.
///
/// ~420 rules across 55 non-terminals targeting kernel soundness bugs:
/// universe levels, inductive types, definitional equality, termination
/// checking, type class resolution, and metaprogramming.
///
/// Escaping: `\{` and `\}` produce literal braces in output (Lean implicit
/// binders). `{NT}` references a non-terminal for Nautilus expansion.

/// Returns all grammar rules as `Vec<Vec<String>>` where each inner vec
/// is `[nonterminal, expansion]`.
pub fn lean4_rules() -> Vec<Vec<String>> {
    rules_raw().into_iter().map(|(nt, exp)| {
        vec![nt.to_string(), exp.to_string()]
    }).collect()
}

fn rules_raw() -> Vec<(&'static str, &'static str)> {
    vec![
        // ================================================================
        // 1. PROGRAM STRUCTURE
        // ================================================================

        // FILE — top-level entry point
        // NautilusContext::new auto-creates a "START -> {FILE}" wrapper
        // since FILE is the first rule's non-terminal.
        // ~50% of alternatives include a golden check
        ("FILE", "{PREAMBLE}\n\n{PROGRAM}\n\n{GOLDEN_CHECK}"),
        ("FILE", "{PREAMBLE}\n\n{PROGRAM}"),
        ("FILE", "{PREAMBLE}\n\n{GOLDEN_CHECK}"),
        ("FILE", "{PREAMBLE}\n\n{PROGRAM}\n\n{PROGRAM}"),
        ("FILE", "{PREAMBLE}\n\n{PROGRAM}\n\n{PROGRAM}\n\n{GOLDEN_CHECK}"),

        // PREAMBLE — imports and universe declarations
        ("PREAMBLE", "{IMPORTS}\n{UNIVERSE_DECLS}\n{OPEN_DECLS}"),
        ("PREAMBLE", "{IMPORTS}\n{UNIVERSE_DECLS}"),
        ("PREAMBLE", "{IMPORTS}"),
        ("PREAMBLE", "{UNIVERSE_DECLS}"),
        ("PREAMBLE", ""),

        // IMPORTS
        ("IMPORTS", "import Lean"),
        ("IMPORTS", "import Lean\nimport Lean.Elab.Command"),
        ("IMPORTS", "import Lean\nimport Lean.Meta"),
        ("IMPORTS", ""),

        // OPEN_DECLS
        ("OPEN_DECLS", "open Lean Elab Command in"),
        ("OPEN_DECLS", "open Lean Meta in"),
        ("OPEN_DECLS", "open Lean in"),
        ("OPEN_DECLS", ""),

        // UNIVERSE_DECLS
        ("UNIVERSE_DECLS", "universe {UVAR}"),
        ("UNIVERSE_DECLS", "universe {UVAR} {UVAR_2}"),
        ("UNIVERSE_DECLS", "universe {UVAR} {UVAR_2} {UVAR_3}"),
        ("UNIVERSE_DECLS", ""),

        // PROGRAM — sequence of declarations
        ("PROGRAM", "{DECL}"),
        ("PROGRAM", "{DECL}\n\n{DECL}"),
        ("PROGRAM", "{DECL}\n\n{DECL}\n\n{DECL}"),
        ("PROGRAM", "{DECL}\n\n{DECL}\n\n{DECL}\n\n{DECL}"),
        ("PROGRAM", "{MUTUAL_BLOCK}"),
        ("PROGRAM", "{MUTUAL_BLOCK}\n\n{DECL}"),
        ("PROGRAM", "{DECL}\n\n{MUTUAL_BLOCK}"),

        // ================================================================
        // 2. DECLARATIONS
        // ================================================================

        // DECL — top-level declaration
        ("DECL", "{DEF_DECL}"),
        ("DECL", "{THEOREM_DECL}"),
        ("DECL", "{INDUCTIVE_DECL}"),
        ("DECL", "{CLASS_DECL}"),
        ("DECL", "{INSTANCE_DECL}"),
        ("DECL", "{STRUCTURE_DECL}"),
        ("DECL", "{ABBREV_DECL}"),
        ("DECL", "{OPAQUE_DECL}"),
        ("DECL", "{ELAB_DECL}"),
        ("DECL", "{MACRO_DECL}"),
        ("DECL", "{EVAL_CMD}"),
        ("DECL", "{SECTION_BLOCK}"),
        ("DECL", "{NAMESPACE_BLOCK}"),

        // DEF_DECL
        ("DEF_DECL", "def {IDENT} : {TYPE} := {TERM}"),
        ("DEF_DECL", "def {IDENT} {BINDERS} : {TYPE} := {TERM}"),
        ("DEF_DECL", "def {IDENT} : {TYPE} :=\n  {TERM}"),
        ("DEF_DECL", "def {IDENT} {BINDERS} : {TYPE} where\n  {MATCH_ARMS}"),
        ("DEF_DECL", "partial def {IDENT} : {TYPE} := {TERM}"),
        ("DEF_DECL", "partial def {IDENT} {BINDERS} : {TYPE} := {TERM}"),
        ("DEF_DECL", "noncomputable def {IDENT} : {TYPE} := {TERM}"),
        ("DEF_DECL", "@[reducible] def {IDENT} : {TYPE} := {TERM}"),
        ("DEF_DECL", "@[inline] def {IDENT} {BINDERS} : {TYPE} := {TERM}"),
        ("DEF_DECL", "unsafe def {IDENT} : {TYPE} := {TERM}"),
        ("DEF_DECL", "unsafe def {IDENT} {BINDERS} : {TYPE} := {TERM}"),
        ("DEF_DECL", "private def {IDENT} : {TYPE} := {TERM}"),
        ("DEF_DECL", "protected def {IDENT} : {TYPE} := {TERM}"),

        // THEOREM_DECL
        ("THEOREM_DECL", "theorem {IDENT} : {PROP_TYPE} := {PROOF_TERM}"),
        ("THEOREM_DECL", "theorem {IDENT} {BINDERS} : {PROP_TYPE} := {PROOF_TERM}"),
        ("THEOREM_DECL", "theorem {IDENT} : {PROP_TYPE} := by\n  {TACTIC_SEQ}"),
        ("THEOREM_DECL", "theorem {IDENT} {BINDERS} : {PROP_TYPE} := by\n  {TACTIC_SEQ}"),
        ("THEOREM_DECL", "theorem {IDENT} : {PROP_TYPE} := by {TACTIC}"),

        // INDUCTIVE_DECL — high multiplicity for attack surface
        ("INDUCTIVE_DECL", "inductive {IDENT_IND} where\n{CTORS}"),
        ("INDUCTIVE_DECL", "inductive {IDENT_IND} : {TYPE} where\n{CTORS}"),
        ("INDUCTIVE_DECL", "inductive {IDENT_IND} {BINDERS} where\n{CTORS}"),
        ("INDUCTIVE_DECL", "inductive {IDENT_IND} : {ULEVEL_ANNOT} where\n{CTORS}"),
        ("INDUCTIVE_DECL", "inductive {IDENT_IND} {BINDERS} : {TYPE} where\n{CTORS}"),
        ("INDUCTIVE_DECL", "inductive {IDENT_IND} : Prop where\n{CTORS}"),
        ("INDUCTIVE_DECL", "inductive {IDENT_IND} : Type where\n{CTORS}"),
        ("INDUCTIVE_DECL", "inductive {IDENT_IND} : Type 1 where\n{CTORS}"),
        // Indexed families
        ("INDUCTIVE_DECL", "inductive {IDENT_IND} : {TYPE} → {TYPE} where\n{CTORS}"),
        ("INDUCTIVE_DECL", "inductive {IDENT_IND} : {TYPE} → Prop where\n{CTORS}"),
        ("INDUCTIVE_DECL", "inductive {IDENT_IND} : {TYPE} → Type where\n{CTORS}"),
        // Nested/recursive inductives (stress-test positivity checker)
        ("INDUCTIVE_DECL", "inductive {IDENT_IND} (α : Type) where\n{CTORS_PARAM}"),
        ("INDUCTIVE_DECL", "inductive {IDENT_IND} (α : Type) : Type where\n{CTORS_PARAM}"),
        // Universe-polymorphic inductives
        ("INDUCTIVE_DECL", "inductive {IDENT_IND}.\\{u\\} : Type u where\n{CTORS}"),
        ("INDUCTIVE_DECL", "inductive {IDENT_IND}.\\{u, v\\} : Type (max u v) where\n{CTORS}"),
        // Unsafe inductives
        ("INDUCTIVE_DECL", "unsafe inductive {IDENT_IND} where\n{CTORS}"),

        // CTORS — constructor lists
        ("CTORS", "  | {IDENT_CTOR} : {CTOR_TYPE}"),
        ("CTORS", "  | {IDENT_CTOR} : {CTOR_TYPE}\n  | {IDENT_CTOR_2} : {CTOR_TYPE}"),
        ("CTORS", "  | {IDENT_CTOR} : {CTOR_TYPE}\n  | {IDENT_CTOR_2} : {CTOR_TYPE}\n  | {IDENT_CTOR_3} : {CTOR_TYPE}"),
        ("CTORS", "  | {IDENT_CTOR}"),
        ("CTORS", "  | {IDENT_CTOR}\n  | {IDENT_CTOR_2}"),
        ("CTORS", "  | {IDENT_CTOR}\n  | {IDENT_CTOR_2}\n  | {IDENT_CTOR_3}"),
        ("CTORS", "  | {IDENT_CTOR}\n  | {IDENT_CTOR_2} : {CTOR_TYPE}"),

        // CTORS_PARAM — constructors for parameterized inductives
        ("CTORS_PARAM", "  | {IDENT_CTOR} : {CTOR_TYPE_PARAM}"),
        ("CTORS_PARAM", "  | {IDENT_CTOR} : {CTOR_TYPE_PARAM}\n  | {IDENT_CTOR_2} : {CTOR_TYPE_PARAM}"),
        ("CTORS_PARAM", "  | {IDENT_CTOR}\n  | {IDENT_CTOR_2} : {CTOR_TYPE_PARAM}"),
        ("CTORS_PARAM", "  | {IDENT_CTOR} : α → {IDENT_IND} α"),
        ("CTORS_PARAM", "  | {IDENT_CTOR} : α → {IDENT_IND} α\n  | {IDENT_CTOR_2} : List ({IDENT_IND} α) → {IDENT_IND} α"),

        // CTOR_TYPE — constructor result types (attack positivity checker)
        ("CTOR_TYPE", "{IDENT_IND}"),
        ("CTOR_TYPE", "{TYPE} → {IDENT_IND}"),
        ("CTOR_TYPE", "{TYPE} → {TYPE} → {IDENT_IND}"),
        ("CTOR_TYPE", "\\{{IDENT} : {TYPE}\\} → {IDENT_IND}"),
        ("CTOR_TYPE", "\\{{IDENT} : {TYPE}\\} → {TYPE} → {IDENT_IND}"),
        ("CTOR_TYPE", "({IDENT} : {TYPE}) → {IDENT_IND}"),
        ("CTOR_TYPE", "({IDENT} : {TYPE}) → ({IDENT} : {TYPE}) → {IDENT_IND}"),
        // Recursive constructors (valid)
        ("CTOR_TYPE", "{IDENT_IND} → {IDENT_IND}"),
        ("CTOR_TYPE", "Nat → {IDENT_IND} → {IDENT_IND}"),
        // Positivity violation attempts (will be rejected, but tests the checker)
        ("CTOR_TYPE", "({IDENT_IND} → {TYPE}) → {IDENT_IND}"),
        ("CTOR_TYPE", "({IDENT_IND} → Nat) → {IDENT_IND}"),
        ("CTOR_TYPE", "(({IDENT_IND} → Bool) → Nat) → {IDENT_IND}"),
        // Nested with standard types
        ("CTOR_TYPE", "List {IDENT_IND} → {IDENT_IND}"),
        ("CTOR_TYPE", "Array {IDENT_IND} → {IDENT_IND}"),
        ("CTOR_TYPE", "Option {IDENT_IND} → {IDENT_IND}"),

        // CTOR_TYPE_PARAM — constructor types for parameterized inductives
        ("CTOR_TYPE_PARAM", "{IDENT_IND} α"),
        ("CTOR_TYPE_PARAM", "α → {IDENT_IND} α"),
        ("CTOR_TYPE_PARAM", "α → α → {IDENT_IND} α"),
        ("CTOR_TYPE_PARAM", "{IDENT_IND} α → {IDENT_IND} α"),
        ("CTOR_TYPE_PARAM", "List ({IDENT_IND} α) → {IDENT_IND} α"),
        ("CTOR_TYPE_PARAM", "({IDENT_IND} α → α) → {IDENT_IND} α"),

        // ABBREV_DECL
        ("ABBREV_DECL", "abbrev {IDENT} := {TERM}"),
        ("ABBREV_DECL", "abbrev {IDENT} : {TYPE} := {TERM}"),
        ("ABBREV_DECL", "abbrev {IDENT} {BINDERS} : {TYPE} := {TERM}"),

        // OPAQUE_DECL
        ("OPAQUE_DECL", "opaque {IDENT} : {TYPE}"),
        ("OPAQUE_DECL", "opaque {IDENT} : {TYPE} := {TERM}"),

        // CLASS_DECL
        ("CLASS_DECL", "class {IDENT_IND} (α : {TYPE}) where\n  {CLASS_FIELDS}"),
        ("CLASS_DECL", "class {IDENT_IND} (α : {TYPE}) extends {TYPE_ATOM} α where\n  {CLASS_FIELDS}"),
        ("CLASS_DECL", "class {IDENT_IND} (α : {TYPE}) (β : {TYPE}) where\n  {CLASS_FIELDS}"),
        ("CLASS_DECL", "class {IDENT_IND} where\n  {CLASS_FIELDS}"),

        // CLASS_FIELDS
        ("CLASS_FIELDS", "{IDENT} : {TYPE}"),
        ("CLASS_FIELDS", "{IDENT} : {TYPE}\n  {IDENT} : {TYPE}"),
        ("CLASS_FIELDS", "{IDENT} : α → α"),
        ("CLASS_FIELDS", "{IDENT} : α\n  {IDENT} : α → α → α"),
        ("CLASS_FIELDS", "{IDENT} : α → β"),

        // INSTANCE_DECL
        ("INSTANCE_DECL", "instance : {IDENT_IND} {TYPE_ATOM} where\n  {INSTANCE_FIELDS}"),
        ("INSTANCE_DECL", "instance {IDENT} : {IDENT_IND} {TYPE_ATOM} where\n  {INSTANCE_FIELDS}"),
        ("INSTANCE_DECL", "instance : {IDENT_IND} {TYPE_ATOM} := {TERM}"),
        ("INSTANCE_DECL", "@[default_instance] instance : {IDENT_IND} {TYPE_ATOM} where\n  {INSTANCE_FIELDS}"),

        // INSTANCE_FIELDS
        ("INSTANCE_FIELDS", "{IDENT} := {TERM}"),
        ("INSTANCE_FIELDS", "{IDENT} := {TERM}\n  {IDENT} := {TERM}"),

        // STRUCTURE_DECL
        ("STRUCTURE_DECL", "structure {IDENT_IND} where\n  {STRUCT_FIELDS}"),
        ("STRUCTURE_DECL", "structure {IDENT_IND} (α : {TYPE}) where\n  {STRUCT_FIELDS}"),
        ("STRUCTURE_DECL", "structure {IDENT_IND} extends {TYPE_ATOM} where\n  {STRUCT_FIELDS}"),
        ("STRUCTURE_DECL", "structure {IDENT_IND} where\n  mk ::\n  {STRUCT_FIELDS}"),

        // STRUCT_FIELDS
        ("STRUCT_FIELDS", "{IDENT} : {TYPE}"),
        ("STRUCT_FIELDS", "{IDENT} : {TYPE}\n  {IDENT} : {TYPE}"),
        ("STRUCT_FIELDS", "{IDENT} : {TYPE}\n  {IDENT} : {TYPE}\n  {IDENT} : {TYPE}"),
        ("STRUCT_FIELDS", "{IDENT} : {TYPE} := {TERM}"),

        // MUTUAL_BLOCK
        ("MUTUAL_BLOCK", "mutual\n{MUTUAL_DECLS}\nend"),

        // MUTUAL_DECLS
        ("MUTUAL_DECLS", "  {DEF_DECL}\n  {DEF_DECL}"),
        ("MUTUAL_DECLS", "  {DEF_DECL}\n  {DEF_DECL}\n  {DEF_DECL}"),
        ("MUTUAL_DECLS", "  {INDUCTIVE_DECL}\n  {INDUCTIVE_DECL}"),
        ("MUTUAL_DECLS", "  {THEOREM_DECL}\n  {THEOREM_DECL}"),

        // SECTION_BLOCK
        ("SECTION_BLOCK", "section {IDENT}\n{DECL}\nend {IDENT}"),
        ("SECTION_BLOCK", "section\nvariable {BINDER_SINGLE}\n{DECL}\nend"),

        // NAMESPACE_BLOCK
        ("NAMESPACE_BLOCK", "namespace {IDENT}\n{DECL}\nend {IDENT}"),

        // EVAL_CMD
        ("EVAL_CMD", "#check {TERM}"),
        ("EVAL_CMD", "#eval {TERM}"),
        ("EVAL_CMD", "#reduce {TERM}"),
        ("EVAL_CMD", "#print {IDENT}"),
        ("EVAL_CMD", "#print axioms {IDENT}"),

        // ================================================================
        // 3. UNIVERSE LEVELS (targets kernel/level.cpp)
        // ================================================================

        // ULEVEL — universe level expressions
        ("ULEVEL", "0"),
        ("ULEVEL", "1"),
        ("ULEVEL", "2"),
        ("ULEVEL", "{UVAR}"),
        ("ULEVEL", "{ULEVEL} + 1"),
        ("ULEVEL", "max {ULEVEL} {ULEVEL}"),
        ("ULEVEL", "imax {ULEVEL} {ULEVEL}"),
        // Deep nesting for stress testing
        ("ULEVEL", "max ({ULEVEL} + 1) {ULEVEL}"),
        ("ULEVEL", "imax ({ULEVEL} + 1) ({ULEVEL} + 1)"),
        ("ULEVEL", "max (max {ULEVEL} {ULEVEL}) {ULEVEL}"),
        ("ULEVEL", "imax {ULEVEL} (imax {ULEVEL} {ULEVEL})"),

        // UVAR — universe variable names (small pool for reuse)
        ("UVAR", "u"),
        ("UVAR", "v"),
        ("UVAR", "w"),
        ("UVAR_2", "v"),
        ("UVAR_2", "w"),
        ("UVAR_3", "w"),

        // ULEVEL_ANNOT — universe annotation on sorts
        ("ULEVEL_ANNOT", "Type"),
        ("ULEVEL_ANNOT", "Type 0"),
        ("ULEVEL_ANNOT", "Type 1"),
        ("ULEVEL_ANNOT", "Type 2"),
        ("ULEVEL_ANNOT", "Type {UVAR}"),
        ("ULEVEL_ANNOT", "Type (max {ULEVEL} {ULEVEL})"),
        ("ULEVEL_ANNOT", "Type (imax {ULEVEL} {ULEVEL})"),
        ("ULEVEL_ANNOT", "Sort {ULEVEL}"),
        ("ULEVEL_ANNOT", "Sort 0"),
        ("ULEVEL_ANNOT", "Sort 1"),
        ("ULEVEL_ANNOT", "Prop"),

        // ================================================================
        // 4. TYPES
        // ================================================================

        // TYPE — general type expressions
        ("TYPE", "{TYPE_ATOM}"),
        ("TYPE", "{TYPE} → {TYPE}"),
        ("TYPE", "∀ {BINDER_SINGLE}, {TYPE}"),
        ("TYPE", "({IDENT} : {TYPE}) → {TYPE}"),
        ("TYPE", "\\{{IDENT} : {TYPE}\\} → {TYPE}"),
        ("TYPE", "[{TYPE_ATOM} {TYPE_ATOM}] → {TYPE}"),
        ("TYPE", "{TYPE} × {TYPE}"),
        ("TYPE", "{ULEVEL_ANNOT}"),

        // TYPE_ATOM — atomic type expressions
        ("TYPE_ATOM", "Nat"),
        ("TYPE_ATOM", "Int"),
        ("TYPE_ATOM", "Bool"),
        ("TYPE_ATOM", "String"),
        ("TYPE_ATOM", "Unit"),
        ("TYPE_ATOM", "Empty"),
        ("TYPE_ATOM", "Fin {NAT_LIT}"),
        ("TYPE_ATOM", "List {TYPE_ATOM}"),
        ("TYPE_ATOM", "Array {TYPE_ATOM}"),
        ("TYPE_ATOM", "Option {TYPE_ATOM}"),
        ("TYPE_ATOM", "Prod {TYPE_ATOM} {TYPE_ATOM}"),
        ("TYPE_ATOM", "Sum {TYPE_ATOM} {TYPE_ATOM}"),
        ("TYPE_ATOM", "Subtype (fun ({IDENT} : {TYPE_ATOM}) => {PROP_TYPE})"),
        ("TYPE_ATOM", "PLift {TYPE_ATOM}"),
        ("TYPE_ATOM", "ULift {TYPE_ATOM}"),
        ("TYPE_ATOM", "{IDENT_IND}"),

        // PROP_TYPE — proposition types (for theorems)
        ("PROP_TYPE", "True"),
        ("PROP_TYPE", "False"),
        ("PROP_TYPE", "{TERM} = {TERM}"),
        ("PROP_TYPE", "{TERM} ≠ {TERM}"),
        ("PROP_TYPE", "{PROP_TYPE} ∧ {PROP_TYPE}"),
        ("PROP_TYPE", "{PROP_TYPE} ∨ {PROP_TYPE}"),
        ("PROP_TYPE", "{PROP_TYPE} → {PROP_TYPE}"),
        ("PROP_TYPE", "¬{PROP_TYPE}"),
        ("PROP_TYPE", "∀ {BINDER_SINGLE}, {PROP_TYPE}"),
        ("PROP_TYPE", "∃ {BINDER_SINGLE}, {PROP_TYPE}"),
        ("PROP_TYPE", "{TERM} < {TERM}"),
        ("PROP_TYPE", "{TERM} ≤ {TERM}"),
        ("PROP_TYPE", "{TERM} > {TERM}"),
        ("PROP_TYPE", "{TERM} ≥ {TERM}"),
        ("PROP_TYPE", "Nonempty {TYPE_ATOM}"),

        // ================================================================
        // 5. TERMS
        // ================================================================

        // TERM — general terms
        ("TERM", "{LITERAL}"),
        ("TERM", "{IDENT}"),
        ("TERM", "{LAMBDA}"),
        ("TERM", "{APP}"),
        ("TERM", "{LET_EXPR}"),
        ("TERM", "{MATCH_EXPR}"),
        ("TERM", "{IF_EXPR}"),
        ("TERM", "({TERM})"),
        ("TERM", "({TERM} : {TYPE})"),
        ("TERM", "⟨{TERM_LIST}⟩"),
        ("TERM", "\\{{TERM_LIST}\\}"),
        ("TERM", "({TERM}, {TERM})"),
        ("TERM", "{TERM}.1"),
        ("TERM", "{TERM}.2"),
        ("TERM", "{TERM} + {TERM}"),
        ("TERM", "{TERM} * {TERM}"),
        ("TERM", "{TERM} - {TERM}"),
        ("TERM", "{TERM} / {TERM}"),
        ("TERM", "{TERM} % {TERM}"),
        ("TERM", "{TERM} ++ {TERM}"),
        ("TERM", "{TERM} :: {TERM}"),
        ("TERM", "do\n  {DO_BODY}"),
        ("TERM", "@{IDENT} {TERM}"),
        ("TERM", "show {TYPE} from {TERM}"),
        ("TERM", "have {IDENT} : {PROP_TYPE} := {PROOF_TERM}\n{TERM}"),
        ("TERM", "by {TACTIC}"),
        ("TERM", "by\n  {TACTIC_SEQ}"),
        ("TERM", "inferInstance"),
        ("TERM", "default"),

        // TERM_LIST
        ("TERM_LIST", "{TERM}"),
        ("TERM_LIST", "{TERM}, {TERM}"),
        ("TERM_LIST", "{TERM}, {TERM}, {TERM}"),

        // PROOF_TERM — terms that serve as proofs
        ("PROOF_TERM", "rfl"),
        ("PROOF_TERM", "trivial"),
        ("PROOF_TERM", "⟨⟩"),
        ("PROOF_TERM", "True.intro"),
        ("PROOF_TERM", "by {TACTIC}"),
        ("PROOF_TERM", "by\n  {TACTIC_SEQ}"),
        ("PROOF_TERM", "{IDENT}"),
        ("PROOF_TERM", "fun {IDENT} => {PROOF_TERM}"),
        ("PROOF_TERM", "fun {IDENT} {IDENT} => {PROOF_TERM}"),
        ("PROOF_TERM", "fun \\{{IDENT}\\} => {PROOF_TERM}"),
        ("PROOF_TERM", "⟨{PROOF_TERM}, {PROOF_TERM}⟩"),
        ("PROOF_TERM", "Or.inl {PROOF_TERM}"),
        ("PROOF_TERM", "Or.inr {PROOF_TERM}"),
        ("PROOF_TERM", "Exists.intro {TERM} {PROOF_TERM}"),
        ("PROOF_TERM", "absurd {PROOF_TERM} {PROOF_TERM}"),
        ("PROOF_TERM", "({PROOF_TERM} : {PROP_TYPE})"),
        ("PROOF_TERM", "show {PROP_TYPE} from {PROOF_TERM}"),
        ("PROOF_TERM", "False.elim {PROOF_TERM}"),
        ("PROOF_TERM", "{IDENT}.rec {PROOF_TERM}"),
        ("PROOF_TERM", "{IDENT}.casesOn {PROOF_TERM}"),
        ("PROOF_TERM", "nomatch {PROOF_TERM}"),
        ("PROOF_TERM", "Eq.mp {PROOF_TERM} {PROOF_TERM}"),
        ("PROOF_TERM", "Eq.mpr {PROOF_TERM} {PROOF_TERM}"),
        ("PROOF_TERM", "cast {PROOF_TERM} {PROOF_TERM}"),
        ("PROOF_TERM", "Quot.mk {IDENT} {TERM}"),
        ("PROOF_TERM", "Quot.sound {PROOF_TERM}"),
        ("PROOF_TERM", "Quot.lift {TERM} {PROOF_TERM}"),
        ("PROOF_TERM", "propext {PROOF_TERM}"),

        // LAMBDA
        ("LAMBDA", "fun {IDENT} => {TERM}"),
        ("LAMBDA", "fun {IDENT} {IDENT} => {TERM}"),
        ("LAMBDA", "fun {IDENT} {IDENT} {IDENT} => {TERM}"),
        ("LAMBDA", "fun ({IDENT} : {TYPE}) => {TERM}"),
        ("LAMBDA", "fun \\{{IDENT} : {TYPE}\\} => {TERM}"),
        ("LAMBDA", "fun ({IDENT} : {TYPE}) ({IDENT} : {TYPE}) => {TERM}"),
        ("LAMBDA", "fun | {PATTERN} => {TERM}\n    | {PATTERN} => {TERM}"),

        // APP — function application
        ("APP", "{IDENT} {TERM}"),
        ("APP", "{IDENT} {TERM} {TERM}"),
        ("APP", "{IDENT} {TERM} {TERM} {TERM}"),
        ("APP", "({TERM}) {TERM}"),
        ("APP", "@{IDENT} {TERM} {TERM}"),
        ("APP", "{IDENT_IND}.{IDENT_CTOR} {TERM}"),
        ("APP", "{IDENT_IND}.mk {TERM}"),
        ("APP", "{IDENT_IND}.rec {TERM}"),
        ("APP", "{IDENT_IND}.casesOn {TERM} {TERM}"),

        // LET_EXPR
        ("LET_EXPR", "let {IDENT} := {TERM}\n{TERM}"),
        ("LET_EXPR", "let {IDENT} : {TYPE} := {TERM}\n{TERM}"),
        ("LET_EXPR", "let rec {IDENT} : {TYPE} := {TERM}\n{TERM}"),
        ("LET_EXPR", "let \\{{IDENT} : {TYPE}\\} := {TERM}\n{TERM}"),

        // IF_EXPR
        ("IF_EXPR", "if {TERM} then {TERM} else {TERM}"),
        ("IF_EXPR", "if h : {PROP_TYPE} then {TERM} else {TERM}"),

        // MATCH_EXPR
        ("MATCH_EXPR", "match {TERM} with\n{MATCH_ARMS}"),
        ("MATCH_EXPR", "match {TERM}, {TERM} with\n{MATCH_ARMS}"),
        ("MATCH_EXPR", "match h : {TERM} with\n{MATCH_ARMS}"),

        // MATCH_ARMS
        ("MATCH_ARMS", "  | {PATTERN} => {TERM}"),
        ("MATCH_ARMS", "  | {PATTERN} => {TERM}\n  | {PATTERN} => {TERM}"),
        ("MATCH_ARMS", "  | {PATTERN} => {TERM}\n  | {PATTERN} => {TERM}\n  | {PATTERN} => {TERM}"),

        // DO_BODY
        ("DO_BODY", "return {TERM}"),
        ("DO_BODY", "let {IDENT} ← {TERM}\n  return {IDENT}"),
        ("DO_BODY", "let {IDENT} ← {TERM}\n  {DO_BODY}"),
        ("DO_BODY", "{TERM}"),

        // ================================================================
        // 6. TACTICS (targets Elaborator → Kernel boundary)
        // ================================================================

        // TACTIC — single tactic
        ("TACTIC", "exact {PROOF_TERM}"),
        ("TACTIC", "apply {PROOF_TERM}"),
        ("TACTIC", "intro {IDENT}"),
        ("TACTIC", "intro {IDENT} {IDENT}"),
        ("TACTIC", "intros"),
        ("TACTIC", "assumption"),
        ("TACTIC", "trivial"),
        ("TACTIC", "rfl"),
        ("TACTIC", "decide"),
        ("TACTIC", "omega"),
        ("TACTIC", "simp"),
        ("TACTIC", "simp [{IDENT}]"),
        ("TACTIC", "simp only [{IDENT}]"),
        ("TACTIC", "simp [*]"),
        ("TACTIC", "simp_all"),
        ("TACTIC", "norm_num"),
        ("TACTIC", "ring"),
        ("TACTIC", "linarith"),
        ("TACTIC", "contradiction"),
        ("TACTIC", "exfalso"),
        ("TACTIC", "constructor"),
        ("TACTIC", "cases {IDENT}"),
        ("TACTIC", "cases {IDENT} with\n{CASE_ARMS}"),
        ("TACTIC", "induction {IDENT} with\n{CASE_ARMS}"),
        ("TACTIC", "rcases {IDENT} with {RCASES_PAT}"),
        ("TACTIC", "obtain ⟨{IDENT}, {IDENT}⟩ := {PROOF_TERM}"),
        ("TACTIC", "have {IDENT} : {PROP_TYPE} := {PROOF_TERM}"),
        ("TACTIC", "have {IDENT} : {PROP_TYPE} := by {TACTIC}"),
        ("TACTIC", "let {IDENT} : {TYPE} := {TERM}"),
        ("TACTIC", "suffices {IDENT} : {PROP_TYPE} by {TACTIC}"),
        ("TACTIC", "show {PROP_TYPE}"),
        ("TACTIC", "rewrite [{PROOF_TERM}]"),
        ("TACTIC", "rw [{PROOF_TERM}]"),
        ("TACTIC", "rw [← {PROOF_TERM}]"),
        ("TACTIC", "calc\n    {TERM} = {TERM} := {PROOF_TERM}\n    _ = {TERM} := {PROOF_TERM}"),
        ("TACTIC", "ext"),
        ("TACTIC", "ext {IDENT}"),
        ("TACTIC", "funext"),
        ("TACTIC", "funext {IDENT}"),
        ("TACTIC", "congr"),
        ("TACTIC", "left"),
        ("TACTIC", "right"),
        ("TACTIC", "use {TERM}"),
        ("TACTIC", "exists {TERM}"),
        ("TACTIC", "refine {PROOF_TERM}"),
        ("TACTIC", "refine ?_"),
        ("TACTIC", "aesop"),
        ("TACTIC", "native_decide"),
        ("TACTIC", "unfold {IDENT}"),
        ("TACTIC", "delta {IDENT}"),
        ("TACTIC", "dsimp"),
        ("TACTIC", "dsimp [{IDENT}]"),
        ("TACTIC", "change {PROP_TYPE}"),
        ("TACTIC", "conv => {CONV_TACTIC}"),

        // CONV_TACTIC
        ("CONV_TACTIC", "rfl"),
        ("CONV_TACTIC", "ring"),
        ("CONV_TACTIC", "simp"),
        ("CONV_TACTIC", "rw [{PROOF_TERM}]"),
        ("CONV_TACTIC", "lhs\n  {CONV_TACTIC}"),
        ("CONV_TACTIC", "rhs\n  {CONV_TACTIC}"),

        // TACTIC_SEQ — sequence of tactics
        ("TACTIC_SEQ", "{TACTIC}"),
        ("TACTIC_SEQ", "{TACTIC}\n  {TACTIC}"),
        ("TACTIC_SEQ", "{TACTIC}\n  {TACTIC}\n  {TACTIC}"),
        ("TACTIC_SEQ", "{TACTIC}\n  {TACTIC}\n  {TACTIC}\n  {TACTIC}"),
        ("TACTIC_SEQ", "{TACTIC} <;> {TACTIC}"),
        ("TACTIC_SEQ", "first\n  | {TACTIC}\n  | {TACTIC}"),

        // CASE_ARMS — for cases/induction
        ("CASE_ARMS", "  | {IDENT_CTOR} => {TACTIC}"),
        ("CASE_ARMS", "  | {IDENT_CTOR} => {TACTIC}\n  | {IDENT_CTOR_2} => {TACTIC}"),
        ("CASE_ARMS", "  | {IDENT_CTOR} {IDENT} => {TACTIC}\n  | {IDENT_CTOR_2} {IDENT} {IDENT} => {TACTIC}"),

        // RCASES_PAT
        ("RCASES_PAT", "⟨{IDENT}, {IDENT}⟩"),
        ("RCASES_PAT", "⟨{IDENT}, {IDENT}, {IDENT}⟩"),
        ("RCASES_PAT", "⟨⟩"),
        ("RCASES_PAT", "({IDENT} | {IDENT})"),

        // ================================================================
        // 7. PATTERNS
        // ================================================================

        ("PATTERN", "{PATTERN_ATOM}"),
        ("PATTERN", "{IDENT_CTOR} {PATTERN_ATOM}"),
        ("PATTERN", "{IDENT_CTOR} {PATTERN_ATOM} {PATTERN_ATOM}"),
        ("PATTERN", "({PATTERN})"),
        ("PATTERN", "{PATTERN_ATOM}, {PATTERN_ATOM}"),

        ("PATTERN_ATOM", "_"),
        ("PATTERN_ATOM", "{IDENT}"),
        ("PATTERN_ATOM", "{LITERAL}"),
        ("PATTERN_ATOM", "0"),
        ("PATTERN_ATOM", "{IDENT} + 1"),
        ("PATTERN_ATOM", "[]"),
        ("PATTERN_ATOM", "{PATTERN_ATOM} :: {PATTERN_ATOM}"),
        ("PATTERN_ATOM", "some {PATTERN_ATOM}"),
        ("PATTERN_ATOM", "none"),
        ("PATTERN_ATOM", "true"),
        ("PATTERN_ATOM", "false"),
        ("PATTERN_ATOM", "⟨{PATTERN_ATOM}, {PATTERN_ATOM}⟩"),

        // ================================================================
        // 8. BINDERS
        // ================================================================

        ("BINDERS", "{BINDER_SINGLE}"),
        ("BINDERS", "{BINDER_SINGLE} {BINDER_SINGLE}"),
        ("BINDERS", "{BINDER_SINGLE} {BINDER_SINGLE} {BINDER_SINGLE}"),

        ("BINDER_SINGLE", "({IDENT} : {TYPE})"),
        ("BINDER_SINGLE", "\\{{IDENT} : {TYPE}\\}"),
        ("BINDER_SINGLE", "[{TYPE_ATOM} {TYPE_ATOM}]"),
        ("BINDER_SINGLE", "({IDENT} : {TYPE}) ({IDENT} : {TYPE})"),
        ("BINDER_SINGLE", "\\{{IDENT} : {TYPE}\\} \\{{IDENT} : {TYPE}\\}"),
        ("BINDER_SINGLE", "[{IDENT_IND} α]"),
        ("BINDER_SINGLE", "(α : Type)"),
        ("BINDER_SINGLE", "(α β : Type)"),
        ("BINDER_SINGLE", "\\{α : Type\\}"),
        ("BINDER_SINGLE", "\\{α β : Type\\}"),
        ("BINDER_SINGLE", "(α : Type u)"),
        ("BINDER_SINGLE", "\\{α : Type u\\}"),
        ("BINDER_SINGLE", "(α : Sort u)"),

        // ================================================================
        // 9. IDENTIFIERS (small pools for name reuse / shadowing)
        // ================================================================

        // IDENT — general identifiers
        ("IDENT", "x"),
        ("IDENT", "y"),
        ("IDENT", "z"),
        ("IDENT", "a"),
        ("IDENT", "b"),
        ("IDENT", "f"),
        ("IDENT", "g"),
        ("IDENT", "h"),
        ("IDENT", "n"),
        ("IDENT", "m"),
        ("IDENT", "p"),
        ("IDENT", "q"),
        ("IDENT", "α"),
        ("IDENT", "β"),
        ("IDENT", "val"),
        ("IDENT", "acc"),
        ("IDENT", "hx"),
        ("IDENT", "hy"),

        // IDENT_IND — inductive type names
        ("IDENT_IND", "MyType"),
        ("IDENT_IND", "MyInd"),
        ("IDENT_IND", "Foo"),
        ("IDENT_IND", "Bar"),
        ("IDENT_IND", "Baz"),
        ("IDENT_IND", "W"),
        ("IDENT_IND", "Tree"),
        ("IDENT_IND", "Expr"),
        ("IDENT_IND", "MyProp"),
        ("IDENT_IND", "MyClass"),
        ("IDENT_IND", "Wrap"),
        ("IDENT_IND", "Container"),
        ("IDENT_IND", "Indexed"),
        ("IDENT_IND", "Nested"),
        ("IDENT_IND", "Evil"),
        ("IDENT_IND", "Tricky"),

        // IDENT_CTOR — constructor names
        ("IDENT_CTOR", "mk"),
        ("IDENT_CTOR", "nil"),
        ("IDENT_CTOR", "cons"),
        ("IDENT_CTOR", "leaf"),
        ("IDENT_CTOR", "node"),
        ("IDENT_CTOR", "zero"),
        ("IDENT_CTOR", "succ"),
        ("IDENT_CTOR", "intro"),
        ("IDENT_CTOR", "inl"),
        ("IDENT_CTOR", "inr"),
        ("IDENT_CTOR", "base"),
        ("IDENT_CTOR", "step"),

        // Duplicate pools for multi-constructor rules
        ("IDENT_CTOR_2", "nil"),
        ("IDENT_CTOR_2", "cons"),
        ("IDENT_CTOR_2", "node"),
        ("IDENT_CTOR_2", "succ"),
        ("IDENT_CTOR_2", "inr"),
        ("IDENT_CTOR_2", "step"),
        ("IDENT_CTOR_2", "other"),

        ("IDENT_CTOR_3", "leaf"),
        ("IDENT_CTOR_3", "base"),
        ("IDENT_CTOR_3", "other"),
        ("IDENT_CTOR_3", "extra"),

        // ================================================================
        // 10. LITERALS
        // ================================================================

        ("LITERAL", "{NAT_LIT}"),
        ("LITERAL", "\"{STR_LIT}\""),
        ("LITERAL", "true"),
        ("LITERAL", "false"),
        ("LITERAL", "()"),
        ("LITERAL", "#[]"),
        ("LITERAL", "[]"),
        ("LITERAL", "[{TERM}]"),
        ("LITERAL", "[{TERM}, {TERM}]"),

        ("NAT_LIT", "0"),
        ("NAT_LIT", "1"),
        ("NAT_LIT", "2"),
        ("NAT_LIT", "3"),
        ("NAT_LIT", "42"),
        ("NAT_LIT", "100"),
        ("NAT_LIT", "256"),
        ("NAT_LIT", "999999999999"),

        ("STR_LIT", "hello"),
        ("STR_LIT", "test"),
        ("STR_LIT", ""),
        ("STR_LIT", "abc"),

        // ================================================================
        // 11. GOLDEN CHECKS — soundness oracle
        // ================================================================

        // GOLDEN_CHECK — various ways to check for accepted False
        ("GOLDEN_CHECK", "{GOLDEN_THEOREM}"),
        ("GOLDEN_CHECK", "{GOLDEN_VERIFY}"),
        ("GOLDEN_CHECK", "{GOLDEN_THEOREM}\n{GOLDEN_VERIFY}"),

        // GOLDEN_THEOREM — theorem claiming False or 0=1
        ("GOLDEN_THEOREM", "theorem soundness_check : False := {PROOF_TERM}"),
        ("GOLDEN_THEOREM", "theorem soundness_check : (0 : Nat) = 1 := {PROOF_TERM}"),
        ("GOLDEN_THEOREM", "theorem soundness_check : (2 + 2 : Nat) = 5 := {PROOF_TERM}"),
        ("GOLDEN_THEOREM", "theorem soundness_check : ∀ (P : Prop), P := {PROOF_TERM}"),
        ("GOLDEN_THEOREM", "theorem soundness_check : False := by\n  {TACTIC_SEQ}"),
        ("GOLDEN_THEOREM", "theorem soundness_check : (0 : Nat) = 1 := by\n  {TACTIC_SEQ}"),
        ("GOLDEN_THEOREM", "theorem soundness_check : Empty := {PROOF_TERM}"),
        ("GOLDEN_THEOREM", "def soundness_check : False := {PROOF_TERM}"),

        // GOLDEN_VERIFY — ask Lean to print axioms used
        ("GOLDEN_VERIFY", "#print axioms soundness_check"),
        ("GOLDEN_VERIFY", "#check (soundness_check : False)"),
        ("GOLDEN_VERIFY", "#check soundness_check"),
        ("GOLDEN_VERIFY", ""),

        // ================================================================
        // 12. METAPROGRAMMING (targets Elaborator/Environment)
        // ================================================================

        // ELAB_DECL — custom elaborators
        ("ELAB_DECL", "elab \"{IDENT}_cmd\" : command => do\n  let env ← Lean.Elab.Command.getEnv\n  Lean.logInfo s!\"env size: \\{env.constants.size\\}\""),
        ("ELAB_DECL", "elab \"{IDENT}_term\" : term => do\n  return Lean.mkConst ``True"),
        ("ELAB_DECL", "elab \"{IDENT}_tactic\" : tactic => do\n  Lean.Elab.Tactic.evalTactic (← `(tactic| trivial))"),
        ("ELAB_DECL", "elab \"{IDENT}_cmd\" : command => do\n  let env ← Lean.Elab.Command.getEnv\n  let some info := env.find? `{IDENT}\n    | throwError \"not found\"\n  Lean.logInfo s!\"found: \\{info.name\\}\""),

        // MACRO_DECL — syntax macros
        ("MACRO_DECL", "macro \"{IDENT}_mac\" : term => `({TERM})"),
        ("MACRO_DECL", "macro \"{IDENT}_mac\" : term => `(by trivial)"),
        ("MACRO_DECL", "macro \"{IDENT}_mac\" : command => `(#check {TERM})"),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{HashMap, HashSet, VecDeque};

    /// Extract nonterminal references from an expansion string.
    /// `{FOO}` is a reference; `\{...\}` is an escaped literal brace.
    fn extract_nt_refs(expansion: &str) -> Vec<String> {
        let bytes = expansion.as_bytes();
        let mut refs = Vec::new();
        let mut i = 0;
        while i < bytes.len() {
            if bytes[i] == b'{' && (i == 0 || bytes[i - 1] != b'\\') {
                // Start of NT reference
                let start = i + 1;
                if let Some(end_offset) = expansion[start..].find('}') {
                    let name = &expansion[start..start + end_offset];
                    // Skip if this looks like an escaped close brace pair
                    if !name.is_empty() && !name.contains('\\') {
                        refs.push(name.to_string());
                    }
                    i = start + end_offset + 1;
                } else {
                    i += 1;
                }
            } else {
                i += 1;
            }
        }
        refs
    }

    #[test]
    fn rules_nonempty() {
        let rules = lean4_rules();
        assert!(rules.len() > 300, "expected 300+ rules, got {}", rules.len());
    }

    #[test]
    fn rules_are_pairs() {
        for rule in lean4_rules() {
            assert_eq!(rule.len(), 2, "each rule must be [nonterminal, expansion]");
        }
    }

    #[test]
    fn first_rule_is_file() {
        let rules = lean4_rules();
        assert_eq!(rules[0][0], "FILE", "first rule must define FILE (Nautilus auto-wraps in START)");
    }

    #[test]
    fn all_nonterminals_nonempty() {
        for (i, rule) in lean4_rules().iter().enumerate() {
            assert!(!rule[0].is_empty(), "rule {i} has empty nonterminal");
        }
    }

    // --- New tests below ---

    #[test]
    fn no_orphan_nonterminals() {
        let raw = rules_raw();
        let defined: HashSet<&str> = raw.iter().map(|(nt, _)| *nt).collect();

        for (i, (nt, expansion)) in raw.iter().enumerate() {
            for ref_nt in extract_nt_refs(expansion) {
                assert!(
                    defined.contains(ref_nt.as_str()),
                    "rule {i} ({nt}): references undefined nonterminal {{{ref_nt}}}"
                );
            }
        }
    }

    #[test]
    fn all_nonterminals_reachable_from_file() {
        let raw = rules_raw();

        // Build adjacency: NT -> set of referenced NTs
        let mut adj: HashMap<&str, HashSet<String>> = HashMap::new();
        let defined: HashSet<&str> = raw.iter().map(|(nt, _)| *nt).collect();
        for (nt, expansion) in &raw {
            let refs = extract_nt_refs(expansion);
            adj.entry(nt).or_default().extend(refs);
        }

        // BFS from FILE
        let mut visited: HashSet<&str> = HashSet::new();
        let mut queue: VecDeque<&str> = VecDeque::new();
        queue.push_back("FILE");
        visited.insert("FILE");

        while let Some(current) = queue.pop_front() {
            if let Some(neighbors) = adj.get(current) {
                for neighbor in neighbors {
                    if let Some(&defined_nt) = defined.iter().find(|&&d| d == neighbor.as_str()) {
                        if visited.insert(defined_nt) {
                            queue.push_back(defined_nt);
                        }
                    }
                }
            }
        }

        let unreachable: Vec<&str> = defined.iter()
            .filter(|nt| !visited.contains(**nt))
            .copied()
            .collect();
        assert!(
            unreachable.is_empty(),
            "unreachable nonterminals from FILE: {unreachable:?}"
        );
    }

    #[test]
    fn no_duplicate_rules() {
        let raw = rules_raw();
        let mut seen: HashSet<(&str, &str)> = HashSet::new();
        for (i, (nt, expansion)) in raw.iter().enumerate() {
            assert!(
                seen.insert((nt, expansion)),
                "duplicate rule at index {i}: ({nt}, {expansion})"
            );
        }
    }

    #[test]
    fn escaped_braces_are_balanced() {
        let raw = rules_raw();
        for (i, (nt, expansion)) in raw.iter().enumerate() {
            let open_count = expansion.matches("\\{").count();
            let close_count = expansion.matches("\\}").count();
            assert_eq!(
                open_count, close_count,
                "rule {i} ({nt}): unbalanced escaped braces (\\{{ = {open_count}, \\}} = {close_count}) in: {expansion}"
            );
        }
    }

    #[test]
    fn rule_count_regression() {
        let count = rules_raw().len();
        assert_eq!(
            count, 515,
            "expected exactly 515 rules, got {count} — was a rule accidentally added or removed?"
        );
    }

    #[test]
    fn golden_check_rules_claim_false() {
        let raw = rules_raw();
        let golden_theorems: Vec<&str> = raw.iter()
            .filter(|(nt, _)| *nt == "GOLDEN_THEOREM")
            .map(|(_, exp)| *exp)
            .collect();

        assert!(
            !golden_theorems.is_empty(),
            "no GOLDEN_THEOREM rules found — soundness oracle is missing"
        );

        // Every golden theorem must claim something false/impossible
        let false_indicators = ["False", "0 : Nat) = 1", "2 + 2 : Nat) = 5", "∀ (P : Prop), P", "Empty"];
        for theorem in &golden_theorems {
            assert!(
                false_indicators.iter().any(|ind| theorem.contains(ind)),
                "GOLDEN_THEOREM doesn't claim something impossible: {theorem}"
            );
        }
    }

    #[test]
    fn all_grammar_categories_present() {
        let raw = rules_raw();
        let defined: HashSet<&str> = raw.iter().map(|(nt, _)| *nt).collect();

        let required = [
            "FILE", "PREAMBLE", "PROGRAM", "DECL",
            "DEF_DECL", "THEOREM_DECL", "INDUCTIVE_DECL",
            "TACTIC", "TACTIC_SEQ", "TERM", "TYPE", "TYPE_ATOM",
            "PROP_TYPE", "PROOF_TERM", "BINDERS", "BINDER_SINGLE",
            "ULEVEL", "GOLDEN_CHECK", "GOLDEN_THEOREM",
            "IDENT", "IDENT_IND", "IDENT_CTOR",
            "ELAB_DECL", "MACRO_DECL",
        ];

        for &cat in &required {
            assert!(
                defined.contains(cat),
                "required grammar category {cat} is missing"
            );
        }
    }

    #[test]
    fn nonterminal_count_per_category() {
        let raw = rules_raw();
        let mut counts: HashMap<&str, usize> = HashMap::new();
        for (nt, _) in &raw {
            *counts.entry(nt).or_default() += 1;
        }

        // Minimum rule counts for critical nonterminals that need diversity
        let minimums: &[(&str, usize)] = &[
            ("TACTIC", 30),
            ("TERM", 15),
            ("TYPE", 5),
            ("PROOF_TERM", 10),
            ("INDUCTIVE_DECL", 10),
            ("IDENT", 10),
            ("IDENT_IND", 10),
        ];

        for &(nt, min) in minimums {
            let actual = counts.get(nt).copied().unwrap_or(0);
            assert!(
                actual >= min,
                "{nt} has only {actual} rules, expected at least {min} for diversity"
            );
        }
    }
}
