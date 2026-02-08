# SOTA Lean 4 Soundness Fuzzer - Design Plan v2

## Context

Prior work on this project found 0 soundness bugs across 615+ manually-crafted attack vectors. The current Nautilus grammar-based approach generates code that is almost always type-invalid, wasting compute budget on parse/elaboration failures. Meanwhile, LLM agents produce valid code but only explore familiar attack patterns. **The gap between these approaches is where soundness bugs hide.** This plan redesigns the fuzzer from first principles, informed by 12 SOTA papers on LLM-guided fuzzing.

---

## Core Insight: The Poisoned Prefix Pattern

Every generated file has the structure:

```lean
-- ========== FUZZER-GENERATED PREFIX ==========
-- (declarations that attempt to corrupt the logical environment)
universe u v w
inductive Evil where ...
instance : ... where ...
def sneaky := ...
-- ...more declarations...

-- ========== FIXED GOLDEN SUFFIX ==========
theorem soundness_check : False := by
  auto  -- or: simp_all; omega; decide; native_decide; aesop; trivial
```

**The fuzzer only generates the PREFIX.** The suffix is fixed and always claims `False`. If the prefix contains declarations that exploit a soundness bug in Lean's kernel, the automation tactic in the suffix will find the proof and the file will compile. **If `lake build` succeeds on this file, we have found a soundness bug.**

This is dramatically simpler and more powerful than generating both declarations AND proofs:
1. **We never need to generate proof terms** -- the hardest part of the old approach
2. **The oracle is trivial**: does `lake build` succeed? (with no `sorry` in prefix)
3. **All fuzzing effort goes into prefix diversity** -- declarations that corrupt the environment
4. **Multiple golden suffixes** can be appended to test different automation tactics

### Golden Suffix Variants (appended to every generated prefix)

```lean
-- Variant 1: kitchen-sink automation
theorem soundness_check_1 : False := by auto

-- Variant 2: simp with all definitions
theorem soundness_check_2 : False := by simp_all

-- Variant 3: native_decide (bypasses kernel for some checks)
theorem soundness_check_3 : False := by native_decide

-- Variant 4: omega (integer arithmetic)
theorem soundness_check_4 : (0 : Nat) = 1 := by omega

-- Variant 5: decide (decidable propositions)
theorem soundness_check_5 : False := by decide

-- Variant 6: aesop (general-purpose search)
theorem soundness_check_6 : False := by aesop

-- Variant 7: exact proof from environment
theorem soundness_check_7 : False := by assumption

-- Variant 8: type class resolution
theorem soundness_check_8 : False := inferInstance
```

Each prefix is tested against ALL variants. Different tactics exercise different code paths -- a bug in `native_decide` is different from a bug in the kernel's type checker.

---

## What the Prefix Generator Must Produce

The prefix is a sequence of Lean declarations designed to **poison the environment** so that `False` becomes provable. The key attack categories:

### Category 1: Poisoned Inductive Types
Inductive types that violate positivity, universe constraints, or well-formedness in subtle ways. If the kernel's positivity checker has a gap, a negative-occurrence inductive could make `False` constructible.

```lean
-- Example: trying to smuggle negative occurrence through a type alias
abbrev F (a : Type) := a -> False
inductive Evil where
  | mk : F Evil -> Evil  -- should be rejected (negative occurrence)
```

### Category 2: Universe Level Tricks
Universe level expressions that confuse the kernel's universe checking. The `imax` function has special behavior (`imax u 0 = 0`) that could lead to inconsistencies.

```lean
universe u v
-- Exploit imax discontinuity
inductive Bad.{w} : Sort (imax w (max u v + 1)) where
  | mk : Bad.{w}
```

### Category 3: Typeclass Poisoning
Instances that make `False` an instance of something, or create circular resolution chains that produce bogus terms.

```lean
class Absurd (a : Prop) where
  proof : a
instance : Absurd False where
  proof := ???  -- if typeclass resolution accepts this...
```

### Category 4: Mutual/Nested Inductive Exploits
Complex mutual blocks where cross-references create subtle inconsistencies.

```lean
mutual
  inductive A where | mk : B -> A
  inductive B where | mk : (A -> False) -> B  -- sneaky negative occurrence
end
```

### Category 5: Definitional Equality Tricks
Definitions that create unexpected definitional equalities, potentially confusing the type checker.

```lean
@[reducible] def MyFalse := True  -- lol
-- Then later, prove MyFalse (which reduces to True) but claim it's False
```

### Category 6: Elaborator Abuse
Macros, custom elaborators, and syntax extensions that produce kernel terms the elaborator wouldn't normally generate.

```lean
elab "evil_term" : term => do
  return Lean.mkConst ``True  -- returns True but claims it can be any type
```

### Category 7: Quotient/Axiom Smuggling
Exploiting the trusted quotient axioms or creating axiom-like declarations via subtle means.

---

## Architecture: Prefix Generator + Fixed Oracle

```
                         STRATEGY LAYER
                  +----------------------------+
                  |  (A) Attack Planner        |
                  |  (LLM + UCB1 bandits)      |
                  +--------------+-------------+
                                 | prefix templates
                                 v
                         GENERATION LAYER
        +-----------------------------------------------+
        |  (B) Prefix Synthesizer   (C) Repair Engine   |
        |  (LLM-generated decls)   (fix syntax/types)   |
        |         |                      ^               |
        |         v                      | errors        |
        |  (D) Structure-Aware Mutator                   |
        |  (Nautilus on PREFIX GRAMMAR ONLY)              |
        +------------------------+-----------------------+
                                 | prefix declarations
                                 v
                         ASSEMBLY + EXECUTION
        +-----------------------------------------------+
        |  Assembler: prefix + FIXED golden suffixes     |
        |           |                                    |
        |  (E) Multi-Stage Executor                      |
        |  (parse -> elaborate -> kernel)                 |
        |           |                                    |
        |  (F) Oracle: did ANY golden suffix compile?    |
        |  (G) Feedback: error stage + error class       |
        +-----------------------------------------------+
```

### Key difference from previous plan
- The **grammar generates ONLY the prefix** (declarations, not proofs)
- The **golden suffixes are fixed** and appended by the assembler
- The **oracle is trivial**: `lake build` succeeded -> soundness bug found
- The **Repair Engine focuses on making prefix declarations compile** (not proofs)
- **Proof terms are never generated** -- automation tactics do the proof search

---

## Revised Grammar Design (PREFIX_GRAMMAR)

The grammar in `generator/src/grammar.rs` should be restructured to generate only prefix declarations. The `GOLDEN_CHECK`, `PROOF_TERM`, `TACTIC`, and `TACTIC_SEQ` non-terminals are removed from the grammar -- they're now in the fixed suffix.

```
FILE -> PREAMBLE \n\n PREFIX_PROGRAM
PREFIX_PROGRAM -> PREFIX_DECL | PREFIX_DECL \n\n PREFIX_DECL | ...
PREFIX_DECL -> INDUCTIVE_DECL | DEF_DECL | ABBREV_DECL | AXIOM_DECL
            | CLASS_DECL | INSTANCE_DECL | STRUCTURE_DECL | MUTUAL_BLOCK
            | OPAQUE_DECL | ELAB_DECL | MACRO_DECL | SECTION_BLOCK | ...
```

The golden suffixes are appended by the executor, not generated by the grammar. This means:
- **100% of grammar rules focus on declaration diversity** -- no wasted rules on proof terms
- **Mutations only affect declarations** -- every mutation changes the logical environment
- **Validity = prefix compiles without the golden suffix** -- much easier to achieve

### New grammar categories to add
1. **ATTR_DECL**: `@[simp] theorem ...`, `@[instance] def ...` -- attributes that affect automation
2. **NOTATION_DECL**: Custom notation that could confuse the parser/elaborator
3. **SCOPED_INSTANCE**: `scoped instance ...` -- instances that only apply in certain scopes
4. **DERIVE_HANDLER**: `deriving instance Decidable` -- generated instances
5. **OPAQUE_TRICK**: `opaque` + `@[reducible]` combinations
6. **UNIVERSE_CMD**: `set_option ... in` -- options that affect checking behavior

---

## Phase 1: Assembler + Executor + Oracle (Week 1-2)

**Why first**: The assembler pattern (prefix + fixed suffix) is the foundation of everything.

### Files to create/modify
- `scaffold/src/scaffold/executor.py` -- Assembler + multi-stage executor
- `scaffold/src/scaffold/oracle.py` -- Simple: did it compile?
- `scaffold/src/scaffold/golden_suffixes.py` -- The 8+ fixed golden suffixes
- Modify `template/` to support parallel copies

### Assembler logic
```python
def assemble(prefix: str) -> list[str]:
    """Combine a generated prefix with each golden suffix."""
    candidates = []
    for suffix in GOLDEN_SUFFIXES:
        full_file = f"{prefix}\n\n{suffix}"
        candidates.append(full_file)
    return candidates

def execute(prefix: str) -> ExecutionResult:
    candidates = assemble(prefix)
    for i, candidate in enumerate(candidates):
        write_to_template(candidate)
        result = lake_build()
        if result.success:
            # CHECK: does the prefix contain sorry, axiom False, etc?
            if not has_escape_hatches(prefix):
                return GOLDEN_SIGNAL(suffix_index=i, prefix=prefix)
        # Even on failure, classify the error for feedback
        classify_error(result.stderr)
    return best_error_result  # deepest stage reached
```

### Prefix validation (anti-cheating)
Before declaring a golden signal, verify the prefix doesn't trivially prove False:
- No `sorry` anywhere in prefix
- No `axiom ... : False` or `axiom ... : 0 = 1`
- No `unsafe` definitions used in logical context
- No `implemented_by` or `extern` that could bypass checking
- Run `#print axioms soundness_check` to verify no unexpected axioms

### Parallel execution
Create pool of 16-64 template copies. Each prefix is tested against all golden suffixes in sequence (fast: ~1-5s per suffix since they share the prefix compilation).

---

## Phase 2: Prefix-Only Grammar + Enhanced Mutator (Week 2-3)

### Files to modify
- `generator/src/grammar.rs` -- Restructure as PREFIX_GRAMMAR
- `generator/src/main.rs` -- Output prefixes only, send to assembler

### Grammar restructuring
1. **Remove**: GOLDEN_CHECK, GOLDEN_THEOREM, GOLDEN_VERIFY, PROOF_TERM, TACTIC, TACTIC_SEQ, CASE_ARMS, RCASES_PAT (these are in the fixed suffix now)
2. **Keep**: All declaration-level non-terminals (INDUCTIVE_DECL, DEF_DECL, etc.)
3. **Expand**: Add many more rules for the 7 attack categories above
4. **Add**: THEOREM_DECL without proof (e.g., `theorem helper : P := sorry` -- these sorrys in *helper lemmas* are fine as long as the golden suffix doesn't use them. Actually: **prefix declarations CAN use sorry** in non-False theorems to build up a library of "proved" lemmas that the golden suffix's automation might use)

Wait -- important refinement: **The prefix CAN contain `sorry`-using helper lemmas** as long as we verify that the final `soundness_check` theorem doesn't transitively depend on them. We check this with `#print axioms soundness_check` -- if it mentions `sorryAx`, it's not a real bug.

### Semantic mutation operators
1. **Universe Perturbation**: Mutate universe level expressions in inductive types
2. **Positivity Scramble**: Rearrange constructor argument positions (positive <-> negative)
3. **Instance Swap**: Replace instance definitions with structurally different implementations
4. **Attribute Toggle**: Add/remove @[simp], @[reducible], @[instance] etc.
5. **Declaration Reorder**: Shuffle declaration order (shouldn't matter but might expose bugs)
6. **Nesting Injection**: Wrap declarations in sections/namespaces/mutual blocks

---

## Phase 3: LLM Seed Generation + Repair (Week 3-4)

### Files to create
- `scaffold/src/scaffold/synthesizer.py` -- LLM prefix generation
- `scaffold/src/scaffold/repair.py` -- Iterative prefix repair
- BAML definitions for structured LLM calls

### Prefix Synthesizer
Ask Claude to generate poisoned prefixes targeting specific attack categories:

```
System: You are an expert in dependent type theory and the Lean 4 kernel.
Generate a sequence of Lean 4 declarations that might exploit a soundness bug
in the kernel's {subsystem} checking. The declarations should:
1. All compile without errors individually
2. Together, create an environment where False might be provable
3. Target {specific_attack_vector}
4. NOT use sorry, axiom False, or unsafe

The declarations will be followed by:
  theorem soundness_check : False := by auto
If your prefix exploits a real kernel bug, this theorem will compile.
```

### Repair Engine (prefix-focused)
When a prefix has syntax/type errors, repair it:
```
for attempt in range(5):
    # Only compile the PREFIX (without golden suffix)
    result = compile(prefix + "\n\n-- placeholder, no golden check")
    if result.success: return prefix
    prefix = llm_fix(prefix, errors, attack_intent)
```

The repair only needs to make the DECLARATIONS valid -- much easier than making proofs valid.

### Sorry-seeding strategy
Generate prefixes where some helper theorems use `sorry`:
```lean
-- Prefix with sorry helpers (fine as long as golden check doesn't depend on them)
theorem helper1 : forall n : Nat, n = n := by sorry
theorem helper2 : forall P Q : Prop, P -> Q := by sorry
-- ... then golden suffix tries: theorem soundness_check : False := by auto
-- If auto can prove False using helper2 (which is unsound), #print axioms will show sorryAx
-- So this is NOT a real bug -- our filter catches it
```

But if the kernel has a bug in how it *checks* these declarations (even the sorry-using ones), the golden suffix might succeed without depending on sorry. This is the sweet spot.

---

## Phase 4: Feedback Loop + Corpus Management (Week 4-5)

### Files to create
- `scaffold/src/scaffold/feedback.py`

### Error classification
For each prefix, track:
- **Best stage reached** across all golden suffix variants
- **Error class** (universe error, positivity, type mismatch, etc.)
- **Which golden suffixes got closest** (some tactics exercise different paths)
- **Prefix complexity** (number of declarations, nesting depth)

### Tiered corpus
| Tier | Criterion | Description |
|------|-----------|-------------|
| 0 | Prefix compiles, golden suffix *almost* works | Highest priority -- closest to success |
| 1 | Prefix compiles, golden suffix fails normally | Good seed, mutation might push it over |
| 2 | Prefix has minor errors | Repair engine candidate |
| Discard | Parse failure | Not useful |

"Almost works" = the golden suffix's error is about the proof not being found (not about declarations being ill-typed). This means the environment is well-formed but the automation couldn't prove False -- exactly one mutation away from a potential bug.

---

## Phase 5: Attack Planner (Week 5-6)

### Files to create
- `scaffold/src/scaffold/planner.py`

### UCB1 bandit over attack categories
Each attack category (universe, positivity, typeclass, etc.) is a bandit arm.
- **Reward** = fraction of prefixes from this category that reach Tier 0 or Tier 1
- **Exploration bonus** = standard UCB1 term
- Templates with higher success at producing compilable prefixes get more attention

### LLM-driven template evolution
When a prefix from category X reaches Tier 0 (prefix compiles, golden fails):
1. Ask LLM: "This prefix compiled but False wasn't provable. What subtle change to the declarations might make False provable?"
2. Generate N variants of the near-miss prefix
3. Test all variants against all golden suffixes

---

## Phase 6: Advanced Differential Testing (Week 6-8)

### Additional checks for flagged candidates
When a golden suffix succeeds:
1. `#print axioms soundness_check` -- verify no `sorryAx`, no unexpected axioms
2. `lean4export` -> examine the exported declaration
3. `comparator` -> cross-check with reference kernel
4. `safeverify` -> independent re-verification
5. `lean4lean` -> pure Lean kernel reimplementation check

### Differential testing for NON-golden-signal cases
Even when the golden suffix fails, differential testing is valuable:
- Run the prefix through Lean at `--trust=0` and `--trust=1`
- Export and re-import declarations
- If any backend disagrees, it's a bug (maybe not soundness, but still interesting)

---

## Domain-Specific Attack Strategies

| Strategy | Target | Prefix Pattern |
|----------|--------|---------------|
| Universe Confusion | `kernel/level.cpp` | Inductives with complex `imax`/`max` universe expressions |
| Positivity Smuggling | `kernel/inductive.cpp` | Negative occurrences hidden via aliases, mutual blocks, typeclasses |
| Reduction Divergence | `kernel/type_checker.cpp` | Complex definitional equalities, unfold chains |
| Prop/Type Boundary | Sort checking | Large elimination, universe-polymorphic Prop inhabitants |
| Quotient Exploits | `Quot` axioms | Quotient types with carefully crafted relations |
| Typeclass Poisoning | Resolution | Instances that make False/Empty/0=1 inferrable |
| Mutual Inductive | `kernel/inductive.cpp` | Cross-dependent mutual blocks |
| Elaborator Gap | Elab -> Kernel | Macros/elaborators producing unusual kernel terms |
| Attribute Confusion | simp/reducible/instance | Attributes that affect automation but not kernel checking |
| Option Manipulation | `set_option` | Options that weaken checking (if any exist) |

---

## Verification Plan

1. **Known-safe test**: Valid Lean file with `theorem : True := trivial` -> golden suffix should fail
2. **Known-sorry test**: `axiom bad : False` prefix -> golden suffix succeeds but `#print axioms` catches it
3. **Prefix-only compilation**: Verify prefixes compile without golden suffix
4. **False positive filter**: Ensure escape hatch detection catches sorry, axiom, unsafe
5. **End-to-end**: Run fuzzer for 1hr, verify:
   - Corpus grows with tiered distribution
   - Multiple attack categories explored
   - No false golden signals
6. **Differential baseline**: Construct file where `--trust=0` != `--trust=1` -> oracle catches it

---

## Deployment

**LLM Backend**: Claude API
- Haiku for high-volume prefix repair (fast, cheap)
- Sonnet for attack planning and template generation (best reasoning)
- BAML for structured LLM I/O

**Compute**: Server / cloud VM
- 16-64 parallel template pool copies
- Docker containers for isolation
- Async queue (Redis or filesystem) between Rust mutator and Python executor

**Mutator**: Hybrid Rust + Python
- Rust/LibAFL Nautilus for high-throughput prefix grammar mutation
- Python/Claude for semantic prefix generation + repair
- Async queue decouples the two

## Cost Estimates

| Resource | Rate | Daily Budget |
|----------|------|-------------|
| Claude Haiku (repair) | ~1000 calls/day | ~$5-15/day |
| Claude Sonnet (planning) | ~50-100 calls/day | ~$5-30/day |
| Lean compilation | ~10,000-50,000/day (16-64 parallel) | Server CPU time |
| Each prefix x 8 golden suffixes | ~8x compile multiplier | Amortized by shared prefix cache |

---

## What Changes from Current Code

| Component | Current | Proposed |
|-----------|---------|----------|
| `generator/src/grammar.rs` | 525 rules including proofs/tactics | PREFIX-ONLY grammar: declarations only |
| `generator/src/main.rs` | Sync build, binary oracle, generates full files | Generates prefixes only, sends to assembler |
| `scaffold/__init__.py` | Empty stub | Orchestrator: assembler + executor + oracle + feedback |
| `template/` | Single copy | Pool of N parallel copies |
| Oracle | `!sorry && exit==0` | Golden suffix compilation + `#print axioms` + differential |
| Feedback | None | Error stage/class taxonomy, tiered corpus, UCB1 planner |
| Golden check | Generated by grammar | FIXED suffix appended by assembler |
