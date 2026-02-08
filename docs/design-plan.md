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

## Phase 1: Assembler + Executor + Oracle ~~(Week 1-2)~~ DONE

**Why first**: The assembler pattern (prefix + fixed suffix) is the foundation of everything.

### Files to create/modify
- [x] `scaffold/src/scaffold/executor.py` -- Assembler + multi-stage executor
- [x] `scaffold/src/scaffold/oracle.py` -- Simple: did it compile?
- [x] `scaffold/src/scaffold/golden_suffixes.py` -- 7 of 8 planned golden suffixes (missing `aesop`)
- [x] `scaffold/src/scaffold/models.py` -- Pydantic data models (Verdict, ErrorCategory, OracleResult, PrefixResult, etc.)
- [x] `scaffold/src/scaffold/diagnostics.py` -- Error categorization with 10 error classes (pulled forward from Phase 4)
- [x] `scaffold/src/scaffold/diagnostic_log.py` -- JSONL append-only logger with session/hash tracking
- [x] `scaffold/src/scaffold/runner.py` -- CLI: `test-prefix`, `fuzz`, `init-pool` commands
- [x] Modify `template/` to support parallel copies (TemplatePool creates N slot copies)

### Assembler logic
- [x] `assemble(prefix, suffix)` -- concatenate prefix + golden suffix
- [x] `execute_prefix(prefix, pool, timeout, suffixes)` -- acquire slot, test against all suffixes, release
- [x] `run_lake_build(project_dir, timeout)` -- subprocess execution with timeout

### Prefix validation (anti-cheating)
- [x] No `sorry` anywhere in prefix
- [x] No `axiom ... : False` or `axiom ... : 0 = 1`
- [x] No `unsafe` definitions used in logical context
- [x] No `implemented_by` or `extern` that could bypass checking
- [x] Run `#print axioms soundness_check` to verify no unexpected axioms (built into golden suffixes)

### Parallel execution
- [x] Template pool with configurable slot count (default 8, 2 pre-built in `artifacts/pool/`)
- [ ] Scale to 16-64 parallel copies (currently 2 pre-built, more can be created via `init-pool`)

### Bonus (not in original plan)
- [x] Test fixtures: 5 `.lean` files for integration smoke testing (`scaffold/src/tests/fixtures/`)
- [x] 31-test diagnostic categorization suite (`scaffold/src/tests/test_diagnostics.py`)
- [x] Golden signal persistence to `artifacts/golden-signals/`

---

## Phase 2: Prefix-Only Grammar + Enhanced Mutator ~~(Week 2-3)~~ NOT STARTED

> **Blocker:** This is the critical missing link. The generator still produces full files (with proofs/tactics), not prefix-only declarations. The scaffold's assembler pipeline and the generator are not yet connected.

### Files to modify
- [ ] `generator/src/grammar.rs` -- Restructure as PREFIX_GRAMMAR
- [ ] `generator/src/main.rs` -- Output prefixes only, send to assembler

### Grammar restructuring
1. [ ] **Remove**: GOLDEN_CHECK, GOLDEN_THEOREM, GOLDEN_VERIFY, PROOF_TERM, TACTIC, TACTIC_SEQ, CASE_ARMS, RCASES_PAT (these are in the fixed suffix now)
2. [x] **Keep**: All declaration-level non-terminals (INDUCTIVE_DECL, DEF_DECL, etc.) -- these already exist in the 515-rule grammar
3. [ ] **Expand**: Add many more rules for the 7 attack categories above
4. [ ] **Add**: THEOREM_DECL without proof (e.g., `theorem helper : P := sorry` -- these sorrys in *helper lemmas* are fine as long as the golden suffix doesn't use them. Actually: **prefix declarations CAN use sorry** in non-False theorems to build up a library of "proved" lemmas that the golden suffix's automation might use)

Wait -- important refinement: **The prefix CAN contain `sorry`-using helper lemmas** as long as we verify that the final `soundness_check` theorem doesn't transitively depend on them. We check this with `#print axioms soundness_check` -- if it mentions `sorryAx`, it's not a real bug.

### Semantic mutation operators
1. [ ] **Universe Perturbation**: Mutate universe level expressions in inductive types
2. [ ] **Positivity Scramble**: Rearrange constructor argument positions (positive <-> negative)
3. [ ] **Instance Swap**: Replace instance definitions with structurally different implementations
4. [ ] **Attribute Toggle**: Add/remove @[simp], @[reducible], @[instance] etc.
5. [ ] **Declaration Reorder**: Shuffle declaration order (shouldn't matter but might expose bugs)
6. [ ] **Nesting Injection**: Wrap declarations in sections/namespaces/mutual blocks

### New grammar categories
1. [ ] **ATTR_DECL**: `@[simp] theorem ...`, `@[instance] def ...`
2. [ ] **NOTATION_DECL**: Custom notation
3. [ ] **SCOPED_INSTANCE**: `scoped instance ...`
4. [ ] **DERIVE_HANDLER**: `deriving instance Decidable`
5. [ ] **OPAQUE_TRICK**: `opaque` + `@[reducible]` combinations
6. [ ] **UNIVERSE_CMD**: `set_option ... in`

### Integration: Wire generator output into scaffold pipeline
- [ ] `gen-sample` outputs prefix-only code (no golden suffix, no proof terms)
- [ ] Scaffold `fuzz` command consumes prefix-only output from generator
- [ ] Shared contract: generator stdout = raw prefix, scaffold appends golden suffixes

---

## Phase 3: LLM Seed Generation + Repair ~~(Week 3-4)~~ NOT STARTED

### Files to create
- [ ] `scaffold/src/scaffold/synthesizer.py` -- LLM prefix generation
- [ ] `scaffold/src/scaffold/repair.py` -- Iterative prefix repair
- [ ] BAML definitions for structured LLM calls (`baml-py` dependency installed but unused)

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

- [ ] Implement LLM call with attack category parameterization
- [ ] Structured output parsing (BAML)
- [ ] Rate limiting and cost tracking

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

- [ ] Implement iterative repair loop
- [ ] Feed diagnostic categorization from `diagnostics.py` into repair prompts
- [ ] Track repair success rates per error category

### Sorry-seeding strategy
- [ ] Generate prefixes where some helper theorems use `sorry`
- [ ] Verify golden suffix doesn't transitively depend on sorry'd helpers via `#print axioms`

---

## Phase 4: Feedback Loop + Corpus Management ~~(Week 4-5)~~ PARTIALLY DONE

### Files to create
- [ ] `scaffold/src/scaffold/feedback.py` -- Feedback loop connecting errors back to generation

### Error classification
- [x] **Error class** tracking (10 categories: PARSE, UNKNOWN_IDENTIFIER, TYPE_MISMATCH, UNIVERSE, POSITIVITY, TERMINATION, TACTIC, ELABORATION, KERNEL, DUPLICATE_DECL, OTHER) -- implemented in `diagnostics.py`
- [x] **Diagnostic logging** with session tracking, prefix hashing, JSONL persistence -- implemented in `diagnostic_log.py`
- [ ] **Best stage reached** across all golden suffix variants (not tracked)
- [ ] **Which golden suffixes got closest** (not tracked)
- [ ] **Prefix complexity** metrics (number of declarations, nesting depth)

### Tiered corpus
| Tier | Criterion | Description |
|------|-----------|-------------|
| 0 | Prefix compiles, golden suffix *almost* works | Highest priority -- closest to success |
| 1 | Prefix compiles, golden suffix fails normally | Good seed, mutation might push it over |
| 2 | Prefix has minor errors | Repair engine candidate |
| Discard | Parse failure | Not useful |

- [ ] Implement tiered corpus storage
- [ ] Classify prefixes into tiers based on execution results
- [ ] Prioritize Tier 0 prefixes for mutation
- [ ] "Almost works" detection (golden suffix error = proof not found, not ill-typed declarations)

### Feedback loop
- [ ] Route error classifications back to generator/mutator
- [ ] Track category-level success rates over time

---

## Phase 5: Attack Planner ~~(Week 5-6)~~ NOT STARTED

### Files to create
- [ ] `scaffold/src/scaffold/planner.py`

### UCB1 bandit over attack categories
Each attack category (universe, positivity, typeclass, etc.) is a bandit arm.
- [ ] **Reward** = fraction of prefixes from this category that reach Tier 0 or Tier 1
- [ ] **Exploration bonus** = standard UCB1 term
- [ ] Templates with higher success at producing compilable prefixes get more attention

### LLM-driven template evolution
When a prefix from category X reaches Tier 0 (prefix compiles, golden fails):
- [ ] Ask LLM: "This prefix compiled but False wasn't provable. What subtle change to the declarations might make False provable?"
- [ ] Generate N variants of the near-miss prefix
- [ ] Test all variants against all golden suffixes

---

## Phase 6: Advanced Differential Testing ~~(Week 6-8)~~ PARTIALLY DONE

### Additional checks for flagged candidates
When a golden suffix succeeds:
1. [x] `#print axioms soundness_check` -- verify no `sorryAx`, no unexpected axioms (in oracle)
2. [ ] `lean4export` -> examine the exported declaration (path configured in `.env`, not wired into pipeline)
3. [x] `comparator` -> cross-check with reference kernel (integrated in `generator/src/bin/main.rs`)
4. [ ] `safeverify` -> independent re-verification
5. [ ] `lean4lean` -> pure Lean kernel reimplementation check

### Differential testing for NON-golden-signal cases
Even when the golden suffix fails, differential testing is valuable:
- [ ] Run the prefix through Lean at `--trust=0` and `--trust=1`
- [ ] Export and re-import declarations
- [ ] If any backend disagrees, it's a bug (maybe not soundness, but still interesting)

### Integration status
- [x] Comparator binary path configured in `.env`
- [x] Comparator config in `template/comparator_config.json`
- [x] Generator main fuzzer uses comparator for TYPE 1/2/3 classification
- [ ] Scaffold pipeline does NOT yet use comparator (only generator does)
- [x] `lean4export` binary path configured in `.env`
- [ ] `lean4export` not called anywhere in the pipeline

---

## Phase 7: Trusted FFI & External Code Boundary Fuzzing — NOT STARTED

> **Motivation:** Lean's kernel and runtime delegate to unverified external code in several places — C++ implementations of `Nat` primitives (via GMP), `@[implemented_by]` overrides, `@[extern]` FFI, and `native_decide`'s compiled code path. Any semantic gap between what the kernel *believes* a term computes and what *actually executes* is a potential soundness hole. Jason Rute's [analysis](https://proofassistants.stackexchange.com/questions/5252/malicious-tampering-of-trusted-libraries) documents that bugs at these FFI trust boundaries have been historically common in Lean 4. The general principle: **anywhere verified Lean hands off to unverified code is an attack surface.**

### New attack categories

#### Category 8: External Code Trust Boundary Exploits
The kernel and runtime trust several categories of external (non-verified) code. Generate prefixes that stress the boundaries where verified logic meets unverified implementation:

**Known trust boundaries to target:**
- [ ] **Kernel `Nat` C++ primitives** — `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.ble`, `Nat.beq`, bitwise ops. These use GMP-backed bignum arithmetic that could disagree with the mathematical definitions at edge cases (historical precedent: `Nat.mod` bugs). But the general pattern is any kernel built-in where the C++ impl could diverge from the Lean spec.
- [ ] **`native_decide` compiled code path** — Compiles Lean to native code for decidable propositions. The compilation itself could introduce bugs independent of GMP.
- [ ] **String/ByteArray/FloatArray primitives** — Other types with C++ backing implementations.
- [ ] **Any future kernel built-in** — The attack surface grows as Lean adds more optimized primitives.

**Fuzzing strategy:** Generate computations that exercise boundary conditions of external implementations — not just GMP limb boundaries, but any case where an optimized implementation might take a different code path than the mathematical definition. Examples: very large values, zero/near-zero, negative-like patterns in unsigned arithmetic, compositions of primitives that interact unexpectedly.

```lean
-- The general pattern: force the kernel to reduce a computation
-- where the external implementation might disagree with the spec.
-- This isn't just about specific magic numbers — it's about
-- finding *any* input where external code diverges from Lean's
-- mathematical definitions.
example : someComplexComputation arg1 arg2 = expectedResult := by native_decide
```

#### Category 9: Specification-Execution Gap Exploits
Any mechanism that allows the *executed* behavior of a term to differ from its *specified* (type-checked) behavior is a potential soundness hole. Generate prefixes that create and exploit such gaps:

- [ ] **`@[implemented_by]`** — Override a function's implementation. Even if our oracle flags these, explore whether the kernel's *own reasoning* is affected by the presence of overrides in the environment (e.g., does reduction use the override or the original?).
- [ ] **`@[extern]`** — FFI declarations where the type signature may not match the external implementation.
- [ ] **Compiler plugins / custom elaborators** — Code that runs at elaboration time and produces kernel terms. A plugin could emit a term that type-checks differently than what the elaborator expects.
- [ ] **`Decidable` instance mismatches** — A `Decidable` instance whose `decide` function disagrees with the proposition it claims to decide. If `native_decide` trusts the instance, this is unsound.
- [ ] **Caching/memoization boundaries** — Any place where the kernel caches a result and the cache could become inconsistent (e.g., `equiv_manager` in the kernel).

**Key insight:** Our oracle already flags `@[implemented_by]` and `@[extern]` as escape hatches when they appear directly. But the interesting attacks are *indirect* — where the gap is introduced through a chain of abstractions, or where the kernel's own reduction machinery is affected by the mere presence of such declarations.

### Differential testing across trust boundaries
Build checker variants that use *different* implementations of the trusted external code, so that any FFI bug shows up as a disagreement:

- [ ] Build `lean4checker` with external implementations disabled or replaced (e.g., pure-Lean `Nat` arithmetic instead of GMP)
- [ ] For flagged candidates, compare results between standard and restricted checker builds
- [ ] Flag any disagreement as a trust-boundary bug
- [ ] This generalizes beyond GMP — any external impl can be swapped for differential testing

---

## Phase 8: Cross-Checker Verification Pipeline — NOT STARTED

> **Motivation:** Our Phase 6 already mentions several independent checkers, but they're treated as one-off checks. A systematic multi-checker pipeline dramatically increases confidence: any candidate that passes Lean's kernel but fails *any* independent checker is flagged. Any candidate that passes *all* checkers despite claiming `False` is a cross-implementation kernel bug (extremely high value, as it would indicate a flaw in the shared mathematical foundations).

### Multi-checker pipeline

For every golden signal candidate and every Tier 0 prefix:

| Checker | What it verifies | How to run |
|---------|-----------------|------------|
| **lean4checker** (standard) | Re-checks exported `.olean` against Lean kernel | `lean4checker` on exported environment |
| **lean4checker** (GMP-free) | Same, but with pure arithmetic (Phase 7) | Custom build without GMP |
| **lean4lean** | Pure Lean reimplementation of kernel | Import and re-check declarations |
| **lean4export → Metamath Zero** | Export to `.mm0` format, verify in MM0 | `lean4export` + `mm0-hs verify` |
| **safeverify** | Independent verification tool | `safeverify` on exported declarations |

### Classification of multi-checker results

| Lean kernel | Independent checkers | Classification |
|-------------|---------------------|----------------|
| Accepts `False` | All reject | **Lean kernel bug** (high value) |
| Accepts `False` | Some reject, some accept | **Shared assumption bug** (very high value) |
| Accepts `False` | All accept | **Foundation bug** (extraordinary value) |
| Rejects `False` | Any disagrees on prefix validity | **Divergence bug** (interesting, not soundness) |

### Implementation
- [ ] Abstract checker interface: `run_checker(project_dir) -> CheckerResult`
- [ ] Concrete implementations for each checker listed above
- [ ] Pipeline orchestrator: run all checkers in parallel for flagged candidates
- [ ] Result aggregation and disagreement detection
- [ ] Wire into scaffold pipeline after oracle step
- [ ] Store multi-checker results alongside diagnostic logs

---

## Phase 9: RL-Guided Exploration — NOT STARTED

> **Motivation:** DeepSeek-Prover v2 demonstrated that an RL-trained AI system can exploit subtle Lean bugs (a front-end issue in their case, but the principle applies to kernel bugs). This validates our LLM-guided approach and suggests RL-based exploration as a high-leverage future direction.

### Reward signal design
Use the tiered corpus classification (Phase 4) as the reward function:

| Outcome | Reward |
|---------|--------|
| Prefix doesn't compile | 0.0 |
| Prefix compiles, golden suffix has type error | 0.3 |
| Prefix compiles, golden suffix fails with "proof not found" | 0.7 (Tier 0) |
| Prefix compiles, golden suffix succeeds (soundness bug!) | 1.0 |

The key insight: a "proof not found" error in the golden suffix means the prefix *almost* corrupted the environment enough — the automation tactic just couldn't find the path. This is a much stronger signal than a type error, which means the prefix's declarations are fundamentally incompatible with the golden check.

### Policy architecture
- [ ] Fine-tune a small LM (e.g., CodeLlama-7B or similar) to generate prefixes
- [ ] Training data: Tier 0/1 prefixes from Phases 1-6 as positive examples
- [ ] Rejection sampling initially, then PPO/DPO once enough signal accumulates
- [ ] Input: attack category + optional seed prefix; Output: complete prefix

### Integration with UCB1 bandits
- [ ] UCB1 bandits from Phase 5 select attack categories at the macro level
- [ ] Within each category, RL policy generates specific prefixes
- [ ] Two-level exploration: bandits explore *which* attack surfaces, RL explores *how* to attack each surface

### Prerequisites and timeline
This phase is speculative and long-term. It depends on:
- [ ] Sufficient training data from Phases 1-6 (likely thousands of Tier 0/1 prefixes)
- [ ] Demonstrated ceiling on LLM-guided generation without RL
- [ ] Compute budget for RL training runs
- Earliest feasible start: after Phases 1-5 are mature and producing corpus data

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
| External Code Trust Boundaries | Kernel C++ primitives, GMP, native code | Computations where external impls might diverge from Lean specs |
| Specification-Execution Gaps | `@[implemented_by]`, `@[extern]`, plugins | Mechanisms creating semantic gaps between type-checked and executed behavior |

---

## Verification Plan

1. [x] **Known-safe test**: Valid Lean file with `theorem : True := trivial` -> golden suffix should fail (`clean_prefix.lean` fixture)
2. [x] **Known-sorry test**: `axiom bad : False` prefix -> golden suffix succeeds but `#print axioms` catches it (oracle escape-hatch detection)
3. [x] **Prefix-only compilation**: Verify prefixes compile without golden suffix (supported by `test-prefix` command)
4. [x] **False positive filter**: Ensure escape hatch detection catches sorry, axiom, unsafe (5 regex patterns in oracle)
5. [ ] **End-to-end**: Run fuzzer for 1hr, verify:
   - [ ] Corpus grows with tiered distribution
   - [ ] Multiple attack categories explored
   - [ ] No false golden signals
6. [ ] **Differential baseline**: Construct file where `--trust=0` != `--trust=1` -> oracle catches it

---

## Deployment

**LLM Backend**: Claude API
- [ ] Haiku for high-volume prefix repair (fast, cheap)
- [ ] Sonnet for attack planning and template generation (best reasoning)
- [ ] BAML for structured LLM I/O (`baml-py` installed, not configured)

**Compute**: Server / cloud VM
- [x] Parallel template pool (configurable slot count)
- [ ] Docker containers for isolation
- [ ] Async queue (Redis or filesystem) between Rust mutator and Python executor

**Mutator**: Hybrid Rust + Python
- [x] Rust/LibAFL Nautilus for high-throughput grammar mutation (515 rules, 3 mutator types)
- [ ] Python/Claude for semantic prefix generation + repair
- [ ] Async queue decouples the two

## Cost Estimates

| Resource | Rate | Daily Budget |
|----------|------|-------------|
| Claude Haiku (repair) | ~1000 calls/day | ~$5-15/day |
| Claude Sonnet (planning) | ~50-100 calls/day | ~$5-30/day |
| Lean compilation | ~10,000-50,000/day (16-64 parallel) | Server CPU time |
| Each prefix x 8 golden suffixes | ~8x compile multiplier | Amortized by shared prefix cache |

---

## What Changes from Current Code

| Component | Current | Proposed | Status |
|-----------|---------|----------|--------|
| `generator/src/grammar.rs` | 515 rules including proofs/tactics | PREFIX-ONLY grammar: declarations only | **Not started** |
| `generator/src/main.rs` | Sync build, binary oracle, generates full files | Generates prefixes only, sends to assembler | **Not started** |
| `scaffold/` | Assembler + executor + oracle + diagnostics | + synthesizer + repair + feedback + planner | **Phase 1 done** |
| `template/` | Single copy + pool slots | Pool of N parallel copies | **Done** |
| Oracle | `!sorry && exit==0` + escape hatches + `#print axioms` | + differential testing | **Partial** |
| Feedback | Error categorization + JSONL logging | + tiered corpus + UCB1 planner | **Partial** |
| Golden check | Generated by grammar AND fixed suffix (disconnected) | FIXED suffix appended by assembler only | **Assembler done, grammar not updated** |

---

## Progress Summary

| Phase | Description | Status |
|-------|-------------|--------|
| **Phase 1** | Assembler + Executor + Oracle | **DONE** |
| **Phase 2** | Prefix-Only Grammar + Enhanced Mutator | **NOT STARTED** (critical blocker) |
| **Phase 3** | LLM Seed Generation + Repair | **NOT STARTED** |
| **Phase 4** | Feedback Loop + Corpus Management | **~30%** (diagnostics done, no feedback loop) |
| **Phase 5** | Attack Planner | **NOT STARTED** |
| **Phase 6** | Advanced Differential Testing | **~25%** (comparator in generator, not in scaffold) |
| **Phase 7** | Trusted FFI & External Code Boundary Fuzzing | **NOT STARTED** |
| **Phase 8** | Cross-Checker Verification Pipeline | **NOT STARTED** |
| **Phase 9** | RL-Guided Exploration | **NOT STARTED** (speculative/long-term) |

**Key architectural gap:** The generator (Rust) and scaffold (Python) pipelines are not connected. The generator still produces full files and runs its own build/comparator loop independently. The scaffold has the assembler + golden suffix pipeline but consumes `gen-sample` output which isn't prefix-only. Phase 2 is the bridge.
