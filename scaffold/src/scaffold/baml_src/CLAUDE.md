# BAML Source for Lean-Fuzz Scaffold

This directory contains BAML (Boundary AI Markup Language) definitions for the scaffold's LLM-powered components. BAML is a DSL for building type-safe LLM function calls with structured inputs/outputs, automatic JSON parsing, and Jinja-based prompt templating.

**Docs**: https://docs.boundaryml.com
**GitHub**: https://github.com/boundaryml/baml

## Setup

```bash
# Add baml-py to the scaffold's dependencies
cd scaffold && uv add baml-py

# Initialize BAML (creates baml_src/ with starter files if needed)
uv run baml-cli init

# Generate the Python client (REQUIRED after every .baml file change)
uv run baml-cli generate
```

The generator config goes in `generators.baml`:
```baml
generator target {
  output_type "python/pydantic"
  output_dir "../baml_client"
  version "0.218.1"
}
```

After `baml-cli generate`, a `baml_client/` directory appears alongside `baml_src/` with Pydantic models and a typed `b` client object.

## Core Concepts

### File Organization
```
baml_src/
  generators.baml   # Code generation config (language, output dir)
  clients.baml      # LLM provider configurations
  types.baml        # Classes (structured data) and enums (classifications)
  functions.baml    # LLM function definitions (prompt + types)
  tests.baml        # Test cases runnable via `baml-cli test`
```

All `.baml` files in `baml_src/` are read together -- types, clients, and functions can reference each other across files.

### Types

**Primitives**: `bool`, `int`, `float`, `string`, `null`

**Composite**: `string[]` (array), `int?` (optional), `string | int` (union), `map<string, int>` (map), `"a" | "b"` (literal union)

**Classes** define structured output schemas. Properties have NO colon:
```baml
class LeanSnippet {
  code string @description("Raw Lean 4 source code")
  imports string[] @description("Required imports, e.g. 'Mathlib.Tactic'")
  is_valid bool
  error_message string?
}
```

**Enums** are for fixed classification sets:
```baml
enum Severity {
  BENIGN @description("No soundness implications")
  SUSPICIOUS @description("Unusual but not necessarily unsound")
  CRITICAL @description("Likely soundness bug -- proof of False accepted")
}
```

### Functions

A function binds a prompt template to typed I/O and an LLM client:
```baml
function ClassifyResult(lean_output: string) -> Severity {
  client Claude
  prompt #"
    {{ _.role("system") }}
    You are a Lean 4 expert analyzing compiler output.

    {{ _.role("user") }}
    Classify the following Lean 4 compiler output by severity.

    {{ lean_output }}

    {{ ctx.output_format }}
  "#
}
```

**Rules**:
- Always reference all input parameters in the prompt
- Always include `{{ ctx.output_format }}` -- this injects the output schema automatically (never write it manually)
- Use `{{ _.role("system") }}` / `{{ _.role("user") }}` for chat models
- Prompts use Jinja: `{% if %}`, `{% for %}`, `{{ variable }}`

### Clients

Shorthand (uses default env vars):
```baml
function Foo(x: string) -> string {
  client "anthropic/claude-sonnet-4-20250514"
  prompt #"..."#
}
```

Named client (full control):
```baml
client<llm> Claude {
  provider anthropic
  options {
    model "claude-sonnet-4-20250514"
    api_key env.ANTHROPIC_API_KEY
    max_tokens 4096
  }
}
```

Fallback for resilience:
```baml
client<llm> Resilient {
  provider fallback
  options {
    strategy [Claude, GPT4]
  }
}
```

### Tests

```baml
test TestClassify {
  functions [ClassifyResult]
  args {
    lean_output "error: type mismatch\n  False\nhas type\n  Prop"
  }
}
```

Run with `uv run baml-cli test`.

## Usage in Python

```python
from baml_client import b
from baml_client.types import LeanSnippet, Severity

# Synchronous call
result: Severity = b.ClassifyResult("lake build succeeded\ntheorem false_proof : False := ...")

# Streaming
stream = b.stream.GenerateLeanCode("inductive type with nested recursion")
for partial in stream:
    print(partial)  # Partial object with nullable fields
final = stream.get_final_response()  # Fully validated LeanSnippet
```

## Nontrivial Examples for Lean-Fuzz

### Example 1: Structured Lean Code Generation with Mutation Guidance

Generate Lean 4 code targeting specific kernel subsystems, guided by mutation strategies from the Rust fuzzer.

```baml
// types.baml

enum KernelSubsystem {
  UNIVERSE_LEVELS @description("Universe polymorphism: Type u, Sort u, universe constraints")
  INDUCTIVE_TYPES @description("Inductive type declarations, recursors, nested/mutual inductives")
  DEFINITIONAL_EQUALITY @description("Reduction rules: beta, delta, iota, zeta, eta")
  TERMINATION_CHECKING @description("Structural recursion, well-founded recursion, decreasing arguments")
  TYPECLASS_RESOLUTION @description("Instance synthesis, diamond inheritance, coherence")
}

class MutationStrategy {
  subsystem KernelSubsystem
  technique string @description("Specific mutation, e.g. 'universe level overflow', 'non-positive occurrence in inductive'")
  constraints string[] @description("Invariants to preserve so the code is not trivially rejected by the parser")
}

class GeneratedLeanCase {
  lean_source string @description("Complete, self-contained Lean 4 file contents")
  expected_behavior string @description("What a sound kernel SHOULD do: accept or reject, and why")
  attack_vector string @description("Which kernel rule this attempts to subvert")
  imports string[] @description("Required lake dependencies beyond Init")
}

// functions.baml

function GenerateFuzzCase(strategy: MutationStrategy, prior_failures: string[]) -> GeneratedLeanCase {
  client Claude
  prompt #"
    {{ _.role("system") }}
    You are a Lean 4 kernel security researcher. Your goal is to generate test cases
    that probe the soundness of Lean 4's type checker. You are NOT trying to crash
    the compiler -- you are trying to construct code that the kernel ACCEPTS but that
    is logically UNSOUND (i.e., proves False).

    Key kernel invariants to target:
    - Universe consistency: no Type : Type
    - Strict positivity for inductives
    - Guard condition for fixpoints
    - Correct reduction of match expressions
    - Sound universe unification

    {{ _.role("user") }}
    Generate a Lean 4 test case targeting the {{ strategy.subsystem }} subsystem
    using the technique: {{ strategy.technique }}

    Constraints to satisfy:
    {% for c in strategy.constraints %}
    - {{ c }}
    {% endfor %}

    {% if prior_failures|length > 0 %}
    The following approaches have already been tried and FAILED (the kernel correctly
    rejected them). Do NOT repeat these patterns:
    {% for f in prior_failures %}
    - {{ f }}
    {% endfor %}
    {% endif %}

    The generated code must:
    1. Be syntactically valid Lean 4 (it should parse without errors)
    2. Attempt to prove `theorem unsound : False := ...` or derive `0 = 1`
    3. NOT use `sorry`, `native_decide` on open terms, or `unsafeCoerce`
    4. NOT rely on known, already-patched bugs

    {{ ctx.output_format }}
  "#
}
```

### Example 2: Differential Analysis of Export Output

Use `lean4export` and `comparator` output to detect semantic divergence between the elaborator and kernel.

```baml
// types.baml

class ExportComparison {
  elaborator_accepts bool @description("Did the elaborator accept the declaration?")
  kernel_accepts bool @description("Did the kernel (via lean4export) accept the declaration?")
  divergence_detected bool @description("True if elaborator and kernel disagree")
  export_diff string? @description("Textual diff of export output if divergence found")
}

class DivergenceAnalysis {
  root_cause string @description("Most likely kernel subsystem responsible for divergence")
  severity Severity
  explanation string @description("Technical explanation of WHY the kernel and elaborator disagree")
  minimal_reproducer string? @description("Attempt to minimize the Lean code to smallest divergence trigger")
  related_issues string[] @description("Known Lean 4 GitHub issues that might be related")
}

// functions.baml

function AnalyzeDivergence(
  lean_source: string,
  comparator_output: string,
  export_output: string
) -> DivergenceAnalysis {
  client Claude
  prompt #"
    {{ _.role("system") }}
    You are analyzing a potential soundness divergence in Lean 4. The `comparator` tool
    detected a discrepancy between two type-checking backends. Your job is to determine
    whether this is a genuine soundness bug, a benign difference, or a tool artifact.

    Background on Lean 4 architecture:
    - The elaborator translates surface Lean into kernel terms (Expr)
    - The kernel is the trusted core that re-checks elaborated terms
    - lean4export serializes kernel-level declarations for external verification
    - comparator cross-checks two builds of the same declaration

    A TRUE soundness bug means: the kernel accepted a proof of False (or an inconsistency).
    A FALSE POSITIVE means: the tools disagree due to caching, universe variable naming, etc.

    {{ _.role("user") }}
    Lean source file:
    ```lean
    {{ lean_source }}
    ```

    comparator output:
    ```
    {{ comparator_output }}
    ```

    lean4export output:
    ```
    {{ export_output }}
    ```

    Analyze this divergence. If you can minimize the reproducer, do so.

    {{ ctx.output_format }}
  "#
}
```

### Example 3: Iterative Refinement with Retry Loop

When generated Lean code fails to parse, use structured error feedback to refine it.

```baml
// types.baml

class RefinedLeanCase {
  lean_source string @description("Corrected Lean 4 source code")
  changes_made string[] @description("List of specific corrections applied")
  confidence float @description("0.0-1.0 confidence this version will parse and elaborate")
}

// functions.baml

function RefineLeanCode(
  original_source: string,
  compiler_errors: string,
  target_theorem: string,
  attempt_number: int
) -> RefinedLeanCase {
  client Claude
  prompt #"
    {{ _.role("system") }}
    You are fixing Lean 4 code that failed to compile. Your goal is to make the code
    compile while PRESERVING the logical attack vector. Do not "fix" the code by
    making it trivially correct -- the point is to probe for soundness bugs.

    Common Lean 4 errors and fixes:
    - "unknown identifier": check imports, namespace opens, spelling
    - "type mismatch": check universe levels, implicit arguments
    - "failed to synthesize instance": add explicit instances or use @[reducible]
    - "structural recursion failed": try well-founded recursion or restructure

    {{ _.role("user") }}
    Attempt {{ attempt_number }} of fixing this Lean code.

    Original source:
    ```lean
    {{ original_source }}
    ```

    Compiler errors:
    ```
    {{ compiler_errors }}
    ```

    The code is intended to prove (or attempt to prove): {{ target_theorem }}

    Fix the compilation errors while keeping the proof strategy intact.
    If the proof strategy is fundamentally broken, explain why in changes_made
    and adapt the approach.

    {{ ctx.output_format }}
  "#
}
```

### Example 4: Batch Classification with Streaming

Classify multiple fuzzing results at once, streaming partial results for fast UI feedback.

```baml
// types.baml

class FuzzResult {
  case_id string
  lean_source string
  build_exit_code int
  build_stdout string
  build_stderr string
}

class ClassifiedResult {
  case_id string
  severity Severity
  is_soundness_bug bool @description("True ONLY if: build succeeds AND code proves False without sorry/axiom abuse")
  summary string @description("One-line summary of what happened")
  details string? @description("Extended analysis if severity is CRITICAL")
}

class BatchClassification {
  results ClassifiedResult[]
  critical_count int @description("Number of CRITICAL results requiring human review")
  summary string @description("Overall batch summary")
}

// functions.baml

function ClassifyBatch(results: FuzzResult[]) -> BatchClassification {
  client Claude
  prompt #"
    {{ _.role("system") }}
    You are triaging a batch of Lean 4 fuzzing results. For each result, determine
    whether it represents a genuine soundness bug. Be CONSERVATIVE -- only mark
    something as a soundness bug if you are highly confident.

    A soundness bug requires ALL of:
    1. Build exit code 0 (compilation succeeded)
    2. The code contains a theorem of type False (or derives a contradiction like 0 = 1)
    3. The proof does NOT use sorry, native_decide on open terms, or other known escape hatches
    4. The proof does NOT rely on axioms beyond the standard ones (propext, quot, choice)

    {{ _.role("user") }}
    Classify these {{ results|length }} fuzzing results:

    {% for r in results %}
    --- Case {{ r.case_id }} ---
    Exit code: {{ r.build_exit_code }}
    Source (first 500 chars): {{ r.lean_source[:500] }}
    Stdout: {{ r.build_stdout[:300] }}
    Stderr: {{ r.build_stderr[:300] }}

    {% endfor %}

    {{ ctx.output_format }}
  "#
}
```

Usage with streaming in Python:
```python
from baml_client import b
from baml_client.types import FuzzResult

results = [
    FuzzResult(case_id="001", lean_source="...", build_exit_code=0, build_stdout="", build_stderr=""),
    FuzzResult(case_id="002", lean_source="...", build_exit_code=1, build_stdout="", build_stderr="error: ..."),
]

# Stream partial results as the LLM generates them
stream = b.stream.ClassifyBatch(results)
for partial in stream:
    if partial.results:
        for r in partial.results:
            if r and r.is_soundness_bug:
                print(f"ALERT: {r.case_id} may be a soundness bug!")

final = stream.get_final_response()
print(f"Batch complete: {final.critical_count} critical findings")
```

### Example 5: Dynamic Types with TypeBuilder

When the set of kernel subsystems or mutation strategies comes from a database or config file at runtime:

```python
from baml_client.type_builder import TypeBuilder
from baml_client import b

# Build enum values dynamically from a config
subsystems = ["UNIVERSE_LEVELS", "INDUCTIVE_TYPES", "CUSTOM_REDUCIBILITY"]

tb = TypeBuilder()
for s in subsystems:
    tb.KernelSubsystem.add_value(s)

# Add a runtime-discovered field
tb.GeneratedLeanCase.add_property("lake_toolchain", tb.string())

result = b.GenerateFuzzCase(strategy, prior_failures, {"tb": tb})
```

### Example 6: Template Strings for Reusable Prompt Fragments

```baml
template_string Lean4Context() #"
# Lean 4 Kernel Architecture
- The kernel is the trusted computing base (~5k lines of C++)
- All proofs are re-checked by the kernel after elaboration
- Key files: type_checker.cpp, inductive.cpp, declaration.cpp
- Universe levels form a partial order: Prop < Type 0 < Type 1 < ...
- Inductives must satisfy strict positivity and universe constraints
"#

template_string FuzzingGuidelines() #"
# Fuzzing Rules
- Generated code must be syntactically valid Lean 4
- Target: proof of False accepted by the kernel
- Do NOT use: sorry, admit, unsafeCoerce, Lean.Elab hacks
- DO target: universe polymorphism, mutual inductives, reduction rules
"#

function SmartGenerate(hint: string) -> GeneratedLeanCase {
  client Claude
  prompt #"
    {{ _.role("system") }}
    {{ Lean4Context() }}
    {{ FuzzingGuidelines() }}

    {{ _.role("user") }}
    Generate a fuzz case based on this hint: {{ hint }}

    {{ ctx.output_format }}
  "#
}
```

## Prompt Engineering Tips

1. **`{{ ctx.output_format }}` is mandatory** -- it tells the LLM exactly what JSON shape to produce. Never manually describe the output schema.
2. **Use `@description` on fields** rather than explaining them in the prompt. BAML injects descriptions into the output format automatically.
3. **Use literal unions for small fixed sets**: `"accept" | "reject" | "timeout"` is better than a 3-value enum when there's no need for `@description` or `@skip`.
4. **Retry policies** handle transient LLM failures automatically:
   ```baml
   retry_policy Persistent {
     max_retries 3
     strategy {
       type exponential_backoff
       delay_ms 500
       multiplier 2.0
       max_delay_ms 30000
     }
   }
   ```
5. **Checks and assertions** validate LLM output structurally:
   ```baml
   class LeanCode {
     source string @assert(not_empty, {{ this|length > 0 }})
     source string @assert(no_sorry, {{ "sorry" not in this }})
   }
   ```
6. **Keep prompts focused** -- one function per task. If you need a pipeline (generate -> compile -> analyze -> refine), make each step its own BAML function and orchestrate in Python.

## Common Pitfalls

- **Forgot `baml-cli generate`**: Any `.baml` change requires regeneration. The Python client won't reflect new types/functions until you run it.
- **Missing `{{ ctx.output_format }}`**: Without this, the LLM doesn't know what JSON to produce and you get parse failures.
- **Colon in class fields**: BAML uses `name type`, not `name: type`. No colons.
- **Optional arrays**: `string[]?` is not supported. Use `string[]` (empty array for "none").
- **Circular imports**: All `.baml` files in `baml_src/` share a single namespace. No import statements needed, but name collisions are errors.
