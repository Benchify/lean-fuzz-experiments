# (Agentic?) Fuzz Attacks: soundness bug discovery in Lean 

# Research Objective: Automated Soundness Discovery in Lean 4
The core goal of this project is to identify logical inconsistencies in the Lean 4 theorem prover. A soundness bug occurs if Lean's kernel—the ultimate arbiter of truth in the system—can be convinced to accept a proof of False.

Rather than testing for simple crashes (segfaults), this architecture aims to generate syntactically valid but logically "poisoned" Lean code to see if the type checker's fundamental rules can be subverted.

## The Fuzzing Pipeline
We utilize a three-tier architecture to bridge the gap between high-performance mutation and the Lean compilation stack:

1. The Generator (Rust + LibAFL): Acts as the "brain." It uses a structured grammar to assemble Lean code snippets. Instead of random bytes, it generates recursive structures (inductives, tactics, and proofs) that are syntactically correct, ensuring we spend our compute budget testing the logic engine rather than the parser.
2. The Scaffold (Python/uv): The "orchestrator." It manages the high-velocity handoff. It takes the output from the generator, injects it into a clean Lean environment, and runs the Lean compiler. It monitors for the "Golden Bug": a state where lake build returns a success code despite the presence of an impossible logical claim.
3. The Template (Lean 4): The "sandbox." A pre-configured Lean project that provides the necessary context and imports for the fuzzer. It serves as the baseline environment to ensure every test case is evaluated under standard library conditions.

## Building Lean Projects
Use [`comparator`](https://github.com/leanprover/comparator), not _just_ vanilla `lake build` for checking Lean projects. `comparator` provides differential testing capabilities that are essential for our fuzzing workflow. We should maybe also use [`safeverify`](https://github.com/gasstationmanager/safeverify) as well.

## External Tool Setup
The pipeline depends on two external Lean tools that must be cloned and built separately. Their binary paths are configured via `.env`.

1. Clone and build [`lean4export`](https://github.com/leanprover/lean4export):
   ```sh
   git clone https://github.com/leanprover/lean4export.git
   cd lean4export && lake build
   ```
2. Clone and build [`comparator`](https://github.com/leanprover/comparator):
   ```sh
   git clone https://github.com/leanprover/comparator.git
   cd comparator && lake build
   ```
3. Set the `_PATH` variables in `.env` to point to the built binaries:
   ```
   LEAN4EXPORT_PATH=<path-to>/lean4export/.lake/build/bin/lean4export
   COMPARATOR_PATH=<path-to>/comparator/.lake/build/bin/comparator
   ```


## Lean 4 Source (Local Reference)
The Lean 4 compiler source is cloned at `lean4/` (gitignored, not a submodule). It exists solely for agentic search during development — never modify it.

Key directories for fuzzing research:
- `lean4/src/kernel/` — C++ kernel (the ultimate fuzzing target): type_checker.cpp, inductive types, universe levels
- `lean4/src/Lean/Parser/` — Parser/syntax definitions (grammar rules for valid Lean code)
- `lean4/src/Lean/Elab/` — Elaborator (translates surface syntax → kernel terms)
- `lean4/src/Lean/Environment.lean` — Declaration types and the trusted environment

External references:
- [lean4lean](https://github.com/digama0/lean4lean) — Pure Lean 4 reimplementation of the kernel
- [Type Checking in Lean 4](https://ammkrn.github.io/type_checking_in_lean4/) — Comprehensive kernel architecture guide

## Success Criteria: The "False" Proof
We are specifically hunting for Semantic Divergence. In a successful exploit, the fuzzer would produce a file that:
- Passes the Lean Elaborator without errors.
- Is accepted by the Kernel.
- Concludes a theorem of type False or 0 = 1.

This approach bypasses the "shallow" bugs of the frontend and aims directly at the mathematical foundation of the prover, such as flaws in universe level handling, inductive type consistency, or termination checking.

