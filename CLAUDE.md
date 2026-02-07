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


## Success Criteria: The "False" Proof
We are specifically hunting for Semantic Divergence. In a successful exploit, the fuzzer would produce a file that:
- Passes the Lean Elaborator without errors.
- Is accepted by the Kernel.
- Concludes a theorem of type False or 0 = 1.

This approach bypasses the "shallow" bugs of the frontend and aims directly at the mathematical foundation of the prover, such as flaws in universe level handling, inductive type consistency, or termination checking.

