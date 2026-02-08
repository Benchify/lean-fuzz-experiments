# (Agentic?) Fuzz Attacks: soundness bug discovery in Lean

## Prerequisites

This project depends on two external Lean tools. Clone and `lake build` each, then configure their paths in `.env`.

### lean4export
```sh
git clone https://github.com/leanprover/lean4export.git
cd lean4export && lake build
```

### comparator
```sh
git clone https://github.com/leanprover/comparator.git
cd comparator && lake build
```

### SafeVerify
```sh
git clone https://github.com/gasstationmanager/safeverify.git
cd safeverify && lake build
```

### .env configuration
Copy `.env.example` or create `.env` at the project root with paths to the built binaries:
```
LEAN4EXPORT_PATH=<path-to>/lean4export/.lake/build/bin/lean4export
COMPARATOR_PATH=<path-to>/comparator/.lake/build/bin/comparator
SAFEVERIFY_PATH=<path-to>/safeverify/.lake/build/bin/safe_verify
```

### Lean 4 source (optional)
For development, clone the Lean 4 source into the repo root for reference:
```sh
git clone https://github.com/leanprover/lean4.git lean4
```
This is gitignored and used only for searching the compiler source.

## Running the Fuzzer

```bash
make run              # Run with 4 parallel workers (default)
make run JOBS=8       # Run with 8 workers
make run DEPTH=10     # Run with custom depth
```

Parallel execution achieves ~4x speedup. Each instance is fully isolated with temp directories.

