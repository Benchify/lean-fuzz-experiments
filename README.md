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

### .env configuration
Copy `.env.example` or create `.env` at the project root with paths to the built binaries:
```
LEAN4EXPORT_PATH=<path-to>/lean4export/.lake/build/bin/lean4export
COMPARATOR_PATH=<path-to>/comparator/.lake/build/bin/comparator
```

