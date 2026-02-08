# generator

Grammar-based fuzzer for Lean 4, built on [LibAFL](https://github.com/AFLplusplus/LibAFL)'s Nautilus engine.

## What it does

`cargo run` starts a continuous fuzz loop that:

1. **Generates** syntactically-valid Lean 4 programs from a ~525-rule context-free grammar (`src/grammar.rs`) covering inductive types, universe levels, tactics, metaprogramming, and more.
2. **Injects** each generated program into `../template/Template/Basic.lean`.
3. **Builds** the template project via `lake build`.
4. **Checks** the result: if the build succeeds _without_ `sorry`, the code is saved to `solutions/` as a "golden signal" candidate — a potential soundness bug where Lean accepted a proof of `False`.

The fuzzer seeds an initial corpus of 8 inputs, then mutates them indefinitely using Nautilus random, recursion, and splice mutators (weighted 6:1:3).

## Binaries

| Binary | Command | Description |
|--------|---------|-------------|
| `generator` | `cargo run` | Main fuzz loop (runs forever) |
| `gen-sample` | `cargo run --bin gen-sample [depth]` | Print a single generated program to stdout. Optional `depth` arg (default 15) controls syntax tree depth. |

## Prerequisites

- The `../template/` Lean project must exist and be buildable with `lake build`.
- `lake` must be on `$PATH`.

## Grammar

The grammar in `src/grammar.rs` targets the kernel's attack surface:

- **Inductive types** — positivity violations, nested/indexed families, universe-polymorphic inductives
- **Universe levels** — deeply nested `max`/`imax` expressions
- **Proof terms** — `Eq.mp`, `cast`, `Quot.sound`, `propext`, recursor abuse
- **Tactics** — `native_decide`, `conv`, `calc`, interleaved `sorry`
- **Metaprogramming** — custom elaborators and macros that inject terms

## Output

- `solutions/` — golden signal candidates (builds that prove `False` without `sorry`)
- `workdir/` — Nautilus splice chunk metadata
- Stats are printed to stdout via LibAFL's `SimpleMonitor`
