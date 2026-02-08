# Parallel Fuzzing Guide

## Quick Start

Run 4 parallel fuzzer instances:
```bash
./run_parallel.sh 4 10
```

This achieves ~4x speedup by running multiple independent fuzzer instances.

## How It Works

Each fuzzer instance:
- ✅ Fully isolated (own temp directories, own corpus)
- ✅ Thread-safe (no conflicts)
- ✅ Independent execution (~0.5-1s per test)
- ❌ Don't share corpus discoveries (limitation)

**Performance:**
- Single instance: ~60-120 tests/minute
- 4 parallel instances: ~240-480 tests/minute
- 8 parallel instances: ~480-960 tests/minute

## Current Architecture

The fuzzer uses isolated temp directories for each test:
1. Creates temp copy of template/ (with .lake/ cache)
2. Writes generated code to temp copy
3. Runs lake build + comparator in isolation
4. Auto-cleans up

This makes each test fully thread-safe and parallelizable.

## Limitations

**No corpus sharing:** Each instance maintains its own corpus. If instance 1 finds an interesting test case, instance 2 won't know about it.

**Solution:** Periodically merge solutions/ directories or use shared storage.

## Future: Proper LibAFL Multi-Core

For coordinated multi-core fuzzing with corpus sharing, we'd need to:

1. **Replace SimpleEventManager** with LlmpRestartingEventManager
2. **Add broker/client architecture** for shared state
3. **Use fork server** or multi-process execution
4. **Shared memory** for corpus synchronization

This requires significant refactoring (~4-8 hours) but would provide:
- ✅ Corpus sharing across cores
- ✅ Coordinated fuzzing campaign
- ✅ Better coverage through sharing

See: https://github.com/AFLplusplus/LibAFL/tree/main/fuzzers for examples

## Manual Parallel Execution

You can also manually run multiple instances in separate terminals:

```bash
# Terminal 1
cd generator && cargo +nightly run --release --bin main -- --depth 10

# Terminal 2
cd generator && cargo +nightly run --release --bin main -- --depth 10

# Terminal 3
cd generator && cargo +nightly run --release --bin main -- --depth 10
```

All instances save to the same `solutions/` directory, so findings are automatically aggregated.
