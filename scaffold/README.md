# Scaffold

Python orchestrator for the poisoned prefix fuzzer. Manages template pools, assembles prefixes with golden suffixes, runs `lake build`, and judges results.

## Quick start

```sh
cd scaffold
uv sync
uv run scaffold --help
```

## Testing

```sh
uv run pytest src/tests/ -v
```

Test fixtures (`.lean` files that trigger specific error categories) live in `src/tests/fixtures/`. Use these for integration smoke tests:

```sh
uv run scaffold test-prefix src/tests/fixtures/parse_error.lean -v
uv run scaffold test-prefix src/tests/fixtures/mixed_errors.lean -v
```
