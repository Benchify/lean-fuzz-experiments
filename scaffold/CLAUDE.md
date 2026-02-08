# Scaffold

## Python codestyle

Lots of `pydantic.BaseModel`, typehints.

- `uv run ty check`
- `uv run ruff check --fix`
- `uv run ruff format`

CLIs with `typer`.

## Testing

Tests live in `scaffold/src/tests/` (configured via `[tool.pytest.ini_options]` in `pyproject.toml`).

```sh
cd scaffold && uv run pytest src/tests/ -v
```

Test fixtures (small `.lean` files for integration testing) live in `scaffold/src/tests/fixtures/`. Use these instead of `artifacts/text2text-agents/` when verifying scaffold behavior:

```sh
uv run scaffold test-prefix scaffold/src/tests/fixtures/parse_error.lean -v
uv run scaffold test-prefix scaffold/src/tests/fixtures/mixed_errors.lean -v
```
