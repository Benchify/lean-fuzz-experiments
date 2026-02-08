# Stresstesting the `generator` rust lib

In this project, please use python to copy `<monorepo-root>/template/` into a tmpdir, use the `<monorepo-root>/generator/` lean code fuzzer to write random stuff into `Basic.lean`, and call `lake build` on it to stresstest the generator. Please write FAILURES to `<monorepo-root>/artifacts/stress_gen/<timestamp-of-run>_<hash-of-code/Basic.lean`, but successes don't need to be persisted. 

add a `uv run stress-gen` command to the `pyproject.toml` when you're ready.
