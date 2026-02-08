import Lean.Parser

open Lean Parser

def main (_args : List String) : IO UInt32 := do
  -- Read Lean code from stdin
  let input ← IO.getStdin >>= fun h => h.readToEnd

  -- Create empty environment. This only knows builtin syntax.
  -- User-defined tactics/syntax will be "unknown" but that's OK -
  -- we only care about catching true parse errors (malformed syntax).
  let env ← Lean.mkEmptyEnvironment

  -- Try to parse as command syntax (top-level Lean commands)
  match runParserCategory env `command input "<stdin>" with
  | .ok _syntax =>
    -- Parse succeeded
    return 0
  | .error msg =>
    -- Parse failed - print error and exit with code 1
    IO.eprintln msg
    return 1
