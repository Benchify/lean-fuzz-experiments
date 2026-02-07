-- Minimal repro for VM crash
unsafe def main : IO Unit := do
  let n : Nat := 42
  let s : String := unsafeCast n
  IO.println s!"Result: {s}"
