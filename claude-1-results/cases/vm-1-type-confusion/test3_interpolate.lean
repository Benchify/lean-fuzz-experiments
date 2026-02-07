unsafe def main : IO Unit := do
  IO.println "[Test 3] String interpolation"
  let n : Nat := 42
  let s : String := unsafeCast n
  IO.println s!"Value: {s}"
