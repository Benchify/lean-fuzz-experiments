unsafe def main : IO Unit := do
  IO.println "[Test 2] Direct println of confused value"
  let n : Nat := 42
  let s : String := unsafeCast n
  IO.println s
