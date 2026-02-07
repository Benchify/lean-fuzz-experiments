unsafe def main : IO Unit := do
  IO.println "[Test 1] String.length on confused Nat"
  let n : Nat := 42
  let s : String := unsafeCast n
  let len := s.length
  IO.println s!"Length: {len}"
