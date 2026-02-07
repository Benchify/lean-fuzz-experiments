unsafe def main : IO Unit := do
  IO.println "[Test 5] Equality check"
  let n : Nat := 42
  let s : String := unsafeCast n
  if s == "test" then
    IO.println "Equal"
  else
    IO.println "Not equal"
