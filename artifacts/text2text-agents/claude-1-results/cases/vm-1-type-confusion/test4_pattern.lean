unsafe def main : IO Unit := do
  IO.println "[Test 4] Pattern match"
  let n : Nat := 42
  let s : String := unsafeCast n
  match s with
  | "" => IO.println "Empty"
  | _ => IO.println "Not empty"
