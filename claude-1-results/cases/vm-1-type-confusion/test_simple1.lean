-- Simplest possible test
unsafe def main : IO Unit := do
  IO.println "Starting"
  let n : Nat := 42
  IO.println "Created Nat"
  let s : String := unsafeCast n
  IO.println "Cast completed"
