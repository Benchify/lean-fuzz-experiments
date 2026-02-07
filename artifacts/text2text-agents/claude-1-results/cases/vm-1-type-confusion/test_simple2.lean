-- No println after cast
unsafe def main : IO Unit := do
  IO.println "Before cast"
  let n : Nat := 42
  let s : String := unsafeCast n
  pure ()
