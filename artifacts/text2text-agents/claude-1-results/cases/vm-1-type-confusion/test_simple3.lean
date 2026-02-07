-- Just cast, no binding
unsafe def main : IO Unit := do
  IO.println "Test"
  let _ : String := unsafeCast (42 : Nat)
  IO.println "Done"
