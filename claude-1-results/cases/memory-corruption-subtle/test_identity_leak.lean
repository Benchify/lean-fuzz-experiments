-- Test 2.1.1: Information Disclosure via Identity Operations
-- Can we transmute types back and forth without dereferencing?

import Lean

unsafe def identityLeakTest1 : IO Unit := do
  IO.println "=== Test: Identity transmutation ==="

  let secret : Nat := 0xDEADBEEF
  IO.println s!"Original secret: {secret}"

  -- Cast to String (type confusion)
  let leaked : String := unsafeCast secret
  IO.println "Casted to String (no crash yet)"

  -- Cast back to Nat WITHOUT dereferencing String
  let recovered : Nat := unsafeCast leaked
  IO.println s!"Recovered value: {recovered}"

  -- Verify round-trip
  if secret == recovered then
    IO.println "✓ LEAK: Round-trip successful! Type confusion can transmute values."
  else
    IO.println "✗ Values differ after round-trip"

unsafe def identityLeakTest2 : IO Unit := do
  IO.println "\n=== Test: Multiple round-trips ==="

  let mut value : Nat := 42

  for i in [0:10] do
    let asString : String := unsafeCast value
    value := unsafeCast asString
    IO.println s!"Round-trip {i}: value = {value}"

  IO.println s!"Final value after 10 round-trips: {value}"

unsafe def identityLeakTest3 : IO Unit := do
  IO.println "\n=== Test: Cross-type transmutation chain ==="

  let original : Nat := 123456
  let asString : String := unsafeCast original
  let asArray : Array Nat := unsafeCast asString
  let asBool : Bool := unsafeCast asArray
  let backToNat : Nat := unsafeCast asBool

  IO.println s!"Original: {original}"
  IO.println s!"After chain: {backToNat}"

  if original == backToNat then
    IO.println "✓ LEAK: Type transmutation chain preserves bit pattern"

unsafe def main : IO Unit := do
  IO.println "Testing information disclosure via identity operations"
  IO.println "These tests check if we can transmute types without crashing\n"

  try
    identityLeakTest1
    identityLeakTest2
    identityLeakTest3
    IO.println "\n✓ All identity leak tests completed successfully"
    IO.println "FINDING: Type confusion allows value preservation without dereference"
  catch e =>
    IO.println s!"\n✗ Test crashed: {e}"
