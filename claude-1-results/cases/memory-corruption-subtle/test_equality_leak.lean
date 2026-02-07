-- Test 2.1.2: Information Disclosure via Equality Testing
-- Does equality checking dereference or use pointer comparison?

import Lean

unsafe def equalityPointerTest : IO Unit := do
  IO.println "=== Test: Equality on type-confused values ==="

  -- Two identical Nats
  let n1 : Nat := 42
  let n2 : Nat := 42

  -- Type confuse both to String
  let s1 : String := unsafeCast n1
  let s2 : String := unsafeCast n2

  IO.println "Comparing type-confused Strings..."

  -- Does == dereference for structural equality, or use pointer/value comparison?
  try
    if s1 == s2 then
      IO.println "✓ LEAK: Strings are equal (pointer/value comparison, no dereference)"
    else
      IO.println "✗ Strings not equal"
  catch e =>
    IO.println s!"✗ Equality check crashed: {e}"

unsafe def equalityDifferentValues : IO Unit := do
  IO.println "\n=== Test: Equality with different values ==="

  let n1 : Nat := 42
  let n2 : Nat := 100

  let s1 : String := unsafeCast n1
  let s2 : String := unsafeCast n2

  try
    if s1 == s2 then
      IO.println "✗ Different values compare equal"
    else
      IO.println "✓ Different values correctly differ"
  catch e =>
    IO.println s!"✗ Equality check crashed: {e}"

unsafe def equalityOracleAttack : IO Unit := do
  IO.println "\n=== Test: Equality as oracle for secret comparison ==="

  -- Simulated secret
  let secret : Nat := 0xDEADBEEF
  let secretConfused : String := unsafeCast secret

  -- Attacker tries to guess secret
  for guess in [0xDEADBEE0:0xDEADBEFF] do
    let guessConfused : String := unsafeCast guess

    try
      if secretConfused == guessConfused then
        IO.println s!"✓ VULNERABILITY: Found secret via equality oracle: {guess}"
        IO.println s!"Secret was: {secret}"
        return
    catch _ =>
      -- Equality check crashed
      pure ()

  IO.println "✗ Could not find secret via equality oracle"

unsafe def equalityTimingOracle : IO Unit := do
  IO.println "\n=== Test: Timing differences in equality ==="

  let n1 : Nat := 42
  let n2 : Nat := 42
  let s1 : String := unsafeCast n1
  let s2 : String := unsafeCast n2

  -- Measure timing
  let start ← IO.monoMsNow

  let mut iterations := 0
  try
    for _ in [0:1000000] do
      if s1 == s2 then
        iterations := iterations + 1
  catch _ =>
    pure ()

  let finish ← IO.monoMsNow
  let elapsed := finish - start

  IO.println s!"Completed {iterations} comparisons in {elapsed}ms"
  if iterations == 1000000 then
    IO.println "✓ LEAK: All comparisons succeeded (no crash)"
  else if iterations > 0 then
    IO.println s!"⚠ PARTIAL: Only {iterations} comparisons succeeded"
  else
    IO.println "✗ All comparisons crashed"

unsafe def main : IO Unit := do
  IO.println "Testing information disclosure via equality operations"
  IO.println "These tests check if equality can leak information\n"

  equalityPointerTest
  equalityDifferentValues
  equalityOracleAttack
  equalityTimingOracle

  IO.println "\n=== Equality Testing Complete ==="
