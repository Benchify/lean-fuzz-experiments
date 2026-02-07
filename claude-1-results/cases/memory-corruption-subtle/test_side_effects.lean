-- Test 2.3.1-2.3.2: Side Effects Before Crash
-- What executes between unsafeCast and the segfault?

import Lean

unsafe def sideEffectTiming : IO Unit := do
  IO.println "=== Test: Side effects before crash ==="

  IO.println "Step 1: Before type confusion"

  let n : Nat := 42
  let s : String := unsafeCast n

  IO.println "Step 2: After cast, before use"
  IO.println "Cast succeeded without crash!"

  IO.println "Step 3: About to dereference..."

  try
    let _ := s.length  -- Crash happens HERE
    IO.println "Step 4: After dereference (shouldn't reach)"
  catch e =>
    IO.println s!"Step 4: Caught crash: {e}"

unsafe def conditionalCrashPath : IO Unit := do
  IO.println "\n=== Test: Conditional execution paths ==="

  let n : Nat := 42
  let s : String := unsafeCast n

  for choice in [true, false] do
    IO.println s!"\nTesting with choice = {choice}"

    if choice then
      IO.println "Safe path: no dereference"
      IO.println "Continuing without crash"
    else
      IO.println "Unsafe path: about to crash"
      try
        IO.println s  -- Crash here
        IO.println "Did not crash?"
      catch _ =>
        IO.println "Crashed as expected"

unsafe def sideEffectExfiltration : IO Unit := do
  IO.println "\n=== Test: Exfiltration before crash ==="

  -- Simulated secret data
  let secret : Nat := 0xDEADBEEF

  -- Type confuse
  let confused : String := unsafeCast secret

  -- Exfiltrate the value BEFORE crashing
  let recovered : Nat := unsafeCast confused
  IO.println s!"Exfiltrated secret: {recovered} (0x{Nat.toDigits 16 recovered})"

  -- Now crash
  IO.println "About to crash..."
  try
    IO.println confused
  catch _ =>
    IO.println "Crashed, but secret already exfiltrated!"

unsafe def multipleOperationsBeforeCrash : IO Unit := do
  IO.println "\n=== Test: Multiple operations before crash ==="

  let n : Nat := 42
  let s : String := unsafeCast n

  IO.println "Operation 1: Cast successful"

  -- Convert back
  let recovered : Nat := unsafeCast s
  IO.println s!"Operation 2: Recovered value {recovered}"

  -- Do it again
  let s2 : String := unsafeCast recovered
  IO.println "Operation 3: Second cast successful"

  -- Use in conditional
  let choice := recovered == 42
  IO.println s!"Operation 4: Conditional check: {choice}"

  -- Store in array
  let arr : Array String := #[s, s2]
  IO.println s!"Operation 5: Stored in array of size {arr.size}"

  -- NOW crash
  IO.println "All operations complete. Now crashing..."
  try
    IO.println s
  catch _ =>
    IO.println "Crashed at the end"

unsafe def crashWindowAnalysis : IO Unit := do
  IO.println "\n=== Test: Analyzing crash window ==="

  let n : Nat := 42
  let s : String := unsafeCast n

  let mut safeOpsCount := 0

  -- How many operations can we do before crash?
  try
    safeOpsCount := safeOpsCount + 1
    let _ : Nat := unsafeCast s

    safeOpsCount := safeOpsCount + 1
    let _ : Bool := unsafeCast s

    safeOpsCount := safeOpsCount + 1
    let _ : Array Nat := unsafeCast s

    safeOpsCount := safeOpsCount + 1
    -- This should crash
    let _ := s.length

    safeOpsCount := safeOpsCount + 1
  catch _ =>
    pure ()

  IO.println s!"Safe operations before crash: {safeOpsCount}"
  IO.println "FINDING: Non-dereferencing operations are safe"

unsafe def partialComputationBeforeCrash : IO Unit := do
  IO.println "\n=== Test: Partial computation extraction ==="

  -- Complex computation that crashes partway through
  let n : Nat := 42
  let s : String := unsafeCast n

  let mut results : Array Nat := #[]

  for i in [0:10] do
    -- Safe operations
    results := results.push i

    if i == 5 then
      -- Unsafe operation in the middle
      try
        let _ := s.length
      catch _ =>
        IO.println s!"Crashed at iteration {i}"

  IO.println s!"Completed {results.size} iterations before crash"
  IO.println s!"Results collected: {results}"

unsafe def main : IO Unit := do
  IO.println "Testing side effects before crash"
  IO.println "These tests analyze what executes before segfault\n"

  sideEffectTiming
  conditionalCrashPath
  sideEffectExfiltration
  multipleOperationsBeforeCrash
  crashWindowAnalysis
  partialComputationBeforeCrash

  IO.println "\n=== Side Effect Testing Complete ==="
  IO.println "KEY FINDING: Cast itself is safe, crash occurs on dereference"
  IO.println "IMPLICATION: Attackers can exfiltrate data before triggering crash"
