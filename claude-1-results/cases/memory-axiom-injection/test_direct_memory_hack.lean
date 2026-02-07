-- CRITICAL TEST: Can we directly manipulate memory to inject axioms?
-- This would be a TRUE SOUNDNESS BREAK if successful

import Lean

-- Test 1: Try to get the environment and manipulate it directly
unsafe def attempt_environment_corruption : IO Unit := do
  IO.println "[CRITICAL] Attempting to corrupt environment in memory"

  -- Get current environment (this is a MetaM operation normally)
  -- Can we access it through unsafe code?

  IO.println "Trying to access environment data structures..."

  -- The environment is likely a complex C++ object
  -- Can we cast it and manipulate it?

-- Test 2: Try to modify the axiom list directly
unsafe def attempt_axiom_injection : MetaM Unit := do
  IO.println "[CRITICAL] Attempting direct axiom injection"

  -- Get environment
  let env ← Lean.getEnv

  IO.println s!"Environment has {env.constants.size} constants"

  -- Try to add a constant directly to the environment
  -- WITHOUT going through addDecl

  -- Can we cast the environment to a mutable pointer?
  let env_ptr : Nat := unsafeCast env
  IO.println s!"Environment pointer: {env_ptr}"

  -- Try to modify it
  -- This is the key: can we write to this memory?

-- Test 3: Type confusion to bypass environment checks
unsafe def test_environment_bypass : IO Unit := do
  IO.println "[CRITICAL] Environment bypass attempt"

  -- Create a fake axiom declaration
  -- Can we inject it into the environment's constant map?

  IO.println "Attempting to create fake axiom entry..."

  -- The environment's constants are in a PersistentHashMap
  -- Can we manipulate this data structure directly?

-- Test 4: Can we use unsafeCast on the environment to modify it?
unsafe def test_cast_environment : MetaM Unit := do
  let env ← Lean.getEnv

  IO.println "[CRITICAL] Casting environment for direct manipulation"

  -- Try to cast to different type and modify
  let env_as_nat : Nat := unsafeCast env
  let env_as_array : Array Nat := unsafeCast env

  IO.println s!"Env as Nat: {env_as_nat}"
  IO.println s!"Env as Array size: {env_as_array.size}"

  -- Can we modify the array representation?
  -- If we could, we might corrupt the environment

-- Test 5: Use reflection to access internal fields
unsafe def test_reflection_access : MetaM Unit := do
  let env ← Lean.getEnv

  IO.println "[CRITICAL] Reflection-based environment access"

  -- Try to access env.constants directly
  let constants := env.constants

  IO.println s!"Constants map size: {constants.size}"

  -- Can we cast the constants map and modify it?
  let map_as_nat : Nat := unsafeCast constants
  IO.println s!"Constants map as Nat: {map_as_nat}"

-- Test 6: Try to create a modified environment and set it
unsafe def test_environment_replacement : MetaM Unit := do
  let env ← Lean.getEnv

  IO.println "[CRITICAL] Environment replacement attempt"

  -- Create a "modified" environment
  -- Can we use setEnv with a corrupted environment?

  try
    -- Try to add our own axiom
    let new_env := env
    -- Somehow modify new_env...

    -- Set it
    Lean.setEnv new_env
    IO.println "Environment replacement succeeded!"
  catch e =>
    IO.println s!"Failed: {e}"

-- Test 7: Memory corruption to inject axiom
unsafe def test_memory_write : IO Unit := do
  IO.println "[CRITICAL] Direct memory write attempt"

  -- Allocate an array
  let mut arr : Array Nat := #[0xDEADBEEF, 0xCAFEBABE]

  -- Get its address
  let addr : Nat := unsafeCast arr

  IO.println s!"Array address: {addr}"

  -- Try to write past the array
  -- Can we hit the environment's memory?

  -- Try to create a large array and spray the heap
  let mut spray : Array Nat := #[]
  for i in [0:10000] do
    spray := spray.push 0x41414141

  IO.println "Heap spray complete"

-- Test 8: Use MetaM to try to bypass checks
unsafe def test_meta_bypass : MetaM Unit := do
  IO.println "[CRITICAL] MetaM-level bypass attempt"

  let env ← Lean.getEnv

  -- Try to construct a ConstantInfo for False
  let falseConst := Lean.mkConst ``False

  -- Try to add it as an axiom without proper checks
  -- Can we call internal functions directly?

  IO.println "Attempting to bypass addAxiom checks..."

-- Main test runner
#eval show IO Unit from do
  IO.println "=== CRITICAL: Direct Memory Axiom Injection Tests ==="
  IO.println "These tests attempt to BREAK SOUNDNESS by directly"
  IO.println "manipulating memory to inject axioms without declaring them"
  IO.println ""

  -- Run unsafe tests
  try
    attempt_environment_corruption
  catch e =>
    IO.println s!"Environment corruption test crashed: {e}"

  try
    test_environment_bypass
  catch e =>
    IO.println s!"Environment bypass test crashed: {e}"

  try
    test_memory_write
  catch e =>
    IO.println s!"Memory write test crashed: {e}"

  IO.println ""
  IO.println "=== Critical Tests Complete ==="
  IO.println "If any succeeded in injecting an axiom, SOUNDNESS IS BROKEN!"
