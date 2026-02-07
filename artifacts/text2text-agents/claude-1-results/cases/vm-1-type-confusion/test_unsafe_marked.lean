-- VM Type Confusion: Testing unsafe marked functions
-- These are marked unsafe, but we want to see if VM protects against type confusion

import Lean

-- Test 1: Unsafe cast Nat to String
unsafe def test_cast_nat_to_string : IO Unit := do
  let n : Nat := 42
  let s : String := unsafeCast n
  IO.println s!"Casted Nat {n} to String: '{s}'"
  IO.println s!"String length: {s.length}"

-- Test 2: Array type confusion
unsafe def test_cast_array_confusion : IO Unit := do
  let arr : Array Nat := #[1, 2, 3, 4, 5]
  let arr2 : Array String := unsafeCast arr
  IO.println s!"Array length after cast: {arr2.size}"
  -- Try to access elements
  for i in [0:arr2.size] do
    try
      let elem := arr2[i]!
      IO.println s!"Element {i}: '{elem}' (length: {elem.length})"
    catch e =>
      IO.println s!"Error accessing element {i}: {e}"

-- Test 3: Function type confusion
unsafe def test_cast_function : IO Unit := do
  let f : Nat → Nat := fun x => x + 1
  let g : String → String := unsafeCast f
  let result := g "hello"
  IO.println s!"Function result: '{result}'"

-- Test 4: Cast between different sized integers
unsafe def test_int_confusion : IO Unit := do
  let n64 : UInt64 := 0xDEADBEEFCAFEBABE
  let n8 : UInt8 := unsafeCast n64
  IO.println s!"UInt64 {n64} cast to UInt8: {n8}"

  let arr8 : ByteArray := ByteArray.mk #[0x41, 0x42, 0x43, 0x44]
  let n32 : UInt32 := unsafeCast arr8
  IO.println s!"ByteArray cast to UInt32: {n32}"

-- Test 5: Proof object examination
unsafe def test_proof_representation : IO Unit := do
  let p : 1 = 1 := rfl
  let n : Nat := unsafeCast p
  IO.println s!"Proof object as Nat: {n}"

  let p2 : True := trivial
  let n2 : Nat := unsafeCast p2
  IO.println s!"True proof as Nat: {n2}"

-- Test 6: Type confusion in polymorphic contexts
unsafe def test_polymorphic_confusion : IO Unit := do
  let list_nat : List Nat := [1, 2, 3]
  let list_str : List String := unsafeCast list_nat
  IO.println s!"List length: {list_str.length}"
  for s in list_str do
    IO.println s!"  Item: '{s}'"

-- Main entry
unsafe def main : IO Unit := do
  IO.println "=== Unsafe VM Type Confusion Tests ==="

  IO.println "\n[Test 1: Nat → String cast]"
  try test_cast_nat_to_string catch e => IO.println s!"Crash: {e}"

  IO.println "\n[Test 2: Array type confusion]"
  try test_cast_array_confusion catch e => IO.println s!"Crash: {e}"

  IO.println "\n[Test 3: Function type confusion]"
  try test_cast_function catch e => IO.println s!"Crash: {e}"

  IO.println "\n[Test 4: Integer size confusion]"
  try test_int_confusion catch e => IO.println s!"Crash: {e}"

  IO.println "\n[Test 5: Proof object inspection]"
  try test_proof_representation catch e => IO.println s!"Crash: {e}"

  IO.println "\n[Test 6: Polymorphic type confusion]"
  try test_polymorphic_confusion catch e => IO.println s!"Crash: {e}"
