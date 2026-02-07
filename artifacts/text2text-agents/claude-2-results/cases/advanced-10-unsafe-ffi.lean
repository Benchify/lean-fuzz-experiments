/-
Advanced Test 10: Unsafe Code and FFI Exploitation
Testing the boundaries between safe and unsafe code

Lean has:
- `unsafe` keyword for potentially unsound code
- FFI via @[extern] for C interop
- unsafeCast for type conversions
- Compile-time vs runtime type checking

Can we use these to:
- Bypass kernel soundness checks?
- Achieve type confusion?
- Cause memory corruption?
- Leak unsafe code into safe contexts?
-/

-- Test 1: Basic unsafe cast
unsafe def unsafeCastTest : Nat :=
  unsafeCast (42 : Int)

-- This is marked unsafe, so should not affect soundness
#check unsafeCastTest  -- Should show as unsafe

-- Test 2: Can we hide unsafe in safe code?
-- This should fail:
-- def hideUnsafe : Nat := unsafeCastTest  -- Should be rejected (unsafe)

-- Test 3: Type confusion via unsafe cast
unsafe def boolAsNat : Nat :=
  unsafeCast true

-- Test 4: Casting between incompatible types
unsafe def stringAsNat : Nat :=
  unsafeCast "hello"

-- Test 5: Unsafe proof "generation"
unsafe def unsafeProof : False :=
  unsafeCast ()

-- Can we use this in safe code?
-- theorem fakeTheorem : False := unsafeProof  -- Should be marked unsafe

-- Test 6: FFI external function
@[extern "nonexistent_c_function"]
opaque ffiTest : Nat → Nat

-- FFI functions are axioms, should be tracked
#check ffiTest

-- Test 7: Can we implement opaque with unsafe?
opaque opaqueAxiom : False

-- This is an axiom, should be tracked even if implemented later
-- unsafe def opaqueAxiom : False := unsafeCast ()

-- Test 8: Unsafe recursion
unsafe def unsafeLoop : Nat := unsafeLoop + 1

-- Does this cause issues during compilation?
-- #eval unsafeLoop  -- Would loop forever

-- Test 9: Mixing unsafe and partial
unsafe partial def unsafePartial (n : Nat) : Nat :=
  if n = 0 then 0
  else unsafePartial n + 1  -- Non-terminating

-- Test 10: Unsafe array access
unsafe def unsafeArrayAccess : IO Nat := do
  let arr : Array Nat := #[1, 2, 3]
  -- Out of bounds access without checking
  return arr.uget 100 (by decide)  -- Provides fake proof of bounds

-- Test 11: Unsafe pointer manipulation (if available)
-- Can we get raw pointers and cause corruption?
-- This would require specific Lean FFI features

-- Test 12: Cast between Prop and Type
unsafe def propAsType : Type :=
  unsafeCast (True : Prop)

-- Test 13: Cast proof to data
unsafe def proofAsData : Nat :=
  unsafeCast (rfl : 1 = 1)

-- Test 14: Circumvent termination checking
unsafe def bypassTermination : Nat → Nat
  | 0 => 0
  | n + 1 => bypassTermination (n + 1) + 1  -- Would loop forever

-- Test 15: Unsafe implementation of safe interface
class SafeInterface (α : Type) where
  safeMethod : α → Nat

-- Can we provide unsafe implementation?
unsafe instance : SafeInterface String where
  safeMethod := fun s => unsafeCast s  -- Type confusion!

-- Using it in safe code:
-- def useSafeInterface (s : String) : Nat :=
--   SafeInterface.safeMethod s  -- Should this be marked unsafe?

-- Test 16: Unsafe in initialization
-- unsafe def globalUnsafe : Nat := unsafeCastTest
-- def useGlobal : Nat := globalUnsafe  -- Does unsafe propagate?

-- Test 17: Unsafe match/pattern
unsafe def unsafeMatch (n : Nat) : Nat :=
  match n with
  | _ => unsafeCast "wrong type"

-- Test 18: Unsafe coercion
unsafe instance : Coe Bool Nat where
  coe := unsafeCast

-- Does this make all Bool→Nat conversions unsafe?
-- def testUnsafeCoe : Nat := (true : Bool)

-- Test 19: @[implemented_by] with unsafe
def safeFunc : Nat := 42

@[implemented_by unsafeCastTest]
def implementedBySafe : Nat := 42

-- Does @[implemented_by] leak unsafety?

-- Test 20: CRITICAL - Can we derive False in safe code?
-- If ANY of the following typechecks WITHOUT unsafe annotation, it's a bug!

-- Attempt 1: Through unsafeCast
-- def attemptFalse1 : False := unsafeCast ()  -- Should require 'unsafe'

-- Attempt 2: Through FFI
-- def attemptFalse2 : False := ffiTest 0  -- FFI should require axiom

-- Attempt 3: Through opaque
-- def attemptFalse3 : False := opaqueAxiom  -- Uses axiom

-- Attempt 4: Through unsafe instance
-- def attemptFalse4 : False :=
--   let n : Nat := SafeInterface.safeMethod "hello"
--   -- If n is garbage, can we derive False?
--   sorry

-- Test 21: Unsafe I/O
unsafe def unsafeIO : IO Unit := do
  IO.println "This is unsafe"
  -- Can unsafe IO leak effects?

-- Test 22: Memory safety - reference counting bypass?
unsafe def rcBypass : Array Nat := unsafeCast ()

-- Test 23: Stack overflow in unsafe
unsafe def unsafeDeepRecursion (n : Nat) : Nat :=
  if n = 0 then 0
  else 1 + unsafeDeepRecursion (n - 1)

-- Test 24: Unsafe and exceptions
unsafe def unsafeThrow : Nat :=
  panic! "unsafe panic"

-- Test 25: Type confusion in collections
unsafe def confusedArray : Array Nat :=
  unsafeCast (#["string", "array"] : Array String)

-- Can we read this as Nat array and cause corruption?
-- def useConfused := confusedArray[0]!

#check unsafeCastTest
#check ffiTest
#check unsafeProof
#check implementedBySafe
