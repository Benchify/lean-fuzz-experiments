-- Critical Test: Can type confusion affect soundness?
-- Can we use VM memory corruption to prove False?

import Lean

/-!
# Soundness Impact Analysis

This test explores whether VM-level type confusion can break
the soundness of Lean's proof system.

Key questions:
1. Does unsafe code execute during proof checking or only at runtime?
2. Can type confusion affect theorem statements?
3. Can we prove False using memory corruption?
4. Is there a boundary between kernel and VM?
-/

-- Test 1: Can unsafe code affect theorem statements?
unsafe def unsafeComputation : Nat :=
  let n : Nat := 42
  let s : String := unsafeCast n
  let recovered : Nat := unsafeCast s
  recovered  -- Returns 42 via type confusion

-- Try to use unsafe computation in a theorem
theorem unsafe_in_theorem : unsafeComputation = 42 := by
  rfl

#check unsafe_in_theorem

-- Test 2: Can we confuse the result to prove wrong equality?
unsafe def confusedEquality : Bool :=
  let x : Nat := 1
  let y : Nat := 2
  let confused : Bool := unsafeCast x
  confused  -- Type confused Nat as Bool

-- Try to derive False from confused computation
theorem test_confused_equality : confusedEquality = true := by
  rfl  -- Will this succeed or fail?

-- Test 3: Attempt to prove False directly using unsafe
unsafe def deriveFalse : False :=
  let proof : True := True.intro
  let falseProof : False := unsafeCast proof
  falseProof

-- Can we actually use this to prove False?
-- theorem false_from_unsafe : False := deriveFalse

-- Test 4: Can unsafe affect decidability?
unsafe def unsafeDecide (p : Prop) : Bool :=
  -- Try to force any proposition to be "decidable"
  true

-- Test 5: Soundness boundary test
unsafe def kernelVsVM : Nat := do
  -- This is unsafe code
  let n : Nat := 42
  let s : String := unsafeCast n
  let recovered : Nat := unsafeCast s
  return recovered

-- Can kernel see the unsafe manipulation?
#eval kernelVsVM  -- Runtime: executes unsafe code
#reduce kernelVsVM  -- Kernel reduction: what happens?

-- Test 6: Proof-carrying unsafe code
structure ProofWithUnsafe where
  value : Nat
  proof : value > 0

unsafe def makeProofWithUnsafe (n : Nat) : ProofWithUnsafe :=
  let fakeProof : n > 0 := unsafeCast ()  -- Type confuse Unit to proof
  ⟨n, fakeProof⟩

-- Will this work?
-- def testProof : ProofWithUnsafe := makeProofWithUnsafe 0

-- Test 7: Can we bypass `sorry` detection?
unsafe def hiddenSorry : 2 + 2 = 5 :=
  unsafeCast ()  -- Cast Unit to proof

-- Test 8: Macro-level hiding
macro "stealth_unsafe" : term => do
  `(unsafeCast ())

-- Can we hide unsafe in macros?
-- unsafe def hidden : False := stealth_unsafe

-- Test 9: Kernel sees through unsafe?
theorem kernel_check : unsafeComputation = 42 := rfl

#print kernel_check
-- Does the kernel see unsafeComputation as a black box?

-- Test 10: Does sorry tracking catch unsafe?
unsafe def unsafe_false : False := unsafeCast ()

-- Check if this is flagged as using sorry
-- #print axioms unsafe_false  -- Will this show sorry?

def main : IO Unit := do
  IO.println "=== Soundness Impact Tests ==="

  IO.println "\n1. Unsafe in theorem:"
  IO.println s!"  unsafeComputation = {unsafeComputation}"
  IO.println s!"  Theorem states: unsafeComputation = 42"

  IO.println "\n2. Confused equality:"
  IO.println s!"  confusedEquality = {confusedEquality}"

  IO.println "\n3. Can we derive False?"
  IO.println "  Attempting to prove False via type confusion..."
  -- If this doesn't crash, we have a soundness issue!
  -- try
  --   let _ := deriveFalse
  --   IO.println "  ⚠️ CRITICAL: Derived False without crash!"
  -- catch _ =>
  --   IO.println "  ✓ Crashed (soundness preserved)"

  IO.println "\n4. Kernel vs VM boundary:"
  IO.println s!"  Runtime result: {kernelVsVM}"

  IO.println "\n=== Analysis ==="
  IO.println "If theorems using unsafe code type-check:"
  IO.println "  ⚠️ Unsafe can affect proof statements"
  IO.println "If we can prove False:"
  IO.println "  🔴 CRITICAL: Soundness is broken"
  IO.println "If kernel rejects unsafe proofs:"
  IO.println "  ✓ Soundness is preserved (VM-only issue)"

#eval main
