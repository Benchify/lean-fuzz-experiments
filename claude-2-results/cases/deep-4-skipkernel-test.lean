/-
Deep Test 4: Testing debug.skipKernelTC Behavior
Precisely determining what this dangerous option actually skips

The option is documented to "skip kernel type checker" but we need
to test EXACTLY what it skips and what it still checks.
-/

-- BASELINE: Without skipKernelTC, these should all error

-- Test 1: Type error (should fail without skip)
-- def typeError : Nat := "hello"  -- Type mismatch

-- Test 2: Axiom with impossible type (should work, it's an axiom)
axiom impossibleAxiom : 1 = 2

-- This is allowed even without skipKernelTC because axioms don't need proofs

-- Test 3: Theorem with sorry (should warn)
theorem sorriedTheorem : 1 = 1 := sorry

-- Now test WITH skipKernelTC enabled

set_option debug.skipKernelTC true

-- Test 4: Can we define things with type errors?
-- def skippedTypeError : Nat := "hello"  -- Still errors at elaboration

-- Test 5: Axiom with obviously false type
axiom skippedAxiom1 : False
axiom skippedAxiom2 : Bool = Nat
axiom skippedAxiom3 : 0 = 1

-- These are axioms, so they don't need proofs anyway

-- Test 6: Theorem with bad proof
-- theorem badProof : 1 = 1 := (sorry : 2 = 2)  -- Type mismatch even with skip

-- Test 7: Non-terminating definition
partial def nonTerminating : Nat := nonTerminating + 1

-- Partial is required even with skipKernelTC

-- Test 8: Inductive with negative occurrence
-- inductive Bad where
--   | mk : (Bad → False) → Bad
-- Should still fail (positivity is checked before kernel)

-- Test 9: Universe inconsistency
-- axiom univBad : Type 0 = Type 1
-- This FAILS even with skipKernelTC! (as we saw above)

-- Test 10: Recursion without termination proof
-- def unprovenRec (n : Nat) : Nat :=
--   match n with
--   | 0 => 0
--   | k + 1 => unprovenRec (k + 2)  -- Increases!
-- termination_by n
-- decreasing_by sorry  -- Does skipKernelTC allow this?

-- Test 11: Mutual recursion without termination
mutual
  def mutA (n : Nat) : Nat :=
    match n with
    | 0 => 0
    | k + 1 => mutB k

  def mutB (n : Nat) : Nat :=
    match n with
    | 0 => 0
    | k + 1 => mutA (k + 1)  -- Not decreasing!
end
termination_by mutA n => n; mutB n => n
decreasing_by sorry; sorry  -- With skipKernelTC?

-- Test 12: Type class with impossible instance
class ImpossibleClass (α : Type) : Prop where
  impossible : α → Empty

-- instance : ImpossibleClass Nat where
--   impossible := sorry  -- With skipKernelTC, is this allowed?

-- Test 13: Coercion creating type confusion
-- instance : Coe Nat Bool where
--   coe := sorry
-- With skipKernelTC, does this work?

-- Test 14: Pattern matching with impossible case
def impossibleMatch (n : Nat) (h : n < 0) : False :=
  match n, h with
  | _, h' => Nat.not_lt_zero n h'

-- Test 15: Definitional equality with skipKernelTC
theorem defEqTest : 2 + 2 = 4 := rfl

-- Does skipKernelTC affect definitional equality checking?

-- Test 16: Proof irrelevance
theorem proof1 : 1 = 1 := rfl
theorem proof2 : 1 = 1 := Eq.refl 1
theorem proofEq : proof1 = proof2 := rfl

-- Test 17: Subsingleton elimination
def subsingletonTest (h1 h2 : 1 = 1) : h1 = h2 := rfl

-- Test 18: Large elimination from Prop
-- inductive PropData : Prop where
--   | mk : Nat → PropData
-- def largeElim : PropData → Nat
--   | .mk n => n
-- Should fail even with skipKernelTC (elaborator rejects)

-- Test 19: Quotient with lying relation
def LyingRel (a b : Nat) : Prop := a = b + 1
axiom lyingRefl : ∀ n, LyingRel n n  -- Lie about reflexivity

def LyingQuot := Quot LyingRel

theorem quotLie : Quot.mk LyingRel 0 = Quot.mk LyingRel 1 :=
  Quot.sound (lyingRefl 0)

-- With skipKernelTC, is the axiom checked?

-- Test 20: Unsafe code in safe context
unsafe def unsafeValue : Nat := unsafeCast "hello"

-- def leakUnsafe : Nat := unsafeValue  -- Should still require unsafe

-- Test 21: FFI with bad signature
@[extern "nonexistent"]
opaque ffiDangerous : Nat

-- With skipKernelTC, is extern declaration checked?

set_option debug.skipKernelTC false  -- Reset

-- ANALYSIS:
-- What does skipKernelTC ACTUALLY skip?

-- From testing:
-- ✓ Skipped: Kernel type checking of definitions
-- ✓ Skipped: Some proof obligations
-- ✗ NOT Skipped: Universe inconsistency checks
-- ✗ NOT Skipped: Elaboration-time type checking
-- ✗ NOT Skipped: Positivity checking
-- ✗ NOT Skipped: Termination checking setup
-- ? Unknown: Does it skip checking imported constants?
-- ? Unknown: Does it affect trust level behavior?

-- SECURITY IMPLICATIONS:
-- If skipKernelTC can be enabled via build system or imports,
-- it could allow unsound code to compile and run.

-- However, it seems to NOT completely bypass all safety checks,
-- so it may not directly allow deriving False.

-- But combined with other exploits (axioms, sorry, etc.),
-- it could weaken the safety guarantees significantly.

#check skippedAxiom1
#check mutA
#check impossibleMatch
#check quotLie
