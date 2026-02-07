/-
UNEXPLORED SOUNDNESS THREATS
What other ways could Lean's soundness be broken?

This file systematically explores attack surfaces we haven't fully tested yet.

Categories:
1. Built-in Axioms and Consistency
2. Universe Polymorphism Edge Cases
3. Quotient Types and Setoids
4. Coinductive Types and Infinity
5. Type Class Coherence
6. Reduction and Definitional Equality
7. Impredicativity of Prop
8. Module System and Imports
9. Computational Irrelevance
10. Sized Types and Termination
-/

import Lean

/-! ## THREAT 1: Inconsistent Built-in Axioms -/

-- Lean has several built-in axioms. Are they consistent?

-- 1. Propositional extensionality
axiom propext {a b : Prop} : (a ↔ b) → a = b

-- 2. Function extensionality
axiom funext {α : Sort u} {β : α → Sort v} {f g : ∀ x, β x} :
  (∀ x, f x = g x) → f = g

-- 3. Quotient types
axiom Quot.sound {α : Sort u} {r : α → α → Prop} {a b : α} :
  r a b → Quot.mk r a = Quot.mk r b

-- 4. Classical choice
axiom Classical.choice {α : Sort u} : Nonempty α → α

-- THREAT: What if these axioms together are inconsistent?
-- Example: Russell's paradox-like constructions

-- Can we construct a paradox using these axioms?

def russell_type : Type 1 := {α : Type // α ∉ α}
-- Note: Above doesn't type-check, but are there subtler versions?

/-! ## THREAT 2: Universe Polymorphism Loopholes -/

-- Can we create universe inconsistencies?

-- Attempt 1: Type-in-Type (should fail)
-- def type_in_type : Type := Type
-- Error: universe level mismatch

-- Attempt 2: Universe level arithmetic errors
universe u v

def universe_confusion (α : Type u) : Type (max u v) := α
-- Is the universe level checking perfect?

-- Attempt 3: Impredicative universe collapse
def collapse (α : Sort u) : Prop := ∃ (_ : α), True

-- Can we use this to collapse universes?
theorem universe_collapse : Type 0 = Prop := by
  sorry  -- Can this be proven without axioms?

/-! ## THREAT 3: Quotient Type Soundness -/

-- Quotients are implemented with axioms
-- Are they truly sound?

-- Create a quotient that identifies different values
def bad_relation (a b : Nat) : Prop := True  -- Everything equal!

def NatMod := Quot bad_relation

-- If everything is equal, we should be able to prove anything
def zero_quot : NatMod := Quot.mk bad_relation 0
def one_quot : NatMod := Quot.mk bad_relation 1

theorem quotient_confusion : zero_quot = one_quot := by
  apply Quot.sound
  trivial  -- bad_relation is always True

-- Now can we use this to prove False?
-- By lifting properties that distinguish 0 and 1?

def nat_of_quot : NatMod → Nat :=
  Quot.lift id (fun a b _ => rfl)  -- Requires proof that id respects relation

-- Above won't work, but are there subtler attacks?

/-! ## THREAT 4: Coinductive Types and Infinity -/

-- Can we create non-terminating computations that type-check?

-- Attempt: Coinductive streams
coinductive Stream (α : Type u) where
  | cons : α → Stream α → Stream α

-- Can we use corecursion to prove False?
def loop : Stream Nat := Stream.cons 0 loop

-- Extract infinite information to prove contradictions?

/-! ## THREAT 5: Type Class Coherence Violations -/

-- We tested some of this, but let's go deeper

-- Two different instances with different behavior
structure Weird where
  n : Nat

instance : Add Weird where
  add a b := ⟨a.n + b.n⟩

instance : Add Weird where  -- Duplicate instance (should warn)
  add a b := ⟨a.n * b.n⟩

-- If both instances exist, which is used?
-- Can we use this ambiguity to prove False?

def test_coherence (a b : Weird) : Weird := a + b

-- What if we prove properties assuming one instance,
-- then use them with the other instance?

/-! ## THREAT 6: Reduction and Definitional Equality Bugs -/

-- Is the reduction algorithm correct?

-- Attempt 1: Circular reductions
def circular1 : Nat := circular2
def circular2 : Nat := circular1

-- Above won't type-check, but are there subtler versions?

-- Attempt 2: Reduction that never terminates
def infinite_reduction : Nat := infinite_reduction + 1

-- Can we create terms that loop during type checking?

-- Attempt 3: Reduction to wrong result
def wrong_reduction : 1 + 1 = 3 := by
  -- If reduction is buggy, might reduce wrongly
  rfl  -- Should fail

/-! ## THREAT 7: Impredicativity of Prop Exploitation -/

-- Prop is impredicative: Prop : Type, but ∀ (p : Prop), p : Prop

-- Can we use this to encode paradoxes?

-- Attempt: Girard's paradox-style construction
def girard_type : Prop := ∀ (p : Prop), p → p

-- Can we construct Russell's paradox in Prop?
def russell_prop : Prop := ∃ (S : Prop → Prop), ∀ p, S p ↔ ¬(p → p)

-- If russell_prop is inhabited, we have False
theorem russell_paradox_attempt : russell_prop → False := by
  sorry  -- Can this be completed?

/-! ## THREAT 8: Module System and Import Cycles -/

-- Can circular imports cause soundness issues?

-- File A.lean:
-- import B
-- def a : Nat := b

-- File B.lean:
-- import A
-- def b : Nat := a

-- If this is allowed, we could have circular definitions
-- that appear well-founded but aren't

/-! ## THREAT 9: Large Elimination Issues -/

-- Converting Prop to Type is restricted
-- Are the restrictions sound?

-- Can't eliminate from Prop to Type (usually)
def large_elim_attempt (h : ∃ n : Nat, n > 0) : Nat :=
  -- This should fail:
  -- h.1  -- Can't extract witness from Prop
  sorry

-- But: Singleton elimination IS allowed
theorem singleton_elim (h : ∃! n : Nat, n = 0) : Nat :=
  0  -- This is allowed because proof is irrelevant

-- Can we abuse singleton elimination?

inductive FalseSubtype : Type where
  | mk : False → FalseSubtype

-- If False, there's exactly one inhabitant (none!)
-- Can we use uniqueness here for large elimination?

/-! ## THREAT 10: Computational Irrelevance Abuse -/

-- Subsingleton types have computational irrelevance
-- Can we abuse this?

-- Mark something as Subsingleton when it's not
instance : Subsingleton Nat where
  allEq := fun _ _ => rfl  -- WRONG! Nats aren't all equal

-- If this is allowed, we could prove anything
theorem nat_confusion : (0 : Nat) = 1 := by
  -- If Nat is considered Subsingleton:
  apply Subsingleton.allEq
  -- This should fail!

/-! ## THREAT 11: Unsafe Code Leaking Into Proofs -/

-- unsafe code can do anything
-- Can it affect soundness?

unsafe def unsafe_false : False :=
  -- In unsafe code, we could:
  -- - Cast arbitrary types
  -- - Create uninitialized values
  -- - Cause undefined behavior
  sorry

-- But can unsafe_false leak into safe proofs?
-- theorem bad_theorem : False := unsafe_false
-- This should be rejected!

-- THREAT: What if unsafe is not properly tracked?

/-! ## THREAT 12: Macro Expansion Bugs -/

-- Macros can generate arbitrary syntax
-- Can malicious macros create unsound code?

macro "inject_axiom" : command => `(axiom secret_false : False)

-- If this is expanded before checking:
-- inject_axiom
-- theorem easy : False := secret_false

-- Does Lean properly validate macro output?

/-! ## THREAT 13: Type Class Synthesis Loops -/

-- Can we create infinite type class synthesis?

class Recursive (α : Type) where
  next : Recursive α

instance : Recursive α where
  next := inferInstance  -- Recursive lookup!

-- This might loop during synthesis
-- Could looping synthesis affect soundness?

/-! ## THREAT 14: Dependent Type Checking Edge Cases -/

-- Dependent types have complex checking
-- Are there edge cases?

-- Type that depends on value
def dependent_type (n : Nat) : Type :=
  match n with
  | 0 => Unit
  | _ => Empty

-- Value of dependent type
def dependent_value (n : Nat) : dependent_type n :=
  match n with
  | 0 => ()
  | _ => .  -- No constructor for Empty

-- Above has problem, but can we exploit checking bugs?

/-! ## THREAT 15: Termination Checker Bypass -/

-- We tested some, but let's try more complex cases

-- Mutual recursion with hidden non-termination
mutual
  def sneaky1 (n : Nat) : Nat :=
    if n = 0 then 0
    else sneaky2 n  -- Doesn't decrease!

  def sneaky2 (n : Nat) : Nat :=
    sneaky1 n  -- Doesn't decrease!
end

-- Can we package non-termination in ways that fool checker?

/-! ## THREAT 16: Elaborator Producing Bad Terms -/

-- Can elaborator create ill-typed terms that kernel misses?

-- Force elaborator to create term with mismatched types
-- This is hard to do directly, but:

def elaborate_confusion : Nat :=
  -- Create complex term that elaborator processes
  -- With type mismatches hidden in complexity
  id (id (id (id (id (id (id (id (id (id 0)))))))))

-- The term above is fine, but can we create
-- situations where elaborator makes mistakes?

/-! ## THREAT 17: Universe Level Polymorphism Bugs -/

-- Complex universe polymorphism might have bugs

-- Function that changes universe levels unexpectedly
def lift_universe.{u} (α : Type u) : Type (u+1) := α
-- Above won't work, but indicates the kind of bug

-- Can we confuse universe unification?
universe u v w

def confuse_universes (α : Type u) (β : Type v) : Type w :=
  α × β  -- This should require w = max u v

-- What if we force w to be smaller?

/-! ## THREAT 18: Optimization Bugs in Native Compiler -/

-- We tested correctness, but aggressive optimization?

-- Code that changes behavior under optimization
def optimization_sensitive : Nat :=
  let huge := List.range 1000000
  huge.length

-- Could optimization bugs affect proofs about code?

/-! ## THREAT 19: Serialization/Deserialization Mismatches -/

-- .olean files store declarations
-- We found some issues, but are there more?

-- Could we serialize one declaration and deserialize as another?
-- Could we inject declarations without kernel validation?
-- Could we modify .olean files to skip checks?

/-! ## THREAT 20: Namespace and Shadowing Bugs -/

-- Can we shadow important declarations?

namespace Bad
  -- Shadow built-in types
  def Nat : Type := Empty
  def True : Prop := False

  -- Now in this namespace:
  theorem shadowing_proof : True := rfl
  -- This should prove False = False, not True!
end Bad

-- Can namespace confusion cause soundness issues?

/-! ## THREAT 21: Attribute and Annotation Bugs -/

-- Attributes affect behavior
-- Can we misuse them?

@[irreducible]
def hidden : Nat := 0

@[reducible]
def exposed : Nat := hidden

-- Can reducibility attributes be used to hide unsound definitions?

/-! ## THREAT 22: Type Inference Unification Bugs -/

-- Type inference uses unification
-- Are there bugs in unification?

def unify_bug (α β : Type) (h : α = β) (a : α) : β :=
  cast h a

-- Complex unification problems might have bugs
-- Can we exploit them?

/-! ## THREAT 23: Proof Irrelevance Edge Cases -/

-- All proofs of same Prop are equal
-- Can we abuse this?

def two_proofs (p : Prop) (h1 h2 : p) : h1 = h2 := rfl

-- What if proof contains computational content hidden somehow?
-- What if proof relies on side effects?

/-! ## THREAT 24: Decidability and Classical Logic Interaction -/

-- Decidable proofs have computational content
-- Classical proofs don't

instance : Decidable False := isFalse id

-- Can we mix decidable and classical in problematic ways?

noncomputable def classical_nat : Nat :=
  if False then 0 else 1

def decidable_nat : Nat :=
  if False then 0 else 1

-- These should be equal, but go through different paths
-- Could differences cause issues?

/-! ## THREAT 25: Meta-level Reflection Bugs -/

-- Lean has meta-level reflection
-- Can we manipulate meta-level to affect object level?

open Lean Elab Command in
elab "meta_inject" : command => do
  -- Can we inject declarations at meta-level
  -- that bypass kernel?
  return ()

-- meta_inject

/-! ## THREAT 26: FFI and Soundness Boundary -/

-- We know FFI can break security
-- But can it break soundness if used in proofs?

@[extern "get_false_proof"]
opaque ffi_false : IO False

-- Can we use this in a proof?
-- theorem ffi_theorem : False := ffi_false  -- Type error! IO False ≠ False

-- But: What if FFI is used in tactics during elaboration?

/-! ## THREAT 27: Panic and Error Handling -/

-- Can we use panic to escape type checking?

def panic_escape : Nat :=
  panic! "Escape!"

-- panic! returns ⊥ (Empty), which can be cast to anything
-- But it's in IO, so shouldn't affect proofs

-- Can we abuse panic in elaboration?

/-! ## THREAT 28: Size Change Principle for Termination -/

-- Lean uses size-change principle
-- Are there patterns it doesn't handle?

def lexicographic_sneaky (n m : Nat) : Nat :=
  if n = 0 then 0
  else if m = 0 then lexicographic_sneaky (n-1) 1000000
  else lexicographic_sneaky n (m-1)
  -- This terminates (lexicographic on (n,m))
  -- Does checker accept it?

-- If checker is incomplete, rejected terminating functions are fine
-- But if checker is unsound, accepted non-terminating ones are BAD

/-! ## THREAD 29: Well-Founded Recursion Soundness -/

-- Well-founded recursion is powerful
-- Is it correctly implemented?

def wf_sneaky : Nat → Nat :=
  WellFounded.fix (measure id).wf fun n f =>
    if n = 0 then 0
    else f n (by omega)  -- Proof that n < n (FALSE!)

-- If proof obligation is not properly checked, we have non-termination

/-! ## THREAT 30: Grind Tactic and Automation Soundness -/

-- Automated tactics generate proofs
-- Are they sound?

example : 1 + 1 = 2 := by
  -- grind
  rfl

-- What if grind (or similar) generates invalid proof terms?
-- Kernel should catch them, but does it always?

/-! ## THREAT 31: Simp Lemma Bugs -/

-- Simp uses rewrite rules
-- Can contradictory simp lemmas prove False?

@[simp] theorem bad_simp1 : (0 : Nat) = 1 := sorry
@[simp] theorem bad_simp2 : (1 : Nat) = 0 := sorry

example : False := by
  have : (0 : Nat) = 1 := by simp
  have : (1 : Nat) = 0 := by simp
  -- Now we have 0 = 1
  omega  -- Should derive contradiction from Nat axioms

-- But wait, the sorry axioms are tracked!
-- Still, can simp create bad proofs if lemmas are inconsistent?

/-! ## THREAT 32: Structure Eta and Definitional Equality -/

-- Structures have eta equality
-- Can we abuse this?

structure Point where
  x : Nat
  y : Nat

def p1 : Point := ⟨0, 1⟩
def p2 : Point := {x := 0, y := 1}

theorem struct_eq : p1 = p2 := rfl  -- Definitionally equal by eta

-- Can we use eta to create circular definitions?

/-! ## THREAT 33: Coercion Chains -/

-- Coercions can chain
-- Can long coercion chains hide type mismatches?

instance : Coe Nat Int where coe := Int.ofNat
instance : Coe Int Rat where coe := Rat.ofInt
-- ... many more coercions

-- Can we coerce things that shouldn't coerce through a long chain?

/-! ## THREAT 34: Notation and Parsing Ambiguity -/

-- Complex notation can be ambiguous
-- Can this hide unsound definitions?

notation:max x " ∘ " y => x + y  -- Redefine function composition!

def confused : Nat → Nat := id ∘ id
-- This is now id + id, not composition!

-- Can notation abuse lead to soundness issues?

/-! ## THREAT 35: Performance-Induced Bugs -/

-- Very large terms might cause:
-- - Timeout (incomplete checking)
-- - Stack overflow (crash during checking)
-- - Memory exhaustion (incomplete checking)

-- Can we exploit resource limits?

def huge_term : Nat :=
  -- Generate term so large that checker times out
  -- But claim it proves False
  sorry

-- If checker times out, does it accept or reject?

/-! ## SUMMARY -/

/-
We've identified 35 potential soundness threat categories:

HIGH PRIORITY (Need Testing):
1. Quotient type consistency
2. Universe polymorphism edge cases
3. Termination checker completeness/soundness
4. Type class coherence issues
5. Reduction algorithm correctness
6. Serialization validation
7. Elaborator correctness

MEDIUM PRIORITY:
8. Impredicativity of Prop
9. Large elimination edge cases
10. Computational irrelevance
11. Dependent type checking
12. Well-founded recursion
13. Mutual recursion
14. Macro expansion validation

LOWER PRIORITY (Likely Safe):
15. Built-in axioms (well-studied)
16. Structure eta equality
17. Coercion chains
18. Namespace shadowing
19. FFI in proofs (type system prevents)
20. Classical/decidable interaction

ALREADY TESTED (This Audit):
21. Kernel bypass - 0 bugs found
22. Buffer overflow - security only, not soundness
23. Native compiler - correct
24. Environment corruption - blocked

NEXT STEPS:
- Test quotient types thoroughly
- Test universe polymorphism edge cases
- Stress test termination checker
- Test type class coherence
- Test serialization with malformed .olean files
-/
