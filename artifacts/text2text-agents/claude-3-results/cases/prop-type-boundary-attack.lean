/-
SOPHISTICATED ATTACK: Prop/Type Boundary Exploitation
Target: The boundary between Prop and Type
Severity: CRITICAL if exploitable

The Prop/Type distinction is fundamental to Lean's design:
- Prop: Universe of propositions (proof irrelevance, erasure)
- Type u: Universe of data types

Breaking this boundary would be catastrophic for soundness.
-/

-- Attack 1: Extracting witnesses from existential in Prop
def PropEx : Prop := ∃ (n : Nat), n > 100

-- We cannot directly extract the witness
-- def extractWitness (h : PropEx) : Nat := ...  -- Not possible

-- But can we do it indirectly?

-- Attack 2: Using Classical.choice
open Classical

axiom prop_ex_proof : PropEx

-- Classical.choose requires the type to be in Type, not Prop
-- def classicalExtract : Nat := Classical.choose prop_ex_proof  -- Fails

-- But what about converting Prop to Type?

-- Attack 3: Prop to Type via Decidable
class DecidableProp (p : Prop) : Type where
  decide : Decidable p

-- Can we use decidability to leak information from Prop?

def decideAndExtract (p : Prop) [DecidableProp p] : Bool :=
  decide p

-- This is OK for decidable props, but can we exploit it?

-- Attack 4: Subtype from Prop
def PropToType (p : Prop) : Type := { _ : Unit // p }

-- This is allowed! But the witness is still irrelevant
-- Can we extract it?

def prop_to_type_test : PropToType True := ⟨(), trivial⟩

-- Attack 5: Sort polymorphism
-- Can we create a function that works on both Prop and Type?

def polymorphicSort.{u} (α : Sort u) : Sort u := α

#check polymorphicSort Prop  -- Sort 0 (Prop)
#check polymorphicSort Nat   -- Sort 0 (Type)
#check polymorphicSort Type  -- Sort 1 (Type 1)

-- Can we confuse the sort levels?

-- Attack 6: PProd (heterogeneous product in Type)
-- PProd.{u,v} α β where α : Sort u, β : Sort v

def mixPropType : PProd Prop Nat := ⟨True, 42⟩

-- Can we extract computational content from the Prop part?

-- Attack 7: PSigma (dependent pair in Type)
def sigmaMixing : PSigma (fun (p : Prop) => if p then Nat else Bool) :=
  ⟨True, 42⟩

-- The first component is Prop, second is Type
-- Can this be exploited?

-- Attack 8: Equality between Prop and Type elements
-- We can have equality at Prop level and Type level

def propEq : Prop := True = True
def typeEq : Prop := (0 : Nat) = (0 : Nat)

-- Both are Props, but about different universes
-- Can we confuse them?

-- Attack 9: Cast between Prop and Type
-- axiom prop_type_cast : Prop = Type  -- This should fail

-- If we had such a cast, we could break everything

-- Attack 10: Recursion into Prop
-- We can define Props recursively

inductive InductiveProp : Nat → Prop where
  | zero : InductiveProp 0
  | succ : InductiveProp n → InductiveProp (n + 1)

-- Can we extract the Nat index?
def extractIndex (h : InductiveProp n) : Nat := n

-- This is OK (n is in Type, not Prop)
-- But what about the proof itself?

-- Attack 11: Large elimination attempt (sophisticated)
-- Direct large elimination is forbidden
-- But what about through composition?

inductive PropData : Prop where
  | mk : Nat → PropData

-- Can't do this directly:
-- def direct_extract : PropData → Nat
--   | .mk n => n

-- But what about:
def indirect_extract_attempt : (h : PropData) → { n : Nat // True } := fun h =>
  -- Can we somehow extract n here?
  ⟨0, trivial⟩

-- Attack 12: Squash type (forces Prop)
-- Squash α makes α into a Prop

def squashNat : Prop := Squash Nat

axiom sq : squashNat

-- Can we extract the Nat from Squash?
-- def unsquash : squashNat → Nat := ...  -- Not possible

-- Attack 13: Prop in function types
def PropFunction : Type := Prop → Nat

def pf : PropFunction := fun p => if p then 1 else 0

-- Wait, we can't decide arbitrary Props!
-- This should fail unless we use Classical

-- Attack 14: Type class on Prop
class PropClass (p : Prop) : Type where
  toNat : Nat

-- Can we use this to leak information?

instance : PropClass True where
  toNat := 42

def leakFromProp (p : Prop) [PropClass p] : Nat :=
  PropClass.toNat

#eval leakFromProp True  -- 42

-- But this is OK - the Nat is in the instance, not the proof

-- Attack 15: Proof relevance via Type dependency
structure ProofRelevant (p : Prop) : Type where
  evidence : p
  data : Nat

-- The proof is now in Type context
def pr : ProofRelevant True := ⟨trivial, 42⟩

-- Can we exploit this?

-- Attack 16: Mixing impredicativity
-- Prop is impredicative, Type is not

def impredicProp : Prop := ∀ (p : Prop), p → p

-- This is OK

-- def impredicType : Type := ∀ (α : Type), α → α
-- This is Type 1, not Type 0 (not impredicative)

-- Can we exploit the boundary?

-- Attack 17: Quotient and Prop/Type
-- Quotient types can be in Prop or Type

def QuotInProp : Prop := Quot (fun (n m : Nat) => n = m)
def QuotInType : Type := Quot (fun (n m : Nat) => n = m)

-- Can we confuse these?

-- Attack 18: Acc (accessibility predicate for well-founded recursion)
-- Acc is in Prop but affects termination

def accExample : Acc (· < ·) (5 : Nat) := by
  constructor
  intro y h
  -- Recursively build Acc proof
  sorry

-- Can we affect computation via Acc proofs?

-- Attack 19: Decidability and Type class resolution
-- Decidable instances bridge Prop and Type

instance : Decidable True where
  decide := true

-- Can we use this to leak information?

-- Attack 20: Native Decidable vs Classical
open Classical

def nativeDec (p : Prop) [Decidable p] : Bool := decide p

-- vs

def classicalDec (p : Prop) : Bool :=
  if Classical.propDecidable.decide then true else false

-- Can these differ in exploitable ways?

-- Attack 21: Epsilon operator (Classical.choose)
axiom exists_large : ∃ n : Nat, n > 1000000

def epsilon_test : Nat := Classical.choose exists_large

-- The Nat is in Type, but derived from Prop
-- Any exploit here?

-- Attack 22: Nonempty vs Inhabited
-- Nonempty is in Prop, Inhabited is in Type

def nonemptyProp : Prop := Nonempty Nat
def inhabitedType : Type := Inhabited Nat

-- Can we confuse these?

instance : Nonempty Nat := ⟨0⟩
instance : Inhabited Nat := ⟨0⟩

-- Attack 23: Prop-valued functions in Type
def functionReturningProp : Nat → Prop := fun n => n > 0

-- This is Type (function type)
-- But returns Props
-- Any confusion possible?

-- Attack 24: Dependent types mixing Prop and Type
def depMixing (p : Prop) : Type := if p then Nat else Bool

-- Wait, can't decide arbitrary p!

-- Need decidability:
def depMixingDec (p : Prop) [Decidable p] : Type :=
  if p then Nat else Bool

-- Attack 25: Proof vs Program extraction
-- Some proof assistants extract programs from proofs
-- Can we trick Lean's extraction?

-- In compiled code, Props are erased
-- Can we observe this?

def withProp (h : True) : Nat := 42
def withoutProp : Nat := 42

-- These should behave identically
-- Any difference in compiled code?

-- Attack 26: Subsingletons at Type level
-- Prop subsingletons are automatic
-- Type subsingletons are not

class TypeSubsingleton (α : Type) : Prop where
  eq : ∀ (a b : α), a = b

-- If we could prove TypeSubsingleton Nat, we'd have 0 = 1!

-- Attack 27: Trunc (propositional truncation)
-- Like Squash, forces prop

def truncNat : Type := Trunc Nat

-- Trunc Nat is in Type but acts like Prop
-- Can we exploit this boundary?

def mkTrunc : truncNat := Trunc.mk 42

-- Can we get 42 back out? No!
-- But can we leak it somehow?

-- Attack 28: Reflection and universe levels
open Lean in

def reflectProp : MetaM Expr := do
  return Expr.sort Level.zero  -- Prop

def reflectType : MetaM Expr := do
  return Expr.sort (Level.succ Level.zero)  -- Type

-- Can metaprogramming confuse these?

-- ULTIMATE TEST: Try to extract Nat from existential in Prop
axiom ultimate_prop : ∃ (n : Nat), n = 12345

-- This should be impossible:
-- def ultimate_extract : Nat := ...
-- If we can do this, we've broken Prop/Type separation!
