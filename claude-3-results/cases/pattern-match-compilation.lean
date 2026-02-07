/-
Attack Vector: Pattern Matching Compilation Bugs
Target: Elaborator's pattern match → recursor compilation
Severity: CRITICAL if exploitable

The elaborator compiles pattern matching to eliminators/recursors.
Bugs in this compilation could:
- Miss cases
- Generate incorrect terms
- Bypass termination checking
- Create type mismatches
-/

-- Test 1: Overlapping patterns
def overlapTest (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 2
  | _ => 3
  | 2 => 4  -- This is unreachable, does elaborator catch it?

#check overlapTest

-- Test 2: Nested pattern matching with dependent types
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

def vecMatch {α : Type} : (n : Nat) → Vec α n → Nat
  | 0, .nil => 0
  | n+1, .cons _ _ => n

-- Test 3: Pattern matching with proof terms
def proofMatch (n : Nat) (h : n > 0) : Nat :=
  match n, h with
  | 0, h => absurd rfl h  -- n = 0 but n > 0
  | m+1, _ => m

-- Test 4: Mutual pattern matching
mutual
  inductive Even : Nat → Prop where
    | zero : Even 0
    | succ : Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | succ : Even n → Odd (n + 1)
end

-- Can pattern matching on mutual inductives be exploited?

-- Test 5: Pattern matching with recursive lets
def recLetMatch (n : Nat) : Nat :=
  match n with
  | 0 =>
      let rec loop (i : Nat) : Nat :=
        if i == 0 then 0 else loop (i - 1)
      loop 10
  | k+1 => k

-- Test 6: Match with complex index unification
inductive Fin : Nat → Type where
  | zero : Fin (n + 1)
  | succ : Fin n → Fin (n + 1)

def finMatch : Fin n → Nat
  | .zero => 0
  | .succ f => finMatch f + 1

-- Test 7: Match on quotient types
-- Quotient pattern matching is restricted, but can we bypass it?

-- Test 8: Pattern match with coercions
inductive Wrapper (α : Type) where
  | wrap : α → Wrapper α

instance : Coe α (Wrapper α) where
  coe x := .wrap x

def wrapperMatch : Wrapper Nat → Nat
  | .wrap n => n
  -- | n => n  -- Can we pattern match on coerced value?

-- Test 9: Inaccessible patterns
def inaccTest : (n : Nat) → Vec Nat n → Nat
  | 0, .nil => 0
  | n+1, .cons x xs => x
  -- What if we write: | _, .nil => 0  ?

-- Test 10: Pattern matching with universe polymorphism
def polyMatch.{u} (α : Type u) : Option α → Bool
  | some _ => true
  | none => false

-- Test 11: Guards in pattern matching
def guardTest (n : Nat) : Nat :=
  match n with
  | k => if k > 10 then k else 0

-- Test 12: As-patterns
def asPatternTest (n : Nat) : Nat :=
  match n with
  | k@(m + 1) => k + m  -- Is this properly compiled?
  | _ => 0

-- Test 13: Or-patterns
def orPatternTest (n : Nat) : Nat :=
  match n with
  | 0 | 1 => 42
  | _ => 0

-- Test 14: Pattern match with type annotations
def annotatedMatch (n : Nat) : Nat :=
  match (n : Nat) with
  | k => k

-- Test 15: Incomplete patterns (should warn/error)
def incompleteMatch : Option Nat → Nat
  | some n => n
  -- Missing: | none => ...

#check incompleteMatch

-- Test 16: Pattern match in type context
def TypeMatch (n : Nat) : Type :=
  match n with
  | 0 => Nat
  | _ => Bool

-- Can this create type soundness issues?
def tmTest : TypeMatch 0 := 42
def tmTest2 : TypeMatch 1 := true

-- Are tmTest and tmTest2 properly type-checked?
