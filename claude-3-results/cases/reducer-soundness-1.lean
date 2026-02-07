/-
Attack: Reducer/Definitional Equality Soundness
Target: Kernel reducer implementation
Strategy: Test complex reduction scenarios that might have bugs

Lean's reducer handles:
- Beta reduction (function application)
- Delta reduction (unfolding definitions)
- Iota reduction (pattern matching/recursors)
- Zeta reduction (let-bindings)
- Projection reduction (structure field access)

Bugs in any of these could make definitionally unequal terms equal,
allowing proofs of False.
-/

-- Test 1: Nested structure projections with complex reducibility
structure A where
  val : Nat

structure B where
  a : A

structure C where
  b : B

def mkC : C := ⟨⟨⟨42⟩⟩⟩

-- Try to confuse projection reduction
def test1 := C.b (mkC)
def test2 := mkC.b

-- These should be definitionally equal
example : test1 = test2 := rfl

-- Test 2: Recursive let-bindings with dependent types
-- Let-rec in dependent type theory is subtle
def complexLet (n : Nat) : Nat :=
  let rec loop (i : Nat) : Nat :=
    if i == 0 then 42
    else loop (i - 1)
  loop n

-- Test 3: Pattern matching reduction edge cases
inductive MyVec (α : Type u) : Nat → Type u where
  | nil : MyVec α 0
  | cons : α → {n : Nat} → MyVec α n → MyVec α (n + 1)

def vecHead {α : Type u} {n : Nat} : MyVec α (n + 1) → α
  | .cons a _ => a

-- Try to confuse the reducer with dependent pattern matching
def vecTest : MyVec Nat 2 := .cons 1 (.cons 2 .nil)
def headTest := vecHead vecTest

-- Test 4: Mutual recursion with complex dependencies
mutual
  def evenNat : Nat → Bool
    | 0 => true
    | n + 1 => oddNat n

  def oddNat : Nat → Bool
    | 0 => false
    | n + 1 => evenNat n
end

-- Test 5: Well-founded recursion with custom measure
def ackermann : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ackermann m 1
  | m + 1, n + 1 => ackermann m (ackermann (m + 1) n)
termination_by m n => (m, n)

-- Test 6: Complex reduction with proofs
def complexProof (n : Nat) : Nat :=
  match h : n with
  | 0 => 0
  | k + 1 => k

-- Test 7: Projection reduction with nested matches
structure Complex where
  field1 : Nat
  field2 : Nat → Nat

def mkComplex : Complex := {
  field1 := 42,
  field2 := fun n => match n with
    | 0 => 1
    | k + 1 => k
}

def projTest := mkComplex.field2 5

-- Test 8: Try to create definitional equality confusion
-- If we can make two different terms reduce to the same normal form incorrectly,
-- we might be able to prove False

axiom magic : 0 = 1

-- Can we hide this behind complex reduction?
def hidden : Nat :=
  let x := 0
  let y := 1
  if x == y then 999 else 0

-- If reducer has bugs, this might not be detected
-- #check (hidden : 0 = 1)  -- This should fail

-- Test 9: Dependent eliminator reduction
inductive Singleton : Nat → Type where
  | mk : Singleton 42

def elimSingleton {α : Type} (f : (n : Nat) → α) : Singleton 42 → α
  | .mk => f 42

-- Test reduction of dependent elimination
def singTest := elimSingleton (fun n => n + 1) .mk

-- Test 10: Quotient reduction (these are axioms but their reduction behavior matters)
-- This is sensitive - quotient types are primitive

-- Try to observe reduction behavior
def quotTest : Quot (α := Nat) (fun _ _ => True) := Quot.mk _ 42
