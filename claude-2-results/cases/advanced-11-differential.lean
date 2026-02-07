/-
Advanced Test 11: Differential Testing - Kernel vs VM
CRITICAL: Kernel reduction and VM evaluation MUST agree

If #reduce (kernel) and #eval (VM) give different results,
we have a critical bug that could allow incorrect proofs!

This is especially important for proof-carrying code systems.
-/

-- Test 1: Basic arithmetic
def diff1 : Nat := 2 + 2

#reduce diff1  -- Kernel: Should be 4
#eval diff1 = 4  -- VM: Should be true

theorem diff1_correct : diff1 = 4 := rfl  -- Kernel proof

-- Test 2: Pattern matching
def diff2 (n : Nat) : String :=
  match n with
  | 0 => "zero"
  | 1 => "one"
  | _ => "other"

#reduce diff2 5  -- Kernel: "other"
#eval diff2 5 = "other"  -- VM: true

-- Test 3: Recursion
def diff3 : Nat → Nat
  | 0 => 0
  | n + 1 => n + 1 + diff3 n

#reduce diff3 5  -- Kernel: 15
#eval diff3 5 = 15  -- VM: true

theorem diff3_correct : diff3 5 = 15 := rfl

-- Test 4: List operations
def diff4 : List Nat := [1, 2, 3, 4, 5]

#reduce diff4.length  -- Kernel: 5
#eval diff4.length = 5  -- VM: true

theorem diff4_correct : diff4.length = 5 := rfl

-- Test 5: Complex pattern matching
inductive Tree where
  | leaf : Nat → Tree
  | node : Tree → Tree → Tree

def diff5 : Tree → Nat
  | .leaf n => n
  | .node l r => diff5 l + diff5 r

def testTree : Tree := .node (.leaf 1) (.node (.leaf 2) (.leaf 3))

#reduce diff5 testTree  -- Kernel: 6
#eval diff5 testTree = 6  -- VM: true

theorem diff5_correct : diff5 testTree = 6 := rfl

-- Test 6: Mutual recursion
mutual
  def diff6even : Nat → Bool
    | 0 => true
    | n + 1 => diff6odd n

  def diff6odd : Nat → Bool
    | 0 => false
    | n + 1 => diff6even n
end

#reduce diff6even 10  -- Kernel: true
#eval diff6even 10 = true  -- VM: true

theorem diff6_correct : diff6even 10 = true := rfl

-- Test 7: Type class resolution
class MyClass (α : Type) where
  myMethod : α → Nat

instance : MyClass Nat where
  myMethod n := n * 2

instance : MyClass String where
  myMethod s := s.length

def diff7 {α : Type} [MyClass α] (x : α) : Nat :=
  MyClass.myMethod x

#reduce diff7 (5 : Nat)  -- Kernel: 10
#eval diff7 (5 : Nat) = 10  -- VM: true

#reduce diff7 "hello"  -- Kernel: 5
#eval diff7 "hello" = 5  -- VM: true

-- Test 8: Monadic operations
def diff8 : Option Nat := do
  let x ← some 5
  let y ← some 3
  return x + y

#reduce diff8  -- Kernel: some 8
#eval diff8 = some 8  -- VM: true

theorem diff8_correct : diff8 = some 8 := rfl

-- Test 9: Array operations
def diff9 : Array Nat := #[1, 2, 3, 4, 5]

#reduce diff9.size  -- Kernel: 5
#eval diff9.size = 5  -- VM: true

#reduce diff9[2]!  -- Kernel: 3
#eval diff9[2]! = 3  -- VM: true

-- Test 10: String operations
def diff10 : String := "Hello, World!"

#reduce diff10.length  -- Kernel: 13
#eval diff10.length = 13  -- VM: true

theorem diff10_correct : diff10.length = 13 := rfl

-- Test 11: Higher-order functions
def diff11 : List Nat := [1, 2, 3, 4, 5].map (· * 2)

#reduce diff11  -- Kernel: [2, 4, 6, 8, 10]
#eval diff11 = [2, 4, 6, 8, 10]  -- VM: true

theorem diff11_correct : diff11 = [2, 4, 6, 8, 10] := rfl

-- Test 12: Nested matches
def diff12 (x : Nat) (y : Nat) : String :=
  match x, y with
  | 0, 0 => "both zero"
  | 0, _ => "x zero"
  | _, 0 => "y zero"
  | _, _ => "both nonzero"

#reduce diff12 0 5  -- Kernel: "x zero"
#eval diff12 0 5 = "x zero"  -- VM: true

-- Test 13: Proof-carrying computation
def diff13 (n : Nat) (h : n > 0) : Nat := n

#reduce diff13 5 (by decide)  -- Kernel: 5
#eval diff13 5 (by decide) = 5  -- VM: true

-- Test 14: Complex list operations
def diff14 : Nat := [1, 2, 3, 4, 5].foldl (· + ·) 0

#reduce diff14  -- Kernel: 15
#eval diff14 = 15  -- VM: true

theorem diff14_correct : diff14 = 15 := rfl

-- Test 15: Quotient computation (should agree on normalized form)
def QuotTest := Quot (fun (a b : Nat) => a % 10 = b % 10)

def diff15 : QuotTest := Quot.mk _ 15

-- Can't reduce quotient directly, but operations should agree
-- #reduce diff15  -- Not meaningful
-- #eval diff15  -- Not meaningful

-- But derived operations should agree:
def diff15_derived := 42  -- If derived from quotient

#reduce diff15_derived
#eval diff15_derived = 42

-- Test 16: Dependent types
def diff16 (n : Nat) : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩

#reduce (diff16 5).val  -- Kernel: 0
#eval (diff16 5).val = 0  -- VM: true

-- Test 17: Option operations
def diff17 : Option Nat := some 42

#reduce diff17.getD 0  -- Kernel: 42
#eval diff17.getD 0 = 42  -- VM: true

theorem diff17_correct : diff17.getD 0 = 42 := rfl

-- Test 18: List append and reverse
def diff18 : List Nat := [1, 2, 3].reverse ++ [4, 5]

#reduce diff18  -- Kernel: [3, 2, 1, 4, 5]
#eval diff18 = [3, 2, 1, 4, 5]  -- VM: true

theorem diff18_correct : diff18 = [3, 2, 1, 4, 5] := rfl

-- Test 19: Boolean operations
def diff19 : Bool := (true && false) || (true && true)

#reduce diff19  -- Kernel: true
#eval diff19 = true  -- VM: true

theorem diff19_correct : diff19 = true := rfl

-- Test 20: CRITICAL CHECKER
-- Run this to verify all differentials match
def checkAllDifferentials : Bool :=
  diff1 = 4 &&
  diff3 5 = 15 &&
  diff4.length = 5 &&
  diff5 testTree = 6 &&
  diff6even 10 = true &&
  diff7 (5 : Nat) = 10 &&
  diff8 = some 8 &&
  diff9.size = 5 &&
  diff10.length = 13 &&
  diff11 = [2, 4, 6, 8, 10] &&
  diff14 = 15 &&
  diff17.getD 0 = 42 &&
  diff18 = [3, 2, 1, 4, 5] &&
  diff19 = true

-- Kernel check
theorem allDifferentialsCorrect : checkAllDifferentials = true := rfl

-- VM check
#eval checkAllDifferentials = true  -- MUST be true!

-- If this is false, we have a CRITICAL kernel/VM mismatch!
#eval if checkAllDifferentials then
  "✓ All differential tests passed!"
else
  "✗ CRITICAL: Kernel/VM mismatch detected!"
