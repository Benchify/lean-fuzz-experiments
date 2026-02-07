/-
Case: soundness-3-inductive-types
Category: Kernel Soundness
Severity: CRITICAL if exploitable

Test: Inductive type soundness
Goal: Test for bugs in inductive type formation and elimination

Known issues:
- Strict positivity violations
- Non-positive occurrences
- Self-referential types
- Large elimination from Prop bugs
-/

-- Test 1: Attempt to create non-strictly-positive type
-- This should be rejected
-- inductive Bad : Type where
--   | mk : (Bad → Nat) → Bad

-- Test 2: Nested inductive with potential issues
inductive Tree (α : Type) : Type where
  | leaf : α → Tree α
  | node : List (Tree α) → Tree α

-- Test 3: Mutual inductive types
mutual
  inductive Even : Nat → Prop where
    | zero : Even 0
    | succ : ∀ n, Odd n → Even (n + 1)
  
  inductive Odd : Nat → Prop where
    | succ : ∀ n, Even n → Odd (n + 1)
end

-- Test 4: Large elimination edge case
inductive SmallType : Prop where
  | intro : Nat → SmallType

-- Can we extract the Nat? This should fail or require special handling
-- def extract : SmallType → Nat
--   | SmallType.intro n => n

-- Test 5: Indexed families
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n + 1)

-- Test 6: Attempt reflexive type
-- inductive Reflexive : Type where
--   | mk : Reflexive → Reflexive  -- Should be rejected