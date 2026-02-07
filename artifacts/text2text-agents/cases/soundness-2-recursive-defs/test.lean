/-
Case: soundness-2-recursive-defs
Category: Kernel Soundness
Severity: CRITICAL if exploitable

Test: Non-terminating recursion and partial functions
Goal: Attempt to exploit recursion to derive False

Known issues:
- Non-terminating recursion can break soundness
- Partial functions violating totality
- Mutual recursion bugs
-/

-- Test 1: Attempt non-structural recursion without proof of termination
-- This should be rejected
partial def loop : Nat → Nat :=
  fun n => loop n

-- Test 2: Use partial to create contradiction?
-- partial is unsafe, but shouldn't allow deriving False in kernel
partial def partialFalse : False :=
  partialFalse

-- This shouldn't work because partial doesn't exist at kernel level

-- Test 3: Nested recursion edge case
def nested (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => nested (nested n)

-- Test 4: Mutual recursion
mutual
  def evenNat : Nat → Bool
    | 0 => true
    | n + 1 => oddNat n
  
  def oddNat : Nat → Bool
    | 0 => false
    | n + 1 => evenNat n
end

-- Test 5: Attempt to use well-founded recursion incorrectly
-- def badWF (n : Nat) : Nat :=
--   have : n < n := sorry  -- If we could prove this, we'd have False
--   badWF n