/-
Case: soundness-1-universe-poly
Category: Kernel Soundness
Severity: CRITICAL if exploitable

Test: Universe polymorphism edge cases
-/

universe u v

-- Test 1: Universe level mismatch (should fail)
-- def universeTest1 : Type u → Type v := fun x => x

-- Test 2: Impredicativity test
def propTest : (α : Type u) → (α → Prop) → Prop := 
  fun α p => ∀ x : α, p x

-- Test 3: Large elimination from Prop
inductive MyFalse : Prop where

def falseElim {α : Type u} : MyFalse → α := 
  fun h => MyFalse.rec (motive := fun _ => α) h

#check falseElim