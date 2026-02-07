/-
Case: resource-1-stack-overflow
Category: Resource Exhaustion / Implementation Security
Severity: MEDIUM-HIGH

Test: Stack overflow through deep recursion/nesting
Goal: Identify stack overflow vulnerabilities that could cause crashes

Attack vectors:
- Deeply nested type expressions
- Deep pattern matching
- Chain of function applications
- Recursive type definitions
-/

-- Test 1: Deeply nested function application
-- This creates a very deep call stack
def deepApply (n : Nat) : Nat → Nat :=
  match n with
  | 0 => id
  | n + 1 => fun x => deepApply n (deepApply n x)

#eval deepApply 10 42  -- Should work
-- #eval deepApply 20 42  -- Might cause stack issues

-- Test 2: Deeply nested type
def NestedType : Nat → Type
  | 0 => Nat
  | n + 1 => NestedType n × NestedType n

-- Test 3: Deep pattern match chain
def deepMatch (n : Nat) (x : Nat) : Nat :=
  match n with
  | 0 => x
  | 1 => match x with
         | 0 => 0
         | _ => deepMatch 0 (x - 1)
  | _ => deepMatch (n - 1) x

-- Test 4: Large tuple nesting
def largeTuple : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat := 
  (0, 1, 2, 3, 4, 5, 6, 7)

-- Test 5: Attempt to create pathologically deep term
-- by using macros or tactics to generate deep structure