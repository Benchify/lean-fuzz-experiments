/-
Case: differential-1-vm-kernel
Category: Differential Testing
Severity: HIGH (miscompilation, UB)

Test: Differential testing between kernel evaluation and VM
Goal: Find discrepancies that could indicate bugs
-/

-- Test 1: Basic computation
def comp1 : Nat := 2 + 2

#eval comp1  -- VM
#reduce comp1  -- Kernel

-- Test 2: Recursion
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

#eval fib 10
#reduce fib 10

-- Test 3: Pattern matching edge cases
def patternTest (x : Option Nat) : Nat :=
  match x with
  | none => 0
  | some n => n + 1

#eval patternTest (some 41)
#reduce patternTest (some 41)

-- Test 4: Mutual recursion
mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n
  
  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

#eval isEven 100
#reduce isEven 4  -- Keep small for kernel

-- Test 5: List operations
def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

#eval sumList [1, 2, 3, 4, 5]
#reduce sumList [1, 2, 3, 4, 5]