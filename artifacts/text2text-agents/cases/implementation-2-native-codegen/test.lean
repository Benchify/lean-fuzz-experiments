/-
Case: implementation-2-native-codegen
Category: Code Generation & Compilation
Severity: HIGH (miscompilation, UB)

Test: Native code generation for potential UB or correctness issues
-/

-- Test 1: Integer overflow
def largeCalc : Nat := 999999999999999999 * 999999999999999999

#eval largeCalc  -- Check if this overflows or is handled correctly

-- Test 2: Division by zero (should be caught)
-- def divZero : Nat := 10 / 0  -- This should error

-- Test 3: Array bounds
def testArray : Array Nat := #[1, 2, 3]
def getElement (i : Nat) : Nat := testArray[i]!

#eval getElement 0  -- Valid
-- #eval getElement 10  -- Out of bounds - should panic

-- Test 4: Recursive call optimization
def tailRecTest : Nat → Nat → Nat
  | 0, acc => acc
  | n+1, acc => tailRecTest n (acc + n)

#eval tailRecTest 1000 0  -- Should not stack overflow

-- Test 5: Pattern matching compilation
def complexMatch (x : Nat) (y : Nat) : Nat :=
  match x, y with
  | 0, 0 => 0
  | 0, _ => 1
  | _, 0 => 2
  | n, m => n + m

#eval complexMatch 5 3

-- Test 6: String operations
def strTest : String := "test" ++ "ing"
#eval strTest.length