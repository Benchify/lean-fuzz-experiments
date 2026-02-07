/-
DIFFERENTIAL SOUNDNESS TESTING
Strategy: Create two different ways to compute the same thing
If they give different results, we have a bug

This tests:
- Reducer consistency
- VM vs kernel consistency
- Elaborator consistency
- Code generation correctness
-/

-- Test 1: VM vs Kernel execution
-- The VM executes code, kernel type-checks it
-- They should agree

def vmTest1 : Nat := 2 + 2
#eval vmTest1  -- VM execution

#check (vmTest1 : Nat)  -- Kernel check

-- If these disagree, bug!

-- Test 2: Multiple evaluation paths
def multiPath (n : Nat) : Nat :=
  if n == 0 then
    0
  else if n == 1 then
    1
  else
    n

#eval multiPath 0  -- Should be 0
#eval multiPath 1  -- Should be 1
#eval multiPath 5  -- Should be 5

-- Test via reduction:
example : multiPath 0 = 0 := rfl
example : multiPath 1 = 1 := rfl
-- example : multiPath 5 = 5 := rfl  -- Won't work (if doesn't reduce)

-- Test 3: Recursive function consistency
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

-- VM execution:
#eval fib 10

-- Kernel reduction (for small values):
example : fib 5 = 5 := rfl

-- Test 4: Mutual recursion consistency
mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n

  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

#eval isEven 10  -- VM
example : isEven 10 = true := rfl  -- Kernel

-- Test 5: Structure projection consistency
structure Point where
  x : Nat
  y : Nat
  z : Nat

def p : Point := ⟨1, 2, 3⟩

#eval p.x  -- VM
#eval p.y  -- VM
#eval p.z  -- VM

example : p.x = 1 := rfl  -- Kernel
example : p.y = 2 := rfl  -- Kernel
example : p.z = 3 := rfl  -- Kernel

-- Test 6: Pattern matching compilation
def matchTest (n : Nat) : Nat :=
  match n with
  | 0 => 100
  | 1 => 200
  | 2 => 300
  | _ => 999

#eval matchTest 0  -- Should be 100
#eval matchTest 1  -- Should be 200
#eval matchTest 2  -- Should be 300
#eval matchTest 5  -- Should be 999

example : matchTest 0 = 100 := rfl
example : matchTest 1 = 200 := rfl
example : matchTest 2 = 300 := rfl

-- Test 7: Array operations
def arrayTest : Array Nat := #[1, 2, 3, 4, 5]

#eval arrayTest.size  -- VM: 5
#eval arrayTest[0]!  -- VM: 1
#eval arrayTest[4]!  -- VM: 5

-- Test 8: String operations
def stringTest : String := "Hello"

#eval stringTest.length  -- VM: 5
#eval stringTest.toList  -- VM: ['H', 'e', 'l', 'l', 'o']

-- Test 9: Integer arithmetic
def intTest1 : Int := -5 + 10
def intTest2 : Int := 5 - 10
def intTest3 : Int := -5 * -5

#eval intTest1  -- 5
#eval intTest2  -- -5
#eval intTest3  -- 25

example : intTest1 = 5 := rfl
example : intTest2 = -5 := rfl
example : intTest3 = 25 := rfl

-- Test 10: Nat subtraction (saturating)
def natSub1 : Nat := 10 - 5
def natSub2 : Nat := 5 - 10  -- Should saturate to 0

#eval natSub1  -- 5
#eval natSub2  -- 0

example : natSub1 = 5 := rfl
example : natSub2 = 0 := rfl

-- Test 11: Division
def divTest1 : Nat := 10 / 2
def divTest2 : Nat := 10 / 3
def divTest3 : Nat := 10 / 0  -- Division by zero

#eval divTest1  -- 5
#eval divTest2  -- 3
#eval divTest3  -- Should be 0 (defined behavior)

example : divTest1 = 5 := rfl
example : divTest2 = 3 := rfl
example : divTest3 = 0 := rfl

-- Test 12: Let bindings
def letTest1 : Nat :=
  let x := 5
  let y := x + 3
  let z := y * 2
  z - x

#eval letTest1  -- (5+3)*2 - 5 = 16 - 5 = 11

example : letTest1 = 11 := rfl

-- Test 13: Nested matches
def nestedMatch (n m : Nat) : Nat :=
  match n with
  | 0 => match m with
    | 0 => 1
    | _ => 2
  | _ => match m with
    | 0 => 3
    | _ => 4

#eval nestedMatch 0 0  -- 1
#eval nestedMatch 0 1  -- 2
#eval nestedMatch 1 0  -- 3
#eval nestedMatch 1 1  -- 4

example : nestedMatch 0 0 = 1 := rfl
example : nestedMatch 0 1 = 2 := rfl
example : nestedMatch 1 0 = 3 := rfl
example : nestedMatch 1 1 = 4 := rfl

-- Test 14: List operations
def listTest : List Nat := [1, 2, 3, 4, 5]

#eval listTest.length  -- 5
#eval listTest.head?  -- some 1
#eval listTest.tail?  -- some [2,3,4,5]

-- Test 15: Option operations
def optTest1 : Option Nat := some 42
def optTest2 : Option Nat := none

#eval optTest1.isSome  -- true
#eval optTest2.isSome  -- false
#eval optTest1.getD 0  -- 42
#eval optTest2.getD 0  -- 0

-- Test 16: Bool operations
def boolTest1 : Bool := true && false
def boolTest2 : Bool := true || false
def boolTest3 : Bool := !true

#eval boolTest1  -- false
#eval boolTest2  -- true
#eval boolTest3  -- false

example : boolTest1 = false := rfl
example : boolTest2 = true := rfl
example : boolTest3 = false := rfl

-- Test 17: Comparison operations
def cmpTest1 : Bool := 5 < 10
def cmpTest2 : Bool := 10 < 5
def cmpTest3 : Bool := 5 == 5
def cmpTest4 : Bool := 5 != 10

#eval cmpTest1  -- true
#eval cmpTest2  -- false
#eval cmpTest3  -- true
#eval cmpTest4  -- true

example : cmpTest1 = true := rfl
example : cmpTest2 = false := rfl
example : cmpTest3 = true := rfl
example : cmpTest4 = true := rfl

-- Test 18: Decidable propositions
def decTest1 : Bool := decide (5 < 10)
def decTest2 : Bool := decide (10 < 5)

#eval decTest1  -- true
#eval decTest2  -- false

example : decTest1 = true := rfl
example : decTest2 = false := rfl

-- If any of these tests show VM vs Kernel disagreement, CRITICAL BUG!
