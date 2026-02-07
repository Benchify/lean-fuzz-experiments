/-
Simplified Native Compiler Differential Testing
Comparing VM execution with compiled binary execution
-/

-- Test 1: Basic Arithmetic
def test1 : IO Unit := do
  let result := 1000000 + 2000000
  IO.println s!"test1: {result}"

-- Test 2: Integer Overflow
def test2 : IO Unit := do
  let max : UInt64 := UInt64.ofNat ((2^64) - 1)
  let overflow := max + 1
  IO.println s!"test2: {overflow}"

-- Test 3: Pattern Matching
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

def tree_sum : Tree Nat → Nat
  | Tree.leaf n => n
  | Tree.node l r => tree_sum l + tree_sum r

def test3 : IO Unit := do
  let tree := Tree.node (Tree.leaf 1) (Tree.leaf 2)
  let result := tree_sum tree
  IO.println s!"test3: {result}"

-- Test 4: Recursion
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def test4 : IO Unit := do
  let result := factorial 10
  IO.println s!"test4: {result}"

-- Test 5: Arrays
def test5 : IO Unit := do
  let arr := #[1, 2, 3, 4, 5]
  let sum := arr.foldl (· + ·) 0
  IO.println s!"test5: {sum}"

-- Test 6: Strings
def test6 : IO Unit := do
  let s1 := "Hello"
  let s2 := "World"
  let concat := s1 ++ " " ++ s2
  IO.println s!"test6: {concat}"

-- Test 7: Option Types
def safe_div (a b : Nat) : Option Nat :=
  if b = 0 then none else some (a / b)

def test7 : IO Unit := do
  match safe_div 10 2 with
  | none => IO.println "test7: none"
  | some v => IO.println s!"test7: {v}"

-- Test 8: Higher-Order Functions
def apply_twice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

def test8 : IO Unit := do
  let double := fun x => x * 2
  let result := apply_twice double 5
  IO.println s!"test8: {result}"

-- Test 9: Floating Point
def test9 : IO Unit := do
  let a : Float := 3.14159
  let b : Float := 2.71828
  let result := a + b
  IO.println s!"test9: {result}"

-- Test 10: Bit Operations
def test10 : IO Unit := do
  let a : UInt64 := 0xFF00FF00
  let b : UInt64 := 0x00FF00FF
  let result := a &&& b
  IO.println s!"test10: {result}"

-- Test 11: Loop
def loop_sum (n : Nat) : Nat :=
  let rec aux (i acc : Nat) :=
    if i >= n then acc
    else aux (i + 1) (acc + i)
  aux 0 0

def test11 : IO Unit := do
  let result := loop_sum 1000
  IO.println s!"test11: {result}"

-- Test 12: Mutual Recursion
mutual
  def even : Nat → Bool
    | 0 => true
    | n + 1 => odd n

  def odd : Nat → Bool
    | 0 => false
    | n + 1 => even n
end

def test12 : IO Unit := do
  let result := even 100
  IO.println s!"test12: {result}"

-- Test 13: List Operations
def test13 : IO Unit := do
  let list := [1, 2, 3, 4, 5]
  let doubled := list.map (· * 2)
  let sum := doubled.foldl (· + ·) 0
  IO.println s!"test13: {sum}"

-- Test 14: ByteArray
def test14 : IO Unit := do
  let ba := ByteArray.mk #[1, 2, 3, 4, 5]
  let sum := ba.data.foldl (fun acc b => acc + b.toNat) 0
  IO.println s!"test14: {sum}"

-- Test 15: Large Numbers
def test15 : IO Unit := do
  let result := (123456789 : Nat) * (987654321 : Nat)
  IO.println s!"test15: {result}"

-- Main test runner
def main : IO Unit := do
  IO.println "╔════════════════════════════════════════╗"
  IO.println "║  Native Compiler Differential Test    ║"
  IO.println "╚════════════════════════════════════════╝"
  IO.println ""

  test1
  test2
  test3
  test4
  test5
  test6
  test7
  test8
  test9
  test10
  test11
  test12
  test13
  test14
  test15

  IO.println ""
  IO.println "All tests complete!"

#eval main
