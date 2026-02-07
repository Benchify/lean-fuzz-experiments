/-
Advanced Test 7: Compiler Backend and Code Generation Exploits
Attempting to find miscompilation bugs that could compute False

The Lean compiler has several backends:
- Bytecode interpreter/VM
- C code generation
- LLVM backend (future)

Even with a sound kernel, miscompilation could:
- Cause VM to produce wrong results
- Make #eval disagree with #reduce (kernel reduction)
- Allow execution of "impossible" code paths

This is critical for proof-carrying code systems!
-/

-- Test 1: Integer overflow (Nat should use bigints)
def bigNat : Nat := 2^1000

#eval bigNat  -- Should handle large numbers correctly

-- Test 2: Array bounds checking
def arrayBounds : IO Unit := do
  let arr : Array Nat := #[1, 2, 3]
  -- This should panic at runtime, not UB:
  -- let x := arr[10]!  -- Out of bounds
  return ()

-- Test 3: Pattern matching compilation
-- Ensure compiled patterns match kernel semantics
def patternTest (n : Nat) : String :=
  match n with
  | 0 => "zero"
  | 1 => "one"
  | _ => "other"

-- Kernel reduction:
#reduce patternTest 0
-- VM evaluation:
#eval patternTest 0
-- These MUST agree!

-- Test 4: Recursion and tail call optimization
-- Incorrect TCO could cause stack overflow or wrong results
def tailRecTest (n : Nat) (acc : Nat := 0) : Nat :=
  match n with
  | 0 => acc
  | n + 1 => tailRecTest n (acc + 1)

#eval tailRecTest 10000  -- Should not stack overflow

-- Test 5: Mutual recursion compilation
mutual
  def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n

  def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

-- Do kernel and VM agree?
#reduce isEven 100
#eval isEven 100

-- Test 6: Closure compilation
-- Closures capture environment - can this be exploited?
def makeClosure (x : Nat) : Nat → Nat :=
  fun y => x + y

def closureTest := makeClosure 42

#eval closureTest 8  -- Should be 50

-- Test 7: Type class dictionary passing
-- Type class instances compiled to dictionaries
-- Any bugs in passing/lookup?
class MyAdd (α : Type) where
  myAdd : α → α → α

instance : MyAdd Nat where
  myAdd := Nat.add

def useTypeClass {α : Type} [MyAdd α] (x y : α) : α :=
  MyAdd.myAdd x y

#eval useTypeClass 3 4  -- Should be 7

-- Test 8: Nested pattern matching
-- Complex patterns could have compilation bugs
def nestedPatternCompile : List (List Nat) → Nat
  | [] => 0
  | [] :: rest => nestedPatternCompile rest
  | (x :: xs) :: rest => x + nestedPatternCompile (xs :: rest)

#eval nestedPatternCompile [[1,2], [3,4]]  -- Should be 10

-- Test 9: Lazy evaluation
-- Lean uses lazy thunks for some computations
def lazyTest : Nat :=
  let x := 42
  let y := x + 1  -- May be compiled as thunk
  y

#eval lazyTest  -- Should force thunk correctly

-- Test 10: FFI boundary
-- C FFI could have type confusion bugs
@[extern "lean_nat_add"]
opaque extAdd : Nat → Nat → Nat

-- Does this match Lean's Nat.add semantics?
-- #eval extAdd 5 7  -- Should be 12

-- Test 11: Reference counting
-- Lean uses RC memory management
-- RC bugs could cause UAF or double-free
def rcTest : IO Unit := do
  let arr := #[1, 2, 3]
  let arr2 := arr  -- Should inc refcount
  -- When arr goes out of scope, arr2 should still be valid
  IO.println s!"{arr2}"

-- Test 12: Unsafe cast in compiled code
-- Even though kernel rejects, compiled code might allow?
-- unsafe def unsafeCastTest : Bool :=
--   unsafeCast (42 : Nat)

-- Test 13: Stack vs heap allocation
-- Large values should be heap-allocated
def largeValue : Array Nat :=
  Array.range 1000000

-- Should not stack overflow
-- #eval largeValue.size

-- Test 14: Proof erasure
-- Proofs should be erased in compiled code
-- But erasure bugs could affect values
def proofErasureTest (h : 1 = 1) : Nat :=
  42  -- h should be erased, not affect result

#eval proofErasureTest rfl  -- Should be 42

-- Test 15: IO and effects
-- IO effects must execute in correct order
def ioOrderTest : IO Unit := do
  IO.println "First"
  IO.println "Second"
  IO.println "Third"

-- Test 16: Panic handling
-- Panics should be safe (no UB)
def panicTest : Nat :=
  if false then
    42
  else
    panic! "This should panic safely"

-- #eval panicTest  -- Should panic cleanly

-- Test 17: String handling
-- Strings are UTF-8, bugs could cause issues
def stringTest : String :=
  "Hello, 世界! 🔥"

#eval stringTest.length  -- Should count Unicode correctly

-- Test 18: Float operations (if enabled)
-- Floating point could have precision bugs
def floatTest : Float :=
  0.1 + 0.2

-- Test 19: Monadic compilation
-- do-notation compiles to bind chains
def monadTest : Option Nat := do
  let x ← some 5
  let y ← some 3
  return x + y

#eval monadTest  -- Should be some 8

-- Test 20: CRITICAL - Differential testing oracle
-- The kernel reduction and VM evaluation MUST agree!
def diffTest1 : Nat := (fun x => x + 1) 41
theorem kernelVersion : diffTest1 = 42 := rfl
#eval diffTest1 = 42  -- VM version, must match!

-- If these disagree, we have a critical bug!
def diffTest2 : List Nat := [1, 2, 3]
theorem kernelList : diffTest2.length = 3 := rfl
#eval diffTest2.length = 3  -- Must be true!

-- Test 21: Stack overflow defense
-- Deeply nested calls should be handled
def deepRecursion (n : Nat) : Nat :=
  if n = 0 then 0
  else 1 + deepRecursion (n - 1)

-- #eval deepRecursion 100000  -- Should not crash (may be slow)

#check bigNat
#check patternTest
#check tailRecTest
#check closureTest
#check monadTest
