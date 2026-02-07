/-
Attack Vector: VM Integer Overflow and Native Type Exploits
Target: Lean VM bytecode interpreter and native types
Severity: CRITICAL if exploitable

Lean 4 has native support for fixed-width integers (UInt8, UInt16, UInt32, UInt64)
and arbitrary precision Nat. The VM implementation might have:
- Integer overflow bugs
- Type confusion between Nat and fixed-width integers
- Array bounds checking failures
- String buffer overflows
-/

-- Test 1: UInt overflow behavior
def maxUInt64 : UInt64 := UInt64.ofNat ((2^64) - 1)

-- Does overflow wrap around or cause UB?
def overflowTest : UInt64 := maxUInt64 + 1

#eval overflowTest  -- Should this wrap to 0 or error?

-- Test 2: Underflow
def underflowTest : UInt64 := 0 - 1

#eval underflowTest

-- Test 3: Type confusion between Nat and UInt
-- Nat is arbitrary precision, UInt is fixed-width
def confusedType : UInt64 := UInt64.ofNat (2^100)  -- Way bigger than 2^64

#eval confusedType  -- What happens?

-- Test 4: Array bounds checking in VM
def arrayTest : Array Nat := #[1, 2, 3]

-- These should be checked, but are they in VM?
-- #eval arrayTest[100]  -- Out of bounds
-- #eval arrayTest[-1]   -- Negative index

-- Test 5: String operations
def largeString : String := String.mk (List.replicate 10000000 'a')

-- Can we cause buffer overflow?
-- #eval largeString.length

-- Test 6: Bit operations edge cases
def bitTest1 : UInt64 := 1 <<< 64  -- Shift by full width
def bitTest2 : UInt64 := 1 <<< 100 -- Shift by more than width

#eval bitTest1
#eval bitTest2

-- Test 7: Division by zero
-- def divZero : UInt64 := 42 / 0  -- Should error, not UB

-- Test 8: Mixing signed and unsigned
def mixedTest : Int := -1
def asUnsigned : UInt64 := mixedTest.toNat.toUInt64

#eval asUnsigned

-- Test 9: Float operations
def floatTest1 : Float := Float.ofNat (2^1024)  -- Infinity?
def floatTest2 : Float := 0.0 / 0.0             -- NaN?
def floatTest3 : Float := 1.0 / 0.0             -- Inf?

#eval floatTest1
#eval floatTest2
#eval floatTest3

-- Test 10: ByteArray operations
def byteArrayTest : ByteArray := ByteArray.mk #[0, 1, 2, 3]

-- #eval byteArrayTest.get! 1000  -- Out of bounds

-- Test 11: Recursive structure size
inductive InfiniteStruct where
  | node : List InfiniteStruct → InfiniteStruct

-- Can we create structures that overflow size calculations?

-- Test 12: Char boundaries
def charTest1 : Char := Char.ofNat 0x110000  -- Beyond Unicode range

#eval charTest1

-- Test 13: Integer multiplication overflow
def mulOverflow : UInt64 := maxUInt64 * maxUInt64

#eval mulOverflow

-- Test 14: Exponentation
def expOverflow : Nat := 2 ^ (2 ^ 30)  -- Huge exponent

-- #eval expOverflow  -- Will this OOM or handle gracefully?

-- Test 15: Comparing Nat with native integers
axiom natVsUInt : (n : Nat) → (u : UInt64) → n.toUInt64 == u

-- Can we create inconsistency in comparison?
