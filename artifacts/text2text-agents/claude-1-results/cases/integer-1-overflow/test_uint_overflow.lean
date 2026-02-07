-- Test integer overflow behaviors in Lean's fixed-width integers
-- Goal: Find discrepancies between VM and kernel, or memory corruption

-- Test 1: UInt8 overflow
def test_uint8_overflow : IO Unit := do
  IO.println "\n=== UInt8 Overflow Test ==="
  let max : UInt8 := 255
  let overflowed := max + 1
  IO.println s!"255 + 1 = {overflowed} (expected: 0 with wrapping)"

  let underflow : UInt8 := 0
  let underflowed := underflow - 1
  IO.println s!"0 - 1 = {underflowed} (expected: 255 with wrapping)"

-- Test 2: UInt64 overflow
def test_uint64_overflow : IO Unit := do
  IO.println "\n=== UInt64 Overflow Test ==="
  let max : UInt64 := 0xFFFFFFFFFFFFFFFF
  let overflowed := max + 1
  IO.println s!"UInt64.max + 1 = {overflowed}"

  -- Test multiplication overflow
  let big : UInt64 := 0x8000000000000000
  let doubled := big * 2
  IO.println s!"2^63 * 2 = {doubled}"

-- Test 3: Shift overflow
def test_shift_overflow : IO Unit := do
  IO.println "\n=== Shift Overflow Test ==="
  let n : UInt64 := 1
  -- Shift by more than bit width
  let shifted := n <<< 128
  IO.println s!"1 <<< 128 = {shifted}"

  let shifted2 := n <<< 65
  IO.println s!"1 <<< 65 = {shifted2}"

-- Test 4: Division by zero
def test_div_zero : IO Unit := do
  IO.println "\n=== Division by Zero Test ==="
  try
    let n : UInt64 := 42
    let result := n / 0
    IO.println s!"42 / 0 = {result} (SHOULD HAVE CRASHED!)"
  catch e =>
    IO.println s!"Caught exception: {e}"

-- Test 5: Array index with overflowed integer
def test_array_overflow_index : IO Unit := do
  IO.println "\n=== Array Index Overflow Test ==="
  let arr : Array Nat := #[1, 2, 3, 4, 5]

  -- Create overflowed index
  let idx : UInt64 := 0xFFFFFFFFFFFFFFFF
  let idx_nat := idx.toNat

  IO.println s!"Overflowed index as Nat: {idx_nat}"

  try
    let elem := arr[idx_nat]!
    IO.println s!"Array element at overflow index: {elem}"
  catch e =>
    IO.println s!"Caught: {e}"

-- Test 6: Negative size for array operations
def test_negative_size : IO Unit := do
  IO.println "\n=== Negative Size Test ==="
  let size : Int := -10

  try
    -- Try to create array with "negative" size
    let arr := Array.mkArray size.toNat 0
    IO.println s!"Created array with negative size? Length: {arr.size}"
  catch e =>
    IO.println s!"Caught: {e}"

-- Test 7: Integer type confusion via computation
def test_type_confusion : IO Unit := do
  IO.println "\n=== Type Confusion via Cast Test ==="

  -- Cast large UInt64 to smaller types
  let large : UInt64 := 0xDEADBEEFCAFEBABE
  let as_u32 : UInt32 := large.toUInt32
  let as_u16 : UInt16 := large.toUInt16
  let as_u8 : UInt8 := large.toUInt8

  IO.println s!"0xDEADBEEFCAFEBABE as UInt32: {as_u32}"
  IO.println s!"0xDEADBEEFCAFEBABE as UInt16: {as_u16}"
  IO.println s!"0xDEADBEEFCAFEBABE as UInt8: {as_u8}"

-- Test 8: Comparison after overflow
def test_comparison_after_overflow : IO Unit := do
  IO.println "\n=== Comparison After Overflow Test ==="

  let max : UInt8 := 255
  let overflowed := max + 1  -- Should wrap to 0

  if overflowed > max then
    IO.println "BUG: 0 > 255 (unsigned comparison broken!)"
  else if overflowed < max then
    IO.println "Correct: 0 < 255"
  else
    IO.println "BUG: 0 == 255"

def main : IO Unit := do
  test_uint8_overflow
  test_uint64_overflow
  test_shift_overflow
  test_div_zero
  test_array_overflow_index
  test_negative_size
  test_type_confusion
  test_comparison_after_overflow

  IO.println "\n=== All integer tests completed ==="
