-- Test integer overflow behaviors

def test_uint8_overflow : IO Unit := do
  IO.println "\n=== UInt8 Overflow Test ==="
  let max : UInt8 := 255
  let overflowed := max + 1
  IO.println s!"255 + 1 = {overflowed}"

  let underflow : UInt8 := 0
  let underflowed := underflow - 1
  IO.println s!"0 - 1 = {underflowed}"

def test_uint64_overflow : IO Unit := do
  IO.println "\n=== UInt64 Overflow Test ==="
  let max : UInt64 := 0xFFFFFFFFFFFFFFFF
  let overflowed := max + 1
  IO.println s!"UInt64.max + 1 = {overflowed}"

  let big : UInt64 := 0x8000000000000000
  let doubled := big * 2
  IO.println s!"2^63 * 2 = {doubled}"

def test_shift_overflow : IO Unit := do
  IO.println "\n=== Shift Overflow Test ==="
  let n : UInt64 := 1
  let shifted := n <<< 128
  IO.println s!"1 <<< 128 = {shifted}"

  let shifted2 := n <<< 65
  IO.println s!"1 <<< 65 = {shifted2}"

def test_div_zero : IO Unit := do
  IO.println "\n=== Division by Zero Test ==="
  try
    let n : UInt64 := 42
    let result := n / 0
    IO.println s!"42 / 0 = {result} (SHOULD PANIC!)"
  catch e =>
    IO.println s!"Caught: {e}"

def test_array_overflow_index : IO Unit := do
  IO.println "\n=== Array Index Overflow Test ==="
  let arr : Array Nat := #[1, 2, 3, 4, 5]
  let idx : UInt64 := 0xFFFFFFFFFFFFFFFF
  let idx_nat := idx.toNat
  IO.println s!"Overflowed index: {idx_nat}"

  try
    let elem := arr[idx_nat]!
    IO.println s!"Element: {elem} (SHOULD HAVE PANICKED!)"
  catch e =>
    IO.println s!"Caught: {e}"

def test_type_confusion : IO Unit := do
  IO.println "\n=== Type Downcasting Test ==="
  let large : UInt64 := 0xDEADBEEFCAFEBABE
  let as_u32 : UInt32 := large.toUInt32
  let as_u16 : UInt16 := large.toUInt16
  let as_u8 : UInt8 := large.toUInt8

  IO.println s!"0xDEADBEEFCAFEBABE -> UInt32: 0x{as_u32.toNat.toHex}"
  IO.println s!"0xDEADBEEFCAFEBABE -> UInt16: 0x{as_u16.toNat.toHex}"
  IO.println s!"0xDEADBEEFCAFEBABE -> UInt8: 0x{as_u8.toNat.toHex}"

def main : IO Unit := do
  test_uint8_overflow
  test_uint64_overflow
  test_shift_overflow
  test_div_zero
  test_array_overflow_index
  test_type_confusion
  IO.println "\n=== Tests completed ==="
