-- Test 6: VM Internals Probing
-- Can we infer VM internal structure through type confusion?

import Lean

unsafe def objectLayoutProbing : IO Unit := do
  IO.println "=== Test: Object layout probing ==="

  -- Create strings of different sizes
  let str1 : String := "A"
  let str2 : String := "AB"
  let str3 : String := "ABC"
  let str4 : String := "ABCD"

  -- Convert to Nat to observe patterns
  let addr1 : Nat := unsafeCast str1
  let addr2 : Nat := unsafeCast str2
  let addr3 : Nat := unsafeCast str3
  let addr4 : Nat := unsafeCast str4

  IO.println s!"String \"A\":    {addr1} (0x{Nat.toDigits 16 addr1})"
  IO.println s!"String \"AB\":   {addr2} (0x{Nat.toDigits 16 addr2})"
  IO.println s!"String \"ABC\":  {addr3} (0x{Nat.toDigits 16 addr3})"
  IO.println s!"String \"ABCD\": {addr4} (0x{Nat.toDigits 16 addr4})"

  -- Analyze patterns
  if addr1 == 0 && addr2 == 0 && addr3 == 0 && addr4 == 0 then
    IO.println "\n✓ Address sanitization confirmed - all addresses zeroed"
  else
    IO.println "\n⚠ Addresses leaked:"
    if addr2 > addr1 && addr3 > addr2 && addr4 > addr3 then
      IO.println "Sequential allocation detected"
      IO.println s!"Allocation granularity: ~{(addr2 - addr1)} bytes"

unsafe def alignmentProbing : IO Unit := do
  IO.println "\n=== Test: Memory alignment probing ==="

  -- Allocate many objects and check alignment
  let mut objects : Array String := #[]
  let mut addresses : Array Nat := #[]

  for i in [0:20] do
    let obj := s!"Object {i}"
    objects := objects.push obj
    let addr : Nat := unsafeCast obj
    addresses := addresses.push addr
    IO.println s!"Object {i}: {addr} (0x{Nat.toDigits 16 addr})"

  -- Check for alignment patterns
  if addresses.all (· == 0) then
    IO.println "\nAddress sanitization prevents alignment analysis"
  else
    -- Check if all addresses are aligned to powers of 2
    let mut alignments : Array Nat := #[]
    for addr in addresses do
      if addr != 0 then
        -- Find alignment
        let mut align := 1
        while align <= addr && addr % align == 0 do
          align := align * 2
        alignments := alignments.push (align / 2)

    IO.println s!"\nDetected alignments: {alignments}"

unsafe def typeTagInference : IO Unit := do
  IO.println "\n=== Test: Type tag inference ==="

  -- Different types, observe bit patterns
  let nat : Nat := 42
  let int : Int := 42
  let str : String := "42"
  let arr : Array Nat := #[42]
  let bool : Bool := true

  let natBits : Nat := unsafeCast nat
  let intBits : Nat := unsafeCast int
  let strBits : Nat := unsafeCast str
  let arrBits : Nat := unsafeCast arr
  let boolBits : Nat := unsafeCast bool

  IO.println s!"Nat 42:        {natBits} (0x{Nat.toDigits 16 natBits})"
  IO.println s!"Int 42:        {intBits} (0x{Nat.toDigits 16 intBits})"
  IO.println s!"String \"42\":   {strBits} (0x{Nat.toDigits 16 strBits})"
  IO.println s!"Array [42]:    {arrBits} (0x{Nat.toDigits 16 arrBits})"
  IO.println s!"Bool true:     {boolBits} (0x{Nat.toDigits 16 boolBits})"

  -- Analyze tag bits (typically low bits)
  IO.println "\nLow 3 bits (potential type tags):"
  IO.println s!"Nat:    {natBits % 8}"
  IO.println s!"Int:    {intBits % 8}"
  IO.println s!"String: {strBits % 8}"
  IO.println s!"Array:  {arrBits % 8}"
  IO.println s!"Bool:   {boolBits % 8}"

unsafe def immediateVsBoxedDetection : IO Unit := do
  IO.println "\n=== Test: Immediate vs boxed value detection ==="

  -- Small Nats might be immediate (unboxed)
  -- Large Nats might be boxed (pointer)
  let small : Nat := 42
  let large : Nat := 1000000000000000000

  let smallBits : Nat := unsafeCast small
  let largeBits : Nat := unsafeCast large

  IO.println s!"Small Nat (42):             {smallBits}"
  IO.println s!"Large Nat (10^18):          {largeBits}"

  -- Immediate values should have specific bit patterns
  -- Pointers should look like addresses

  if smallBits == 42 || smallBits == 0 then
    IO.println "Small Nat: likely immediate value or sanitized"
  else
    IO.println s!"Small Nat: pointer? (0x{Nat.toDigits 16 smallBits})"

  if largeBits > 0x1000 && largeBits != large then
    IO.println s!"Large Nat: likely boxed (pointer: 0x{Nat.toDigits 16 largeBits})"
  else
    IO.println "Large Nat: representation unclear"

unsafe def closureLayoutProbing : IO Unit := do
  IO.println "\n=== Test: Closure layout probing ==="

  let x := 42
  let closure1 := fun () => x
  let closure2 := fun () => x + 1
  let closure3 := fun (y : Nat) => x + y

  -- Try to probe closure structure
  let bits1 : Nat := unsafeCast closure1
  let bits2 : Nat := unsafeCast closure2
  let bits3 : Nat := unsafeCast closure3

  IO.println s!"Closure 1: {bits1} (0x{Nat.toDigits 16 bits1})"
  IO.println s!"Closure 2: {bits2} (0x{Nat.toDigits 16 bits2})"
  IO.println s!"Closure 3: {bits3} (0x{Nat.toDigits 16 bits3})"

  if bits1 == 0 then
    IO.println "Closures sanitized"
  else
    IO.println "Closure structure might be leaked"

unsafe def ioHandleProbing : IO Unit := do
  IO.println "\n=== Test: IO handle probing ==="

  -- Open files and probe handles
  try
    let handle1 ← IO.FS.Handle.mk "/tmp/test1.txt" IO.FS.Mode.write
    let handle2 ← IO.FS.Handle.mk "/tmp/test2.txt" IO.FS.Mode.write

    let bits1 : Nat := unsafeCast handle1
    let bits2 : Nat := unsafeCast handle2

    IO.println s!"Handle 1: {bits1} (0x{Nat.toDigits 16 bits1})"
    IO.println s!"Handle 2: {bits2} (0x{Nat.toDigits 16 bits2})"

    -- File descriptors are typically small integers (3, 4, 5, ...)
    if bits1 < 100 && bits2 < 100 then
      IO.println "Handles might be file descriptors"

    handle1.close
    handle2.close
  catch e =>
    IO.println s!"Error: {e}"

unsafe def arrayInternalStructure : IO Unit := do
  IO.println "\n=== Test: Array internal structure ==="

  let arr1 : Array Nat := #[]
  let arr2 : Array Nat := #[1]
  let arr3 : Array Nat := #[1, 2, 3]

  let bits1 : Nat := unsafeCast arr1
  let bits2 : Nat := unsafeCast arr2
  let bits3 : Nat := unsafeCast arr3

  IO.println s!"Empty array:      {bits1} (0x{Nat.toDigits 16 bits1})"
  IO.println s!"Array [1]:        {bits2} (0x{Nat.toDigits 16 bits2})"
  IO.println s!"Array [1,2,3]:    {bits3} (0x{Nat.toDigits 16 bits3})"

  -- Arrays have size and capacity fields
  -- Try to infer structure

unsafe def referenceEquality : IO Unit := do
  IO.println "\n=== Test: Reference equality vs value equality ==="

  let str1 : String := "test"
  let str2 : String := "test"
  let str3 := str1  -- Same reference

  let addr1 : Nat := unsafeCast str1
  let addr2 : Nat := unsafeCast str2
  let addr3 : Nat := unsafeCast str3

  IO.println s!"str1: {addr1}"
  IO.println s!"str2: {addr2}"
  IO.println s!"str3: {addr3}"

  if addr1 == addr2 then
    IO.println "String interning detected (same address)"
  else
    IO.println "No string interning (different addresses)"

  if addr1 == addr3 then
    IO.println "Reference equality preserved"

unsafe def main : IO Unit := do
  IO.println "Testing VM internals probing"
  IO.println "Can we infer VM structure through type confusion?\n"

  objectLayoutProbing
  alignmentProbing
  typeTagInference
  immediateVsBoxedDetection
  closureLayoutProbing
  ioHandleProbing
  arrayInternalStructure
  referenceEquality

  IO.println "\n=== VM Probing Complete ==="
  IO.println "Note: Address sanitization limits information disclosure"
