-- Test 5.1: Garbage Collector Exploitation
-- How does GC interact with type-confused pointers?

import Lean

unsafe def gcScanningConfusion : IO Unit := do
  IO.println "=== Test: GC scanning of confused types ==="

  -- Allocate real String object
  let realString : String := "Hello World - This is a heap-allocated string"
  IO.println s!"Original string: {realString}"

  -- Type confuse to Nat
  let asNat : Nat := unsafeCast realString
  IO.println s!"As Nat: {asNat}"

  -- Store in Nat array (GC will scan this array)
  let arr : Array Nat := #[asNat, 1, 2, 3]
  IO.println s!"Stored in Nat array, size: {arr.size}"

  -- Trigger GC by allocating lots of objects
  IO.println "Triggering GC..."
  let mut waste : Array String := #[]
  for i in [0:10000] do
    waste := waste.push s!"GC pressure string number {i}"

  IO.println "GC triggered (hopefully)"

  -- Try to recover the string
  let recovered : String := unsafeCast arr[0]!
  IO.println "Attempting to read recovered string..."

  try
    IO.println s!"Recovered string: {recovered}"
    IO.println "✓ String survived GC cycle"
  catch _ =>
    IO.println "✗ String was corrupted or freed by GC"

unsafe def useAfterFreeAttempt : IO Unit := do
  IO.println "\n=== Test: Use-after-free via type confusion ==="

  -- Create temporary string in inner scope
  let addr : Nat := do
    let temp : String := "temporary string"
    IO.println s!"Temp string: {temp}"
    unsafeCast temp  -- Leak the "pointer" as Nat

  IO.println s!"String address leaked as: {addr}"

  -- Force GC
  IO.println "Forcing GC to free temporary string..."
  let mut waste : Array String := #[]
  for i in [0:100000] do
    waste := waste.push s!"Force GC {i}"

  -- Try to use freed memory
  IO.println "Attempting use-after-free..."
  let dangling : String := unsafeCast addr

  try
    IO.println s!"Dangling string: {dangling}"
    IO.println "⚠ Use-after-free succeeded (GC didn't free it?)"
  catch _ =>
    IO.println "✓ Crashed (expected - use after free)"

unsafe def gcDoubleFreeTest : IO Unit := do
  IO.println "\n=== Test: Potential double-free ==="

  let str : String := "Test string for double-free"

  -- Store string in two places with different types
  let asNat : Nat := unsafeCast str
  let arr1 : Array String := #[str]
  let arr2 : Array Nat := #[asNat]

  IO.println "String stored in Array String and Array Nat"

  -- Trigger GC
  let mut waste : Array String := #[]
  for i in [0:50000] do
    waste := waste.push s!"GC trigger {i}"

  IO.println "GC triggered - checking for double-free..."

  -- Try to access both
  try
    IO.println s!"From String array: {arr1[0]!}"
    let recovered : String := unsafeCast arr2[0]!
    IO.println s!"From Nat array: {recovered}"
  catch _ =>
    IO.println "Crashed (possible GC corruption)"

unsafe def gcLeakTest : IO Unit := do
  IO.println "\n=== Test: GC memory leak via type confusion ==="

  let mut totalAllocated : Nat := 0

  for round in [0:100] do
    -- Allocate strings
    let mut strings : Array String := #[]
    for i in [0:1000] do
      strings := strings.push s!"String {round}-{i}"
      totalAllocated := totalAllocated + 1

    -- Type confuse to Nat array (GC might not trace)
    let confused : Array Nat := unsafeCast strings

    -- Let confused array go out of scope
    IO.println s!"Round {round}: allocated {totalAllocated} total strings"

  IO.println "\nIf memory usage grew unbounded, GC leak detected"

unsafe def gcCorruptionDetection : IO Unit := do
  IO.println "\n=== Test: Detecting GC corruption ==="

  structure Marker where
    magic : Nat  -- 0xDEADBEEF
    data : String

  let marker : Marker := ⟨0xDEADBEEF, "corruption detector"⟩

  -- Type confuse
  let confused : Nat := unsafeCast marker

  -- Store in array
  let arr : Array Nat := #[confused, 1, 2, 3]

  -- Heavy GC pressure
  let mut waste : Array String := #[]
  for i in [0:50000] do
    waste := waste.push s!"GC stress {i}"

  -- Check marker integrity
  let recovered : Marker := unsafeCast arr[0]!

  if recovered.magic == 0xDEADBEEF then
    IO.println "✓ Marker intact - no corruption detected"
    IO.println s!"Data: {recovered.data}"
  else
    IO.println s!"✗ Marker corrupted: magic = {recovered.magic}"

unsafe def gcPinningTest : IO Unit := do
  IO.println "\n=== Test: GC pinning behavior ==="

  let str : String := "pinned string"
  let addr1 : Nat := unsafeCast str

  IO.println s!"Initial address: {addr1}"

  -- Trigger multiple GC cycles
  for round in [0:10] do
    let mut waste : Array String := #[]
    for i in [0:10000] do
      waste := waste.push s!"GC round {round} item {i}"

    let addr2 : Nat := unsafeCast str
    IO.println s!"After GC round {round}: {addr2}"

    if addr2 != addr1 then
      IO.println "⚠ String moved by GC (copying collector)"
      return

  IO.println "✓ String not moved (pinned or non-moving GC)"

unsafe def main : IO Unit := do
  IO.println "Testing GC interaction with type confusion"
  IO.println "These tests probe garbage collector behavior\n"

  gcScanningConfusion
  useAfterFreeAttempt
  gcDoubleFreeTest
  gcLeakTest
  gcCorruptionDetection
  gcPinningTest

  IO.println "\n=== GC Interaction Testing Complete ==="
