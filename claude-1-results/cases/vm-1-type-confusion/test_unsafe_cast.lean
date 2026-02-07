-- VM Type Confusion Attack: Unsafe Cast Exploitation
-- Testing if we can confuse the VM's type system using unsafeCast

import Lean

-- Test 1: Try to cast between incompatible types
def test_cast_nat_to_string : IO Unit := do
  let n : Nat := 42
  -- Try to unsafeCast Nat to String - what does VM do?
  let s : String := unsafeCast n
  IO.println s"Casted value: {s}"

-- Test 2: Cast between pointer-like types
def test_cast_array_confusion : IO Unit := do
  let arr : Array Nat := #[1, 2, 3, 4, 5]
  -- Try to reinterpret Array Nat as Array String
  let arr2 : Array String := unsafeCast arr
  for s in arr2 do
    IO.println s"Element: {s}"

-- Test 3: Cast function types
def test_cast_function : IO Unit := do
  let f : Nat → Nat := fun x => x + 1
  -- Try to reinterpret as different function type
  let g : String → String := unsafeCast f
  let result := g "hello"
  IO.println s"Function result: {result}"

-- Test 4: Cast proof objects to data
def test_cast_proof : IO Unit := do
  let p : 1 = 1 := rfl
  -- Try to cast proof to Nat - does this leak kernel data?
  let n : Nat := unsafeCast p
  IO.println s"Proof as Nat: {n}"

-- Test 5: Type confusion with IO actions
def test_cast_io : IO Unit := do
  let io1 : IO Nat := pure 42
  -- Reinterpret IO Nat as IO String
  let io2 : IO String := unsafeCast io1
  let result ← io2
  IO.println s"IO result: {result}"

-- Main entry point
def main : IO Unit := do
  IO.println "=== VM Type Confusion Tests ==="

  IO.println "\n[Test 1: Nat to String]"
  try
    test_cast_nat_to_string
  catch e =>
    IO.println s"Error: {e}"

  IO.println "\n[Test 2: Array Type Confusion]"
  try
    test_cast_array_confusion
  catch e =>
    IO.println s"Error: {e}"

  IO.println "\n[Test 3: Function Type Confusion]"
  try
    test_cast_function
  catch e =>
    IO.println s"Error: {e}"

  IO.println "\n[Test 4: Proof to Data Cast]"
  try
    test_cast_proof
  catch e =>
    IO.println s"Error: {e}"

  IO.println "\n[Test 5: IO Type Confusion]"
  try
    test_cast_io
  catch e =>
    IO.println s"Error: {e}"
