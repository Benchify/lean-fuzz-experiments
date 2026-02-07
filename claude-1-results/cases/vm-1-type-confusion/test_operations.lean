-- Test which operations on type-confused values crash

-- Test 1: String.length
unsafe def test1 : IO Unit := do
  IO.println "[1] Testing String.length on confused type"
  let n : Nat := 42
  let s : String := unsafeCast n
  let len := s.length
  IO.println s!"Length: {len}"

-- Test 2: Direct println (not interpolation)
unsafe def test2 : IO Unit := do
  IO.println "[2] Testing direct println"
  let n : Nat := 42
  let s : String := unsafeCast n
  IO.println s

-- Test 3: String interpolation
unsafe def test3 : IO Unit := do
  IO.println "[3] Testing string interpolation"
  let n : Nat := 42
  let s : String := unsafeCast n
  IO.println s!"Value: {s}"

-- Test 4: Pattern matching on confused String
unsafe def test4 : IO Unit := do
  IO.println "[4] Testing pattern matching"
  let n : Nat := 42
  let s : String := unsafeCast n
  match s with
  | "" => IO.println "Empty"
  | _ => IO.println "Not empty"

-- Test 5: Equality check
unsafe def test5 : IO Unit := do
  IO.println "[5] Testing equality"
  let n : Nat := 42
  let s : String := unsafeCast n
  if s == "test" then
    IO.println "Equal"
  else
    IO.println "Not equal"

def main : IO Unit := do
  IO.println "=== Testing individual operations ==="
  IO.println "Note: Crash will show Exit: 139\n"
