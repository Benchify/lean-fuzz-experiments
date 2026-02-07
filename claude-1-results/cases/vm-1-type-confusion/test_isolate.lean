-- Isolate which operation causes the crash

-- Test A: Just the cast, no string operations
unsafe def testA : IO Unit := do
  IO.println "Test A: Cast only"
  let n : Nat := 42
  let s : String := unsafeCast n
  IO.println "Cast completed successfully"

-- Test B: Cast and get length
unsafe def testB : IO Unit := do
  IO.println "Test B: Cast + length"
  let n : Nat := 42
  let s : String := unsafeCast n
  let _ := s.length  -- Don't print, just access
  IO.println "Length access completed"

-- Test C: Cast and print
unsafe def testC : IO Unit := do
  IO.println "Test C: Cast + interpolation"
  let n : Nat := 42
  let s : String := unsafeCast n
  IO.println s!"Result: {s}"

-- Test D: Cast and print without interpolation
unsafe def testD : IO Unit := do
  IO.println "Test D: Cast + direct print"
  let n : Nat := 42
  let s : String := unsafeCast n
  IO.println s

unsafe def main : IO Unit := do
  try testA catch e => IO.println s!"A crashed: {e}"
  try testB catch e => IO.println s!"B crashed: {e}"
  try testC catch e => IO.println s!"C crashed: {e}"
  try testD catch e => IO.println s!"D crashed: {e}"
