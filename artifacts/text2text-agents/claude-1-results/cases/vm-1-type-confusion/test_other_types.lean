-- Test which type confusions cause crashes

-- Test 1: Array confusion
unsafe def test1 : IO Unit := do
  IO.println "Test 1: Array Nat → Array String"
  let arr : Array Nat := #[1, 2, 3]
  let arr2 : Array String := unsafeCast arr
  IO.println s!"Array size: {arr2.size}"

-- Test 2: List confusion
unsafe def test2 : IO Unit := do
  IO.println "Test 2: List Nat → List String"
  let list : List Nat := [1, 2, 3]
  let list2 : List String := unsafeCast list
  IO.println s!"List length: {list2.length}"

-- Test 3: Option confusion
unsafe def test3 : IO Unit := do
  IO.println "Test 3: Option Nat → Option String"
  let opt : Option Nat := some 42
  let opt2 : Option String := unsafeCast opt
  match opt2 with
  | none => IO.println "None"
  | some s => IO.println s!"Some: {s}"

-- Test 4: Simple cast without using the value
unsafe def test4 : IO Unit := do
  IO.println "Test 4: Cast Nat → String (unused)"
  let n : Nat := 42
  let _ : String := unsafeCast n
  IO.println "Cast completed"

unsafe def main : IO Unit := do
  try test1 catch e => IO.println s!"Test 1 crashed: {e}"
  IO.println ""
  try test2 catch e => IO.println s!"Test 2 crashed: {e}"
  IO.println ""
  try test3 catch e => IO.println s!"Test 3 crashed: {e}"
  IO.println ""
  try test4 catch e => IO.println s!"Test 4 crashed: {e}"
