-- Test 3.1.1: Non-Crashing Type Confusions
-- Type confusion between types with compatible memory layouts

import Lean

unsafe def compatibleStructures : IO Unit := do
  IO.println "=== Test: Compatible structure layouts ==="

  structure TypeA where
    x : Nat
    y : Nat

  structure TypeB where
    a : Nat
    b : Nat

  let valA : TypeA := ⟨42, 100⟩
  IO.println s!"TypeA: x={valA.x}, y={valA.y}"

  -- Type confuse to TypeB
  let valB : TypeB := unsafeCast valA

  -- This should NOT crash if layouts are identical
  IO.println s!"TypeB: a={valB.a}, b={valB.b}"

  if valB.a == 42 && valB.b == 100 then
    IO.println "✓ VULNERABILITY: Silent type confusion succeeded"
    IO.println "Data accessible through wrong type without crash"

unsafe def subtypeConfusion : IO Unit := do
  IO.println "\n=== Test: Subtype/supertype confusion ==="

  structure Small where
    value : Nat

  structure Large where
    value : Nat
    extra : String

  -- Small to Large (dangerous - reading uninitialized)
  let small : Small := ⟨42⟩
  let large : Large := unsafeCast small

  IO.println s!"Large.value: {large.value}"

  try
    IO.println s!"Large.extra: {large.extra}"
    IO.println "⚠ Read uninitialized memory without crash"
  catch _ =>
    IO.println "Crashed reading uninitialized field"

unsafe def primitiveTypeConfusion : IO Unit := do
  IO.println "\n=== Test: Primitive type confusion ==="

  -- Nat to Int
  let n : Nat := 42
  let i : Int := unsafeCast n
  IO.println s!"Nat 42 as Int: {i}"

  -- Bool to Nat
  let b : Bool := true
  let n2 : Nat := unsafeCast b
  IO.println s!"Bool true as Nat: {n2}"

  -- Nat to Bool
  let n3 : Nat := 1
  let b2 : Bool := unsafeCast n3
  IO.println s!"Nat 1 as Bool: {b2}"

  IO.println "✓ Primitive type confusions succeed silently"

unsafe def arrayConfusion : IO Unit := do
  IO.println "\n=== Test: Array type confusion ==="

  let arrNat : Array Nat := #[1, 2, 3, 4, 5]
  IO.println s!"Array Nat: {arrNat}"

  -- Cast to Array of different type
  let arrInt : Array Int := unsafeCast arrNat
  IO.println s!"Array Int: {arrInt}"

  -- Access elements
  IO.println s!"Element 0: {arrInt[0]!}"
  IO.println s!"Element 4: {arrInt[4]!}"

  IO.println "✓ Array type confusion succeeds (same memory layout)"

unsafe def optionConfusion : IO Unit := do
  IO.println "\n=== Test: Option type confusion ==="

  let someVal : Option Nat := some 42
  let someStr : Option String := unsafeCast someVal

  match someStr with
  | none => IO.println "none"
  | some s =>
    IO.println "some (confused value)"
    try
      IO.println s!"String: {s}"
    catch _ =>
      IO.println "Crashed dereferencing confused String"

unsafe def privacyViolation : IO Unit := do
  IO.println "\n=== Test: Privacy violation via type confusion ==="

  -- Simulated private structure
  structure SecretData where
    private mk ::
    privateKey : Nat
    publicData : String

  let secret := SecretData.mk 0xDEADBEEF "public_info"

  -- Cast to structure with same layout but no privacy
  structure LeakedData where
    exposedKey : Nat
    exposedString : String

  let leaked : LeakedData := unsafeCast secret

  IO.println s!"Leaked private key: {leaked.exposedKey}"
  IO.println s!"Leaked string: {leaked.exposedString}"

  IO.println "⚠ CRITICAL: Privacy violation without crash"

unsafe def authenticationBypass : IO Unit := do
  IO.println "\n=== Test: Authentication bypass ==="

  structure User where
    isAdmin : Bool
    name : String

  structure Admin where
    isAdmin : Bool
    name : String

  let normalUser : User := ⟨false, "alice"⟩
  IO.println s!"User: isAdmin={normalUser.isAdmin}, name={normalUser.name}"

  -- Type confuse to Admin
  let fakeAdmin : Admin := unsafeCast normalUser

  IO.println s!"Admin: isAdmin={fakeAdmin.isAdmin}, name={fakeAdmin.name}"

  -- Simulate authentication check
  def checkAdminAccess (admin : Admin) : IO Unit := do
    if admin.isAdmin then
      IO.println "✓ ADMIN ACCESS GRANTED"
    else
      IO.println "✗ Access denied - not admin"

  -- This correctly denies (isAdmin is still false)
  checkAdminAccess fakeAdmin

  -- But what if we set isAdmin first?
  let realUser : User := ⟨true, "bob"⟩
  let elevatedUser : Admin := unsafeCast realUser

  IO.println "\nTesting with isAdmin=true:"
  checkAdminAccess elevatedUser

unsafe def pairReinterpretation : IO Unit := do
  IO.println "\n=== Test: Pair/tuple reinterpretation ==="

  let pair1 : Nat × Nat := (42, 100)
  let pair2 : String × String := unsafeCast pair1

  IO.println s!"Original: ({pair1.1}, {pair1.2})"

  try
    IO.println s!"Confused: ({pair2.1}, {pair2.2})"
  catch _ =>
    IO.println "Crashed accessing confused pair"

  -- But accessing just structure without dereferencing
  let back : Nat × Nat := unsafeCast pair2
  IO.println s!"Recovered: ({back.1}, {back.2})"

unsafe def main : IO Unit := do
  IO.println "Testing non-crashing type confusions"
  IO.println "These test types with compatible memory layouts\n"

  compatibleStructures
  subtypeConfusion
  primitiveTypeConfusion
  arrayConfusion
  optionConfusion
  privacyViolation
  authenticationBypass
  pairReinterpretation

  IO.println "\n=== Compatible Layout Testing Complete ==="
  IO.println "CRITICAL FINDINGS:"
  IO.println "1. Type confusion succeeds silently for compatible layouts"
  IO.println "2. Privacy violations possible without crashes"
  IO.println "3. Potential for logic bugs and security bypasses"
