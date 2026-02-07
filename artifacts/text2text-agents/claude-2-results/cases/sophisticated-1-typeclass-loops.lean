/-
Sophisticated Attack 1: Type Class Resolution Exploits
Targeting: Instance resolution algorithm, unification, infinite loops

Type class resolution is complex and might have:
- Infinite loop vulnerabilities
- Backtracking bugs
- Diamond problem issues
- Priority confusion
-/

-- Test 1: Circular instance dependency
class CircA (α : Type) where
  toB : CircB α

class CircB (α : Type) where
  toA : CircA α

-- Can we create instances that loop?
-- instance : CircA Nat where
--   toB := { toA := inferInstance }  -- Should detect cycle

-- Test 2: Diamond inheritance with conflicting instances
class Top (α : Type) where
  top : Nat

class Left (α : Type) extends Top α where
  left : Nat

class Right (α : Type) extends Top α where
  right : Nat

class Bottom (α : Type) extends Left α, Right α where
  bottom : Nat

-- Diamond: Bottom → Left → Top
--         Bottom → Right → Top
-- Does instance resolution handle diamond correctly?

instance : Top Nat where top := 1
instance : Left Nat where top := 2; left := 3
instance : Right Nat where top := 4; right := 5
instance : Bottom Nat where top := 6; left := 7; right := 8; bottom := 9

-- Which 'top' gets selected?
#eval (Top.top : Nat)  -- Should be unambiguous

-- Test 3: Overlapping instances with different priorities
class Overlap (α : Type) where
  value : Nat

-- Two instances for the same type
instance (priority := high) : Overlap Nat where
  value := 42

instance (priority := low) : Overlap Nat where
  value := 99

-- Does priority work correctly?
#eval (Overlap.value : Nat)  -- Should be 42 (high priority)

-- Test 4: Transitive instance synthesis
class Trans1 (α β : Type) where
  trans1 : α → β

class Trans2 (β γ : Type) where
  trans2 : β → γ

class Trans3 (α γ : Type) where
  trans3 : α → γ

-- If we have α → β and β → γ, can we synthesize α → γ?
instance : Trans1 Nat Bool where trans1 n := n > 0
instance : Trans2 Bool String where trans2 b := if b then "yes" else "no"

-- Should require manual instance or fail:
-- instance [Trans1 α β] [Trans2 β γ] : Trans3 α γ where
--   trans3 x := Trans2.trans2 (Trans1.trans1 x)

-- Test 5: Universe polymorphic type class loop
class PolyLoop.{u} (α : Type u) where
  loop : PolyLoop α  -- Self-referential!

-- Can we create this? Should be rejected.
-- instance : PolyLoop Nat where
--   loop := inferInstance  -- Would create infinite loop

-- Test 6: Out parameter confusion
class OutParam (α : Type) (β : outParam Type) where
  convert : α → β

instance : OutParam Nat Nat where convert := id
instance : OutParam Nat Bool where convert n := n > 0

-- Ambiguity - which instance?
-- def testOut (n : Nat) := OutParam.convert n  -- Should fail or pick deterministically

-- Test 7: Default instances creating loops
class DefaultLoop (α : Type) where
  value : α

instance [Inhabited α] : DefaultLoop α where
  value := default

instance [DefaultLoop α] : Inhabited α where
  default := DefaultLoop.value

-- Circular dependency between Inhabited and DefaultLoop
-- def testDefault : DefaultLoop Nat := inferInstance  -- Should detect cycle

-- Test 8: Complex diamond with coercions
class CoerceTop (α : Type) where
  toNat : α → Nat

class CoerceLeft (α : Type) extends CoerceTop α where
  leftValue : Nat

class CoerceRight (α : Type) extends CoerceTop α where
  rightValue : Nat

instance : CoerceTop Bool where
  toNat b := if b then 1 else 0

instance : CoerceLeft Bool where
  toNat b := if b then 10 else 0  -- Different implementation!
  leftValue := 42

instance : CoerceRight Bool where
  toNat b := if b then 100 else 0  -- Yet another!
  rightValue := 99

-- Which toNat is used?
-- #eval CoerceTop.toNat true  -- Should be deterministic

-- Test 9: Mutually dependent instances with default values
class MutA (α : Type) where
  mutAVal : Nat

class MutB (α : Type) where
  mutBVal : Nat

instance [MutB α] : MutA α where
  mutAVal := MutB.mutBVal + 1

instance [MutA α] : MutB α where
  mutBVal := MutA.mutAVal + 1

-- Circular: MutA needs MutB, MutB needs MutA
-- def testMut : MutA Nat := inferInstance  -- Should fail

-- Test 10: Type family instance overlap
class TypeFamily (α : Type) where
  Result : Type
  compute : α → Result

instance : TypeFamily Nat where
  Result := Bool
  compute n := n > 0

instance : TypeFamily Nat where  -- Duplicate!
  Result := String
  compute n := toString n

-- Should reject duplicate instance

-- Test 11: Dependent type class with universe issues
class DepClass.{u, v} (α : Type u) where
  DepType : Type v
  depVal : α → DepType

-- Can we confuse universe levels?
instance : DepClass.{0, 1} Nat where
  DepType := Type
  depVal _ := Nat

-- Does this allow Type : Type through the back door?

-- Test 12: Projection confusion
structure MyStruct (α : Type) where
  field1 : α
  field2 : α

class HasField (S : Type) (α : Type) where
  getField : S → α

instance : HasField (MyStruct Nat) Nat where
  getField s := s.field1

instance : HasField (MyStruct Nat) Nat where  -- Duplicate with different impl
  getField s := s.field2

-- Which projection is used?

-- Test 13: Subsingleton instance manipulation
class MySingleton (α : Type) : Prop where
  isSingleton : ∀ (x y : α), x = y

-- If we can prove this for inhabited types incorrectly, we get issues
-- instance : MySingleton Nat where
--   isSingleton := fun x y => sorry  -- Lying

-- Test 14: Local instance shadowing global
def testLocalInstance : Nat :=
  let inst : Inhabited Nat := ⟨42⟩  -- Local instance, different default
  default  -- Which default?

-- Test 15: Instance from proof
def proofInstance (h : ∀ α, Inhabited α) : Inhabited Empty :=
  h Empty

-- If we could derive this, we'd have False
-- theorem deriveFalse (h : ∀ α, Inhabited α) : False :=
--   nomatch (proofInstance h).default

#check CircA
#check Bottom
#check (Overlap.value : Nat)
