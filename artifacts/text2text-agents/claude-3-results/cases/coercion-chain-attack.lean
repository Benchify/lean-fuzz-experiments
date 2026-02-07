/-
Attack Vector: Coercion Chain Type Confusion
Target: Elaborator coercion resolution
Severity: CRITICAL if exploitable

Strategy: Chain multiple implicit coercions to create type confusion
If the elaborator doesn't properly validate coercion chains, we might
be able to coerce incompatible types and prove False.
-/

-- Set up a coercion chain
structure Wrapper1 (α : Type) where
  val : α

structure Wrapper2 (α : Type) where
  val : α

structure Wrapper3 (α : Type) where
  val : α

-- Create coercion instances
instance : Coe (Wrapper1 α) α where
  coe w := w.val

instance : Coe α (Wrapper2 α) where
  coe x := ⟨x⟩

instance : Coe (Wrapper2 α) (Wrapper3 α) where
  coe w := ⟨w.val⟩

-- Test: Can we create a coercion loop?
instance [Inhabited α] : Coe (Wrapper3 α) (Wrapper1 α) where
  coe w := ⟨w.val⟩

-- If elaborator doesn't detect cycles, this could loop infinitely
-- def test1 : Wrapper1 Nat := (42 : Nat)

-- Test: Chain coercions with dependent types
structure DepWrapper (n : Nat) where
  val : Fin n

-- Try to coerce between different indices
instance : CoeDep (DepWrapper (n+1)) w (Fin (n+1)) where
  coe := w.val

-- Can we confuse dependent coercions?
-- def test2 : Fin 5 := (⟨0, by omega⟩ : DepWrapper 6)

-- Test: Coercion through Prop
structure PropWrapper where
  prop : Prop

instance : Coe PropWrapper Prop where
  coe w := w.prop

-- Try to extract computational content from Prop
-- def test3 : Nat := (⟨True⟩ : PropWrapper)

-- Test: Coercion with universe polymorphism
structure UnivWrapper.{u} (α : Type u) where
  val : α

instance : CoeOut (UnivWrapper.{u} α) α where
  coe w := w.val

-- Can we confuse universe levels?
-- def test4 : Type := (⟨Nat⟩ : UnivWrapper.{1} Type)

-- Test: Transitive coercion soundness
axiom A : Type
axiom B : Type
axiom C : Type
axiom coerceAB : A → B
axiom coerceBC : B → C

instance : Coe A B where coe := coerceAB
instance : Coe B C where coe := coerceBC

-- If we can coerce A to C transitively, but also directly with different semantics,
-- we might create inconsistency
axiom coerceAC_different : A → C
-- instance : Coe A C where coe := coerceAC_different  -- Ambiguous coercion

-- Test: Coercion in pattern matching
inductive CoerceSum (α β : Type) where
  | left : α → CoerceSum α β
  | right : β → CoerceSum α β

instance [Coe α β] : Coe (CoerceSum α γ) (CoerceSum β γ) where
  coe
    | .left a => .left (a : β)
    | .right g => .right g

-- Can pattern matching + coercion create unsoundness?

-- Test: Coercion + subtypes
def Pos : Type := { n : Nat // n > 0 }

instance : Coe Pos Nat where
  coe p := p.val

-- Try to reverse coercion unsafely
-- def unsafeCoerce (n : Nat) : Pos := n  -- Should fail

-- Test: Coercion in type class resolution
class Convertible (α β : Type) where
  convert : α → β

instance [Convertible α β] : Coe α β where
  coe := Convertible.convert

-- Create circular convertibility
instance : Convertible Nat Int where
  convert n := Int.ofNat n

-- If we add: instance : Convertible Int Nat
-- We could create a cycle

-- Test: Function coercion
instance : CoeFun (Nat → Nat) (fun _ => Nat → Nat) where
  coe f := f

-- Can we exploit function coercion?
def funcTest : Nat := (fun x => x + 1) 5
