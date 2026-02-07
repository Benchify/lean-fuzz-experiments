/-
Case: soundness-6-elaborator-typeclass
Category: Elaborator Soundness - Type Classes
Severity: CRITICAL if exploitable

Test: Type class resolution and elaboration edge cases
-/

-- Test 1: Overlapping instances (should be rejected)
class MyClass (α : Type) where
  val : α

instance : MyClass Nat where
  val := 0

-- Try to add another instance for Nat (should error or be handled)
-- instance : MyClass Nat where
--   val := 1

-- Test 2: Circular instance resolution
-- class A (α : Type) where
--   toB : B α

-- class B (α : Type) where
--   toA : A α

-- Test 3: Type class with dependent types
class Container (α : Type u) where
  size : Nat

instance : Container (List α) where
  size := 0  -- Should really be list.length but this tests compilation

-- Test 4: Defaulting and ambiguity
class HasDefault (α : Type) where
  default : α

instance : HasDefault Nat where
  default := 0

instance : HasDefault Bool where
  default := false

-- Can we create ambiguity?
def getDefault [HasDefault α] : α := HasDefault.default

#check (getDefault : Nat)
#check (getDefault : Bool)

-- Test 5: Coe (coercion) chains
instance : Coe Nat Int where
  coe n := Int.ofNat n

-- Can we create unsound coercions?
-- def badCoe : Coe False True where
--   coe _ := True.intro  -- Can't have False to construct from

#check (42 : Int)  -- Should coerce