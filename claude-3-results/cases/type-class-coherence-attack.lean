/-
SOPHISTICATED ATTACK: Type Class Coherence Violations
Target: Type class instance resolution and uniqueness
Severity: CRITICAL if exploitable

Type class coherence means: for any given type and class, there should be
at most one instance (up to definitional equality). If we can create
multiple distinguishable instances, we can break invariants.

This is extremely subtle and could break soundness indirectly.
-/

-- Attack 1: Overlapping instances with different behavior
class MyClass (α : Type) where
  value : Nat

instance inst1 : MyClass Nat where
  value := 42

-- Try to create conflicting instance
-- instance inst2 : MyClass Nat where
--   value := 99

-- Lean should reject this, but what about indirect routes?

-- Attack 2: Instance through different paths
class ClassA (α : Type) where
  valA : Nat

class ClassB (α : Type) where
  valB : Nat

instance : ClassA Nat where
  valA := 1

instance : ClassB Nat where
  valB := 2

-- Now create class that can use either
class ClassC (α : Type) where
  valC : Nat

-- Two different ways to get ClassC Nat:
instance [ClassA α] : ClassC α where
  valC := ClassA.valA

-- If we had another instance:
-- instance [ClassB α] : ClassC α where
--   valC := ClassB.valB

-- These would conflict! Can we sneak this in?

-- Attack 3: Local instances
section LocalTest
  local instance : MyClass Bool where
    value := 100

  def localTest : Nat := MyClass.value (α := Bool)
  -- Inside section: 100
end LocalTest

-- Outside section, different instance?
-- Can we create confusion?

-- Attack 4: Default instances
class HasDefault (α : Type) where
  default : α

instance : HasDefault Nat where
  default := 0

instance [Inhabited α] : HasDefault α where
  default := Inhabited.default

-- For Nat, both instances apply!
-- Which is chosen?

-- Attack 5: Orphan instances (instances in different modules)
-- In module A: instance : MyClass String := ...
-- In module B: instance : MyClass String := ...
-- Both imported -> conflict!

-- Attack 6: Conditional instances
instance [BEq α] : MyClass α where
  value := 42

-- If we later add BEq Nat, do we get conflict?

-- Attack 7: Type class recursion
class Rec1 (α : Type) where
  val1 : Nat

class Rec2 (α : Type) where
  val2 : Nat

instance [Rec2 α] : Rec1 α where
  val1 := Rec2.val2 + 1

instance [Rec1 α] : Rec2 α where
  val2 := Rec1.val1 + 1

-- Circular dependency! What happens?
-- #check (Rec1.val1 : Nat)  -- Should fail or loop

-- Attack 8: Instance diamonds
class Base (α : Type) where
  baseVal : Nat

class Left (α : Type) extends Base α where
  leftVal : Nat

class Right (α : Type) extends Base α where
  rightVal : Nat

class Bottom (α : Type) extends Left α, Right α where
  bottomVal : Nat

-- Bottom inherits Base twice!
-- Is the Base instance unified?

-- Attack 9: Implicit vs explicit instance arguments
def useImplicit [MyClass α] : Nat :=
  MyClass.value

def useExplicit (inst : MyClass α) : Nat :=
  inst.value

-- Can these give different results?

-- Attack 10: Instance synthesis order
class Order1 (α : Type) where
  ord1 : Nat

class Order2 (α : Type) where
  ord2 : Nat

instance [Order1 α] [Order2 α] : MyClass α where
  value := Order1.ord1 + Order2.ord2

-- If we reverse the order of instance arguments, same result?

-- Attack 11: OutParam
class WithOutParam (α : Type) (β : outParam Type) where
  convert : α → β

-- OutParam changes instance resolution
-- Can we exploit this?

-- Attack 12: Type class with dependent types
class DepClass (n : Nat) where
  depVal : Fin n

instance : DepClass 5 where
  depVal := ⟨0, by omega⟩

instance : DepClass 5 where
  depVal := ⟨1, by omega⟩  -- Different value, same n!

-- Should be rejected, but what if we hide it?

-- Attack 13: Coherence through coercions
instance : Coe Nat Int where
  coe := Int.ofNat

class IntClass (α : Type) where
  toInt : α → Int

instance [Coe α Int] : IntClass α where
  toInt := fun x => (x : Int)

-- Multiple paths to IntClass?

-- Attack 14: Non-canonical instances
class Monoid (α : Type) where
  empty : α
  append : α → α → α

-- Nat with + is a monoid
instance : Monoid Nat where
  empty := 0
  append := (· + ·)

-- But Nat with * is also a monoid!
-- instance : Monoid Nat where
--   empty := 1
--   append := (· * ·)

-- Can we have both?

-- Attack 15: Propositional type classes
class PropClass (α : Type) : Prop where
  prop : α → Prop

-- Type classes can be in Prop!
-- Does this affect coherence?

instance : PropClass Nat where
  prop := fun n => n > 0

-- Can we have multiple instances (proof irrelevance)?

-- Attack 16: Inhabited vs Nonempty
class MyInhabited (α : Type) : Type where
  default : α

class MyNonempty (α : Type) : Prop where
  exists : Nonempty α

-- Inhabited is Type, Nonempty is Prop
-- Different coherence requirements!

-- Attack 17: Reducible vs irreducible instances
@[reducible]
instance reducible_inst : MyClass Unit where
  value := 1

@[irreducible]
instance irreducible_inst : MyClass Empty where
  value := 2

-- Does transparency affect instance resolution?

-- Attack 18: Instance via auxiliary definition
def auxDef (α : Type) : MyClass α where
  value := 99

instance indirect_instance : MyClass String :=
  auxDef String

-- Can we hide multiple instances this way?

-- Attack 19: Heterogeneous instance equality
-- Can two instances be propositionally equal but not definitionally?

instance inst_a : MyClass Bool where value := 0 + 0
instance inst_b : MyClass Empty where value := 0

-- Both have value 0, but different types
-- Any confusion?

-- Attack 20: Trans-module instance conflicts
-- File A defines instance
-- File B defines instance
-- File C imports both
-- Conflict should be detected, but is it?

-- Attack 21: Delayed instance synthesis
-- Sometimes instances are synthesized late
-- Can we exploit timing?

def delayedUse : Nat :=
  -- Instance synthesized here
  MyClass.value (α := Nat)

-- vs

def earlyUse [MyClass Nat] : Nat :=
  MyClass.value

-- Same instance?

-- Attack 22: Scoped instances
scoped instance : MyClass Char where
  value := 65

-- Scoped instances only active when namespace is open
-- Can we create conflicts?

-- Attack 23: Instance priorities
instance (priority := high) highPriorityInst : MyClass Float where
  value := 1

instance (priority := low) lowPriorityInst : MyClass Float where
  value := 2

-- Higher priority should win, but does it always?

-- Attack 24: Partial instances
class PartialClass (α : Type) where
  part1 : Nat
  part2 : Nat

-- Provide instance for only part1?
-- instance : PartialClass String where
--   part1 := 42
  -- part2 missing!

-- Attack 25: Transitive instances
class Trans1 (α : Type) where
  t1 : α

class Trans2 (α : Type) where
  t2 : α

class Trans3 (α : Type) where
  t3 : α

instance [Trans1 α] : Trans2 α where
  t2 := Trans1.t1

instance [Trans2 α] : Trans3 α where
  t3 := Trans2.t2

-- Can we create diamond with transitivity?

-- Attack 26: Instance unification
def useGeneric {α : Type} [MyClass α] (x : α) : Nat :=
  MyClass.value

-- What if α unifies with multiple types with instances?

-- Attack 27: Default method overriding
class WithDefault (α : Type) where
  method : Nat
  derived : Nat := method + 1

instance : WithDefault Nat where
  method := 10
  derived := 999  -- Override default!

-- Is this coherent with the default impl?

-- Attack 28: Instance through equality
axiom type_eq : Nat = Bool

-- If we had this, could we use it for instances?
-- def confusing [MyClass Nat] : MyClass Bool :=
--   cast (by rw [←type_eq]) inferInstance

-- Attack 29: Unification ambiguity
class Ambiguous (α : Type) (β : Type) where
  amb : Nat

instance : Ambiguous Nat Bool where
  amb := 1

instance : Ambiguous Bool Nat where
  amb := 2

def testAmbiguous : Nat :=
  @Ambiguous.amb _ _ _  -- Which instance?

-- Attack 30: Runtime vs compile-time instances
-- In VM, instances might be resolved differently than in kernel?

-- ULTIMATE TEST: Can we create two instances that behave differently?
class Ultimate (α : Type) where
  compute : α → Nat

instance : Ultimate Nat where
  compute := fun n => n

-- If we could add:
-- instance : Ultimate Nat where
--   compute := fun n => n + 1

-- We'd have incoherence!
-- Can we sneak this in via modules, local instances, or other tricks?
