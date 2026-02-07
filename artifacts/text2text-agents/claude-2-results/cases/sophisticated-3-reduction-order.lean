/-
Sophisticated Attack 3: Reduction Order and Let-Polymorphism
Targeting: Order of reduction, let-binding polymorphism, opacity

Reduction order bugs can lead to:
- Infinite reduction loops
- Non-confluence
- Definitional equality issues
- Let-polymorphism soundness problems
-/

-- Test 1: Reduction order dependency
def reduceA := reduceB + 1
def reduceB := reduceA - 1

-- Circular definition - does reduction terminate?
-- #reduce reduceA  -- Should fail or detect cycle

-- Test 2: Let-binding generalization
def letPoly1 :=
  let id := fun x => x
  (id 5, id "hello")  -- id should be polymorphic

-- Works correctly

-- But what about:
def letPoly2 :=
  let id : Nat → Nat := fun x => x  -- Monomorphic type annotation
  (id 5, id "hello")  -- Should fail on second use

-- Should fail correctly

-- Test 3: Let-binding in types
def typeWithLet (n : Nat) :=
  let T := Nat
  let x : T := 42
  x + n

-- Does let-reduction in types work correctly?

-- Test 4: Opaque reduction bypass
opaque secretValue : Nat := 42

def useSecret := secretValue + 1

-- Can we see through opaque?
-- theorem seeOpaque : secretValue = 42 := rfl  -- Should fail (opaque)

-- Test 5: Noncomputable reduction
noncomputable def noncomp : Nat :=
  Classical.choice ⟨42⟩

-- Can we reduce noncomputable?
-- #reduce noncomp  -- Should fail

-- But can we prove things about it?
-- theorem noncompEq : noncomp = 42 := rfl  -- Should fail (can't reduce)

-- Test 6: Mutual reduction dependency
mutual
  def evenOrOdd (n : Nat) : String :=
    if n = 0 then "even"
    else oddOrEven (n - 1)

  def oddOrEven (n : Nat) : String :=
    if n = 0 then "odd"
    else evenOrOdd (n - 1)
end

-- Does mutual reduction work correctly?
#reduce evenOrOdd 10

-- Test 7: Let with dependent types
def depLet (n : Nat) (h : n > 0) :=
  let m : {m : Nat // m = n} := ⟨n, rfl⟩
  m.val + 1

-- Dependent let-binding reduction

-- Test 8: Reduction in match scrutinee
def matchReduce (n : Nat) : Nat :=
  match (let x := 5; x + n) with
  | 0 => 0
  | k + 1 => k

-- Let inside match scrutinee

-- Test 9: Proof reduction order
theorem proofReduce1 : 2 + 2 = 4 := rfl
theorem proofReduce2 : 2 + 2 = 4 := proofReduce1

-- Does proof reduction create issues?

-- Test 10: Infinite type in reduction
-- def infiniteType := (infiniteType, Nat)  -- Should fail (occurs check)

-- Test 11: Universe polymorphic let
def polyUnivLet.{u} (α : Type u) :=
  let id : {β : Type u} → β → β := fun x => x
  id α

-- Universe polymorphism in let

-- Test 12: Reduction with type classes
def classReduce [ToString α] (x : α) :=
  let s := toString x
  s ++ s

-- Type class reduction in let

-- Test 13: Lazy vs strict reduction
def lazyTest :=
  let x := (1 + 1 : Nat)
  let y := x + x
  y  -- Is x reduced once or twice?

#reduce lazyTest  -- Should be 4

-- Test 14: Let-binding shadowing
def shadowTest :=
  let x := 5
  let x := x + 1  -- Shadow x
  let x := x * 2  -- Shadow again
  x

#reduce shadowTest  -- Should be 12

-- Test 15: Reduction with coercions
def coerceReduce : Nat :=
  let b : Bool := true
  let n : Nat := if b then 1 else 0
  n

-- Test 16: Let in proof term
theorem letProof : 2 + 2 = 4 :=
  let h : 2 + 2 = 4 := rfl
  h

-- Is this equivalent to just rfl?
theorem letProofEq : letProof = rfl := rfl  -- Proof irrelevance

-- Test 17: Partial application reduction
def partialApply :=
  let add := fun x y => x + y
  let add5 := add 5
  add5 10

#reduce partialApply  -- Should be 15

-- Test 18: Reduction with do-notation
def doReduce : Option Nat := do
  let x ← some 5
  let y := x + 1
  return x + y

#reduce doReduce  -- Should be some 11

-- Test 19: Type family reduction
inductive Vect : Nat → Type → Type where
  | nil : Vect 0 α
  | cons : α → Vect n α → Vect (n + 1) α

def vectHead {α : Type} : {n : Nat} → Vect (n + 1) α → α
  | _, .cons x _ => x

-- Does reduction handle the n+1 pattern correctly?

-- Test 20: Circular type through let?
-- def circType :=
--   let T := Nat → circType
--   T
-- Should fail (occurs check)

-- Test 21: Reduction with large numbers
def hugeNumber := 2^1000
def hugeCompute := hugeNumber + hugeNumber

-- Does reduction handle big integers correctly?
-- #reduce hugeCompute  -- Might be slow but should work

-- Test 22: Reduction order with proofs
def proofOrder (n : Nat) (h1 : n > 0) (h2 : n < 10) : Nat :=
  let p1 := h1
  let p2 := h2
  n

-- Proofs in let-bindings (should be erased)

-- Test 23: Match on let-bound variable
def matchLet (n : Nat) : Nat :=
  let m := n + 1
  match m with
  | 0 => 0
  | k + 1 => k

-- Test 24: Nested let with same names
def nestedLetShadow :=
  let x := 1
  let y := (let x := 2; x + x)  -- Inner x shadows outer
  x + y  -- Outer x + inner result

#reduce nestedLetShadow  -- Should be 1 + 4 = 5

-- Test 25: Let-binding with type mismatch
-- def letMismatch :=
--   let x : Nat := "hello"  -- Type error
--   x
-- Should fail at type checking

-- Test 26: Reduction with macros
macro "magic_number" : term => `(42)

def macroReduce := magic_number + 1

#reduce macroReduce  -- Should reduce through macro

-- Test 27: Let with partial patterns
def letPattern (p : Nat × Nat) : Nat :=
  let (x, y) := p
  x + y

-- Pattern matching in let

-- Test 28: Transparent vs opaque reduction
@[inline] def transparentDef := 42
opaque opaqueDef : Nat := 42

def useTransparent := transparentDef + 1  -- Can reduce
def useOpaque := opaqueDef + 1  -- Cannot reduce through

-- #reduce useTransparent  -- Should see 43
-- #reduce useOpaque  -- Should see opaqueDef + 1

-- Test 29: Reduction with subtype
def subtypeReduce (n : {x : Nat // x > 0}) : Nat :=
  let m := n.val
  m + 1

-- Test 30: Circular let via function
-- def circularLet :=
--   let f := fun x => circularLet
--   f ()
-- Should fail (circularity)

#check letPoly1
#check evenOrOdd
#check depLet
#check lazyTest
#check partialApply
#check vectHead
#check macroReduce
