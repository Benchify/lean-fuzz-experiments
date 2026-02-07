/-
SOPHISTICATED ATTACK: Auto-Generated Code Exploitation
Target: Lean's code generators (recursors, equation lemmas, etc.)
Severity: CRITICAL if exploitable

Lean automatically generates:
- Recursors for inductive types
- Equation lemmas for definitions
- Constructor injections
- No-confusion theorems
- Below recursion schemes

Bugs in these generators could compromise soundness.
-/

-- Attack 1: Inspect generated recursors
inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

-- Lean generates MyNat.rec, MyNat.recOn, MyNat.casesOn
#check @MyNat.rec
#check @MyNat.recOn
#check @MyNat.casesOn

-- Can we find inconsistencies in generated code?

-- Attack 2: Mutual inductive types - complex recursor generation
mutual
  inductive Tree (α : Type) : Type where
    | leaf : α → Tree α
    | node : Forest α → Tree α

  inductive Forest (α : Type) : Type where
    | nil : Forest α
    | cons : Tree α → Forest α → Forest α
end

-- Mutual recursion generates complex recursors
#check @Tree.rec
#check @Forest.rec

-- Can we exploit the mutual recursor generation?

def treeSize {α : Type} : Tree α → Nat
  | .leaf _ => 1
  | .node f => forestSize f + 1

def forestSize {α : Type} : Forest α → Nat
  | .nil => 0
  | .cons t f => treeSize t + forestSize f

-- Attack 3: Nested inductive types
inductive NestedTree (α : Type) : Type where
  | leaf : α → NestedTree α
  | node : List (NestedTree α) → NestedTree α

-- Nested inductives have complex recursors
#check @NestedTree.rec

-- Can we find bugs in nested recursor generation?

-- Attack 4: Indexed inductive families
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

-- Indexed types have dependent recursors
#check @Vec.rec

-- The recursor must respect indices - can we break this?

def vecMap {α β : Type} (f : α → β) : Vec α n → Vec β n
  | .nil => .nil
  | .cons a v => .cons (f a) (vecMap f v)

-- Attack 5: No-confusion and injectivity
-- Lean generates no-confusion theorems

#check @MyNat.noConfusion
#check @Vec.noConfusion

-- These state different constructors are different
-- Can we violate this?

theorem zero_ne_succ : MyNat.zero ≠ MyNat.succ n := fun h =>
  MyNat.noConfusion h

-- Can we create a type where no-confusion is wrong?

-- Attack 6: Equation compiler
-- Pattern matching compiles to recursors via equation compiler

def complicated (n : Nat) (m : Nat) : Nat :=
  match n, m with
  | 0, 0 => 1
  | 0, k + 1 => 2
  | n + 1, 0 => 3
  | n + 1, m + 1 => complicated n m

-- Lean generates equation lemmas:
-- #check complicated.eq_1
-- #check complicated.eq_2
-- etc.

-- Can the equation compiler generate wrong equations?

-- Attack 7: Nested pattern matching
def nestedMatch (x : Option (Option Nat)) : Nat :=
  match x with
  | none => 0
  | some none => 1
  | some (some n) => n

-- Nested matching generates complex code
-- Can we find bugs?

-- Attack 8: Inaccessible patterns with dependencies
def depMatch : (n : Nat) → Vec Nat n → Nat
  | 0, .nil => 0
  | n + 1, .cons x _ => x

-- The pattern matching must ensure indices match
-- Can we confuse the generator?

-- Attack 9: Overlapping patterns detection
def overlapDetection (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | _ => 2
  | 0 => 3  -- Should be detected as unreachable

-- If detection fails, we might get wrong equation lemmas

-- Attack 10: Structural recursion vs well-founded
def structRec : Nat → Nat
  | 0 => 0
  | n + 1 => structRec n

def wfRec (n : Nat) : Nat :=
  if n == 0 then 0
  else wfRec (n - 1)
termination_by n

-- Different recursion schemes might have bugs

-- Attack 11: Auto-generated instances
-- Lean generates instances automatically

inductive MyType : Type where
  | mk : Nat → Bool → MyType
  deriving Repr, BEq, Inhabited

-- Can auto-derived instances be wrong?

-- Attack 12: Induction principles
-- Beyond basic recursor, Lean generates induction principles

theorem myNat_ind (P : MyNat → Prop)
  (h0 : P MyNat.zero)
  (hS : ∀ n, P n → P (MyNat.succ n)) :
  ∀ n, P n := fun n =>
  MyNat.rec h0 (fun _ ih => hS _ ih) n

-- Is this always correct?

-- Attack 13: Dependent eliminators with complex motives
def complexMotive : Vec Nat n → Type
  | .nil => Nat
  | .cons _ _ => Bool

def elimWithComplexMotive : (v : Vec Nat n) → complexMotive v
  | .nil => 42
  | .cons _ _ => true

-- Complex motives stress the eliminator generator

-- Attack 14: Recursive structures
structure RecStruct where
  value : Nat
  next : Option RecStruct

-- Can recursor handle recursive structures?
-- #check @RecStruct.rec

-- Attack 15: Mutual structures
mutual
  structure A where
    b : Option B

  structure B where
    a : Option A
end

-- Mutual structures have complex recursors
-- #check @A.rec

-- Attack 16: Dependent record projection
structure DepRecord where
  n : Nat
  data : Fin n

-- Projections must respect dependencies
def getN (r : DepRecord) : Nat := r.n
def getData (r : DepRecord) : Fin r.n := r.data

-- Can we break the dependency tracking?

-- Attack 17: Equation lemmas for complex recursion
def ackermann : Nat → Nat → Nat
  | 0, m => m + 1
  | n + 1, 0 => ackermann n 1
  | n + 1, m + 1 => ackermann n (ackermann (n + 1) m)
termination_by n m => (n, m)

-- Complex recursion generates many equation lemmas
-- Are they all consistent?

-- Attack 18: Pattern matching on proofs
def matchOnEq {α : Type} {x y : α} (h : x = y) : x = y :=
  match h with
  | rfl => rfl

-- Pattern matching on equality is subtle
-- Can we exploit it?

-- Attack 19: Constructor injections
-- If MyNat.succ n = MyNat.succ m, then n = m

theorem succ_inj {n m : MyNat} (h : MyNat.succ n = MyNat.succ m) : n = m :=
  MyNat.noConfusion h (fun h => h)

-- Is injectivity always correct?

-- Attack 20: Below recursion
-- For nested recursion, Lean uses "below" scheme

def weirdNested : Nat → Nat
  | 0 => 0
  | n + 1 => weirdNested (weirdNested n)
termination_by n => n

-- Below scheme is complex - can we find bugs?

-- Attack 21: Quotient recursor
-- Quotients have special recursors

def QuotNat := Quot (fun (n m : Nat) => n % 2 = m % 2)

def quotElim (q : QuotNat) : Nat :=
  Quot.lift (fun n => n % 2) (fun _ _ h => by simp [h]) q

-- Quotient elimination must respect equivalence
-- Can we violate this?

-- Attack 22: Inspect equation lemmas
-- #print complicated.eq_1
-- Can we find inconsistent equation lemmas?

-- Attack 23: Smart constructors and recursor mismatch
inductive SmartType : Type where
  | mk : (n : Nat) → (h : n > 0) → SmartType

-- Constructor takes proof
def smartRec : SmartType → Nat
  | .mk n _ => n

-- Does recursor properly ignore proof?

-- Attack 24: CasesOn vs RecOn
-- casesOn doesn't allow recursion, recOn does
-- Can we confuse them?

def usesCasesOn (n : MyNat) : Nat :=
  MyNat.casesOn n 0 (fun _ => 1)

def usesRecOn (n : MyNat) : Nat :=
  MyNat.recOn n 0 (fun _ ih => ih + 1)

-- Are these always consistent?

-- Attack 25: Generated code in different modes
-- Interpreter vs VM vs compiled code
-- Do they all use same generated code?

def testGenerated (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => k

-- Test in interpreter
#reduce testGenerated 5

-- Test in VM
#eval testGenerated 5

-- Would compiled code differ?
