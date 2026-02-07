/-
Advanced Test 3: Pattern Matching Compilation Bugs
Attempting to exploit the pattern match compiler to derive False

Historical context: Pattern matching compilation is complex and has been
a source of soundness bugs in Coq, Agda, and other systems. Issues include:
- Incorrect coverage checking
- Wrong accessibility predicates for dependent matching
- Overlapping pattern handling
- Nested pattern translation bugs
-/

-- Test 1: Overlapping patterns with dependencies
def overlapTest1 (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => n + 1
  | _ => 42  -- Unreachable, but does compiler handle correctly?

-- Test 2: Deep nested matching with dependencies
inductive Deep where
  | leaf : Nat → Deep
  | node : Deep → Deep → Deep

def deepMatch (d : Deep) : Nat :=
  match d with
  | Deep.leaf n =>
    match n with
    | 0 => 0
    | n + 1 =>
      match d with  -- Re-matching outer variable inside
      | Deep.leaf m => m
      | _ => 100  -- Should be unreachable, type checker should know
  | Deep.node l r =>
    match l with
    | Deep.leaf _ => 1
    | Deep.node _ _ =>
      match r with
      | Deep.leaf _ => 2
      | Deep.node _ _ => 3

-- Test 3: Dependent pattern matching on equality proofs
def eqTest {α : Type} (x y : α) (h : x = y) : x = y :=
  match h with
  | rfl => rfl

-- Can we confuse the system with nested equality matches?
def nestedEqTest {α : Type} (x y z : α) (h1 : x = y) (h2 : y = z) : x = z :=
  match h1, h2 with
  | rfl, rfl => rfl

-- Test 4: Inaccessible patterns
def inaccTest {α : Type} (x : α) (h : x = x) : Nat :=
  match x, h with
  | _, rfl => 0

-- Test 5: K axiom / UIP test (should not be provable without axiom)
-- def uipTest {α : Type} (x : α) (h1 h2 : x = x) : h1 = h2 :=
--   match h1, h2 with
--   | rfl, rfl => rfl  -- This would prove UIP!

-- Test 6: Dependent matching with contradictory patterns
def contradictoryTest (n : Nat) (h : n = n + 1) : False :=
  match n, h with
  | 0, h' => by
    cases h'  -- 0 = 1, contradiction
  | m + 1, h' => by
    cases h'  -- m + 1 = m + 2, contradiction

-- Test 7: Mutual inductive pattern matching
mutual
  inductive Even : Nat → Type where
    | zero : Even 0
    | succ : {n : Nat} → Odd n → Even (n + 1)

  inductive Odd : Nat → Type where
    | succ : {n : Nat} → Even n → Odd (n + 1)
end

def evenOrOdd (n : Nat) : (Even n) ⊕ (Odd n) ⊕ Unit :=
  match n with
  | 0 => Sum.inl Even.zero
  | n + 1 => Sum.inr (Sum.inr ())  -- Incomplete, but does this compile?

-- Test 8: Pattern matching on proof-irrelevant Prop
def propMatch (P : Prop) (h1 h2 : P) : h1 = h2 :=
  rfl  -- This uses proof irrelevance, which is OK in Prop

-- But what about pattern matching?
def propPatternMatch (P : Prop) (h : P) : Nat :=
  match h with
  | _ => 0  -- Does this generate correct code?

-- Test 9: Large pattern matching (does compilation scale?)
inductive BigType where
  | c0 | c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9
  | c10 | c11 | c12 | c13 | c14 | c15 | c16 | c17 | c18 | c19

def bigMatch (b : BigType) : Nat :=
  match b with
  | .c0 => 0 | .c1 => 1 | .c2 => 2 | .c3 => 3 | .c4 => 4
  | .c5 => 5 | .c6 => 6 | .c7 => 7 | .c8 => 8 | .c9 => 9
  | .c10 => 10 | .c11 => 11 | .c12 => 12 | .c13 => 13 | .c14 => 14
  | .c15 => 15 | .c16 => 16 | .c17 => 17 | .c18 => 18 | .c19 => 19

-- Test 10: Nested pattern with partial matching
def partialNested : Option (Option Nat) → Nat
  | some (some n) => n
  | some none => 0
  | none => 1

#check overlapTest1
#check deepMatch
#check contradictoryTest
#check bigMatch
