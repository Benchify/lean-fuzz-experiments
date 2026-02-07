/-
Sophisticated Attack 2: Well-Founded Recursion Bypasses
Targeting: Termination checker, accessibility predicates, decreasing arguments

Well-founded recursion is critical for soundness. Potential exploits:
- Fake termination proofs
- Accessibility predicate confusion
- Measure function bugs
- Mutual recursion termination bypass
-/

-- Test 1: Fake well-founded relation
def fakeWF : Nat → Nat → Prop := fun x y => x = y + 1

-- Claim it's well-founded (lying)
-- axiom fakeWF_wf : WellFounded fakeWF

-- If we could use this, we could define non-terminating functions
-- def loopWithFake (n : Nat) : Nat :=
--   loopWithFake (n + 1)
-- termination_by n
-- decreasing_by exact fakeWF_wf.apply n

-- Test 2: Circular measure
def circularMeasure1 (n : Nat) : Nat := circularMeasure2 n + 1
def circularMeasure2 (n : Nat) : Nat := circularMeasure1 n - 1

-- Can we use circularMeasure as termination measure?
-- def testCircular (n : Nat) : Nat :=
--   match n with
--   | 0 => 0
--   | k + 1 => testCircular (k + 1)  -- Not decreasing
-- termination_by circularMeasure1 n

-- Test 3: Mutual recursion with fake decreasing
mutual
  def mutualA (n : Nat) : Nat :=
    match n with
    | 0 => 0
    | k + 1 => mutualB k + 1

  def mutualB (n : Nat) : Nat :=
    match n with
    | 0 => 0
    | k + 1 => mutualA (k + 1)  -- Not actually decreasing!
end
termination_by mutualA n => n; mutualB n => n

-- Test 4: Accessibility predicate manipulation
-- Acc is the accessibility predicate for well-founded recursion
def fakeAcc {α : Type} (r : α → α → Prop) (x : α) : Acc r x :=
  Acc.intro x (fun y _ => fakeAcc r y)  -- Circular!

-- Can we use this to bypass termination checking?
-- def loopWithAcc (n : Nat) : Nat :=
--   @WellFounded.fix Nat (fun _ => Nat) _ _ n
--   where
--     wf := ⟨fakeAcc _⟩

-- Test 5: Decreasing by sorry
def decreaseBySorry (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => decreaseBySorry (k + 2)  -- Increasing!
termination_by n
decreasing_by sorry  -- Lying about decrease

-- Does 'sorry' in termination proof affect anything?

-- Test 6: Well-founded on empty type
def emptyWF : Empty → Empty → Prop := fun _ _ => True

instance : WellFounded emptyWF where
  apply := fun x => Empty.rec (motive := fun _ => Acc emptyWF _) x

-- Valid (trivially WF on empty type), but can we exploit it?

-- Test 7: Lexicographic order confusion
def lexBug (n m : Nat) : Nat :=
  match n, m with
  | 0, _ => 0
  | _, 0 => 0
  | n' + 1, m' + 1 => lexBug (n' + 1) m'  -- Only m decreases
termination_by (n, m)

-- Lexicographic should handle this correctly

-- Test 8: Size change principle violation
inductive Tree where
  | leaf : Nat → Tree
  | node : Tree → Tree → Tree

def treeSize : Tree → Nat
  | .leaf _ => 1
  | .node l r => 1 + treeSize l + treeSize r

-- Not decreasing on tree structure
def treeBug (t : Tree) : Nat :=
  match t with
  | .leaf n => n
  | .node l r =>
    let t' := Tree.node (Tree.node l r) (Tree.leaf 0)
    treeBug t'  -- Size increased!
termination_by treeSize t
decreasing_by sorry

-- Test 9: Nested recursion
def nested (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => nested (nested k)  -- Nested calls are tricky!
termination_by n

-- This should actually be valid (both calls decrease)

-- Test 10: Parameter vs index confusion
inductive Vec : Nat → Type where
  | nil : Vec 0
  | cons : {n : Nat} → Nat → Vec n → Vec (n + 1)

-- Recursion on index (length)
def vecSum : {n : Nat} → Vec n → Nat
  | _, .nil => 0
  | _, .cons x xs => x + vecSum xs

-- Valid, decreases on n

-- Can we confuse parameter and index?
def vecBug : (n : Nat) → Vec n → Nat
  | n, .nil => 0
  | n, .cons x xs => vecBug (n + 1) xs  -- Claim to increase n?
-- Should fail: xs has length n-1, not n+1

-- Test 11: Subterm relation manipulation
inductive Nested where
  | empty : Nested
  | wrap : List Nested → Nested

def nestedDepth : Nested → Nat
  | .empty => 0
  | .wrap xs => 1 + (xs.map nestedDepth).foldl max 0

-- Subterm relation should handle List
def nestedCount : Nested → Nat
  | .empty => 0
  | .wrap xs => xs.foldl (fun acc x => acc + nestedCount x) 0
termination_by n => n

-- Test 12: GuardedRecursion bypass attempt
-- partial def guardedLoop : Nat := guardedLoop + 1

-- Can we hide this in a guarded context?
-- def streamLoop : Nat → Stream Nat
--   | n => n :: streamLoop (n + 1)  -- Infinite stream is OK

-- Test 13: Sized types emulation
structure Sized (α : Type) where
  value : α
  size : Nat

def sizedRec {α : Type} (f : Sized α → α) (s : Sized α) : α :=
  if s.size = 0 then s.value
  else sizedRec f ⟨f s, s.size - 1⟩
termination_by s.size

-- Can we pass fake sizes?
def fakeSized : Sized Nat := ⟨0, 1000000⟩
-- #eval sizedRec (fun s => s.value + 1) fakeSized  -- Long recursion

-- Test 14: Heterogeneous mutual recursion
mutual
  inductive EvenList : Type where
    | nil : EvenList
    | cons : Nat → OddList → EvenList

  inductive OddList : Type where
    | cons : Nat → EvenList → OddList
end

mutual
  def evenLen : EvenList → Nat
    | .nil => 0
    | .cons _ odd => 1 + oddLen odd

  def oddLen : OddList → Nat
    | .cons _ even => 1 + evenLen even
end
termination_by evenLen e => e; oddLen o => o

-- Test 15: Decreasing modulo computation
def modCompute (n : Nat) : Nat :=
  let m := n * 2  -- Compute something
  match m with
  | 0 => 0
  | k + 1 => modCompute (k / 2)  -- Divide back down
termination_by n

-- Is n → n*2 → n*2/2 = n correctly handled?

-- Test 16: Using well-founded fix directly
def directFix (n : Nat) : Nat :=
  WellFounded.fix (α := Nat) (C := fun _ => Nat)
    (Nat.lt_wfRel.wf)
    (fun x rec => if x = 0 then 0 else rec (x + 1) sorry)
    n

-- Can we pass bad proofs to 'rec'?

-- Test 17: Infinite type via recursion (should fail)
-- inductive InfType where
--   | mk : (Nat → InfType) → InfType

-- This should be rejected (not strictly positive)

-- Test 18: Tricky measure with overflow
def overflowMeasure (n : Nat) : Nat :=
  if n > 1000000 then 0 else 1000000 - n

def measureOverflow (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => measureOverflow (k + 2)  -- Increases n
termination_by overflowMeasure n
decreasing_by sorry

-- Test 19: Rose tree recursion
inductive Rose (α : Type) where
  | node : α → List (Rose α) → Rose α

def roseMap {α β : Type} (f : α → β) : Rose α → Rose β
  | .node x children => .node (f x) (children.map (roseMap f))
termination_by r => r

-- Structural recursion on nested type

-- Test 20: Coinductive-style divergence
-- Can we encode divergent streams as inductive types?
structure PseudoStream where
  head : Nat
  tail : Unit → PseudoStream

def pseudoStreamFrom (n : Nat) : PseudoStream :=
  ⟨n, fun () => pseudoStreamFrom (n + 1)⟩

-- This diverges but uses thunks (Unit →)
-- #eval (pseudoStreamFrom 0).tail ()  -- Would diverge

#check mutualA
#check vecSum
#check nestedCount
#check sizedRec
#check roseMap
