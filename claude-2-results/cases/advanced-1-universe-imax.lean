/-
Advanced Test 1: Universe imax manipulation
Attempting to exploit universe level imax (impredicative max) semantics

The imax operator in Lean: imax u 0 = 0, imax u (v+1) = max u (v+1)
This is used for dependent function types where the codomain might be Prop

Exploit vector: Can we trick the kernel into thinking a Type lives in Prop?
-/

universe u v w

-- Test 1: imax with polymorphic levels
-- Trying to create a Type that kernel thinks is Prop
def imaxTrick1 : Type (imax u 0) := PUnit

-- Test 2: Nested imax
def imaxTrick2 : Type (imax (imax u v) 0) := PUnit

-- Test 3: imax with max interaction
-- imax (max u v) w vs max (imax u w) (imax v w)
def imaxMaxTest {α : Type u} {β : Type v} :
  Type (imax (max u v) 0) := α × β

-- Test 4: Try to large-eliminate using imax confusion
inductive PropBox : Prop where
  | mk : PropBox

-- Can we convince the system this is actually in Type?
def attemptLargeElim : PropBox → Type (imax u 0) :=
  fun _ => PUnit

-- Test 5: Universe level substitution trick
def substTrick (α : Type u) : Type (imax u 0) :=
  α → PUnit

-- If we instantiate with Prop, we get Prop → PUnit : Type 0
-- But we declared the result at imax u 0
-- With u := 0, imax 0 0 = 0, so this might create confusion
def instantiated := substTrick Prop

-- Test 6: Try to build False using universe confusion
-- If we could somehow large-eliminate from Prop by confusing levels...
inductive TrickBox (α : Type u) : Type (imax u 0) where
  | mk : α → TrickBox α

-- Test 7: Circular universe level constraints
-- Can we create unsatisfiable constraints that pass kernel?
def circularLevels :
  (α : Type u) → (β : Type v) →
  (u = v) → (v = u + 1) → False :=
  fun _ _ _ _ => sorry  -- Actually unsolvable, but does kernel catch it?

#check circularLevels
#check imaxTrick1
#check attemptLargeElim
