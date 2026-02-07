/-
MODULE A for cross-module soundness attack
-/

-- Export definitions that will be imported by module B
axiom magic_axiom : Nat = Bool

-- Hidden instance
instance : ToString Nat where
  toString := fun _ => "hidden"

-- Definition with hidden axiom usage
def sneaky : Nat := 42

-- Type alias
def MyNat := Nat

-- Proof that relies on axiom
theorem sneaky_theorem : True := trivial
