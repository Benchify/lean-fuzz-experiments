/-
MODULE B - imports A and tries to exploit cross-module boundary
-/

import CrossModuleAttackA

-- Try to exploit definitions from A
def use_sneaky : Nat := CrossModuleAttackA.sneaky

-- Try to use the magic axiom
-- def exploit_magic : Bool := cast CrossModuleAttackA.magic_axiom 0

-- Conflicting instance?
instance : ToString Nat where
  toString := fun n => toString n

-- Using type alias - does it preserve axioms?
def use_alias : CrossModuleAttackA.MyNat := 42

-- Can we observe which ToString instance is used?
#eval toString (42 : Nat)
