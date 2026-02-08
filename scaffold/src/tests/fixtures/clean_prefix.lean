-- Fixture: valid Lean code (no errors), but cannot prove False.
def myNat : Nat := 42

structure MyPair (α β : Type) where
  fst : α
  snd : β

def myPair : MyPair Nat Bool := { fst := 1, snd := true }
