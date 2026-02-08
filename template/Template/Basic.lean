import Lean

open Lean Meta in

elab "x_term" : term => do
  return Lean.mkConst ``True

opaque n : Bool

abbrev n := sorry

elab "n_term" : term => do
  return Lean.mkConst ``True