-- Test: Can metaprogramming bypass kernel type checking?
-- Goal: Try to derive False using #eval and metaprogramming

import Lean

-- Test 1: Generate False proof using meta-programming
#eval show Lean.MetaM Unit from do
  Lean.logInfo "Attempting to construct False proof via meta"
  -- Try to construct a proof of False
  let falseTy := Lean.Expr.const ``False []
  Lean.logInfo s!"False type: {falseTy}"

-- Test 2: Use macro system to generate unsound proof
macro "derive_false" : term => `(sorry)

def false_proof : False := derive_false

-- This should show an axiom warning
#check false_proof

-- Test 3: Try to use implementedBy to bypass kernel
@[implementedBy false_proof]
constant evil_false : False

-- Test 4: Runtime evaluation confusion
def runtime_false : IO False := do
  IO.println "This shouldn't be callable!"
  -- Try to confuse runtime vs kernel
  throw (IO.userError "Can't actually create False")

-- Test 5: Elab command to add axioms
elab "#add_axiom" : command => do
  Lean.logInfo "[ATTACK] Trying to add axiom through elaboration"
  -- Try to inject an axiom into the environment
  let env ← Lean.Elab.Command.getEnv
  Lean.logInfo s!"Environment has {env.constants.size} constants"

#add_axiom

-- Test 6: Tactic-generated proof
theorem false_via_tactic : False := by
  -- Can tactics bypass kernel?
  sorry

#check false_via_tactic

-- Test 7: Check if sorry is tracked
#print axioms false_via_tactic
