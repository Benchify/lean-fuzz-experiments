/-
Case: soundness-7-environment-manipulation
Category: Environment/State Manipulation
Severity: CRITICAL if exploitable

Test: Can metaprogramming manipulate the environment to bypass checks?
-/

import Lean

open Lean Elab Command

-- Test 1: Try to add declaration without kernel check
-- This should fail or be properly validated

elab "try_add_axiom" : command => do
  let env ← getEnv
  -- Try to add False as an axiom directly
  -- This should be rejected or properly tracked
  logInfo "Environment manipulation test"

try_add_axiom

-- Test 2: Modify existing declarations?
-- Can we change a theorem after it's been proven?

theorem myTheorem : True := trivial

-- Try to access and modify environment
elab "inspect_env" : command => do
  let env ← getEnv
  let some info := env.find? `myTheorem
    | throwError "Not found"
  logInfo s!"Found: {info.toConst.name}"

inspect_env

-- Test 3: Import manipulation
-- Can we trick the import system?

#check True

-- Test 4: Namespace/scope manipulation
namespace Hidden
  axiom dangerous : False
end Hidden

-- Can we hide this from --trust=0?

-- Test 5: Attribute manipulation
def myDef : Nat := 42

-- Can we add @[simp] or other attributes that might affect elaboration?