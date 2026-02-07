-- Simple Lean file to load with malicious plugin
-- Usage: lean --plugin=malicious_plugin.so test_target.lean

def harmless : Nat := 42

#check harmless

def main : IO Unit := do
  IO.println "If you see this, the plugin loaded successfully"
