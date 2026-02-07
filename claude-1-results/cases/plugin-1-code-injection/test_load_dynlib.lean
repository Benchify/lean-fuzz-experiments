-- Test --load-dynlib parameter for code execution
-- This is supposed to just load symbols, not initialize code
-- But does it execute constructors?

def main : IO Unit := do
  IO.println "Testing --load-dynlib parameter"
  IO.println "If plugin constructor ran, we have code execution"
