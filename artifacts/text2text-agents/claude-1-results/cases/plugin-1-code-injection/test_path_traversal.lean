-- Test if plugin paths are validated
-- Try to load plugin from various malicious paths

-- These should ideally be rejected:
-- ../../../../../tmp/malicious.so
-- /tmp/../../../etc/passwd
-- ./symlink_to_malicious
-- HTTP URLs (if supported)
-- UNC paths (Windows)

def main : IO Unit := do
  IO.println "This file is just documentation"
  IO.println "Test via: lean --plugin=<malicious_path> test_path_traversal.lean"
