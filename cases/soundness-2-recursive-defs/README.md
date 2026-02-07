# Case: soundness-2-recursive-defs

## Category
Kernel Soundness - Recursion

## Severity
CRITICAL (if exploitable)

## Description
Tests for soundness bugs in recursive definitions. Non-terminating recursion or incorrect termination proofs could allow deriving False.

## Attack Vectors
1. Non-structural recursion without termination proof
2. Partial functions reaching kernel level
3. Mutual recursion with cycles
4. Well-founded recursion with fake proofs
5. Nested recursion edge cases

## Expected Behavior
- `partial` defs should not reach kernel level
- All kernel-checked recursion must prove termination
- No way to create non-terminating proofs

## Running the Test
```bash
cd cases/soundness-2-recursive-defs
make test
```