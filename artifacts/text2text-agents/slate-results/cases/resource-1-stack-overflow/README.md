# Case: resource-1-stack-overflow

## Category
Resource Exhaustion - Stack Overflow

## Severity
MEDIUM-HIGH (DoS, potential crash)

## Description
Tests for stack overflow vulnerabilities through:
- Deeply nested expressions
- Recursive type definitions
- Deep function application chains
- Pattern matching depth

## Expected Behavior
Lean should either:
1. Handle deep nesting within reasonable limits
2. Provide clear error messages for exceeded limits
3. NOT crash or corrupt memory

## Attack Obfuscation Techniques
Attackers could hide stack overflow attacks via:
1. **Tactic-generated terms**: Using tactics/macros to build deep terms incrementally
2. **Type-level recursion**: Hiding depth in type computations rather than terms
3. **Mutual dependencies**: Distributing depth across multiple mutually recursive definitions
4. **Elaboration-time expansion**: Terms that look shallow but expand deeply during elaboration
5. **Import chains**: Deep dependency chains across multiple files

## Running
```bash
cd cases/resource-1-stack-overflow
make test
```