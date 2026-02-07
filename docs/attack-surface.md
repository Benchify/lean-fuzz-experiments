# Lean 4 Attack Surface Analysis

## Overview

This document maps the attack surface of Lean 4 from a security perspective, identifying components that could be exploited for soundness violations or implementation vulnerabilities.

## Architecture Overview

Lean 4 consists of several major components:

```
User Input (.lean files)
    ↓
Parser (Lean syntax → AST)
    ↓
Elaborator (AST → Typed Expressions)
    ↓
Kernel (Type Checking)
    ↓
Code Generation (C/LLVM) + Interpreter
    ↓
Execution / .olean serialization
```

## Attack Surface Components

### 1. Parser
**Entry Point**: Lean source code files (.lean)
**Risk Level**: HIGH
**Attack Vectors**:
- Malformed syntax causing crashes
- Buffer overflows in string/number parsing
- Stack overflow from deeply nested expressions
- Integer overflow in size calculations
- Unicode/encoding edge cases

**Trust Boundary**: Untrusted user input → Trusted AST

### 2. Elaborator
**Entry Point**: AST from parser
**Risk Level**: CRITICAL
**Attack Vectors**:
- Type system bypasses through clever elaboration
- Metaprogramming/macro soundness bugs
- Unification algorithm bugs
- Type class resolution infinite loops
- Implicit argument handling bugs

**Trust Boundary**: Untrusted AST → Kernel-level terms

### 3. Kernel
**Entry Point**: Elaborated expressions
**Risk Level**: CRITICAL
**Attack Vectors**:
- Universe level inconsistencies
- Reduction bugs in type checking
- Definitional equality bugs
- Inductive type construction bugs
- Axiom injection through bugs

**Trust Boundary**: THE CORE TRUST BOUNDARY - kernel must be sound

### 4. Code Generation
**Entry Point**: Kernel-checked definitions
**Risk Level**: MEDIUM-HIGH
**Attack Vectors**:
- Miscompilation leading to runtime type confusion
- Memory safety bugs in generated C code
- UB in C codegen breaking Lean's guarantees
- LLVM backend bugs

**Trust Boundary**: Safe Lean code → C/LLVM (may contain UB)

### 5. Interpreter/VM
**Entry Point**: Compiled bytecode
**Risk Level**: MEDIUM-HIGH
**Attack Vectors**:
- VM escape through bytecode bugs
- Type confusion in interpreter
- Memory corruption in runtime
- FFI boundary violations

### 6. Serialization (.olean files)
**Entry Point**: Compiled module files
**Risk Level**: HIGH
**Attack Vectors**:
- Deserialization bugs allowing arbitrary code
- Type confusion from corrupted .olean
- Malformed data causing crashes
- Axiom injection through file corruption

**Trust Boundary**: Filesystem → Trusted module state

### 7. LSP Server
**Entry Point**: LSP messages
**Risk Level**: MEDIUM
**Attack Vectors**:
- Resource exhaustion (DoS)
- Information disclosure
- Command injection if handling external tools

## High-Priority Testing Targets

1. **Kernel Soundness** - Can we derive False without axioms?
2. **Elaborator Soundness** - Can elaboration create ill-typed kernel terms?
3. **Parser Robustness** - Crashes, hangs, memory corruption
4. **Serialization Safety** - .olean corruption attacks
5. **Resource Exhaustion** - Stack/memory/timeout bypasses
6. **VM/Codegen Safety** - Type confusion, memory safety

## Known Mitigations in Lean 4

- Small trusted kernel (compared to elaborator)
- Trust levels (`--trust=0` forces full kernel checking)
- Memory/timeout limits (`-M`, `-T` flags)
- Separate elaboration and checking phases

## Testing Strategy

For each component:
1. Black-box fuzzing with malformed inputs
2. Property-based testing for soundness
3. Differential testing (kernel vs VM, different trust levels)
4. Manual code review of critical paths
5. Exploit development for confirmed bugs