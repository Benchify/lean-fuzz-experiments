# Case: implementation-1-ffi-unsafe

## Category
Implementation Security - FFI/Unsafe Code

## Severity
CRITICAL (memory corruption, code execution)

## Description
Tests whether unsafe code, FFI, or external functions can:
1. Bypass kernel type checking
2. Cause memory corruption
3. Execute arbitrary code
4. Inject unsound proofs

## Attack Vectors
1. Unsafe casts between incompatible types
2. FFI functions with incorrect type signatures
3. Pointer manipulation
4. IO side effects modifying environment
5. Using unsafe code to create kernel-level proofs

## Expected Behavior
- Unsafe code should be tracked and not usable in kernel proofs
- FFI cannot bypass kernel checks
- Memory safety violations should be caught or isolated

## Obfuscation Techniques
1. **Staged compilation**: Using compile-time metaprogramming to hide unsafe code
2. **Transitive dependencies**: Unsafe code in deep dependencies
3. **Macro-generated FFI**: Generating FFI calls via macros
4. **Type confusion**: Exploiting subtyping or coercions
5. **ABI mismatches**: Declaring wrong signatures for external functions

## Running
```bash
cd cases/implementation-1-ffi-unsafe
make test
```