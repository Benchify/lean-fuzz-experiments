# Case: serialize-1-olean-corruption

## Category
Serialization Security

## Severity
HIGH-CRITICAL (memory corruption, code execution)

## Description
Tests .olean file deserialization robustness against:
- Bit flips and corruption
- Truncated files
- Malformed headers
- Invalid data structures

## Attack Vectors
1. Corrupted .olean files causing crashes
2. Deserialization bugs leading to memory corruption
3. Type confusion from malformed serialized data
4. Arbitrary code execution via corrupted bytecode
5. Axiom injection through file manipulation

## Expected Behavior
Lean should:
- Detect corrupted .olean files
- Report clear errors
- NOT crash or hang
- NOT execute arbitrary code
- NOT allow soundness violations

## Obfuscation Techniques
Attackers might hide .olean corruption through:
1. **Partial corruption**: Only corrupting specific fields while keeping file parseable
2. **Checksum bypass**: If checksums exist, crafting collisions
3. **Version mismatch**: Using .olean from different Lean versions
4. **Dependency poisoning**: Corrupting transitive dependencies
5. **Race conditions**: Modifying .olean files during compilation
6. **Cache poisoning**: Injecting into build cache/package managers

## Running
```bash
cd cases/serialize-1-olean-corruption
python3 test.py
```