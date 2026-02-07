# Case: parser-1-malformed-input

## Category
Parser Robustness / Implementation Security

## Severity
HIGH (crashes/hangs), MEDIUM (DoS)

## Description
Fuzzing the Lean parser with malformed and edge-case inputs to find:
- Crashes (memory corruption)
- Hangs (infinite loops)
- Resource exhaustion
- Assertion failures

## Attack Vectors
1. Deeply nested expressions (stack overflow)
2. Extreme identifier lengths (buffer overflow)
3. Unicode edge cases (encoding bugs)
4. Null bytes and control characters
5. Integer overflow in number parsing
6. Malformed string literals

## Expected Behavior
Parser should handle all malformed input gracefully without:
- Crashing
- Hanging indefinitely
- Memory corruption
- Resource exhaustion beyond reasonable limits

## Running the Test
```bash
cd cases/parser-1-malformed-input
./fuzz-input.sh
```

## Potential Obfuscation Techniques by Attackers
Attackers might try to hide parser exploitation through:
1. **Whitespace padding**: Embedding malicious patterns in legitimate-looking whitespace
2. **Comment hiding**: Placing crash-inducing patterns in comments
3. **Macro expansion**: Using macros to generate malformed input at elaboration time
4. **Unicode normalization**: Using different Unicode forms (NFC/NFD) to bypass filters
5. **Incremental compilation**: Splitting attack across multiple files
6. **LSP messages**: Sending malformed input via LSP rather than files