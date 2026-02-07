# Subtle Memory Corruption Exploitation Tests

This directory contains comprehensive tests exploring **subtle exploitation techniques** for the Lean VM memory corruption vulnerability (VM-TYPECONF-001). These tests go beyond simple crashes to investigate information disclosure, side channels, and silent type confusion.

## Test Categories

### 1. Information Disclosure (`test_identity_leak.lean`, `test_equality_leak.lean`)
Tests whether type confusion can leak information without dereferencing:
- **Identity transmutation**: Round-trip type conversions
- **Equality oracles**: Using equality checks to infer secrets
- **Value preservation**: Type confusion without crashes

**Key Questions**:
- Can we transmute types back and forth without crash?
- Does equality checking dereference or use value comparison?
- Can we build an oracle to guess secret values?

### 2. Timing Attacks (`test_timing_oracle.lean`)
Tests whether crash timing characteristics leak information:
- **Crash timing measurement**: Do different values crash at different times?
- **Operation timing differences**: Do different operations have different timings?
- **Statistical analysis**: Can we reliably measure timing variations?
- **Side-channel exfiltration**: Can we infer secrets from timing?

**Key Questions**:
- Do crashes have measurable timing variations?
- Can timing be used as a covert channel?
- Is statistical timing analysis viable?

### 3. Side Effects Before Crash (`test_side_effects.lean`)
Tests what executes between `unsafeCast` and the segfault:
- **Crash window analysis**: What operations succeed before crash?
- **Conditional paths**: Can we avoid crash in some code paths?
- **Exfiltration before crash**: Can we extract data before triggering crash?
- **Partial computations**: Can we get partial results?

**Key Questions**:
- When exactly does the crash occur?
- Can we do useful work before crash?
- Can attackers exfiltrate data before triggering segfault?

### 4. Silent Type Confusion (`test_compatible_layouts.lean`)
Tests type confusion between types with compatible memory layouts:
- **Structure layout matching**: Same-layout structures
- **Primitive type confusion**: Nat, Int, Bool conversions
- **Privacy violations**: Accessing private fields through wrong type
- **Authentication bypass**: Role confusion attacks

**Key Questions**:
- Can type confusion succeed without crashes?
- Are privacy modifiers bypassed?
- Can authentication be circumvented?

### 5. Garbage Collector Exploitation (`test_gc_interaction.lean`)
Tests how GC interacts with type-confused pointers:
- **GC scanning**: Does GC correctly handle confused types?
- **Use-after-free**: Can we access freed memory?
- **Double-free**: Can confused pointers cause double-free?
- **Memory leaks**: Does type confusion prevent GC tracing?
- **Object pinning**: Does GC move objects?

**Key Questions**:
- Does GC correctly trace type-confused pointers?
- Can we trigger use-after-free?
- Is memory corruption possible through GC interaction?

### 6. Covert Channels (`test_crash_location_channel.lean`)
Tests crash location/pattern as information exfiltration channel:
- **Crash location encoding**: Different locations encode different values
- **Stack trace exfiltration**: Stack depth encodes data
- **Crash sequence**: Multiple crashes transmit message
- **Exception messages**: Do error messages leak information?

**Key Questions**:
- Can crash location leak information?
- Can we encode data in crash patterns?
- Is exfiltration via controlled crashes viable?

### 7. VM Internals Probing (`test_vm_probing.lean`)
Tests whether we can infer VM internal structure:
- **Object layout**: Memory allocation patterns
- **Alignment**: Object alignment detection
- **Type tags**: Internal type representation
- **Immediate vs boxed**: Value encoding strategy
- **Reference equality**: Object identity vs value equality

**Key Questions**:
- Can we infer VM memory layout?
- Are type tags discoverable?
- Does address sanitization prevent all probing?

## Running the Tests

### Run All Tests
```bash
./run_all_tests.sh
```

This will:
- Run all 8 test categories
- Save results to `./test_results/`
- Generate a summary report
- Highlight key findings (vulnerabilities, leaks, defenses)

### Run Individual Tests
```bash
lake env lean test_identity_leak.lean
lake env lean test_timing_oracle.lean
# etc.
```

### Expected Outcomes

| Test | Expected Result | Significance |
|------|----------------|--------------|
| `test_identity_leak.lean` | Exit 0 (success) | Type transmutation works without crash |
| `test_equality_leak.lean` | Exit 0 or 139 | Depends on equality implementation |
| `test_timing_oracle.lean` | Exit 0 or 139 | Timing measurements may succeed |
| `test_side_effects.lean` | Exit 0 or 139 | Demonstrates crash window |
| `test_compatible_layouts.lean` | Exit 0 (success) | **CRITICAL**: Silent type confusion |
| `test_gc_interaction.lean` | Exit 0 or 139 | GC behavior with confused types |
| `test_crash_location_channel.lean` | Exit 139 (crash) | Demonstrates covert channel |
| `test_vm_probing.lean` | Exit 0 (success) | Address sanitization prevents probing |

## Key Findings

### ✓ Confirmed Defenses
1. **Address Sanitization**: `unsafeCast` returns 0 instead of real addresses
2. **Immediate Crashes**: Most dereferences cause immediate segfault
3. **GC Robustness**: Garbage collector handles type confusion correctly

### ⚠ Vulnerabilities Discovered
1. **Silent Type Confusion**: Compatible-layout structures can be confused without crash
2. **Privacy Bypass**: Private fields accessible through type confusion
3. **Information Leakage**: Value preservation through non-dereferencing operations
4. **Crash Window**: Operations execute between cast and crash
5. **Covert Channels**: Crash location/pattern can encode information

### 🔴 Critical Risks
1. **Authentication Bypass**: Role confusion in same-layout structures
2. **Data Exfiltration**: Values extracted before crash
3. **Denial of Service**: Repeated crashes through type confusion
4. **Supply Chain**: Subtle bugs hard to detect in code review

## Analysis

### What Works (Exploitation Succeeds)
- ✅ Type transmutation without dereferencing
- ✅ Silent confusion of compatible structures
- ✅ Privacy violation through layout matching
- ✅ Exfiltration before crash via non-dereferencing operations

### What Fails (Defenses Work)
- ❌ Memory address disclosure (sanitized to 0)
- ❌ Direct memory manipulation (no addresses available)
- ❌ Reliable timing oracle (too much noise)
- ❌ GC exploitation (robust object tracking)

### The Crash Window
The critical finding is that **crashes don't occur at `unsafeCast`** but rather at the **first dereference operation**. This creates a window where:
1. Type confusion has already occurred
2. Values can be inspected via casting operations
3. Data can be exfiltrated
4. Conditional paths can avoid crash

This window makes the vulnerability more exploitable than initially thought.

## Threat Scenarios

### Scenario 1: Supply Chain Attack
Malicious package publishes code with subtle type confusion:
```lean
unsafe def processData (input : UserData) : IO Result := do
  -- Type confuse to bypass validation
  let bypassed : ValidatedData := unsafeCast input
  -- Use without validation (compatible layout)
  processValidatedData bypassed
```

**Impact**: Validation bypass, no crash, hard to detect

### Scenario 2: Authentication Bypass
```lean
structure User where
  isAdmin : Bool
  name : String

structure Admin where
  isAdmin : Bool
  name : String

unsafe def elevatePrivileges (user : User) : Admin :=
  unsafeCast user  -- Works if isAdmin=true!
```

**Impact**: Role confusion, privilege escalation

### Scenario 3: Information Exfiltration
```lean
unsafe def exfiltrateSecret (secret : Nat) : IO Unit := do
  let confused : String := unsafeCast secret
  let recovered : Nat := unsafeCast confused
  -- Exfiltrate recovered value before crash
  sendToAttacker recovered
  -- Now crash (but secret already stolen)
  let _ := confused.length
```

**Impact**: Data theft before detection

## Recommendations

### For Users
1. **Avoid `unsafe` code** unless absolutely necessary
2. **Audit dependencies** that use `unsafe` keyword
3. **Use linters** to flag suspicious unsafe patterns
4. **Isolate unsafe code** in minimal, well-tested modules

### For Implementers
1. **Runtime type checks** even in unsafe mode
2. **Stronger sanitization** beyond address zeroing
3. **Capability system** for unsafe operations
4. **Audit logging** when unsafe code executes

### For Package Managers
1. **Flag unsafe packages** in registry
2. **Require security audits** for unsafe code
3. **Dependency analysis** for transitive unsafe usage

## Conclusion

While Lean's address sanitization prevents direct memory exploitation, **subtle attack vectors remain**:
- Silent type confusion for compatible layouts
- Information disclosure through non-dereferencing operations
- Crash window allowing partial exploitation
- Covert channels via crash behavior

The overall risk level is **MODERATE** for regular use, but **HIGH** in adversarial environments or security-critical applications.

## Related Documentation

- [MEMORY_CORRUPTION_DEEPDIVE.md](../../MEMORY_CORRUPTION_DEEPDIVE.md) - Comprehensive theoretical analysis
- [COMPLETE_AUDIT_SUMMARY.md](../../COMPLETE_AUDIT_SUMMARY.md) - Full audit summary
- [FINDINGS.md](../../FINDINGS.md) - Phase 1 findings including VM-TYPECONF-001

---

**Test Suite Version**: 1.0
**Last Updated**: 2026-01-31
**Test Coverage**: 8 categories, 50+ individual test cases
