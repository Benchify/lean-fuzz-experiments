#!/bin/bash

# Lean 4.27.0 Native Compiler Differential Testing Script
# Compares VM execution with compiled binary execution

set -e

echo "╔══════════════════════════════════════════════════════════════╗"
echo "║  Lean 4.27.0 Native Compiler Differential Testing           ║"
echo "║  Comparing VM vs Compiled Execution                          ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo ""

TEST_FILE="native-compiler-differential-test.lean"

if [ ! -f "$TEST_FILE" ]; then
    echo "❌ ERROR: Test file not found: $TEST_FILE"
    exit 1
fi

echo "Test file: $TEST_FILE"
echo ""

# Check Lean installation
if ! command -v lean &> /dev/null; then
    echo "❌ ERROR: lean command not found"
    echo "Please ensure Lean 4 is installed and in PATH"
    exit 1
fi

LEAN_VERSION=$(lean --version | head -1)
echo "Lean version: $LEAN_VERSION"
echo ""

echo "═══════════════════════════════════════════════════════════════"
echo "STEP 1: Running Tests in VM (Interpreted)"
echo "═══════════════════════════════════════════════════════════════"
echo ""

echo "Executing: lean --run $TEST_FILE"
echo ""

if lean --run "$TEST_FILE" > vm-output.txt 2>&1; then
    echo "✓ VM execution completed successfully"
else
    VM_EXIT=$?
    echo "❌ VM execution failed with exit code: $VM_EXIT"
    cat vm-output.txt
    exit $VM_EXIT
fi

echo ""
cat vm-output.txt
echo ""

echo "═══════════════════════════════════════════════════════════════"
echo "STEP 2: Compiling to C Code"
echo "═══════════════════════════════════════════════════════════════"
echo ""

BASENAME="${TEST_FILE%.lean}"
C_FILE="${BASENAME}.c"

echo "Executing: lean --c=$C_FILE $TEST_FILE"

if lean --c="$C_FILE" "$TEST_FILE" 2>&1 | tee compile-to-c.log; then
    echo "✓ Compilation to C successful"
else
    echo "❌ Compilation to C failed"
    exit 1
fi

if [ ! -f "$C_FILE" ]; then
    echo "❌ ERROR: C file not generated: $C_FILE"
    exit 1
fi

C_SIZE=$(wc -l < "$C_FILE")
echo "✓ Generated C file: $C_FILE ($C_SIZE lines)"
echo ""

echo "═══════════════════════════════════════════════════════════════"
echo "STEP 3: Compiling C to Binary"
echo "═══════════════════════════════════════════════════════════════"
echo ""

LEAN_TOOLCHAIN="$HOME/.elan/toolchains/leanprover--lean4---v4.27.0"
LEAN_INCLUDE="$LEAN_TOOLCHAIN/include"
LEAN_LIB="$LEAN_TOOLCHAIN/lib/lean"
BINARY="${BASENAME}-compiled"

echo "Compiling with gcc..."

# Detect compiler flags needed
if gcc "$C_FILE" \
    -I"$LEAN_INCLUDE" \
    -L"$LEAN_LIB" \
    -lleanshared \
    -o "$BINARY" \
    -O2 \
    2>&1 | tee compile-to-binary.log; then
    echo "✓ Binary compilation successful"
else
    echo "❌ Binary compilation failed"
    echo ""
    echo "Trying alternative compilation flags..."

    # Try with different flags
    if gcc "$C_FILE" \
        -I"$LEAN_INCLUDE" \
        -L"$LEAN_LIB" \
        -lleanshared -lInit -lLean -lStd \
        -o "$BINARY" \
        -O2 \
        2>&1 | tee compile-to-binary-alt.log; then
        echo "✓ Binary compilation successful (alternative flags)"
    else
        echo "❌ Binary compilation failed with alternative flags"
        echo "See compile-to-binary.log for details"
        exit 1
    fi
fi

if [ ! -f "$BINARY" ]; then
    echo "❌ ERROR: Binary not generated: $BINARY"
    exit 1
fi

BINARY_SIZE=$(ls -lh "$BINARY" | awk '{print $5}')
echo "✓ Generated binary: $BINARY ($BINARY_SIZE)"
echo ""

echo "═══════════════════════════════════════════════════════════════"
echo "STEP 4: Running Compiled Binary"
echo "═══════════════════════════════════════════════════════════════"
echo ""

# Set library path
if [ "$(uname)" == "Darwin" ]; then
    export DYLD_LIBRARY_PATH="$LEAN_LIB:$DYLD_LIBRARY_PATH"
else
    export LD_LIBRARY_PATH="$LEAN_LIB:$LD_LIBRARY_PATH"
fi

echo "Executing: ./$BINARY"
echo ""

if "./$BINARY" > compiled-output.txt 2>&1; then
    echo "✓ Compiled binary execution completed successfully"
    COMPILED_EXIT=0
else
    COMPILED_EXIT=$?
    echo "❌ Compiled binary execution failed with exit code: $COMPILED_EXIT"
fi

echo ""
cat compiled-output.txt
echo ""

echo "═══════════════════════════════════════════════════════════════"
echo "STEP 5: Comparing VM vs Compiled Output"
echo "═══════════════════════════════════════════════════════════════"
echo ""

echo "Comparing outputs..."
echo ""

# Check if files are identical
if diff -u vm-output.txt compiled-output.txt > diff-output.txt; then
    echo "✓✓✓ PERFECT MATCH ✓✓✓"
    echo ""
    echo "VM and compiled outputs are IDENTICAL!"
    echo "No discrepancies found."
    echo ""
    DIFF_RESULT=0
else
    echo "⚠️⚠️⚠️ DIFFERENCES DETECTED ⚠️⚠️⚠️"
    echo ""
    echo "Differences between VM and compiled execution:"
    echo ""
    cat diff-output.txt | head -50
    echo ""
    if [ $(wc -l < diff-output.txt) -gt 50 ]; then
        echo "... (truncated, see diff-output.txt for full diff)"
    fi
    DIFF_RESULT=1
fi

echo ""
echo "═══════════════════════════════════════════════════════════════"
echo "STEP 6: Detailed Analysis"
echo "═══════════════════════════════════════════════════════════════"
echo ""

# Extract test results from both outputs
echo "Analyzing test results..."
echo ""

VM_TESTS=$(grep -c "VM result:" vm-output.txt || echo "0")
COMPILED_TESTS=$(grep -c "VM result:" compiled-output.txt || echo "0")

echo "VM executed $VM_TESTS tests"
echo "Compiled executed $COMPILED_TESTS tests"
echo ""

if [ "$VM_TESTS" != "$COMPILED_TESTS" ]; then
    echo "⚠️  WARNING: Different number of tests executed!"
    echo "   This might indicate a crash or early exit in one version."
fi

# Check for specific discrepancies
echo "Checking for specific issues..."
echo ""

# Overflow behavior
echo "Integer overflow results:"
VM_OVERFLOW=$(grep "uint64_overflow" vm-output.txt | head -1 || echo "Not found")
COMPILED_OVERFLOW=$(grep "uint64_overflow" compiled-output.txt | head -1 || echo "Not found")
echo "  VM:       $VM_OVERFLOW"
echo "  Compiled: $COMPILED_OVERFLOW"
if [ "$VM_OVERFLOW" != "$COMPILED_OVERFLOW" ]; then
    echo "  ⚠️  DIFFERENCE IN OVERFLOW BEHAVIOR!"
fi
echo ""

# Floating point
echo "Floating point results:"
VM_FLOAT=$(grep "float_sqrt" vm-output.txt | head -1 || echo "Not found")
COMPILED_FLOAT=$(grep "float_sqrt" compiled-output.txt | head -1 || echo "Not found")
echo "  VM:       $VM_FLOAT"
echo "  Compiled: $COMPILED_FLOAT"
if [ "$VM_FLOAT" != "$COMPILED_FLOAT" ]; then
    echo "  ⚠️  DIFFERENCE IN FLOATING POINT BEHAVIOR!"
fi
echo ""

# Performance-sensitive tests
echo "Optimization-sensitive test:"
VM_OPT=$(grep "loop_heavy" vm-output.txt | head -1 || echo "Not found")
COMPILED_OPT=$(grep "loop_heavy" compiled-output.txt | head -1 || echo "Not found")
echo "  VM:       $VM_OPT"
echo "  Compiled: $COMPILED_OPT"
if [ "$VM_OPT" != "$COMPILED_OPT" ]; then
    echo "  ⚠️  DIFFERENCE IN OPTIMIZED CODE BEHAVIOR!"
fi
echo ""

echo "═══════════════════════════════════════════════════════════════"
echo "SUMMARY"
echo "═══════════════════════════════════════════════════════════════"
echo ""

echo "Generated files:"
echo "  - $C_FILE: Generated C code"
echo "  - $BINARY: Compiled binary"
echo "  - vm-output.txt: VM execution output"
echo "  - compiled-output.txt: Compiled execution output"
echo "  - diff-output.txt: Differences (if any)"
echo ""

if [ $DIFF_RESULT -eq 0 ]; then
    echo "✓✓✓ RESULT: COMPILER IS CORRECT ✓✓✓"
    echo ""
    echo "The native compiler produces output identical to the VM."
    echo "No correctness issues detected."
    echo ""
    EXIT_CODE=0
else
    echo "🚨🚨🚨 RESULT: DIFFERENCES FOUND 🚨🚨🚨"
    echo ""
    echo "The native compiler produces DIFFERENT output from the VM!"
    echo ""
    echo "This could indicate:"
    echo "  1. Compiler optimization bug"
    echo "  2. Incorrect code generation"
    echo "  3. Undefined behavior in generated code"
    echo "  4. Soundness issue if proven properties are violated"
    echo ""
    echo "⚠️  MANUAL REVIEW REQUIRED!"
    echo ""
    echo "Review diff-output.txt for details."
    EXIT_CODE=1
fi

if [ $COMPILED_EXIT -ne 0 ]; then
    echo "⚠️  Additionally: Compiled binary crashed (exit code $COMPILED_EXIT)"
    echo "   This might indicate a code generation bug."
    EXIT_CODE=1
fi

echo ""
echo "═══════════════════════════════════════════════════════════════"
echo ""

# Clean up option
echo "To clean up generated files:"
echo "  rm $C_FILE $BINARY vm-output.txt compiled-output.txt diff-output.txt *.log"
echo ""

exit $EXIT_CODE
