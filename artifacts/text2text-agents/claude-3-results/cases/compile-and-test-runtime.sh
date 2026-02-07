#!/bin/bash

# Lean 4.27.0 C Runtime Exploitation - Compilation and Testing Script
# This script attempts to compile and run the runtime exploitation tests

set -e  # Exit on error

echo "╔══════════════════════════════════════════════════════════════╗"
echo "║  Lean 4.27.0 C Runtime Exploitation Test                    ║"
echo "║  Compilation and Execution Script                           ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo ""

# Detect Lean installation
LEAN_TOOLCHAIN="$HOME/.elan/toolchains/leanprover--lean4---v4.27.0"

if [ ! -d "$LEAN_TOOLCHAIN" ]; then
    echo "❌ ERROR: Lean 4.27.0 not found at $LEAN_TOOLCHAIN"
    echo ""
    echo "Please install Lean 4.27.0:"
    echo "  elan toolchain install leanprover/lean4:v4.27.0"
    exit 1
fi

LEAN_INCLUDE="$LEAN_TOOLCHAIN/include"
LEAN_LIB="$LEAN_TOOLCHAIN/lib/lean"

if [ ! -f "$LEAN_INCLUDE/lean/lean.h" ]; then
    echo "❌ ERROR: lean.h not found at $LEAN_INCLUDE/lean/lean.h"
    exit 1
fi

if [ ! -f "$LEAN_LIB/libleanshared.dylib" ] && [ ! -f "$LEAN_LIB/libleanshared.so" ]; then
    echo "❌ ERROR: Lean shared library not found in $LEAN_LIB"
    exit 1
fi

echo "✓ Found Lean installation"
echo "  Include: $LEAN_INCLUDE"
echo "  Library: $LEAN_LIB"
echo ""

# Compile the exploitation test
echo "═══════════════════════════════════════════════════════════════"
echo "STEP 1: Compiling C Runtime Exploitation Test"
echo "═══════════════════════════════════════════════════════════════"
echo ""

SOURCE_FILE="runtime-exploit-real.c"
OBJECT_FILE="runtime-exploit-real.o"
EXECUTABLE="runtime-exploit"

echo "Compiling $SOURCE_FILE..."

# Try to compile
if gcc -c "$SOURCE_FILE" \
    -I"$LEAN_INCLUDE" \
    -o "$OBJECT_FILE" \
    -Wall -Wextra \
    2>&1 | tee compile.log; then
    echo "✓ Compilation successful"
else
    echo "❌ Compilation failed! See compile.log for details"
    echo ""
    echo "Common issues:"
    echo "  - Missing function declarations"
    echo "  - Incorrect header paths"
    echo "  - API changes in Lean 4.27.0"
    echo ""
    echo "Attempting to extract useful info from errors..."
    grep -E "error:|warning:|undefined" compile.log || true
    exit 1
fi

echo ""
echo "Linking with Lean runtime..."

# Detect platform
if [ "$(uname)" == "Darwin" ]; then
    LEAN_SHARED_LIB="$LEAN_LIB/libleanshared.dylib"
else
    LEAN_SHARED_LIB="$LEAN_LIB/libleanshared.so"
fi

if gcc "$OBJECT_FILE" \
    -L"$LEAN_LIB" \
    -lleanshared \
    -o "$EXECUTABLE" \
    2>&1 | tee link.log; then
    echo "✓ Linking successful"
else
    echo "❌ Linking failed! See link.log for details"
    exit 1
fi

echo ""
echo "═══════════════════════════════════════════════════════════════"
echo "STEP 2: Running Exploitation Tests"
echo "═══════════════════════════════════════════════════════════════"
echo ""

# Set library path
if [ "$(uname)" == "Darwin" ]; then
    export DYLD_LIBRARY_PATH="$LEAN_LIB:$DYLD_LIBRARY_PATH"
else
    export LD_LIBRARY_PATH="$LEAN_LIB:$LD_LIBRARY_PATH"
fi

echo "Executing $EXECUTABLE..."
echo ""

if "./$EXECUTABLE" 2>&1 | tee execution.log; then
    EXIT_CODE=0
else
    EXIT_CODE=$?
fi

echo ""
echo "═══════════════════════════════════════════════════════════════"
echo "RESULTS ANALYSIS"
echo "═══════════════════════════════════════════════════════════════"
echo ""

if [ $EXIT_CODE -ne 0 ]; then
    echo "⚠️  Program exited with code $EXIT_CODE"
    echo ""
    if [ $EXIT_CODE -eq 139 ] || [ $EXIT_CODE -eq 11 ]; then
        echo "🚨 SEGMENTATION FAULT DETECTED!"
        echo "   This indicates MEMORY CORRUPTION vulnerability!"
        echo "   One or more exploits succeeded in corrupting memory."
    elif [ $EXIT_CODE -eq 134 ] || [ $EXIT_CODE -eq 6 ]; then
        echo "🚨 ABORT/ASSERTION FAILURE DETECTED!"
        echo "   This might indicate a runtime check caught corruption."
    else
        echo "⚠️  Unexpected exit code: $EXIT_CODE"
    fi
else
    echo "✓ Program completed without crashing"
    echo ""
    echo "Analyzing output for successful exploits..."
    echo ""

    if grep -q "\[SUCCESS\]" execution.log; then
        echo "🚨 SUCCESSFUL EXPLOITS FOUND:"
        grep "\[SUCCESS\]" execution.log
        echo ""
        echo "⚠️  Memory corruption vulnerabilities detected!"
    else
        echo "✓ No successful exploits detected"
    fi

    if grep -q "\[CRITICAL\]" execution.log; then
        echo ""
        echo "🚨 CRITICAL VULNERABILITIES FOUND:"
        grep "\[CRITICAL\]" execution.log
    fi

    if grep -q "\[FAILED\]" execution.log; then
        echo ""
        echo "✓ Attacks that were blocked:"
        grep "\[FAILED\]" execution.log | head -5
        echo "   ... (use 'cat execution.log' for full output)"
    fi
fi

echo ""
echo "═══════════════════════════════════════════════════════════════"
echo "SUMMARY"
echo "═══════════════════════════════════════════════════════════════"
echo ""
echo "Output files:"
echo "  - compile.log: Compilation output"
echo "  - link.log: Linking output"
echo "  - execution.log: Execution output"
echo ""
echo "Executable: $EXECUTABLE"
echo ""

if [ $EXIT_CODE -eq 0 ]; then
    echo "Overall result: Tests completed"
else
    echo "Overall result: Program crashed (potential vulnerability!)"
fi

echo ""
echo "Next steps:"
echo "  1. Review execution.log for detailed output"
echo "  2. Check for CRITICAL or SUCCESS markers"
echo "  3. If crashes occurred, investigate with debugger:"
echo "     lldb ./$EXECUTABLE"
echo "     or"
echo "     gdb ./$EXECUTABLE"
echo ""

exit $EXIT_CODE
