#!/bin/bash

# Run all subtle memory corruption tests
# This script systematically tests every exploitation angle

set -e

RESULTS_DIR="./test_results"
mkdir -p "$RESULTS_DIR"

echo "========================================"
echo "Subtle Memory Corruption Test Suite"
echo "========================================"
echo ""

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

run_test() {
    local test_name=$1
    local test_file=$2
    local result_file="$RESULTS_DIR/${test_name}.txt"

    echo -e "${YELLOW}Running: $test_name${NC}"
    echo "Test: $test_name" > "$result_file"
    echo "File: $test_file" >> "$result_file"
    echo "========================================" >> "$result_file"

    set +e
    lake env lean "$test_file" >> "$result_file" 2>&1
    local exit_code=$?
    set -e

    echo "Exit code: $exit_code" >> "$result_file"

    if [ $exit_code -eq 0 ]; then
        echo -e "${GREEN}✓ Completed (exit 0)${NC}"
    elif [ $exit_code -eq 139 ]; then
        echo -e "${RED}✗ Segfault (exit 139)${NC}"
    else
        echo -e "${YELLOW}⚠ Exit code: $exit_code${NC}"
    fi

    echo ""
    return $exit_code
}

# Track results
TOTAL=0
PASSED=0
CRASHED=0
FAILED=0

echo "=== INFORMATION DISCLOSURE TESTS ==="
echo ""

run_test "identity_leak" "test_identity_leak.lean" && PASSED=$((PASSED+1)) || [ $? -eq 139 ] && CRASHED=$((CRASHED+1)) || FAILED=$((FAILED+1))
TOTAL=$((TOTAL+1))

run_test "equality_leak" "test_equality_leak.lean" && PASSED=$((PASSED+1)) || [ $? -eq 139 ] && CRASHED=$((CRASHED+1)) || FAILED=$((FAILED+1))
TOTAL=$((TOTAL+1))

run_test "timing_oracle" "test_timing_oracle.lean" && PASSED=$((PASSED+1)) || [ $? -eq 139 ] && CRASHED=$((CRASHED+1)) || FAILED=$((FAILED+1))
TOTAL=$((TOTAL+1))

echo "=== SIDE EFFECT TESTS ==="
echo ""

run_test "side_effects" "test_side_effects.lean" && PASSED=$((PASSED+1)) || [ $? -eq 139 ] && CRASHED=$((CRASHED+1)) || FAILED=$((FAILED+1))
TOTAL=$((TOTAL+1))

echo "=== SILENT TYPE CONFUSION TESTS ==="
echo ""

run_test "compatible_layouts" "test_compatible_layouts.lean" && PASSED=$((PASSED+1)) || [ $? -eq 139 ] && CRASHED=$((CRASHED+1)) || FAILED=$((FAILED+1))
TOTAL=$((TOTAL+1))

echo "=== GARBAGE COLLECTOR TESTS ==="
echo ""

run_test "gc_interaction" "test_gc_interaction.lean" && PASSED=$((PASSED+1)) || [ $? -eq 139 ] && CRASHED=$((CRASHED+1)) || FAILED=$((FAILED+1))
TOTAL=$((TOTAL+1))

echo "=== COVERT CHANNEL TESTS ==="
echo ""

run_test "crash_location_channel" "test_crash_location_channel.lean" && PASSED=$((PASSED+1)) || [ $? -eq 139 ] && CRASHED=$((CRASHED+1)) || FAILED=$((FAILED+1))
TOTAL=$((TOTAL+1))

echo "=== VM INTERNALS TESTS ==="
echo ""

run_test "vm_probing" "test_vm_probing.lean" && PASSED=$((PASSED+1)) || [ $? -eq 139 ] && CRASHED=$((CRASHED+1)) || FAILED=$((FAILED+1))
TOTAL=$((TOTAL+1))

echo ""
echo "========================================"
echo "TEST SUITE COMPLETE"
echo "========================================"
echo ""
echo "Total tests: $TOTAL"
echo -e "${GREEN}Passed:      $PASSED${NC}"
echo -e "${RED}Crashed:     $CRASHED${NC}"
echo -e "${YELLOW}Failed:      $FAILED${NC}"
echo ""
echo "Results saved to: $RESULTS_DIR/"
echo ""

# Generate summary report
SUMMARY_FILE="$RESULTS_DIR/SUMMARY.txt"
echo "Subtle Memory Corruption Test Suite - Summary" > "$SUMMARY_FILE"
echo "=============================================" >> "$SUMMARY_FILE"
echo "" >> "$SUMMARY_FILE"
echo "Total tests: $TOTAL" >> "$SUMMARY_FILE"
echo "Passed:      $PASSED" >> "$SUMMARY_FILE"
echo "Crashed:     $CRASHED" >> "$SUMMARY_FILE"
echo "Failed:      $FAILED" >> "$SUMMARY_FILE"
echo "" >> "$SUMMARY_FILE"
echo "Individual Test Results:" >> "$SUMMARY_FILE"
echo "========================" >> "$SUMMARY_FILE"

for result in "$RESULTS_DIR"/*.txt; do
    if [ -f "$result" ] && [ "$result" != "$SUMMARY_FILE" ]; then
        test_name=$(basename "$result" .txt)
        exit_code=$(grep "Exit code:" "$result" | cut -d' ' -f3)
        echo "$test_name: exit $exit_code" >> "$SUMMARY_FILE"
    fi
done

echo ""
echo "Summary report: $SUMMARY_FILE"
echo ""

# Analysis
echo "=== ANALYSIS ==="
echo ""

if [ $PASSED -gt 0 ]; then
    echo -e "${GREEN}$PASSED tests completed successfully${NC}"
    echo "These tests demonstrate exploitation techniques that don't crash immediately"
    echo ""
fi

if [ $CRASHED -gt 0 ]; then
    echo -e "${RED}$CRASHED tests triggered segfaults${NC}"
    echo "Crashes indicate exploitation was detected/prevented"
    echo ""
fi

if [ $FAILED -gt 0 ]; then
    echo -e "${YELLOW}$FAILED tests failed with other errors${NC}"
    echo ""
fi

echo "For detailed results, see files in $RESULTS_DIR/"
echo ""

# Check for key findings
echo "=== KEY FINDINGS ==="
echo ""

if grep -q "VULNERABILITY" "$RESULTS_DIR"/*.txt 2>/dev/null; then
    echo -e "${RED}⚠ VULNERABILITIES DETECTED${NC}"
    echo "The following vulnerabilities were found:"
    grep -h "VULNERABILITY" "$RESULTS_DIR"/*.txt | sort | uniq
    echo ""
fi

if grep -q "LEAK" "$RESULTS_DIR"/*.txt 2>/dev/null; then
    echo -e "${YELLOW}⚠ INFORMATION LEAKS DETECTED${NC}"
    echo "The following leaks were found:"
    grep -h "LEAK" "$RESULTS_DIR"/*.txt | sort | uniq
    echo ""
fi

if grep -q "Address sanitization" "$RESULTS_DIR"/*.txt 2>/dev/null; then
    echo -e "${GREEN}✓ ADDRESS SANITIZATION CONFIRMED${NC}"
    echo "Address sanitization is preventing memory address disclosure"
    echo ""
fi

echo "========================================"
echo "END OF TEST SUITE"
echo "========================================"
