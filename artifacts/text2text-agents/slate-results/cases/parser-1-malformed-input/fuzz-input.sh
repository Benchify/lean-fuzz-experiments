#!/bin/bash
# Parser fuzzing - malformed input test

cd "$(dirname "$0")"

echo "=== Parser Fuzzing - Malformed Inputs ==="

# Test 1: Deeply nested expressions
echo "Test 1: Deep nesting (stack overflow attempt)"
python3 -c "print('def test := ' + '(' * 5000 + '0' + ')' * 5000)" > deep_nest.lean
timeout 5 lean deep_nest.lean 2>&1 | head -20

# Test 2: Extreme identifier length
echo -e "\nTest 2: Extreme identifier length"
python3 -c "print('def ' + 'a' * 50000 + ' := 0')" > long_id.lean
timeout 5 lean long_id.lean 2>&1 | head -20

# Test 3: Unicode edge cases
echo -e "\nTest 3: Unicode edge cases"
cat > unicode_test.lean << 'EOF'
def 𝕏 := 0
def 🔥 := 1
EOF
timeout 5 lean unicode_test.lean 2>&1

# Test 4: Null bytes
echo -e "\nTest 4: Null bytes"
printf 'def test := \x00\n' > null_bytes.lean
timeout 5 lean null_bytes.lean 2>&1 | head -20

# Test 5: Malformed numbers
echo -e "\nTest 5: Malformed numbers"
cat > malformed_nums.lean << 'EOF'
def t1 := 99999999999999999999999999999999999999999999999999999999
EOF
timeout 5 lean malformed_nums.lean 2>&1

echo -e "\n=== Fuzzing complete ==="