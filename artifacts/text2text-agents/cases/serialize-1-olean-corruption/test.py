#!/usr/bin/env python3
"""
Case: serialize-1-olean-corruption
Category: Serialization Security
Severity: HIGH-CRITICAL

Test .olean file corruption to find deserialization bugs
"""

import os
import subprocess
import struct
import random

def create_test_lean():
    """Create a simple Lean file to compile"""
    with open("test.lean", "w") as f:
        f.write("""
def testDef : Nat := 42
theorem testTheorem : testDef = 42 := rfl
""")

def compile_lean():
    """Compile to .olean"""
    result = subprocess.run(
        ["lean", "test.lean", "-o", "test.olean"],
        capture_output=True,
        text=True
    )
    return result.returncode == 0

def corrupt_olean(filename, corruption_type):
    """Apply various corruption strategies"""
    with open(filename, "rb") as f:
        data = bytearray(f.read())
    
    if corruption_type == "flip_bits":
        # Flip random bits
        for _ in range(10):
            pos = random.randint(0, len(data) - 1)
            data[pos] ^= (1 << random.randint(0, 7))
    
    elif corruption_type == "truncate":
        # Truncate file
        data = data[:len(data) // 2]
    
    elif corruption_type == "zeros":
        # Insert zeros
        pos = len(data) // 2
        data[pos:pos] = b'\x00' * 100
    
    elif corruption_type == "ff":
        # Insert 0xFF bytes
        pos = len(data) // 2
        data[pos:pos] = b'\xFF' * 100
    
    elif corruption_type == "header":
        # Corrupt just the header
        if len(data) > 16:
            for i in range(min(16, len(data))):
                data[i] = random.randint(0, 255)
    
    with open(filename + ".corrupted", "wb") as f:
        f.write(data)

def test_corrupted(filename):
    """Test if Lean handles corrupted .olean gracefully"""
    # Try to use the corrupted file
    with open("test_import.lean", "w") as f:
        f.write("import test\n#check testDef\n")
    
    # Move corrupted file to expected location
    os.rename(filename, "test.olean")
    
    result = subprocess.run(
        ["lean", "test_import.lean"],
        capture_output=True,
        text=True,
        timeout=5
    )
    
    return result

def main():
    print("=== .olean Corruption Test ===\n")
    
    # Create and compile test file
    create_test_lean()
    if not compile_lean():
        print("Failed to compile test.lean")
        return
    
    # Back up original
    subprocess.run(["cp", "test.olean", "test.olean.orig"])
    
    corruption_types = ["flip_bits", "truncate", "zeros", "ff", "header"]
    
    for ctype in corruption_types:
        print(f"\nTest: {ctype} corruption")
        print("-" * 40)
        
        # Restore original
        subprocess.run(["cp", "test.olean.orig", "test.olean"])
        
        # Corrupt
        corrupt_olean("test.olean", ctype)
        
        try:
            result = test_corrupted("test.olean.corrupted")
            print(f"Return code: {result.returncode}")
            if result.stderr:
                print(f"Stderr: {result.stderr[:200]}")
            if "error" not in result.stderr.lower():
                print("⚠️  WARNING: No error reported for corrupted file!")
        except subprocess.TimeoutExpired:
            print("⚠️  TIMEOUT: Lean hung on corrupted file!")
        except Exception as e:
            print(f"Exception: {e}")
    
    print("\n=== Test Complete ===")

if __name__ == "__main__":
    main()