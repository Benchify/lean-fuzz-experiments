#!/usr/bin/env python3
"""
.olean File Corruption Fuzzer
Systematically corrupts compiled Lean object files to test deserialization robustness
"""

import subprocess
import os
import shutil
from pathlib import Path

class OleanCorruptor:
    def __init__(self, olean_file: str):
        self.olean_file = olean_file
        self.results = []

        # Read original file
        with open(olean_file, 'rb') as f:
            self.original_data = f.read()

        print(f"[*] Loaded .olean file: {olean_file} ({len(self.original_data)} bytes)")

    def test_corruption(self, name: str, corrupted_data: bytes) -> dict:
        """Test a corrupted .olean file"""
        # Write corrupted file
        test_file = self.olean_file + ".corrupted"
        with open(test_file, 'wb') as f:
            f.write(corrupted_data)

        # Create a test Lean file that imports it
        test_lean = self.olean_file.replace('.olean', '_import_test.lean')
        module_name = Path(self.olean_file).stem

        with open(test_lean, 'w') as f:
            f.write(f"import {module_name}\n")
            f.write(f"#check {module_name}.olenTest1\n")

        # Try to use the corrupted .olean
        # First, replace original with corrupted
        backup = self.olean_file + ".backup"
        shutil.copy(self.olean_file, backup)
        shutil.copy(test_file, self.olean_file)

        result = {
            'name': name,
            'exit_code': None,
            'stdout': '',
            'stderr': '',
            'detected': False
        }

        try:
            proc = subprocess.run(
                ['lean', test_lean],
                capture_output=True,
                text=True,
                timeout=5
            )
            result['exit_code'] = proc.returncode
            result['stdout'] = proc.stdout
            result['stderr'] = proc.stderr

            # Check if corruption was detected
            if 'corrupt' in proc.stderr.lower() or 'invalid' in proc.stderr.lower():
                result['detected'] = True
            elif proc.returncode != 0:
                result['detected'] = True  # Some error occurred

        except subprocess.TimeoutExpired:
            result['exit_code'] = -1
            result['stderr'] = 'TIMEOUT'
        except Exception as e:
            result['exit_code'] = -2
            result['stderr'] = str(e)
        finally:
            # Restore original
            shutil.copy(backup, self.olean_file)
            try:
                os.unlink(test_file)
                os.unlink(test_lean)
                os.unlink(backup)
            except:
                pass

        return result

    def corrupt_header(self):
        """Corrupt the file header"""
        print("[*] Testing header corruption...")

        # Corrupt first 4 bytes (magic number)
        corrupted = b'\x00\x00\x00\x00' + self.original_data[4:]
        result = self.test_corruption("header_magic", corrupted)
        self.results.append(result)

        if not result['detected']:
            print("  [!] WARNING: Header magic corruption not detected!")

        # Corrupt bytes 4-8 (possibly version)
        corrupted = self.original_data[:4] + b'\xFF\xFF\xFF\xFF' + self.original_data[8:]
        result = self.test_corruption("header_version", corrupted)
        self.results.append(result)

        if not result['detected']:
            print("  [!] WARNING: Header version corruption not detected!")

    def corrupt_random_bytes(self, count: int = 10):
        """Flip random bytes"""
        print(f"[*] Testing random byte corruption ({count} samples)...")

        import random
        for i in range(count):
            # Pick random position
            pos = random.randint(0, len(self.original_data) - 1)

            # Flip byte
            data = bytearray(self.original_data)
            data[pos] = data[pos] ^ 0xFF

            result = self.test_corruption(f"random_byte_{i}_pos_{pos}", bytes(data))
            self.results.append(result)

            if not result['detected']:
                print(f"  [!] WARNING: Byte flip at position {pos} not detected!")

    def corrupt_truncate(self):
        """Test truncated files"""
        print("[*] Testing truncation...")

        # Truncate at various points
        for fraction in [0.9, 0.75, 0.5, 0.25, 0.1]:
            size = int(len(self.original_data) * fraction)
            corrupted = self.original_data[:size]
            result = self.test_corruption(f"truncate_{int(fraction*100)}pct", corrupted)
            self.results.append(result)

            if not result['detected']:
                print(f"  [!] WARNING: {int(fraction*100)}% truncation not detected!")

    def corrupt_append(self):
        """Append garbage data"""
        print("[*] Testing appended garbage...")

        corrupted = self.original_data + b'\x00' * 1000
        result = self.test_corruption("append_garbage", corrupted)
        self.results.append(result)

        if not result['detected']:
            print("  [!] WARNING: Appended garbage not detected!")

    def corrupt_zero_out(self):
        """Zero out sections"""
        print("[*] Testing zero-out corruption...")

        # Zero out middle section
        start = len(self.original_data) // 4
        end = len(self.original_data) // 2
        data = bytearray(self.original_data)
        data[start:end] = b'\x00' * (end - start)
        result = self.test_corruption("zero_middle", bytes(data))
        self.results.append(result)

        if not result['detected']:
            print("  [!] WARNING: Middle section zeroing not detected!")

    def corrupt_swap_bytes(self):
        """Swap sections of the file"""
        print("[*] Testing byte swapping...")

        mid = len(self.original_data) // 2
        quarter = len(self.original_data) // 4

        # Swap first and second quarters
        data = bytearray(self.original_data)
        data[:quarter], data[quarter:mid] = data[quarter:mid], data[:quarter]
        result = self.test_corruption("swap_quarters", bytes(data))
        self.results.append(result)

        if not result['detected']:
            print("  [!] WARNING: Quarter swap not detected!")

    def run_all_corruptions(self):
        """Run all corruption tests"""
        print("\n[*] Starting .olean corruption testing...\n")

        self.corrupt_header()
        self.corrupt_truncate()
        self.corrupt_random_bytes(20)
        self.corrupt_append()
        self.corrupt_zero_out()
        self.corrupt_swap_bytes()

        print(f"\n[*] Corruption testing complete!")
        print(f"[*] Total tests: {len(self.results)}")

        # Count undetected
        undetected = [r for r in self.results if not r['detected']]
        print(f"[*] Undetected corruptions: {len(undetected)}")

        if undetected:
            print("\n[!] CRITICAL: The following corruptions were NOT detected:")
            for r in undetected:
                print(f"    - {r['name']}")
                print(f"      Exit code: {r['exit_code']}")
                print(f"      Stderr: {r['stderr'][:100]}")

        return self.results, undetected

def main():
    # Find the .olean file
    olean_file = "advanced-9-olean-exploit.olean"

    if not os.path.exists(olean_file):
        print(f"[!] Error: {olean_file} not found")
        print("[*] Run: lean advanced-9-olean-exploit.lean first")
        return

    corruptor = OleanCorruptor(olean_file)
    results, undetected = corruptor.run_all_corruptions()

    # Save results
    with open("olean_corruption_results.txt", "w") as f:
        f.write(f"Total tests: {len(results)}\n")
        f.write(f"Undetected: {len(undetected)}\n\n")

        for r in results:
            f.write(f"Test: {r['name']}\n")
            f.write(f"  Detected: {r['detected']}\n")
            f.write(f"  Exit code: {r['exit_code']}\n")
            f.write(f"  Stderr: {r['stderr'][:200]}\n\n")

    print("\n[*] Results saved to olean_corruption_results.txt")

if __name__ == "__main__":
    main()
