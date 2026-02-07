#!/usr/bin/env python3
"""
Advanced Lean 4 Fuzzing Harness
Generates Lean code targeting specific vulnerability patterns
"""

import subprocess
import tempfile
import os
import random
import string
import itertools
from pathlib import Path
from typing import List, Tuple, Optional

class LeanFuzzer:
    def __init__(self, lean_path: str = "lean"):
        self.lean_path = lean_path
        self.crashes = []
        self.interesting = []

    def run_lean(self, code: str, timeout: int = 5) -> Tuple[int, str, str]:
        """Run Lean on code, return (exit_code, stdout, stderr)"""
        with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
            f.write(code)
            f.flush()
            temp_file = f.name

        try:
            result = subprocess.run(
                [self.lean_path, temp_file],
                capture_output=True,
                text=True,
                timeout=timeout
            )
            return result.returncode, result.stdout, result.stderr
        except subprocess.TimeoutExpired:
            return -1, "", "TIMEOUT"
        except Exception as e:
            return -2, "", str(e)
        finally:
            try:
                os.unlink(temp_file)
            except:
                pass

    def generate_deep_nesting(self, depth: int, pattern: str = "()") -> str:
        """Generate deeply nested expressions"""
        if pattern == "()":
            return "(" * depth + "0" + ")" * depth
        elif pattern == "lambda":
            result = "0"
            for i in range(depth):
                result = f"(fun x{i} => {result})"
            return result
        elif pattern == "match":
            result = "0"
            for i in range(depth):
                result = f"match {result} with | n => n"
            return result
        return ""

    def generate_universe_exploit(self) -> str:
        """Generate universe level manipulation attempts"""
        templates = [
            # imax tricks
            "def test : Type (imax {u} 0) := PUnit",
            "def test : Type (imax (max {u} {v}) 0) := PUnit",
            # Universe level equations
            "def test (h : {u} = {u} + 1) : False := sorry",
            # Large elimination attempts
            """inductive PropBox : Prop where
  | mk : PropBox

def test : PropBox → Type {u} := fun _ => PUnit""",
        ]
        template = random.choice(templates)
        u = random.randint(0, 5)
        v = random.randint(0, 5)
        return template.format(u=u, v=v)

    def generate_positivity_exploit(self) -> str:
        """Generate positivity checking bypass attempts"""
        templates = [
            # Hidden negative occurrence
            """def Hidden := Bad
inductive Bad where
  | mk : (Hidden → False) → Bad""",
            # Through mutual induction
            """mutual
  inductive A where | mk : B → A
  inductive B where | mk : (A → False) → B
end""",
            # Through containers
            """inductive Container (α : Type) where | mk : α → Container α
inductive Bad where | mk : Container (Bad → False) → Bad""",
        ]
        return random.choice(templates)

    def generate_quotient_exploit(self) -> str:
        """Generate quotient type exploitation attempts"""
        templates = [
            # Quotient with lying relation
            """def badRel (a b : Nat) : Prop := a = b + 1
def Q := Quot badRel
axiom lie : badRel 0 0  -- Lie about reflexivity
theorem exploit : Quot.mk badRel 0 = Quot.mk badRel 1 := Quot.sound lie""",
            # Incorrect lift
            """def Q := Quot (fun (a b : Nat) => True)
def bad_lift : Q → Nat := Quot.lift id (fun _ _ _ => sorry)
theorem exploit : bad_lift (Quot.mk _ 0) = bad_lift (Quot.mk _ 1) := sorry""",
        ]
        return random.choice(templates)

    def generate_pattern_match_exploit(self) -> str:
        """Generate pattern matching compilation exploits"""
        templates = [
            # Overlapping patterns with dependencies
            """def test (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => n
  | _ => 42""",
            # Nested dependent matching
            """def test {α : Type} (x y : α) (h1 h2 : x = y) : h1 = h2 :=
  match h1, h2 with
  | rfl, rfl => rfl""",
        ]
        return random.choice(templates)

    def generate_elaborator_exploit(self) -> str:
        """Generate elaborator/macro exploitation attempts"""
        templates = [
            # Recursive macros
            """macro "m1" : term => `(m2)
macro "m2" : term => `(m1)
def test := m1""",
            # Environment manipulation
            """elab "bad" : command => do
  return ()

bad""",
        ]
        return random.choice(templates)

    def generate_combined_exploit(self) -> str:
        """Generate combined feature exploits"""
        # Combine multiple vulnerability patterns
        parts = [
            "universe u v",
            self.generate_universe_exploit(),
            self.generate_positivity_exploit(),
            self.generate_quotient_exploit(),
        ]
        return "\n\n".join(parts)

    def fuzz_deep_nesting(self, samples: int = 100):
        """Fuzz test deep nesting attacks"""
        print(f"[*] Fuzzing deep nesting ({samples} samples)...")
        for i in range(samples):
            depth = random.randint(100, 10000)
            pattern = random.choice(["()", "lambda", "match"])
            code = f"def test := {self.generate_deep_nesting(depth, pattern)}"

            exit_code, stdout, stderr = self.run_lean(code, timeout=10)

            if exit_code == -1:
                print(f"[!] TIMEOUT at depth {depth}, pattern {pattern}")
                self.interesting.append(("timeout", depth, pattern, code))
            elif exit_code < 0 or "stack overflow" in stderr.lower() or "segfault" in stderr.lower():
                print(f"[!] CRASH at depth {depth}, pattern {pattern}")
                self.crashes.append(("crash", depth, pattern, code, stderr))

    def fuzz_universe_levels(self, samples: int = 100):
        """Fuzz test universe level manipulation"""
        print(f"[*] Fuzzing universe levels ({samples} samples)...")
        for i in range(samples):
            code = self.generate_universe_exploit()
            exit_code, stdout, stderr = self.run_lean(code)

            # Look for kernel accepts but shouldn't
            if exit_code == 0 and "sorry" not in code:
                print(f"[!] POTENTIAL SOUNDNESS BUG: Universe exploit accepted!")
                self.crashes.append(("soundness", "universe", code, stderr))

    def fuzz_positivity(self, samples: int = 100):
        """Fuzz test positivity checking"""
        print(f"[*] Fuzzing positivity checking ({samples} samples)...")
        for i in range(samples):
            code = self.generate_positivity_exploit()
            exit_code, stdout, stderr = self.run_lean(code)

            if exit_code == 0:
                print(f"[!] POTENTIAL SOUNDNESS BUG: Negative occurrence accepted!")
                self.crashes.append(("soundness", "positivity", code, stderr))

    def fuzz_quotients(self, samples: int = 100):
        """Fuzz test quotient types"""
        print(f"[*] Fuzzing quotient types ({samples} samples)...")
        for i in range(samples):
            code = self.generate_quotient_exploit()
            exit_code, stdout, stderr = self.run_lean(code)

            # Quotients with axioms are OK, but should be marked
            if exit_code == 0 and "sorry" not in code and "axiom" not in code:
                if "false" in code.lower():
                    print(f"[!] POTENTIAL SOUNDNESS BUG: Quotient exploit!")
                    self.crashes.append(("soundness", "quotient", code, stderr))

    def run_all_fuzzing(self):
        """Run all fuzzing campaigns"""
        print("[*] Starting comprehensive fuzzing campaign...")
        print(f"[*] Testing Lean at: {self.lean_path}")

        self.fuzz_deep_nesting(samples=50)
        self.fuzz_universe_levels(samples=100)
        self.fuzz_positivity(samples=100)
        self.fuzz_quotients(samples=50)

        print(f"\n[*] Fuzzing complete!")
        print(f"[*] Crashes found: {len(self.crashes)}")
        print(f"[*] Interesting cases: {len(self.interesting)}")

        return self.crashes, self.interesting

    def save_results(self, output_dir: str = "fuzz_results"):
        """Save fuzzing results"""
        Path(output_dir).mkdir(exist_ok=True)

        for i, crash in enumerate(self.crashes):
            with open(f"{output_dir}/crash_{i}.txt", "w") as f:
                f.write(str(crash))

        for i, interesting in enumerate(self.interesting):
            with open(f"{output_dir}/interesting_{i}.txt", "w") as f:
                f.write(str(interesting))

        print(f"[*] Results saved to {output_dir}/")

def main():
    fuzzer = LeanFuzzer()
    crashes, interesting = fuzzer.run_all_fuzzing()
    fuzzer.save_results("claude-2-results/fuzz_results")

    if crashes:
        print("\n[!] CRITICAL FINDINGS:")
        for crash in crashes:
            print(f"    {crash[0]}: {crash[1]}")
    else:
        print("\n[+] No critical bugs found in fuzzing")

if __name__ == "__main__":
    main()
