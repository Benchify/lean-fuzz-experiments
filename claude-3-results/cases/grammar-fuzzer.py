#!/usr/bin/env python3
"""
Grammar-Based Fuzzer for Lean 4
Generates syntactically valid but semantically malicious Lean code

This fuzzer targets:
1. Parser edge cases
2. Elaborator crashes
3. Kernel bypass attempts
4. Type checker edge cases
5. Resource exhaustion
"""

import random
import string
import subprocess
import os
from typing import List

class LeanFuzzer:
    def __init__(self):
        self.fuzz_iterations = 1000
        self.crash_count = 0
        self.timeout_count = 0
        self.output_dir = "fuzz_outputs"
        os.makedirs(self.output_dir, exist_ok=True)

    def gen_ident(self, length=None) -> str:
        """Generate random identifier"""
        if length is None:
            length = random.randint(1, 20)
        first = random.choice(string.ascii_letters + '_')
        rest = ''.join(random.choices(string.ascii_letters + string.digits + '_', k=length-1))
        return first + rest

    def gen_nat(self) -> str:
        """Generate random natural number"""
        choices = [
            "0",
            str(random.randint(1, 100)),
            str(random.randint(100, 10000)),
            str(2**31 - 1),
            str(2**32),
            str(2**64),
            str(2**128),
        ]
        return random.choice(choices)

    def gen_type_expr(self, depth=0) -> str:
        """Generate random type expression"""
        if depth > 5:
            return random.choice(["Nat", "Bool", "String", "Unit", "Prop"])

        choices = [
            "Nat",
            "Bool",
            "String",
            "Int",
            "Prop",
            "Type",
            f"Type {random.randint(0, 10)}",
            f"{self.gen_type_expr(depth+1)} → {self.gen_type_expr(depth+1)}",
            f"Option {self.gen_type_expr(depth+1)}",
            f"List {self.gen_type_expr(depth+1)}",
            f"Array {self.gen_type_expr(depth+1)}",
        ]
        return random.choice(choices)

    def gen_term_expr(self, depth=0) -> str:
        """Generate random term expression"""
        if depth > 10:
            return random.choice(["0", "true", "false", '""'])

        choices = [
            self.gen_nat(),
            "true",
            "false",
            f'"{self.gen_ident()}"',
            f"({self.gen_term_expr(depth+1)})",
            f"{self.gen_term_expr(depth+1)} + {self.gen_term_expr(depth+1)}",
            f"{self.gen_term_expr(depth+1)} - {self.gen_term_expr(depth+1)}",
            f"{self.gen_term_expr(depth+1)} * {self.gen_term_expr(depth+1)}",
            f"fun x => {self.gen_term_expr(depth+1)}",
            f"if {self.gen_term_expr(depth+1)} == {self.gen_term_expr(depth+1)} then {self.gen_term_expr(depth+1)} else {self.gen_term_expr(depth+1)}",
            f"match {self.gen_term_expr(depth+1)} with | _ => {self.gen_term_expr(depth+1)}",
            f"let x := {self.gen_term_expr(depth+1)}; {self.gen_term_expr(depth+1)}",
        ]
        return random.choice(choices)

    def gen_deep_nesting(self, depth: int) -> str:
        """Generate deeply nested expression"""
        if depth <= 0:
            return "0"
        return f"({self.gen_deep_nesting(depth-1)})"

    def gen_large_definition(self) -> str:
        """Generate definition with many parameters"""
        num_params = random.randint(10, 50)
        params = [f"(x{i} : Nat)" for i in range(num_params)]
        return f"def {self.gen_ident()} {' '.join(params)} : Nat := x0"

    def gen_mutual_recursion(self, n: int) -> str:
        """Generate mutual recursive definitions"""
        code = "mutual\n"
        for i in range(n):
            next_i = (i + 1) % n
            code += f"  def f{i} : Nat → Nat\n"
            code += f"    | 0 => 0\n"
            code += f"    | n + 1 => f{next_i} n\n"
        code += "end\n"
        return code

    def gen_complex_inductive(self) -> str:
        """Generate complex inductive type"""
        name = self.gen_ident()
        num_constructors = random.randint(1, 10)
        code = f"inductive {name} where\n"
        for i in range(num_constructors):
            num_params = random.randint(0, 5)
            params = [f": {self.gen_type_expr(2)}" for _ in range(num_params)]
            code += f"  | c{i} {' '.join(params)} : {name}\n"
        return code

    def gen_universe_exploit(self) -> str:
        """Generate universe level exploits"""
        templates = [
            "def f.{u, v} : Type u → Type v := fun x => x",
            "def f.{u} : Type u → Type (u+1) := fun x => x",
            "def f : Type → Type 1 := fun x => x",
            "universe u\ndef f : Type u → Type u := fun x => x",
        ]
        return random.choice(templates)

    def gen_axiom_hiding(self) -> str:
        """Try to hide axiom usage"""
        return """
macro "hidden_axiom" : term => `(sorry)
axiom bad : False := hidden_axiom
"""

    def gen_quotient_exploit(self) -> str:
        """Generate quotient type edge cases"""
        return """
def r : Nat → Nat → Prop := fun _ _ => True
def q := Quot r
def q_mk : Nat → q := Quot.mk r
"""

    def gen_coercion_cycle(self) -> str:
        """Generate circular coercions"""
        return """
structure A where val : Nat
structure B where val : Nat
instance : Coe A B where coe x := ⟨x.val⟩
instance : Coe B A where coe x := ⟨x.val⟩
def test : A := (⟨42⟩ : B)
"""

    def gen_type_class_loop(self) -> str:
        """Generate type class resolution loop"""
        return """
class C1 (α : Type) where
  f : α → α
class C2 (α : Type) where
  g : α → α
instance [C2 α] : C1 α where f := C2.g
instance [C1 α] : C2 α where g := C1.f
"""

    def gen_malformed_syntax(self) -> str:
        """Generate syntactically malformed code"""
        templates = [
            "def := 42",
            "def f : :=",
            "def f : Nat Nat := 0",
            "theorem : False",
            "structure where",
            "inductive where",
            "match with",
            "fun => x",
            "if then else",
        ]
        return random.choice(templates)

    def generate_fuzz_file(self, filename: str) -> str:
        """Generate a complete fuzz test file"""
        generators = [
            self.gen_large_definition,
            lambda: self.gen_mutual_recursion(random.randint(2, 10)),
            self.gen_complex_inductive,
            self.gen_universe_exploit,
            self.gen_axiom_hiding,
            self.gen_quotient_exploit,
            self.gen_coercion_cycle,
            self.gen_type_class_loop,
            self.gen_malformed_syntax,
            lambda: f"def {self.gen_ident()} : {self.gen_type_expr()} := {self.gen_term_expr()}",
            lambda: f"#eval {self.gen_term_expr()}",
            lambda: f"example : {self.gen_type_expr()} := {self.gen_term_expr()}",
        ]

        code = "-- Automatically generated fuzz test\n"
        code += f"-- File: {filename}\n\n"

        # Generate multiple constructs
        num_constructs = random.randint(5, 20)
        for _ in range(num_constructs):
            try:
                code += random.choice(generators)() + "\n\n"
            except:
                pass  # Skip if generation fails

        return code

    def test_lean_file(self, filepath: str) -> dict:
        """Test a Lean file and return results"""
        result = {
            'file': filepath,
            'crashed': False,
            'timeout': False,
            'exit_code': None,
            'stderr': '',
            'stdout': '',
        }

        try:
            proc = subprocess.run(
                ['lean', filepath],
                capture_output=True,
                text=True,
                timeout=10,
            )
            result['exit_code'] = proc.returncode
            result['stderr'] = proc.stderr
            result['stdout'] = proc.stdout

            # Check for crashes
            if 'stack overflow' in proc.stderr.lower():
                result['crashed'] = True
                self.crash_count += 1
            if 'segmentation fault' in proc.stderr.lower():
                result['crashed'] = True
                self.crash_count += 1
            if proc.returncode < 0:  # Signal
                result['crashed'] = True
                self.crash_count += 1

        except subprocess.TimeoutExpired:
            result['timeout'] = True
            self.timeout_count += 1

        return result

    def run_fuzzing_campaign(self):
        """Run full fuzzing campaign"""
        print(f"[*] Starting fuzzing campaign: {self.fuzz_iterations} iterations")
        print(f"[*] Output directory: {self.output_dir}")

        interesting_cases = []

        for i in range(self.fuzz_iterations):
            if i % 100 == 0:
                print(f"[*] Progress: {i}/{self.fuzz_iterations} (Crashes: {self.crash_count}, Timeouts: {self.timeout_count})")

            # Generate test file
            filename = f"{self.output_dir}/fuzz_{i:06d}.lean"
            code = self.generate_fuzz_file(filename)

            with open(filename, 'w') as f:
                f.write(code)

            # Test it
            result = self.test_lean_file(filename)

            # Save interesting cases
            if result['crashed'] or result['timeout']:
                interesting_cases.append(result)
                crash_file = f"{self.output_dir}/CRASH_{i:06d}.lean"
                with open(crash_file, 'w') as f:
                    f.write(code)
                print(f"[!] FOUND INTERESTING CASE: {crash_file}")
                print(f"    Crashed: {result['crashed']}, Timeout: {result['timeout']}")
                print(f"    Exit code: {result['exit_code']}")
                print(f"    Stderr: {result['stderr'][:200]}")

        print("\n" + "="*80)
        print(f"[*] Fuzzing campaign complete!")
        print(f"[*] Total iterations: {self.fuzz_iterations}")
        print(f"[*] Crashes found: {self.crash_count}")
        print(f"[*] Timeouts: {self.timeout_count}")
        print(f"[*] Interesting cases saved to: {self.output_dir}/CRASH_*.lean")
        print("="*80)

        return interesting_cases


if __name__ == '__main__':
    fuzzer = LeanFuzzer()
    fuzzer.run_fuzzing_campaign()
