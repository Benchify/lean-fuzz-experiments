-- Automatically generated fuzz test
-- File: fuzz_outputs/fuzz_000000.lean

def PV3cUFRoq (x0 : Nat) (x1 : Nat) (x2 : Nat) (x3 : Nat) (x4 : Nat) (x5 : Nat) (x6 : Nat) (x7 : Nat) (x8 : Nat) (x9 : Nat) (x10 : Nat) (x11 : Nat) (x12 : Nat) (x13 : Nat) (x14 : Nat) (x15 : Nat) (x16 : Nat) (x17 : Nat) (x18 : Nat) (x19 : Nat) (x20 : Nat) (x21 : Nat) (x22 : Nat) (x23 : Nat) (x24 : Nat) (x25 : Nat) (x26 : Nat) (x27 : Nat) (x28 : Nat) (x29 : Nat) (x30 : Nat) (x31 : Nat) (x32 : Nat) (x33 : Nat) (x34 : Nat) (x35 : Nat) (x36 : Nat) (x37 : Nat) (x38 : Nat) (x39 : Nat) (x40 : Nat) (x41 : Nat) (x42 : Nat) (x43 : Nat) : Nat := x0

def f : Type → Type 1 := fun x => x


class C1 (α : Type) where
  f : α → α
class C2 (α : Type) where
  g : α → α
instance [C2 α] : C1 α where f := C2.g
instance [C1 α] : C2 α where g := C1.f



def r : Nat → Nat → Prop := fun _ _ => True
def q := Quot r
def q_mk : Nat → q := Quot.mk r


def puIvBoIX_r9y (x0 : Nat) (x1 : Nat) (x2 : Nat) (x3 : Nat) (x4 : Nat) (x5 : Nat) (x6 : Nat) (x7 : Nat) (x8 : Nat) (x9 : Nat) (x10 : Nat) (x11 : Nat) : Nat := x0

inductive where

mutual
  def f0 : Nat → Nat
    | 0 => 0
    | n + 1 => f1 n
  def f1 : Nat → Nat
    | 0 => 0
    | n + 1 => f2 n
  def f2 : Nat → Nat
    | 0 => 0
    | n + 1 => f3 n
  def f3 : Nat → Nat
    | 0 => 0
    | n + 1 => f4 n
  def f4 : Nat → Nat
    | 0 => 0
    | n + 1 => f5 n
  def f5 : Nat → Nat
    | 0 => 0
    | n + 1 => f6 n
  def f6 : Nat → Nat
    | 0 => 0
    | n + 1 => f0 n
end



class C1 (α : Type) where
  f : α → α
class C2 (α : Type) where
  g : α → α
instance [C2 α] : C1 α where f := C2.g
instance [C1 α] : C2 α where g := C1.f


if then else

mutual
  def f0 : Nat → Nat
    | 0 => 0
    | n + 1 => f1 n
  def f1 : Nat → Nat
    | 0 => 0
    | n + 1 => f2 n
  def f2 : Nat → Nat
    | 0 => 0
    | n + 1 => f3 n
  def f3 : Nat → Nat
    | 0 => 0
    | n + 1 => f4 n
  def f4 : Nat → Nat
    | 0 => 0
    | n + 1 => f5 n
  def f5 : Nat → Nat
    | 0 => 0
    | n + 1 => f6 n
  def f6 : Nat → Nat
    | 0 => 0
    | n + 1 => f7 n
  def f7 : Nat → Nat
    | 0 => 0
    | n + 1 => f0 n
end


def f : Type → Type 1 := fun x => x


def r : Nat → Nat → Prop := fun _ _ => True
def q := Quot r
def q_mk : Nat → q := Quot.mk r



macro "hidden_axiom" : term => `(sorry)
axiom bad : False := hidden_axiom



macro "hidden_axiom" : term => `(sorry)
axiom bad : False := hidden_axiom



class C1 (α : Type) where
  f : α → α
class C2 (α : Type) where
  g : α → α
instance [C2 α] : C1 α where f := C2.g
instance [C1 α] : C2 α where g := C1.f



class C1 (α : Type) where
  f : α → α
class C2 (α : Type) where
  g : α → α
instance [C2 α] : C1 α where f := C2.g
instance [C1 α] : C2 α where g := C1.f



macro "hidden_axiom" : term => `(sorry)
axiom bad : False := hidden_axiom



macro "hidden_axiom" : term => `(sorry)
axiom bad : False := hidden_axiom


universe u
def f : Type u → Type u := fun x => x

