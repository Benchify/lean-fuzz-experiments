-- Fixture: triggers multiple error categories (UNKNOWN_IDENTIFIER + TYPE_MISMATCH).
def foo := nonexistentFunction 42
def bar : Bool := (42 : Nat)
