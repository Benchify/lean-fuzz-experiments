-- Fixture: triggers a PARSE error (unexpected token).
def foo :=
  let x := 42
  x +
