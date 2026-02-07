def main : IO Unit := do
  IO.println "=== UInt8 Overflow ==="
  let max : UInt8 := 255
  IO.println s!"255 + 1 = {max + 1}"
  IO.println s!"0 - 1 = {(0 : UInt8) - 1}"

  IO.println "\n=== UInt64 Overflow ==="
  let u64max : UInt64 := 0xFFFFFFFFFFFFFFFF
  IO.println s!"UInt64.max + 1 = {u64max + 1}"

  IO.println "\n=== Shift Overflow ==="
  IO.println s!"1 <<< 128 = {(1 : UInt64) <<< 128}"
  IO.println s!"1 <<< 65 = {(1 : UInt64) <<< 65}"

  IO.println "\n=== Division by Zero ==="
  IO.println s!"42 / 0 = {(42 : UInt64) / 0}"

  IO.println "\n=== Type Downcast ==="
  let large : UInt64 := 0xDEADBEEFCAFEBABE
  IO.println s!"0xDEADBEEFCAFEBABE as UInt32: {large.toUInt32}"
  IO.println s!"0xDEADBEEFCAFEBABE as UInt8: {large.toUInt8}"
