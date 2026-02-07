-- Test 2.2.1: Timing-Based Information Disclosure
-- Can we infer secrets based on crash timing?

import Lean

unsafe def crashTimingOracle (value : Nat) : IO Nat := do
  let start ← IO.monoMsNow

  let confused : String := unsafeCast value

  try
    -- Different operations might crash at different times
    let _ := confused.length
    pure ()
  catch _ =>
    pure ()

  let finish ← IO.monoMsNow
  return (finish - start)

unsafe def timingOracleAttack : IO Unit := do
  IO.println "=== Test: Crash timing oracle ==="
  IO.println "Measuring if different values crash at different times\n"

  let testValues : Array Nat := #[
    0,           -- Null pointer
    1,           -- Invalid low address
    42,          -- Small value
    0x1000,      -- Page boundary
    0x10000,     -- Higher address
    0x7FFFFFFF,  -- Max 32-bit
    0xDEADBEEF   -- Pattern
  ]

  let mut timings : Array (Nat × Nat) := #[]

  for value in testValues do
    let elapsed ← crashTimingOracle value
    timings := timings.push (value, elapsed)
    IO.println s!"Value {value} (0x{Nat.toDigits 16 value}): {elapsed}ms"

  IO.println "\n=== Analysis ==="

  -- Check for timing variations
  let mut minTime := 1000000
  let mut maxTime := 0

  for (_, time) in timings do
    if time < minTime then minTime := time
    if time > maxTime then maxTime := time

  let variation := maxTime - minTime
  IO.println s!"Min time: {minTime}ms"
  IO.println s!"Max time: {maxTime}ms"
  IO.println s!"Variation: {variation}ms"

  if variation > 10 then
    IO.println "⚠ VULNERABILITY: Significant timing variation detected"
    IO.println "Timing oracle may leak information about values"
  else if variation > 0 then
    IO.println "⚠ Minimal timing variation detected"
  else
    IO.println "✓ No timing variation (oracle not viable)"

unsafe def operationTimingDifference : IO Unit := do
  IO.println "\n=== Test: Different operations, different timings ==="

  let value : Nat := 42
  let confused : String := unsafeCast value

  -- Test different operations
  let operations : Array (String × (String → IO Unit)) := #[
    ("length", fun s => do let _ := s.length; pure ()),
    ("isEmpty", fun s => do let _ := s.isEmpty; pure ()),
    ("front", fun s => do let _ := s.front; pure ()),
    ("get 0", fun s => do let _ := s.get ⟨0, by omega⟩; pure ())
  ]

  for (name, op) in operations do
    let start ← IO.monoMsNow
    try
      op confused
    catch _ =>
      pure ()
    let finish ← IO.monoMsNow
    IO.println s!"{name}: {finish - start}ms"

unsafe def statisticalTimingAnalysis : IO Unit := do
  IO.println "\n=== Test: Statistical timing analysis ==="

  let samples := 100
  let value : Nat := 42

  let mut times : Array Nat := #[]

  for _ in [0:samples] do
    let time ← crashTimingOracle value
    times := times.push time

  -- Calculate statistics
  let mut sum : Nat := 0
  for t in times do
    sum := sum + t
  let mean := sum / samples

  IO.println s!"Samples: {samples}"
  IO.println s!"Mean time: {mean}ms"
  IO.println s!"First sample: {times[0]!}ms"
  IO.println s!"Last sample: {times[samples-1]!}ms"

unsafe def sidChannelExfiltration : IO Unit := do
  IO.println "\n=== Test: Side-channel exfiltration attempt ==="

  -- Simulated secret bit
  let secretBit : Bool := true

  -- Choose value based on secret
  let value : Nat := if secretBit then 0x1000 else 0x2000
  let confused : String := unsafeCast value

  -- Measure crash characteristics
  let start ← IO.monoMsNow
  try
    let _ := confused.length
    IO.println "Did not crash?"
  catch _ =>
    pure ()
  let finish ← IO.monoMsNow

  -- Attacker observes timing
  let elapsed := finish - start
  IO.println s!"Observed timing: {elapsed}ms"

  -- Try to infer secret
  let inferredBit := elapsed < 5  -- Threshold-based inference

  if inferredBit == secretBit then
    IO.println s!"⚠ LEAK: Correctly inferred secret bit: {secretBit}"
  else
    IO.println "✓ Could not infer secret bit from timing"

unsafe def main : IO Unit := do
  IO.println "Testing timing-based information disclosure"
  IO.println "These tests measure if crash timing leaks information\n"

  timingOracleAttack
  operationTimingDifference
  statisticalTimingAnalysis
  sidChannelExfiltration

  IO.println "\n=== Timing Oracle Testing Complete ==="
