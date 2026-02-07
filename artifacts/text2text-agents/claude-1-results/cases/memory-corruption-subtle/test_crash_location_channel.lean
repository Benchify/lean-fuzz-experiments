-- Test 3.3.1: Crash Location as Covert Channel
-- Can crash location leak information?

import Lean

unsafe def crashLocationBitChannel (bit : Bool) : IO Unit := do
  IO.println s!"=== Transmitting bit: {bit} ==="

  let n : Nat := if bit then 42 else 100
  let s : String := unsafeCast n

  if bit then
    -- Crash at location A
    IO.println "Path A: calling length"
    let _ := s.length
    pure ()
  else
    -- Crash at location B
    IO.println "Path B: calling isEmpty"
    let _ := s.isEmpty
    pure ()

unsafe def crashLocationByteChannel (byte : Nat) : IO Unit := do
  IO.println s!"=== Transmitting byte: {byte} ==="

  let n : Nat := byte
  let s : String := unsafeCast n

  -- Different crash locations for different byte values
  match byte % 8 with
  | 0 => let _ := s.length; pure ()
  | 1 => let _ := s.isEmpty; pure ()
  | 2 => let _ := s.front; pure ()
  | 3 => let _ := s.back; pure ()
  | 4 => let _ := s.toList; pure ()
  | 5 => let _ := s.data; pure ()
  | 6 => let _ := s.startsWith ""; pure ()
  | 7 => let _ := s.endsWith ""; pure ()
  | _ => pure ()

unsafe def exfiltrateViaStackTrace (secret : Nat) : IO Unit := do
  IO.println s!"\n=== Exfiltrating secret via stack trace: {secret} ==="

  let confused : String := unsafeCast secret

  -- Different call depths for different secrets
  let rec crashAtDepth : Nat → IO Unit
    | 0 => do
      IO.println "Crashing at depth 0"
      let _ := confused.length
      pure ()
    | n+1 => do
      IO.println s!"Depth {n+1}"
      crashAtDepth n

  -- Crash depth encodes secret value
  crashAtDepth (secret % 10)

unsafe def timingBasedStackTrace : IO Unit := do
  IO.println "\n=== Timing-based stack trace inference ==="

  let operations : Array (String × (String → IO Unit)) := #[
    ("length", fun s => do let _ := s.length; pure ()),
    ("isEmpty", fun s => do let _ := s.isEmpty; pure ()),
    ("front", fun s => do let _ := s.front; pure ()),
    ("toUpper", fun s => do let _ := s.toUpper; pure ())
  ]

  for (name, op) in operations do
    let n : Nat := 42
    let s : String := unsafeCast n

    let start ← IO.monoMsNow
    try
      op s
    catch _ =>
      pure ()
    let finish ← IO.monoMsNow

    IO.println s!"{name}: crashed in {finish - start}ms"

unsafe def crashCountChannel : IO Unit := do
  IO.println "\n=== Crash count as covert channel ==="

  -- Encode message in number of crashes
  let message : Nat := 5  -- "5" encoded as 5 crashes

  IO.println s!"Encoding message: {message} (will crash {message} times)"

  for i in [0:message] do
    IO.println s!"\nCrash {i+1} of {message}"
    try
      let n : Nat := 42
      let s : String := unsafeCast n
      let _ := s.length
      pure ()
    catch _ =>
      IO.println "Crashed (observer can count these)"

unsafe def exceptionMessageChannel : IO Unit := do
  IO.println "\n=== Exception message as channel ==="

  let n : Nat := 42
  let s : String := unsafeCast n

  try
    -- Different operations might have different error messages
    IO.println "Attempting to extract exception message..."
    let _ := s.length
    pure ()
  catch e =>
    IO.println s!"Exception caught: {e}"
    IO.println "Observer may extract information from exception"

unsafe def controlledCrashSequence (data : Array Nat) : IO Unit := do
  IO.println "\n=== Exfiltrating array via crash sequence ==="
  IO.println s!"Data to exfiltrate: {data}"

  for (i, value) in data.toList.enum do
    IO.println s!"\nExfiltrating byte {i}: {value}"

    let confused : String := unsafeCast value

    -- Crash location encodes value
    match value % 4 with
    | 0 =>
      try let _ := confused.length; pure () catch _ => pure ()
    | 1 =>
      try let _ := confused.isEmpty; pure () catch _ => pure ()
    | 2 =>
      try let _ := confused.front; pure () catch _ => pure ()
    | 3 =>
      try let _ := confused.back; pure () catch _ => pure ()
    | _ => pure ()

unsafe def reconstructFromCrashes : IO Unit := do
  IO.println "\n=== Reconstructing data from crash patterns ==="

  let originalData : Array Nat := #[42, 100, 255, 0, 128]
  IO.println s!"Original data: {originalData}"

  IO.println "\nCrash pattern:"
  for value in originalData do
    let pattern := value % 4
    IO.println s!"Value {value} → Pattern {pattern}"

unsafe def main : IO Unit := do
  IO.println "Testing crash location as covert channel"
  IO.println "Can we exfiltrate information via crash location?\n"

  -- Test bit transmission
  IO.println "=== Bit Channel ==="
  try
    crashLocationBitChannel true
  catch _ =>
    IO.println "Crashed (bit=true)"

  try
    crashLocationBitChannel false
  catch _ =>
    IO.println "Crashed (bit=false)"

  -- Test byte transmission
  IO.println "\n=== Byte Channel ==="
  for byte in [0:8] do
    try
      crashLocationByteChannel byte
    catch _ =>
      IO.println s!"Crashed for byte {byte}"

  -- Test stack trace exfiltration
  try
    exfiltrateViaStackTrace 7
  catch _ =>
    IO.println "Stack trace exfiltration crashed"

  timingBasedStackTrace
  exceptionMessageChannel
  controlledCrashSequence #[1, 2, 3, 0]
  reconstructFromCrashes

  IO.println "\n=== Covert Channel Testing Complete ==="
  IO.println "FINDING: Crash location and pattern may leak information"
  IO.println "RISK: Side-channel exfiltration through controlled crashes"
