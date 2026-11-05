import Metrology.ProbLang.Interp.Sample

/-! # ProbLang sampling executable

`problang-sample <engine> <runs> <ms>` reads one JSON program from stdin and periodically writes
JSON `Summary` values through the final run; closing stdin stops it with its Lean caller. -/

open Lean ProbLang ProbLang.Interp.Sample

/-- Run the requested sampling engine and stream JSON summaries to stdout. -/
def main (args : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let program ← stdin.getLine
  let [name, runs, ms] := args
    | IO.eprintln "usage: problang-sample <engine> <runs> <ms>"; return 1
  let some (_, run) := engines.find? (·.1 == name)
    | IO.eprintln s!"unknown engine: {name}"; return 1
  let (some runs, some ms) := (runs.toNat?, ms.toNat?)
    | IO.eprintln s!"not numbers: {runs} {ms}"; return 1
  match decodeProgram program with
  | .error err =>
    IO.eprintln s!"cannot read the program: {err}"
    return 1
  | .ok e =>
    -- Stop if the caller goes away.
    let _ ← IO.asTask (prio := .dedicated) do
      discard stdin.readToEnd
      IO.Process.exit (α := Unit) 1
    let stdout ← IO.getStdout
    draw run e runs ms fun s => do
      stdout.putStrLn s.toJson.compress
      stdout.flush
    -- Exit now rather than wait for the task above.
    IO.Process.exit 0
