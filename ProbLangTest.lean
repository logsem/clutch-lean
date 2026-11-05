module

public import Metrology.ProbLang.Test

/-! # ProbLang test runner

The `DetStep_discrete` examples execute at elaboration time, so compiling this file runs the suite.
-/

@[expose] public section

/-- Print a success message after the elaboration-time tests pass. -/
def main : IO Unit := do
  IO.println "All ProbLang tests passed."
