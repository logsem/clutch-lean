module

public import Metrology.ProbLang.Interp.BigStepIO
public import Lean.Data.Json.FromToJson

@[expose] public section

/-! # Drawing samples from a program

`problang-sample` runs a program many times and sends summaries to the `#sample` widget as JSON.
`ToJson Float` keeps only six decimals, so floats travel as the hex of their IEEE bits (`hex`).
-/

open Lean

namespace ProbLang

/-- Registers travel as their architectural index. -/
instance : ToJson Asm.Reg := ⟨fun r => toJson r.val⟩

/-- Decoding a register checks its architectural bound. -/
instance : FromJson Asm.Reg where
  fromJson? json := do
    let n ← (fromJson? json : Except String Nat)
    if h : n < 32 then return ⟨n, h⟩
    else throw "assembly register index must be less than 32"

deriving instance ToJson, FromJson for Asm.Len, Asm.ArgKind, Asm.CallSig, Asm.Sig,
  Asm.Imm, Asm.Operand, Asm.Instr, Asm.Section, Asm.Directive, Asm.Line, Asm.AsmProg,
  Asm.Code, Asm.BoundaryValue, Asm.Replay

deriving instance ToJson, FromJson for Var, BaseLit, UnOp, BinOp, Pat, Exp

namespace Interp.Sample

/-- The engines a sample can be drawn with, by name. `tacoma` is the environment machine. -/
def engines : Array (String × (Exp Float → IO (Exp Float))) :=
  #[("tacoma", eval)]

/-- The IEEE bits of `x` as 16 hex digits. -/
def hex (x : Float) : String :=
  let digits := Nat.toDigits 16 x.toBits.toNat
  String.ofList (List.replicate (16 - digits.length) '0' ++ digits)

/-- Encode a float as `hex`. -/
@[reducible] def hexToJson : ToJson Float := ⟨fun x => toJson (hex x)⟩

/-- Decode a float from the hex of its IEEE bits. -/
@[reducible] def hexFromJson : FromJson Float := ⟨fun j => do
  let s ← j.getStr?
  let err := s!"expected the hex bits of a float, got '{s}'"
  let some bits := s.foldl (fun acc c => do return (← acc) * 16 + (← hexDigit c)) (some 0)
    | throw err
  unless 0 < s.length && s.length ≤ 16 do throw err
  return .ofBits bits.toUInt64⟩
where
  hexDigit (c : Char) : Option Nat :=
    if c.isDigit then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else none

/-- What a batch of runs returned. -/
structure Summary where
  /-- How many runs there were. -/
  runs : Nat := 0
  /-- How many runs returned `true` and `false`. -/
  bools : Nat × Nat := (0, 0)
  /-- Each integer returned, with how many runs returned it, in increasing order. -/
  ints : Array (Int × Nat) := #[]
  /-- The finite reals returned, one per run. -/
  reals : Array Float := #[]
  /-- Runs that returned anything else, including non-finite reals, or failed. -/
  other : Nat := 0
  /-- The error of the first failed run, if any. -/
  failure? : Option String := none

/-- A summary as JSON, with its reals packed into one string of `hex` digits. -/
def Summary.toJson (s : Summary) : Json :=
  json% { runs: $(s.runs), bools: $(s.bools), ints: $(s.ints),
          reals: $(String.join (s.reals.map hex).toList), other: $(s.other),
          failure: $(s.failure?) }

/-- A `Summary` under construction. -/
structure Tally where
  runs : Nat := 0
  trues : Nat := 0
  falses : Nat := 0
  ints : Std.HashMap Int Nat := {}
  reals : Array Float := #[]
  other : Nat := 0
  failure? : Option String := none

/-- Count the outcome of one more run. -/
def Tally.add (t : Tally) (outcome : Except IO.Error (Exp Float)) : Tally :=
  let t := { t with runs := t.runs + 1 }
  match outcome with
  | .ok (.lit (.bool true)) => { t with trues := t.trues + 1 }
  | .ok (.lit (.bool false)) => { t with falses := t.falses + 1 }
  | .ok (.lit (.int z)) => { t with ints := t.ints.alter z fun c => some (c.getD 0 + 1) }
  | .ok (.lit (.real r)) =>
    if r.isFinite then { t with reals := t.reals.push r } else { t with other := t.other + 1 }
  | .ok _ => { t with other := t.other + 1 }
  | .error err => { t with other := t.other + 1, failure? := t.failure? <|> some (toString err) }

/-- The runs counted so far. -/
def Tally.summary (t : Tally) : Summary :=
  { runs := t.runs, bools := (t.trues, t.falses), ints := t.ints.toArray.qsort (·.1 < ·.1),
    reals := t.reals, other := t.other, failure? := t.failure? }

/-- At most this many runs go into one `Summary` from `draw`, so that fast programs report in small
steps. -/
def maxChunk : Nat := 20000

/-- Run `e` with `run` `n` times, passing the runs since the last call to `emit` every `maxChunk`
runs or `ms` milliseconds, whichever comes first, and once more at the end. -/
def draw (run : Exp Float → IO (Exp Float)) (e : Exp Float) (n ms : Nat)
    (emit : Summary → IO Unit) : IO Unit := do
  let mut t : Tally := {}
  let mut last ← IO.monoMsNow
  for _ in [0:n] do
    t := t.add (← (run e).toBaseIO)
    if t.runs ≥ maxChunk || (← IO.monoMsNow) - last ≥ ms then
      emit t.summary
      t := {}
      last ← IO.monoMsNow
  if t.runs > 0 then emit t.summary

/-- A program as JSON. -/
def encodeProgram (e : Exp Float) : String := letI := hexToJson; (toJson e).compress

/-- Read back an `encodeProgram`. -/
def decodeProgram (s : String) : Except String (Exp Float) :=
  letI := hexFromJson; Json.parse s >>= fromJson?

end Interp.Sample
end ProbLang
