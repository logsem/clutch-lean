module

public import Metrology.ProbLang.Asm.Syntax

/-! # GNU RISC-V assembly parsing -/

@[expose] public section

namespace ProbLang.Asm

open Int Imm

/-- Convert an optional parse result to a diagnostic. -/
def optionExcept {α : Type} (x : Option α) (error : String) : Except String α :=
  match x with
  | some a => .ok a
  | none => .error error

variable (s : String)

/-- Remove surrounding ASCII whitespace. -/
def trim : String := s.trimAscii.toString

/-- The ABI register names in numeric order. -/
def abiNames : List String :=
  ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1", "a0", "a1", "a2",
    "a3", "a4", "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9",
    "s10", "s11", "t3", "t4", "t5", "t6"]

/-- Parse a numeric or ABI register name. -/
def parseReg : Option Reg := do
  let n ← if s == "fp" then some 8 else if s.startsWith "x" then
    (s.drop 1).toString.toNat? else List.idxOf? s abiNames
  if h : n < 32 then some ⟨n, h⟩ else none

/-- Read one hexadecimal digit. -/
def hexDigit (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10) else none

/-- Parse a signed decimal or hexadecimal assembly integer. -/
def parseInt : Option Int := do
  let neg := s.startsWith "-"
  let t := if neg then (s.drop 1).toString else s
  let n ← if t.startsWith "0x" then
    (t.drop 2).toString.toList.foldlM (fun n c => do pure (16 * n + (← hexDigit c))) 0
    else t.toNat?
  pure (if neg then -(ofNat n) else ofNat n)

/-- Read an immediate or symbolic relocation. -/
def parseImm : Except String Imm := do
  if let some n := parseInt s then return .int n
  for (pre, ctor) in [("%pcrel_hi(", pcrelHi), ("%pcrel_lo(", pcrelLo),
      ("%hi(", hi), ("%lo(", lo)] do
    if s.startsWith pre && s.endsWith ")" then
      return ctor (((s.drop pre.length).toString.dropEnd 1).toString)
  if s.isEmpty then throw "empty immediate"
  return .symbol s

/-- Read a register, immediate, or memory operand. -/
def parseOperand : Except String Operand := do
  let s := trim s
  if let some r := parseReg s then return .reg r
  let parts := s.splitOn "("
  if parts.length ≥ 2 && s.endsWith ")" then
    let base := ((parts.getLast!).dropEnd 1).toString
    if let some r := parseReg base then
      let offset := "(".intercalate parts.dropLast
      return .mem (← parseImm (trim offset)) r
  return .imm (← parseImm s)

/-- Decode escaped assembler string bytes with a bounded scan. -/
def quotedBytes : Nat → List Char → Except String (List Int)
  | 0, [] => .ok []
  | 0, _ => .error "string scan exhausted"
  | _ + 1, [] => .ok []
  | fuel + 1, '\\' :: c :: cs => do
    if '0' ≤ c && c ≤ '7' then
      let digits := (c :: cs).take 3 |>.takeWhile (fun d => '0' ≤ d && d ≤ '7')
      let value := digits.foldl (fun n d => 8 * n + d.toNat - '0'.toNat) 0
      if value ≥ 256 then throw "octal string escape exceeds one byte"
      return (ofNat value) :: (← quotedBytes fuel ((c :: cs).drop digits.length))
    let value ← match c with
      | 'n' => pure 10
      | 'r' => pure 13
      | 't' => pure 9
      | 'b' => pure 8
      | 'f' => pure 12
      | 'v' => pure 11
      | 'a' => pure 7
      | '\\' => pure 92
      | '"' => pure 34
      | _ => throw s!"unsupported string escape '{c}'"
    return value :: (← quotedBytes fuel cs)
  | fuel + 1, c :: cs => do
    if c == '\\' then throw "unfinished string escape"
    if c.toNat ≥ 128 then throw "non-ASCII source character; use escaped bytes"
    return ofNat c.toNat :: (← quotedBytes fuel cs)

/-- Parse a quoted assembler byte string. -/
def parseQuoted : Except String (List Int) := do
  if !(s.startsWith "\"" && s.endsWith "\"") then throw "expected quoted string"
  let chars := ((s.drop 1).toString.dropEnd 1).toString.toList
  quotedBytes (chars.length + 1) chars

/-- Read a supported GNU assembler directive. -/
def parseDirective (name args : String) : Except String Directive := do
  match name with
  | ".text" => return .section .text
  | ".section" =>
    let sec :=  trim ((args.splitOn ",")[0]!)
    if sec.startsWith ".rodata" || sec.startsWith ".srodata" then
      return .section .rodata
    if sec == ".text" then return .section .text
    throw s!"unsupported section '{sec}'"
  | ".p2align" | ".align" =>
    let some n := (trim ((args.splitOn ",")[0]!)).toNat? | throw "invalid alignment"
    return .align n
  | ".zero" =>
    let some n := args.toNat? | throw "invalid zero count"
    return .zero n
  | ".ascii" | ".asciz" | ".string" =>
    return .data 1 ((← parseQuoted args) ++ if name == ".ascii" then [] else [0])
  | ".byte" | ".half" | ".2byte" | ".word" | ".4byte" | ".dword" | ".8byte"
  | ".quad" =>
    let width := if name == ".byte" then 1 else if name == ".half" || name == ".2byte"
      then 2 else if name == ".word" || name == ".4byte" then 4 else 8
    let values ← (args.splitOn ",").mapM fun s =>
      optionExcept (parseInt (trim s)) s!"invalid data integer '{s}'"
    return .data width values
  | ".globl" | ".global" | ".type" | ".size" | ".attribute" | ".file" | ".option"
  | ".ident" | ".addrsig" | ".addrsig_sym" => return .metadata name args
  | _ => throw s!"unsupported directive '{name}'"

/-- Remove comments outside assembler string literals. -/
def stripComment (raw : String) : String := Id.run do
  let mut quoted := false
  let mut escaped := false
  let mut out := []
  for c in raw.toList do
    if c == '#' && !quoted then break
    if c == '"' && !escaped then quoted := !quoted
    out := c :: out
    escaped := c == '\\' && !escaped
  return String.ofList out.reverse

/-- Read one assembler line after removing its comment. -/
def parseLine (raw : String) : Except String (List Line) := do
  let s := trim (stripComment raw)
  if s.isEmpty then return []
  if s.endsWith ":" then return [.label ((s.dropEnd 1).toString)]
  let words := (s.splitOn "\t").flatMap (·.splitOn " ") |>.filter (!·.isEmpty)
  let name := words[0]!
  let args := trim ((s.drop name.length).toString)
  if name.startsWith "." then return [.directive (← parseDirective name args)]
  let operands ← if args.isEmpty then pure [] else (args.splitOn ",").mapM parseOperand
  return [.instr ⟨name, operands⟩]

/-- Parse GNU assembly and choose its first global symbol as the entry point. -/
def parse (source : String) (entry : String := "") : Except String AsmProg := do
  let mut lines := []
  let mut selected := entry
  for (raw, index) in (source.splitOn "\n").zipIdx do
    let parsed ← (parseLine raw).mapError (fun e => s!"line {index + 1}: {e}")
    for line in parsed do
      if selected.isEmpty then
        match line with
        | .directive (.metadata ".globl" name) | .directive (.metadata ".global" name) =>
          selected := name
        | _ => pure ()
    lines := lines ++ parsed
  if selected.isEmpty then
    selected := (lines.findSome? fun l => match l with
      | .label name => some name
      | _ => none).getD ""
  if selected.isEmpty then throw "assembly has no entry label"
  return ⟨lines, selected⟩

end ProbLang.Asm
