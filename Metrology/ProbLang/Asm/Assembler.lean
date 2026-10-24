module

public import Metrology.ProbLang.Asm.Parser

/-! # Uncompressed RISC-V assembly encoding -/

@[expose] public section

namespace ProbLang.Asm

/-- A word emitted at a code offset and its expanded source instruction. -/
structure EncodedInstr where
  /-- The instruction offset from the image base. -/
  offset : Nat
  /-- The instruction after pseudo-instruction expansion. -/
  instruction : Instr
  /-- The encoded uncompressed word. -/
  word : BitVec 32
  deriving Repr

/-- A position-independent machine-code image with a separate read-only data region. -/
structure Image where
  /-- The complete little-endian image. -/
  bytes : List UInt8
  /-- The length of the executable region. -/
  textLen : Nat
  /-- The aligned read-only data offset. -/
  rodataOff : Nat
  /-- The entry point offset. -/
  entry : Nat
  /-- The read-only slots containing imported function addresses. -/
  importSlots : List (String × Nat)
  /-- The emitted instruction words with their source mapping. -/
  instructions : List EncodedInstr
  /-- All defined symbols and their image offsets. -/
  labels : List (String × Nat)
  deriving Repr

namespace Encode

/-- Resolve a symbol to its image offset. -/
def lookupLabel (labels : List (String × Nat)) (name : String) : Except String Nat :=
  optionExcept (labels.lookup name) s!"undefined symbol '{name}'"

/-- The low bits of a signed integer. -/
def bits (value : Int) (width : Nat) : Nat :=
  (value % (2 ^ width : Nat)).toNat

/-- Encode an I-format instruction. -/
def iword (opcode rd funct rs : Nat) (imm : Int) : Nat :=
  opcode + rd * 2^7 + funct * 2^12 + rs * 2^15 + bits imm 12 * 2^20

/-- Encode an R-format instruction. -/
def rword (opcode rd funct rs rt funct7 : Nat) : Nat :=
  opcode + rd * 2^7 + funct * 2^12 + rs * 2^15 + rt * 2^20 + funct7 * 2^25

/-- Encode an S-format instruction. -/
def sword (opcode funct rs rt : Nat) (imm : Int) : Nat :=
  let k := bits imm 12
  opcode + k % 32 * 2^7 + funct * 2^12 + rs * 2^15 + rt * 2^20 + k / 32 * 2^25

/-- Encode a B-format instruction. -/
def bword (funct rs rt : Nat) (imm : Int) : Nat :=
  let k := bits imm 13
  0x63 + k / 2^11 % 2 * 2^7 + k / 2 % 16 * 2^8 + funct * 2^12 + rs * 2^15 +
    rt * 2^20 + k / 2^5 % 64 * 2^25 + k / 2^12 * 2^31

/-- Encode a J-format instruction. -/
def jword (rd : Nat) (imm : Int) : Nat :=
  let k := bits imm 21
  0x6f + rd * 2^7 + k / 2^12 % 256 * 2^12 + k / 2^11 % 2 * 2^20 +
    k / 2 % 1024 * 2^21 + k / 2^20 * 2^31

/-- Check a signed immediate width. -/
def signed (width : Nat) (z : Int) : Except String Int :=
  if -(2 ^ (width - 1) : Nat) ≤ z && z < (2 ^ (width - 1) : Nat) then .ok z
  else .error s!"immediate {z} does not fit signed {width} bits"

/-- The rounded high part of a PC-relative offset. -/
def hi (z : Int) : Int := (z + 0x800) / 0x1000

/-- The signed low part of a PC-relative offset. -/
def lo (z : Int) : Int := z - hi z * 0x1000

/-- Expand a signed RV64 literal into base instructions. -/
def liExpansion (rd : Operand) : Nat → Int → Except String (List Instr)
  | 0, _ => .error "literal exceeds RV64 expansion bound"
  | fuel + 1, z => do
    if -2048 ≤ z && z < 2048 then
      return [⟨"addi", [rd, .reg ⟨0, by decide⟩, .imm (.int z)]⟩]
    if -(2^31 : Nat) ≤ z && z < (2^31 : Nat) then
      return [⟨"lui", [rd, .imm (.int (hi z))]⟩,
        ⟨"addiw", [rd, rd, .imm (.int (lo z))]⟩]
    let prefixWords ← liExpansion rd fuel (hi z)
    return prefixWords ++ [⟨"slli", [rd, rd, .imm (.int 12)]⟩,
      ⟨"addi", [rd, rd, .imm (.int (lo z))]⟩]

/-- Normalize a GNU 64-bit integer literal to its signed register value. -/
def literal64 (z : Int) : Except String Int := do
  if -(2^63 : Nat) ≤ z && z < (2^64 : Nat) then
    return if z ≥ (2^63 : Nat) then z - (2^64 : Nat) else z
  throw "literal exceeds 64 bits"

/-- The expanded size of a supported source instruction. -/
def instrSize (i : Instr) : Nat :=
  if ["call", "tail", "la", "lla"].contains i.mnemonic then 8
  else if i.mnemonic == "li" then
    match i.operands with
    | [.reg _, .imm (.int z)] =>
      ((literal64 z >>= liExpansion (.reg ⟨0, by decide⟩) 6).toOption.getD []).length * 4
    | _ => 4
  else 4

/-- Round an offset up to a power-of-two boundary. -/
def align (offset power : Nat) : Nat :=
  let n := 2 ^ power
  (offset + n - 1) / n * n

/-- The offset following a source line. -/
def lineEnd (offset : Nat) : Line → Nat
  | .instr i => offset + instrSize i
  | .directive (.align n) => align offset n
  | .directive (.data width vs) => offset + width * vs.length
  | .directive (.ascii s terminated) => offset + s.utf8ByteSize + if terminated then 1 else 0
  | .directive (.zero n) => offset + n
  | _ => offset

/-- Assign offsets to labels in one section. -/
def layout (lines : List Line) (start : Nat) :
    Except String (Nat × List (String × Nat)) := do
  let mut offset := start
  let mut labels := []
  for line in lines do
    if let .label name := line then
      if labels.any (·.1 == name) then throw s!"duplicate label '{name}'"
      labels := labels ++ [(name, offset)]
    offset := lineEnd offset line
  return (offset, labels)

/-- Separate executable lines from read-only data lines. -/
def sections (lines : List Line) : List Line × List Line := Id.run do
  let mut sec := Section.text
  let mut text := []
  let mut data := []
  for line in lines do
    match line with
    | .directive (.section kind) => sec := kind
    | _ =>
      if sec == .text then text := text ++ [line] else data := data ++ [line]
  return (text, data)

/-- Resolve a low relocation through its matching high-relocation anchor. -/
def pcrelTarget (lines : List Line) (labels : List (String × Nat)) (anchor : String) :
    Except String Int := do
  let anchorOff ← lookupLabel labels anchor
  let mut offset := 0
  for line in lines do
    if offset == anchorOff then
      if let .instr ⟨"auipc", [.reg _, .imm (.pcrelHi target)]⟩ := line then
        return (← lookupLabel labels target) - (anchorOff : Int)
    offset := lineEnd offset line
  throw s!"PC-relative low relocation '{anchor}' has no matching auipc"

/-- Resolve an immediate at an instruction offset. -/
def resolve (lines : List Line) (labels : List (String × Nat)) (pc : Nat) :
    Imm → Except String Int
  | .int z => .ok z
  | .symbol name z => return (← lookupLabel labels name) + z
  | .hi name => return hi (← lookupLabel labels name)
  | .lo name => return lo (← lookupLabel labels name)
  | .pcrelHi name => return hi ((← lookupLabel labels name) - (pc : Int))
  | .pcrelLo anchor => return lo (← pcrelTarget lines labels anchor)

/-- Construct an instruction from a mnemonic and operands. -/
def ins (mnemonic : String) (operands : List Operand) : Instr := ⟨mnemonic, operands⟩

/-- Construct a numeric register operand. -/
def reg (n : Nat) (h : n < 32 := by decide) : Operand := .reg ⟨n, h⟩

/-- Construct a constant immediate operand. -/
def imm (z : Int) : Operand := .imm (.int z)

/-- The `auipc` and follow-up pair reaching a symbol PC-relatively through `temp`. -/
def pcrelPair (labels : List (String × Nat)) (pc : Nat) (target : String)
    (temp : Operand) (second : Int → Instr) : Except String (List Instr) := do
  let d : Int := (← lookupLabel labels target) - pc
  let _ ← signed 32 d
  return [ins "auipc" [temp, imm (hi d)], second (lo d)]

/-- Expand supported pseudo-instructions into base instructions. -/
def expand (i : Instr) (labels : List (String × Nat)) (pc : Nat) :
    Except String (List Instr) := do
  let ⟨name, args⟩ := i
  match name, args with
  | "ret", [] => return [ins "jalr" [reg 0, .mem (.int 0) ⟨1, by decide⟩]]
  | "nop", [] => return [ins "addi" [reg 0, reg 0, imm 0]]
  | "mv", [rd, rs] => return [ins "addi" [rd, rs, imm 0]]
  | "not", [rd, rs] => return [ins "xori" [rd, rs, imm (-1)]]
  | "neg", [rd, rs] => return [ins "sub" [rd, reg 0, rs]]
  | "negw", [rd, rs] => return [ins "subw" [rd, reg 0, rs]]
  | "sext.w", [rd, rs] => return [ins "addiw" [rd, rs, imm 0]]
  | "zext.b", [rd, rs] => return [ins "andi" [rd, rs, imm 255]]
  | "seqz", [rd, rs] => return [ins "sltiu" [rd, rs, imm 1]]
  | "snez", [rd, rs] => return [ins "sltu" [rd, reg 0, rs]]
  | "jr", [rs] => return [ins "jalr" [reg 0, rs, imm 0]]
  | "j", [target] => return [ins "jal" [reg 0, target]]
  | "beqz", [rs, target] => return [ins "beq" [rs, reg 0, target]]
  | "bnez", [rs, target] => return [ins "bne" [rs, reg 0, target]]
  | "bgt", [rs, rt, target] => return [ins "blt" [rt, rs, target]]
  | "ble", [rs, rt, target] => return [ins "bge" [rt, rs, target]]
  | "bgtu", [rs, rt, target] => return [ins "bltu" [rt, rs, target]]
  | "bleu", [rs, rt, target] => return [ins "bgeu" [rt, rs, target]]
  | "li", [rd, .imm (.int z)] => liExpansion rd 6 (← literal64 z)
  | "call", [.imm (.symbol target 0)] | "tail", [.imm (.symbol target 0)] =>
    let temp := if name == "call" then reg 1 else reg 6
    let dest := if name == "call" then reg 1 else reg 0
    pcrelPair labels pc target temp fun l => ins "jalr" [dest, temp, imm l]
  | "la", [rd, .imm (.symbol target 0)] | "lla", [rd, .imm (.symbol target 0)] =>
    pcrelPair labels pc target rd fun l => ins "addi" [rd, rd, imm l]
  | _, _ => return [i]

/-- The funct3 and funct7 fields of the register-register instructions. -/
def rTable : List (String × Nat × Nat) :=
  [("add", 0, 0), ("sub", 0, 32), ("sll", 1, 0), ("slt", 2, 0), ("sltu", 3, 0),
    ("xor", 4, 0), ("srl", 5, 0), ("sra", 5, 32), ("or", 6, 0), ("and", 7, 0),
    ("mul", 0, 1), ("mulh", 1, 1), ("mulhsu", 2, 1), ("mulhu", 3, 1),
    ("div", 4, 1), ("divu", 5, 1), ("rem", 6, 1), ("remu", 7, 1),
    ("addw", 0, 0), ("subw", 0, 32), ("sllw", 1, 0), ("srlw", 5, 0),
    ("sraw", 5, 32), ("mulw", 0, 1), ("divw", 4, 1), ("divuw", 5, 1),
    ("remw", 6, 1), ("remuw", 7, 1)]

/-- The funct3 and immediate-extra fields of the register-immediate instructions. -/
def iTable : List (String × Nat × Nat) :=
  [("addi", 0, 0), ("slti", 2, 0), ("sltiu", 3, 0), ("xori", 4, 0),
    ("ori", 6, 0), ("andi", 7, 0), ("slli", 1, 0), ("srli", 5, 0),
    ("srai", 5, 1024), ("addiw", 0, 0), ("slliw", 1, 0), ("srliw", 5, 0),
    ("sraiw", 5, 1024)]

/-- The funct3 field of the conditional branches. -/
def branchTable : List (String × Nat) :=
  [("beq", 0), ("bne", 1), ("blt", 4), ("bge", 5), ("bltu", 6), ("bgeu", 7)]

/-- The funct3 field of the loads. -/
def loadTable : List (String × Nat) :=
  [("lb", 0), ("lh", 1), ("lw", 2), ("ld", 3), ("lbu", 4), ("lhu", 5), ("lwu", 6)]

/-- The funct3 field of the stores. -/
def storeTable : List (String × Nat) := [("sb", 0), ("sh", 1), ("sw", 2), ("sd", 3)]

/-- Encode a register-register instruction. -/
def encodeR (name : String) (rd rs rt : Reg) : Except String Nat := do
  let some (f, f7) := rTable.lookup name | throw s!"unknown R instruction '{name}'"
  return rword (if name.endsWith "w" then 0x3b else 0x33) rd.val f rs.val rt.val f7

/-- Encode a register-register-immediate instruction: branch, `jalr` or arithmetic. -/
def encodeI (lines : List Line) (labels : List (String × Nat)) (pc : Nat)
    (name : String) (rd rs : Reg) (value : Imm) : Except String Nat := do
  let z ← resolve lines labels pc value
  if let some f := branchTable.lookup name then
    let d ← signed 13 (z - pc)
    if d % 2 != 0 then throw "unaligned branch"
    return bword f rd.val rs.val d
  if name == "jalr" then return iword 0x67 rd.val 0 rs.val (← signed 12 z)
  let some (f, extra) := iTable.lookup name | throw s!"unknown I instruction '{name}'"
  let shift := ["slli", "srli", "srai", "slliw", "srliw", "sraiw"].contains name
  if shift then
    if z < 0 || z ≥ (if name.endsWith "w" then 32 else 64) then
      throw "shift amount out of range"
  else let _ ← signed 12 z
  let opcode := if name.endsWith "w" then 0x1b else 0x13
  return iword opcode rd.val f rs.val (z + extra)

/-- Encode a load, store or memory-form `jalr`. -/
def encodeMem (name : String) (rd rs : Reg) (z : Int) : Except String Nat :=
  if name == "jalr" then pure (iword 0x67 rd.val 0 rs.val z)
  else if let some f := loadTable.lookup name then pure (iword 0x03 rd.val f rs.val z)
  else if let some f := storeTable.lookup name then pure (sword 0x23 f rs.val rd.val z)
  else throw s!"unknown memory instruction '{name}'"

/-- Encode an upper-immediate or `jal` instruction. -/
def encodeU (name : String) (rd : Reg) (z : Int) (pc : Nat) : Except String Nat := do
  if name == "lui" || name == "auipc" then
    if z < -0x80000 || z ≥ 0x100000 then throw "upper immediate out of range"
    return (if name == "lui" then 0x37 else 0x17) + rd.val * 2^7 + bits z 20 * 2^12
  else if name == "jal" then
    let d ← signed 21 (z - pc)
    if d % 2 != 0 then throw "unaligned jump"
    return jword rd.val d
  else throw s!"unknown upper/jump instruction '{name}'"

/-- Encode one expanded instruction with checked immediate ranges. -/
def encode (lines : List Line) (labels : List (String × Nat)) (pc : Nat)
    (i : Instr) : Except String (BitVec 32) := do
  let ⟨name, args⟩ := i
  let word ← match args with
  | [.reg rd, .reg rs, .reg rt] => encodeR name rd rs rt
  | [.reg rd, .reg rs, .imm value] => encodeI lines labels pc name rd rs value
  | [.reg rd, .mem value rs] => encodeMem name rd rs (← signed 12 (← resolve lines labels pc value))
  | [.reg rd, .imm value] => encodeU name rd (← resolve lines labels pc value) pc
  | _ => throw s!"unsupported instruction '{name}' or operand form"
  return BitVec.ofNat 32 word

end Encode

open Encode

/-- Encode an integer as little-endian bytes. -/
def bytesOf (width : Nat) (z : Int) : List UInt8 :=
  (List.range width).map fun i => UInt8.ofNat ((bits z (8 * width) / 2^(8 * i)) % 256)

/-- Encode consecutive instructions starting at `offset`. -/
def encodeRun (text : List Line) (labels : List (String × Nat)) (offset : Nat)
    (code : List Instr) : Except String (List UInt8 × List EncodedInstr) := do
  let mut bytes := []
  let mut instructions := []
  let mut pc := offset
  for instr in code do
    let word ← encode text labels pc instr
    bytes := bytes ++ bytesOf 4 word.toNat
    instructions := instructions ++ [⟨pc, instr, word⟩]
    pc := pc + 4
  return (bytes, instructions)

/-- Emit bytes and instruction words for a laid-out section; `text` is the executable section
that resolves PC-relative low relocations, and `executable` pads alignment with nops. -/
def emit (lines text : List Line) (labels : List (String × Nat)) (start : Nat)
    (executable : Bool) : Except String (List UInt8 × List EncodedInstr) := do
  let mut offset := start
  let mut bytes := []
  let mut instructions := []
  for line in lines do
    match line with
    | .instr i =>
      if !executable then throw "instructions in rodata"
      let (b, is) ← encodeRun text labels offset (← expand i labels offset)
      bytes := bytes ++ b
      instructions := instructions ++ is
      offset := offset + b.length
    | .directive (.data width values) =>
      bytes := bytes ++ values.flatMap (bytesOf width)
      offset := offset + width * values.length
    | .directive (.ascii value terminated) =>
      let data := value.toUTF8.data.toList ++ if terminated then [0] else []
      bytes := bytes ++ data
      offset := offset + data.length
    | .directive (.zero count) =>
      bytes := bytes ++ List.replicate count 0
      offset := offset + count
    | .directive (.align power) =>
      let pad := align offset power - offset
      if executable then
        if pad % 4 != 0 then throw "unaligned instruction padding"
        let (b, is) ← encodeRun text labels offset
          (List.replicate (pad / 4) (ins "addi" [reg 0, reg 0, imm 0]))
        bytes := bytes ++ b
        instructions := instructions ++ is
      else bytes := bytes ++ List.replicate pad 0
      offset := offset + pad
    | _ => pure ()
  return (bytes, instructions)

/-- Collect unresolved direct calls in source order. -/
def externalCalls (text : List Line) : List String :=
  let defined := text.filterMap fun l => match l with
    | .label name => some name
    | _ => none
  (text.filterMap fun l => match l with
    | .instr ⟨name, [.imm (.symbol target 0)]⟩ =>
      if (name == "call" || name == "tail") && !defined.contains target then some target else none
    | _ => none).eraseDups

/-- The read-only slot storing an imported function's open address. -/
def importSlotName (name : String) : String := ".Lasm_import_slot_" ++ name

/-- A PIC trampoline jumping through an imported function's slot. -/
def importStub (name : String) : List Line :=
  [.label name,
    .instr ⟨"auipc", [reg 28, .imm (.pcrelHi (importSlotName name))]⟩,
    .instr ⟨"ld", [reg 28, .mem (.pcrelLo name) ⟨28, by decide⟩]⟩,
    .instr ⟨"jr", [reg 28]⟩]

/-- Assemble a supported GNU fragment to uncompressed RV64 words and read-only bytes. -/
def assemble (prog : AsmProg) : Except String Image := do
  let (originalText, originalData) := sections prog.lines
  let imports := externalCalls originalText
  let text := originalText ++ imports.flatMap importStub
  let data := originalData ++ imports.flatMap fun name =>
    [.directive (.align 3), .label (importSlotName name), .directive (.zero 8)]
  let (textLen, textLabels) ← layout text 0
  let rodataOff := align textLen 3
  let (_, dataLabels) ← layout data rodataOff
  let labels := textLabels ++ dataLabels
  if (labels.map (·.1)).eraseDups.length != labels.length then throw "duplicate section label"
  let entry ← lookupLabel textLabels prog.entry
  let (textBytes, instructions) ← emit text text labels 0 true
  let (dataBytes, _) ← emit data text labels rodataOff false
  return ⟨textBytes ++ List.replicate (rodataOff - textLen) 0 ++ dataBytes,
    textLen, rodataOff, entry,
    ← imports.mapM (fun name => return (name, ← lookupLabel labels (importSlotName name))),
    instructions, labels⟩

end ProbLang.Asm
