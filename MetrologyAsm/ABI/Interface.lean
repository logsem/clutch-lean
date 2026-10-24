import Metrology.ProbLang.Asm.Execution
import Metrology.ProbLang.Asm.Assembler
import MetrologyAsm.Sail.MemoryRules

/-! # The Sail interpretation of foreign assembly calls -/

namespace MetrologyAsm

open ProbLang ProbLang.Asm RiscvZkvm.Sail.Functions
open Sail.ConcurrencyInterfaceV1

/-- The pointer regions determined by the original argument tuple. -/
def callRegions (code : Code) (args : List BoundaryValue) : List Region :=
  regions code.sig.toCallSig (boundaryArgs args)

/-- A byte lies in a nonwrapping physical interval. -/
def inSpan (base width address : Nat) : Prop := base ≤ address ∧ address < base + width

/-- Two nonwrapping physical intervals have no common byte. -/
def disjointSpans (a n b m : Nat) : Prop := a + n ≤ b ∨ b + m ≤ a

/-- A physical byte belongs to the embedded logical footprint. -/
def footprintByte (ι : Placement) (code : Code) (args : List BoundaryValue) (a : Nat) : Prop :=
  ∃ r ∈ callRegions code args, inSpan (ι.addr r.base).toNat (r.length * (r.width / 8)) a

/-- Pointer regions sit contiguously in disjoint, aligned physical storage (facet 1). -/
def footprintPlacement (ι : Placement) (code : Code) (args : List BoundaryValue) : Prop :=
  (∀ r ∈ callRegions code args,
    (ι.addr r.base).toNat % 8 = 0 ∧ ι.addr r.base ≠ 0 ∧
      InUserRam (ι.addr r.base) (r.length * (r.width / 8)) ∧
      ∀ i < r.length,
        (ι.addr (r.base + (i : Int))).toNat = (ι.addr r.base).toNat + i * (r.width / 8)) ∧
    ∀ r ∈ callRegions code args, ∀ q ∈ callRegions code args, r ≠ q →
      disjointSpans (ι.addr r.base).toNat (r.length * (r.width / 8))
        (ι.addr q.base).toNat (q.length * (q.width / 8))

/-- The footprint stores the representable logical integers as little-endian bytes (facet 2). -/
def footprintContents (ι : Placement) (code : Code) (args : List BoundaryValue)
    (heap : LocHeap BoundaryValue) (s : Mach) : Prop :=
  validFragment code args heap ∧ ∀ r ∈ callRegions code args, ∀ i < r.length,
    ∃ z, heap[r.base + (i : Int)]? = some (.int z) ∧ inRange r.signed r.width z = true ∧
      WordAt s (ι.addr (r.base + (i : Int))) (r.width / 8) (BitVec.ofInt (8 * (r.width / 8)) z)

/-- The register word of a scalar argument. -/
def argumentWord (ι : Placement) : BoundaryValue → BitVec 64
  | .int z => BitVec.ofInt 64 z
  | .loc l => ι.addr l
  | .unit => 0

/-- The argument registers in psABI order. -/
def argumentRegisters : List Register := [.x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- Read one argument register by its tuple index. -/
noncomputable def argumentRegister (s : Mach) : Nat → Option (BitVec 64)
  | 0 => s.regs.get? .x10
  | 1 => s.regs.get? .x11
  | 2 => s.regs.get? .x12
  | 3 => s.regs.get? .x13
  | 4 => s.regs.get? .x14
  | 5 => s.regs.get? .x15
  | 6 => s.regs.get? .x16
  | 7 => s.regs.get? .x17
  | _ => none

/-- Declared scalar arguments are fixed in registers and the rest stay open (facet 3). -/
def argumentBindings (ι : Placement) (args : List BoundaryValue) (s : Mach) : Prop :=
  ∀ i v, args[i]? = some v → argumentRegister s i = some (argumentWord ι v)

/-- The encoded address of a footprint location or a region's one-past endpoint. -/
def pointerWord (ι : Placement) (code : Code) (args : List BoundaryValue)
    (l : Loc) : Option (BitVec 64) :=
  if l ∈ callFootprint code args then some (ι.addr l) else
    ((callRegions code args).find? (fun r => l == r.base + (r.length : Int))).map fun r =>
      BitVec.ofNat 64 ((ι.addr r.base).toNat + r.length * (r.width / 8))

/-- Decode a pointer by the fixed logical footprint and its one-past endpoints. -/
def decodePointer (ι : Placement) (code : Code) (args : List BoundaryValue)
    (word : BitVec 64) : Option BoundaryValue :=
  let candidates := footprintLocations (callFootprint code args) ++
    (callRegions code args).map (fun r => r.base + (r.length : Int))
  (candidates.find? (fun l => pointerWord ι code args l == some word)).map BoundaryValue.loc

/-- A scalar register decodes by its declared signedness or pointer representation (facet 4). -/
def decodeValue (ι : Placement) (code : Code) (args : List BoundaryValue)
    (kind : ArgKind) (word : BitVec 64) : Option BoundaryValue :=
  match kind with
  | .int width =>
    let z := (word.setWidth width).toInt
    if inRange true width z then some (.int z) else none
  | .uint width =>
    let z := ((word.setWidth width).toNat : Int)
    if inRange false width z then some (.int z) else none
  | .loc | .array _ _ => decodePointer ι code args word
  | .unit => some .unit

/-- Read and decode the bytes of one logical cell from the actual Sail memory. -/
noncomputable def decodeCell (ι : Placement) (r : Region) (l : Loc)
    (s : Mach) : Option BoundaryValue := do
  let ((word, _), _) ← runSail (PreSail.readBytes (r.width / 8) (ι.addr l).toNat) s
  let z := if r.signed then (word.setWidth r.width).toInt else ((word.setWidth r.width).toNat : Int)
  if inRange r.signed r.width z then some (.int z) else none

/-- Decode every owned cell in logical order, rejecting unallocated or ill-typed bytes. -/
noncomputable def decodeF (ι : Placement) (code : Code) (args : List BoundaryValue)
    (F : Finset Loc) (s : Mach) : Option (LocHeap BoundaryValue) := do
  let entries ← (footprintLocations F).mapM fun l => do
    let r ← (callRegions code args).find? (fun r => decide (l ∈ r.cells))
    return (l, ← decodeCell ι r l s)
  return Iris.Std.PartialMap.ofList entries

/-- Patch the import slots of an assembled image with the placement's external addresses. -/
def relocatedBytes (ι : Placement) (image : Image) : List UInt8 :=
  image.importSlots.foldl (fun bytes (name, offset) =>
    (List.range 8).foldl (fun bytes i =>
      bytes.set (offset + i) (UInt8.ofNat ((ι.importAddr name).toNat / 2 ^ (8 * i)))) bytes)
    image.bytes

/-- A byte or instruction belongs to the assembled executable interval. -/
def codeRange (ι : Placement) (code : Code) (address : BitVec 64) : Prop :=
  ∃ image, assemble code.prog = .ok image ∧ inSpan ι.codeBase.toNat image.textLen address.toNat

/-- A byte belongs to the assembled image, including read-only data and import slots. -/
def imageByte (ι : Placement) (code : Code) (address : Nat) : Prop :=
  ∃ image, assemble code.prog = .ok image ∧ inSpan ι.codeBase.toNat image.bytes.length address

/-- The assembled image is installed apart from the footprint, with the entry PC set (facet 5). -/
def codeImage (ι : Placement) (code : Code) (args : List BoundaryValue) (s : Mach) : Prop :=
  ∃ image, assemble code.prog = .ok image ∧ InUserRam ι.codeBase image.bytes.length ∧
    ι.codeBase.toNat % 8 = 0 ∧ image.entry < image.textLen ∧
    pc s = some (BitVec.ofNat 64 (ι.codeBase.toNat + image.entry)) ∧
    (∀ i byte, (relocatedBytes ι image)[i]? = some byte →
      s.mem.get? (ι.codeBase.toNat + i) = some (BitVec.ofNat 8 byte.toNat)) ∧
    ∀ r ∈ callRegions code args,
      disjointSpans ι.codeBase.toNat image.bytes.length
        (ι.addr r.base).toNat (r.length * (r.width / 8))

/-- Import addresses are distinct and lie outside the code and owned data (facet 6). -/
def importPlacement (ι : Placement) (code : Code) (args : List BoundaryValue) : Prop :=
  (∀ name sig, (name, sig) ∈ code.sig.imports → ¬ imageByte ι code (ι.importAddr name).toNat ∧
      ¬ footprintByte ι code args (ι.importAddr name).toNat ∧
      (ι.importAddr name).toNat % 4 = 0) ∧
    ∀ n s m t, (n, s) ∈ code.sig.imports → (m, t) ∈ code.sig.imports → n ≠ m →
      ι.importAddr n ≠ ι.importAddr m

/-- The return address is aligned and differs from code, data and import stops (facet 7). -/
def returnPlacement (ι : Placement) (code : Code) (args : List BoundaryValue) (s : Mach) : Prop :=
  s.regs.get? .x1 = some ι.retAddr ∧ ι.retAddr.toNat % 4 = 0 ∧
    ¬ imageByte ι code ι.retAddr.toNat ∧ ¬ footprintByte ι code args ι.retAddr.toNat ∧
    ∀ name sig, (name, sig) ∈ code.sig.imports → ι.retAddr ≠ ι.importAddr name

/-- A byte is in the scratch stack interval reserved by the signature. -/
def stackByte (code : Code) (sp : BitVec 64) (a : Nat) : Prop :=
  inSpan (sp.toNat - code.sig.stackBound) code.sig.stackBound a

/-- A mapped, aligned scratch stack is separate from code, data and stops (facet 8). -/
def stackPlacement (ι : Placement) (code : Code) (args : List BoundaryValue) (s : Mach) : Prop :=
  ∃ sp, s.regs.get? .x2 = some sp ∧ sp.toNat % 16 = 0 ∧ code.sig.stackBound ≤ sp.toNat ∧
    InUserRam (BitVec.ofNat 64 (sp.toNat - code.sig.stackBound)) code.sig.stackBound ∧
    (∀ a, stackByte code sp a → ¬ footprintByte ι code args a ∧
      ¬ imageByte ι code a ∧ a ≠ ι.retAddr.toNat ∧
      ∀ name sig, (name, sig) ∈ code.sig.imports → a ≠ (ι.importAddr name).toNat)

/-- The integer registers preserved by the psABI, including the stack pointer (facet 9). -/
def calleeSaved : List Register :=
  [.x2, .x3, .x4, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- A return restores every callee-saved integer register (facet 9). -/
def calleeSavedRestored (s t : Mach) : Prop :=
  ∀ r ∈ calleeSaved, t.regs.get? r = s.regs.get? r

/-- The caller-saved integer and floating-point registers (facet 10). -/
def scratchRegisters : List Register :=
  [.x1, .x5, .x6, .x7, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x28, .x29,
    .x30, .x31, .f0, .f1, .f2, .f3, .f4, .f5, .f6, .f7, .f8, .f9, .f10, .f11, .f12,
    .f13, .f14, .f15, .f16, .f17, .f18, .f19, .f20, .f21, .f22, .f23, .f24, .f25,
    .f26, .f27, .f28, .f29, .f30, .f31]

/-- Every memory byte outside the footprint and scratch stack is preserved (facet 11). -/
def memoryFrame (ι : Placement) (code : Code) (args : List BoundaryValue) (s t : Mach) : Prop :=
  ∃ sp, s.regs.get? .x2 = some sp ∧ ∀ a,
    ¬ footprintByte ι code args a → ¬ stackByte code sp a → t.mem.get? a = s.mem.get? a

/-- Architectural counters, configuration and model state are preserved across the foreign call. -/
def configurationFrame (s t : Mach) : Prop :=
  (∀ r, r ∉ scratchRegisters → r ∉ calleeSaved →
    r ∉ [Register.PC, .nextPC, .minstret_increment] → t.regs.get? r = s.regs.get? r) ∧
    t.choiceState = s.choiceState ∧ t.tags = s.tags ∧ t.cycleCount = s.cycleCount ∧
      t.sailOutput = s.sailOutput

/-- The machine runs in user mode with trap vectors away from every ordinary stop (facet 12). -/
def machineConfiguration (ι : Placement) (code : Code) (s : Mach) : Prop :=
  UserConfig s ∧ ∀ value ∈ [s.regs.get? .mtvec, s.regs.get? .stvec], ∃ v,
    value = some v ∧ ¬ codeRange ι code v ∧ v ≠ ι.retAddr ∧
      ∀ name sig, (name, sig) ∈ code.sig.imports → v ≠ ι.importAddr name

/-- Decode the unique return or import observation of a stopped machine state. -/
noncomputable def observe (ι : Placement) (code : Code) (args : List BoundaryValue)
    (F : Finset Loc) (s : Mach) : Option (Stop BoundaryValue) := do
  let p ← pc s
  let heap ← decodeF ι code args F s
  if p == ι.retAddr then
    let word ← argumentRegister s 0
    return .ret (← decodeValue ι code args code.sig.result word) heap
  else
    let (name, sig) ← code.sig.imports.find? (fun entry => p == ι.importAddr entry.1)
    let values ← (sig.args.zipIdx).mapM fun (kind, i) => do
      return ← decodeValue ι code args kind (← argumentRegister s i)
    return .call name values heap

/-- The entry facets of a foreign call over the unmodified Sail machine. -/
def RVCompat (ι : Placement) (code : Code) (args : List BoundaryValue)
    (heap : LocHeap BoundaryValue) (s : Mach) : Prop :=
  footprintPlacement ι code args ∧ footprintContents ι code args heap s ∧
    argumentBindings ι args s ∧ codeImage ι code args s ∧ importPlacement ι code args ∧
    returnPlacement ι code args s ∧ stackPlacement ι code args s ∧ machineConfiguration ι code s

/-- The exit facets and deterministic decoded observation of a foreign call. -/
def RVExitCompat (ι : Placement) (code : Code) (args : List BoundaryValue)
    (F : Finset Loc) (s t : Mach) (stop : Stop BoundaryValue) : Prop :=
  observe ι code args F t = some stop ∧ memoryFrame ι code args s t ∧
    configurationFrame s t ∧ machineConfiguration ι code t ∧
    footprintPlacement ι code args ∧ F = callFootprint code args ∧
    match stop with
    | .ret _ _ => calleeSavedRestored s t
    | .call _ _ _ => ∃ ra, t.regs.get? .x1 = some ra ∧ codeRange ι code ra

/-- Resume an import with new footprint bytes and a return value while preserving its frame. -/
def RVResume (ι : Placement) (code : Code) (args : List BoundaryValue)
    (F : Finset Loc) (s : Mach) (response : BoundaryValue) (heap : LocHeap BoundaryValue)
    (t : Mach) : Prop :=
  ∃ name sig ra word,
    (name, sig) ∈ code.sig.imports ∧ pc s = some (ι.importAddr name) ∧
    s.regs.get? .x1 = some ra ∧ codeRange ι code ra ∧ pc t = some ra ∧
    (match response with
      | .loc l => pointerWord ι code args l = some word
      | _ => word = argumentWord ι response) ∧
    t.regs.get? .x10 = some word ∧ F = callFootprint code args ∧
    footprintContents ι code args heap t ∧ UserConfig t ∧
    calleeSavedRestored s t ∧ configurationFrame s t ∧
    ∀ a, ¬ footprintByte ι code args a → t.mem.get? a = s.mem.get? a

/-- The RISC-V interpretation uses actual Sail steps and the explicit ABI facets. -/
noncomputable def rv : AsmSemantics Code BoundaryValue where
  Mach := Mach
  runs ι code s Q := RunsTo (codeRange ι code) Q s
  Compat := RVCompat
  ExitCompat := RVExitCompat
  Resume := RVResume
  ResponseOK := boundaryResponseOK
  invalidResult := .unit

/-- Plain assembly specifications are quantified over every compatible Sail placement and state. -/
def RVSpec (code : Code) (args : List BoundaryValue) (heap : LocHeap BoundaryValue)
    (tree : Interaction BoundaryValue) : Prop :=
  rv.Spec code args (callFootprint code args) heap tree

/-- Deterministic Sail execution gives a shared stop for two terminating specifications. -/
theorem rv_runs_agree (ι : Placement) (code : Code) (s : Mach) (P Q : Mach → Prop)
    (hP : rv.runs ι code s P) (hQ : rv.runs ι code s Q) : ∃ t, P t ∧ Q t := hP.agree hQ

/-- Functional decoding gives each stopped Sail state at most one observation. -/
theorem rv_exit_det (ι : Placement) (code : Code) (args : List BoundaryValue)
    (F : Finset Loc) (s t : Mach) (a b : Stop BoundaryValue)
    (ha : rv.ExitCompat ι code args F s t a) (hb : rv.ExitCompat ι code args F s t b) : a = b :=
  Option.some.inj (ha.1.symm.trans hb.1)

end MetrologyAsm
