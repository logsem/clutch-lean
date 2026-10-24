import MetrologyAsm.Examples.OTP.Boundary
import MetrologyAsm.Sail.IntegerSteps

/-! # Physical addresses and separation for the OTP image and scratch stack -/

namespace MetrologyAsm.OTP

open ProbLang ProbLang.Asm Sail

/-- The address of an instruction indexed by its uncompressed word position. -/
def codePC (base : BitVec 64) (index : Nat) : BitVec 64 :=
  BitVec.addInt base (4 * (index : Int))

/-- The first instruction is at the image base. -/
@[simp] theorem codePC_zero (base : BitVec 64) : codePC base 0 = base := by
  simp [codePC, BitVec.addInt]

/-- Advancing by one instruction chooses the next word index. -/
theorem codePC_next (base : BitVec 64) (index : Nat) :
    BitVec.addInt (codePC base index) 4 = codePC base (index + 1) := by
  simp only [codePC, addInt_compose]
  congr 1

section CodeImage

variable {base : BitVec 64} (hram : InUserRam base 88)

include hram

/-- Image word addresses do not wrap within the eighty-eight-byte mapped image. -/
theorem codePC_toNat {index : Nat} (hi : index ≤ 22) :
    (codePC base index).toNat = base.toNat + 4 * index := by
  have hsmall : 4 * index < 2 ^ 64 := by omega
  have hsum : base.toNat + 4 * index < 2 ^ 64 := by
    obtain ⟨_, hend⟩ := hram
    omega
  simp only [codePC, BitVec.addInt, BitVec.toNat_add]
  have hcast : BitVec.ofInt 64 (4 * (index : Int)) = BitVec.ofNat 64 (4 * index) := by
    rw [show (4 * (index : Int)) = ((4 * index : Nat) : Int) by omega, BitVec.ofInt_natCast]
  rw [hcast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall, Nat.mod_eq_of_lt hsum]

/-- Every emitted instruction word is mapped into configured RAM. -/
theorem codePC_inUserRam {index : Nat} (hi : index < 20) :
    InUserRam (codePC base index) 4 := by
  rw [InUserRam, codePC_toNat hram (by omega)]
  obtain ⟨hl, hu⟩ := hram
  constructor <;> omega

/-- Every emitted word has the required four-byte instruction alignment. -/
theorem codePC_aligned (halign : base.toNat % 8 = 0) {index : Nat} (hi : index < 20) :
    (codePC base index).toNat % 4 = 0 := by
  rw [codePC_toNat hram (by omega)]
  omega

/-- The relocated eight-byte import slot is mapped within the complete image. -/
theorem slot_inUserRam : InUserRam (codePC base 20) 8 := by
  rw [InUserRam, codePC_toNat hram (by decide)]
  obtain ⟨hl, hu⟩ := hram
  constructor <;> omega

/-- The relocated import slot retains the image's eight-byte alignment. -/
theorem slot_aligned (halign : base.toNat % 8 = 0) : (codePC base 20).toNat % 8 = 0 := by
  rw [codePC_toNat hram (by decide)]
  omega

end CodeImage

section Stack

variable (sp : BitVec 64)

/-- The stack pointer after reserving the compiler's thirty-two-byte frame. -/
def reservedSP : BitVec 64 := BitVec.addInt sp (-32)

/-- A byte offset within the reserved scratch frame. -/
def stackAddress (offset : Nat) : BitVec 64 :=
  BitVec.addInt (reservedSP sp) (offset : Int)

/-- Reserving the scratch frame does not wrap a sufficiently large original stack pointer. -/
theorem reservedSP_toNat (hsp : 32 ≤ sp.toNat) :
    (reservedSP sp).toNat = sp.toNat - 32 := by
  have hsub : reservedSP sp = sp - 32#64 := by
    unfold reservedSP BitVec.addInt
    rw [BitVec.ofInt_neg, BitVec.sub_eq_add_neg]
    rfl
  have hle : 32#64 ≤ sp := by
    rw [BitVec.le_def]
    change 32 ≤ sp.toNat
    exact hsp
  rw [hsub, BitVec.toNat_sub_of_le hle]
  rfl

/-- Releasing the frame recovers the original stack pointer exactly. -/
theorem reservedSP_cancel : BitVec.addInt (reservedSP sp) 32 = sp := by
  rw [reservedSP, addInt_compose]
  simp [BitVec.addInt]

/-- Adding a bounded natural displacement to a word has its nonwrapping natural sum. -/
private theorem addNat_toNat (word : BitVec 64) (offset : Nat)
    (hsmall : offset < 2 ^ 64) (hsum : word.toNat + offset < 2 ^ 64) :
    (BitVec.addInt word (offset : Int)).toNat = word.toNat + offset := by
  simp only [BitVec.addInt, BitVec.ofInt_natCast, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hsmall, Nat.mod_eq_of_lt hsum]

/-- Scratch-slot offsets have their nonwrapping natural addresses. -/
theorem stackAddress_toNat (hsp : 32 ≤ sp.toNat)
    {offset : Nat} (hoff : offset ≤ 32) :
    (stackAddress sp offset).toNat = sp.toNat - 32 + offset := by
  have hsmall : offset < 2 ^ 64 := by omega
  have hbase := reservedSP_toNat sp hsp
  have hsum : (reservedSP sp).toNat + offset < 2 ^ 64 := by
    rw [hbase]
    have := sp.isLt
    omega
  calc
    (stackAddress sp offset).toNat = (reservedSP sp).toNat + offset := addNat_toNat _ _ hsmall hsum
    _ = sp.toNat - 32 + offset := congrArg (· + offset) hbase

/-- Distinct aligned scratch slots do not overlap. -/
theorem stackAddress_disjoint (hsp : 32 ≤ sp.toNat)
    {first second : Nat} (hf : first + 8 ≤ 32) (hs : second + 8 ≤ 32)
    (halignf : first % 8 = 0) (haligns : second % 8 = 0) (hne : first ≠ second) :
    disjointSpans (stackAddress sp first).toNat 8 (stackAddress sp second).toNat 8 := by
  rw [stackAddress_toNat sp hsp (by omega), stackAddress_toNat sp hsp (by omega)]
  unfold disjointSpans
  omega

end Stack

/-- Raw address facts that a compiled OTP run needs for its image, pad byte and scratch frame. -/
structure RawLayout (base sp pad callback ret : BitVec 64) : Prop where
  /-- The entire code and relocation image is mapped into user RAM. -/
  codeRam : InUserRam base 88
  /-- The image begins at an ABI-aligned address. -/
  codeAlign : base.toNat % 8 = 0
  /-- The original stack pointer permits a nonwrapping reservation. -/
  stackLower : 32 ≤ sp.toNat
  /-- The original stack pointer is sixteen-byte aligned. -/
  stackAlign : sp.toNat % 16 = 0
  /-- The complete reserved scratch interval is mapped. -/
  stackRam : InUserRam (BitVec.ofNat 64 (sp.toNat - 32)) 32
  /-- The private pad cell is mapped. -/
  padRam : InUserRam pad 1
  /-- The code image and reserved scratch interval do not overlap. -/
  codeStack : disjointSpans base.toNat 88 (sp.toNat - 32) 32
  /-- The code image and owned pad byte do not overlap. -/
  codePad : disjointSpans base.toNat 88 pad.toNat 1
  /-- The scratch frame and owned pad byte do not overlap. -/
  stackPad : disjointSpans (sp.toNat - 32) 32 pad.toNat 1
  /-- The imported function address is instruction aligned. -/
  callbackAlign : callback.toNat % 4 = 0
  /-- The original return target is instruction aligned. -/
  returnAlign : ret.toNat % 4 = 0

section RawLayoutFacts

variable {base sp pad callback ret : BitVec 64} (h : RawLayout base sp pad callback ret)
  {offset : Nat}

include h

/-- Each complete doubleword slot in the scratch frame is mapped. -/
theorem RawLayout.stack_inUserRam (hoff : offset + 8 ≤ 32) :
    InUserRam (stackAddress sp offset) 8 := by
  rw [InUserRam, stackAddress_toNat sp h.stackLower (by omega)]
  have hstack := h.stackRam
  have hsmall : sp.toNat - 32 < 2 ^ 64 := by have := sp.isLt; omega
  simp only [InUserRam, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall] at hstack
  constructor <;> omega

/-- Eight-byte-aligned offsets remain aligned in the sixteen-byte-aligned scratch frame. -/
theorem RawLayout.stack_aligned (hoff : offset ≤ 32) (halign : offset % 8 = 0) :
    (stackAddress sp offset).toNat % 8 = 0 := by
  rw [stackAddress_toNat sp h.stackLower hoff]
  have := h.stackAlign
  have := h.stackLower
  omega

/-- A scratch write preserves the instruction word at one code index. -/
theorem RawLayout.stack_code_disjoint {index : Nat} (hoff : offset + 8 ≤ 32)
    (hi : index < 20) :
    disjointSpans (stackAddress sp offset).toNat 8 (codePC base index).toNat 4 := by
  rw [stackAddress_toNat sp h.stackLower (by omega), codePC_toNat h.codeRam (by omega)]
  have := h.codeStack
  unfold disjointSpans at *
  omega

/-- A scratch write preserves the relocated import slot. -/
theorem RawLayout.stack_slot_disjoint (hoff : offset + 8 ≤ 32) :
    disjointSpans (stackAddress sp offset).toNat 8 (codePC base 20).toNat 8 := by
  rw [stackAddress_toNat sp h.stackLower (by omega), codePC_toNat h.codeRam (by decide)]
  have := h.codeStack
  unfold disjointSpans at *
  omega

/-- A scratch write leaves the private pad byte outside its modified interval. -/
theorem RawLayout.stack_pad_disjoint (hoff : offset + 8 ≤ 32) :
    disjointSpans (stackAddress sp offset).toNat 8 pad.toNat 1 := by
  rw [stackAddress_toNat sp h.stackLower (by omega)]
  have := h.stackPad
  unfold disjointSpans at *
  omega

end RawLayoutFacts

end MetrologyAsm.OTP
