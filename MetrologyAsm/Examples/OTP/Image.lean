import MetrologyAsm.Examples.OTP.Layout
import MetrologyAsm.Examples.OTP.Steps

/-! # Physical instruction and relocation assertions for the compiled OTP image -/

namespace MetrologyAsm.OTP

/-- Every compiled instruction and the relocated randombytes address are installed. -/
structure ImageAt (s : Mach) (base callback : BitVec 64) : Prop where
  /-- All twenty words have the exact compiler/decoder-certified encodings. -/
  words : ∀ i : Fin 20, Word32At s (codePC base i) (otpWord i)
  /-- The relocation slot contains the concrete callback entry. -/
  slot : Word64At s (codePC base 20) callback

/-- Equal memory retains every instruction and import-address byte. -/
theorem ImageAt.of_mem_eq {s t : Mach} {base callback : BitVec 64}
    (h : ImageAt s base callback) (hm : t.mem = s.mem) : ImageAt t base callback :=
  ⟨fun i => (h.words i).of_mem_eq hm, h.slot.of_mem_eq hm⟩

/-- Pointwise preservation of the installed image suffices even when private pad memory changes. -/
theorem ImageAt.of_mem_eq_on_image {s t : Mach} {base callback : BitVec 64}
    (h : ImageAt s base callback) (hram : InUserRam base 88)
    (hm : ∀ address, inSpan base.toNat 88 address → t.mem.get? address = s.mem.get? address) :
    ImageAt t base callback := by
  constructor
  · intro j i hi
    rw [hm]
    · exact h.words j i hi
    · have hj := j.isLt
      rw [codePC_toNat hram (by omega)]
      constructor <;> omega
  · intro i hi
    rw [hm]
    · exact h.slot i hi
    · rw [codePC_toNat hram (by decide)]
      constructor <;> omega

/-- A scratch-frame write preserves the complete executable and relocated image. -/
theorem ImageAt.write64State {s : Mach} {base sp pad callback ret : BitVec 64}
    (h : ImageAt s base callback) (layout : RawLayout base sp pad callback ret)
    (value : BitVec 64) {offset : Nat} (hoff : offset + 8 ≤ 32) :
    ImageAt (write64State s (stackAddress sp offset) value) base callback :=
  ⟨fun i => (h.words i).write64State value (layout.stack_code_disjoint hoff i.isLt),
    h.slot.write64State value (layout.stack_slot_disjoint hoff)⟩

/-- The seven source words executed after the randombytes callback returns. -/
structure ContinuationAt (s : Mach) (base : BitVec 64) : Prop where
  /-- Read the freshly sampled pad byte. -/
  loadPad : Word32At s (codePC base 10) 0x00044503#32
  /-- Combine the pad with the saved message. -/
  xor : Word32At s (codePC base 11) 0x00954533#32
  /-- Restore the caller's return address. -/
  restoreRA : Word32At s (codePC base 12) 0x01813083#32
  /-- Restore the caller's s0. -/
  restoreS0 : Word32At s (codePC base 13) 0x01013403#32
  /-- Restore the caller's s1. -/
  restoreS1 : Word32At s (codePC base 14) 0x00813483#32
  /-- Release the scratch frame. -/
  release : Word32At s (codePC base 15) 0x02010113#32
  /-- Return to the caller. -/
  ret : Word32At s (codePC base 16) 0x00008067#32

/-- The complete compiler image contains its post-callback continuation. -/
theorem ImageAt.continuation {s : Mach} {base callback : BitVec 64}
    (h : ImageAt s base callback) : ContinuationAt s base :=
  ⟨h.words ⟨10, by decide⟩, h.words ⟨11, by decide⟩, h.words ⟨12, by decide⟩,
    h.words ⟨13, by decide⟩, h.words ⟨14, by decide⟩, h.words ⟨15, by decide⟩,
    h.words ⟨16, by decide⟩⟩

/-- Equal memory retains the seven continuation instruction words. -/
theorem ContinuationAt.of_mem_eq {s t : Mach} {base : BitVec 64}
    (h : ContinuationAt s base) (hm : t.mem = s.mem) : ContinuationAt t base :=
  ⟨h.loadPad.of_mem_eq hm, h.xor.of_mem_eq hm, h.restoreRA.of_mem_eq hm,
    h.restoreS0.of_mem_eq hm, h.restoreS1.of_mem_eq hm, h.release.of_mem_eq hm,
    h.ret.of_mem_eq hm⟩

end MetrologyAsm.OTP
