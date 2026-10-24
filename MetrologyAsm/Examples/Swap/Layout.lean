import MetrologyAsm.Profile.Config

/-! # Address arithmetic for the five-instruction exchange -/

namespace MetrologyAsm

open Sail.BitVec

/-- The address of an uncompressed instruction relative to the image base. -/
def pcAt (base : BitVec 64) (i : Nat) : BitVec 64 :=
  addInt base (4 * (i : Int))

/-- An instruction address in a mapped exchange image does not wrap. -/
theorem pcAt_toNat {base : BitVec 64} (hram : InUserRam base 20) {i : Nat} (hi : i < 5) :
    (pcAt base i).toNat = base.toNat + 4 * i := by
  have hsmall : 4 * i < 2 ^ 64 := by omega
  have hsum : base.toNat + 4 * i < 2 ^ 64 := by
    obtain ⟨_, hend⟩ := hram
    omega
  simp only [pcAt, addInt, BitVec.toNat_add]
  have hcast : BitVec.ofInt 64 (4 * (i : Int)) = BitVec.ofNat 64 (4 * i) := by
    rw [show (4 * (i : Int)) = ((4 * i : Nat) : Int) by omega, BitVec.ofInt_natCast]
  rw [hcast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall, Nat.mod_eq_of_lt hsum]

/-- Each instruction of a mapped exchange image is mapped. -/
theorem pcAt_inUserRam {base : BitVec 64} (hram : InUserRam base 20) {i : Nat}
    (hi : i < 5) : InUserRam (pcAt base i) 4 := by
  rw [InUserRam, pcAt_toNat hram hi]
  obtain ⟨hstart, hend⟩ := hram
  constructor <;> omega

/-- Each instruction of an aligned exchange image is aligned. -/
theorem pcAt_aligned {base : BitVec 64} (hram : InUserRam base 20)
    (halign : base.toNat % 4 = 0) {i : Nat} (hi : i < 5) :
    (pcAt base i).toNat % 4 = 0 := by
  rw [pcAt_toNat hram hi, Nat.add_mod, halign, Nat.mul_mod]
  simp

/-- Advancing an instruction address selects the next image word. -/
theorem pcAt_next (base : BitVec 64) (i : Nat) :
    addInt (pcAt base i) 4 = pcAt base (i + 1) := by
  change (base + BitVec.ofInt 64 (4 * (i : Int))) + BitVec.ofInt 64 4 = _
  rw [BitVec.add_assoc, ← BitVec.ofInt_add]
  unfold pcAt addInt
  congr 2

/-- The first instruction is at the image base. -/
@[simp] theorem pcAt_zero (base : BitVec 64) : pcAt base 0 = base := by
  simp [pcAt, addInt]

end MetrologyAsm
