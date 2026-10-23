import MetrologyAsm.Examples.OTP.Image
import MetrologyAsm.Examples.OTP.Placement

/-! # The actual relocated source image supplies all OTP instruction and slot assertions -/

namespace MetrologyAsm.OTP

open ProbLang ProbLang.Asm
open List (range getElem?_append_left getElem?_append_right getElem?_take_of_lt getElem?_range)

/-- Every emitted instruction byte agrees with its officially decoded source word. -/
theorem otp_byte_certificate : ∀ j : Fin 20, ∀ i : Fin 4,
    otpImage.bytes[4 * j.val + i.val]? =
      some (UInt8.ofNat ((otpWord j).toNat / 2 ^ (8 * i.val))) := by
  decide +kernel

/-- Relocation preserves the eighty text bytes and patches the sole eight-byte import slot. -/
theorem relocatedBytes_otp (ι : Placement) :
    relocatedBytes ι otpImage = otpImage.bytes.take 80 ++
      (range 8).map (fun i => UInt8.ofNat ((ι.importAddr "randombytes").toNat / 2 ^ (8 * i))) := by
  rfl

/-- Every relocated executable byte equals its retained compiler-output byte. -/
theorem relocatedBytes_otp_text (ι : Placement) (i : Nat) (hi : i < 80) :
    (relocatedBytes ι otpImage)[i]? = otpImage.bytes[i]? := by
  rw [relocatedBytes_otp, getElem?_append_left (by simpa using hi)]
  exact getElem?_take_of_lt hi

/-- The imported function pointer is installed in little-endian order at text offset eighty. -/
theorem relocatedBytes_otp_slot (ι : Placement) (i : Nat) (hi : i < 8) :
    (relocatedBytes ι otpImage)[80 + i]? =
      some (UInt8.ofNat ((ι.importAddr "randombytes").toNat / 2 ^ (8 * i))) := by
  rw [relocatedBytes_otp, getElem?_append_right (by simp)]
  simp [getElem?_range hi]

/-- The real code-image facet installs all twenty instructions and the concrete randombytes slot. -/
theorem ImageAt.of_codeImage (ι : Placement) (s : Mach) (message : Int) (pad : Loc)
    (h : codeImage ι otpCode (otpArgs message pad) s) :
    ImageAt s ι.codeBase (ι.importAddr "randombytes") := by
  obtain ⟨image, hi, hram, _, _, _, hbytes, _⟩ := h
  have heq : image = otpImage := Except.ok.inj (hi.symm.trans assemble_otpImage)
  subst image
  have hram88 : InUserRam ι.codeBase 88 := hram
  constructor
  · intro j i hi
    have hj := j.isLt
    have htext : 4 * j.val + i < 80 := by omega
    have hlook := hbytes (4 * j.val + i) (UInt8.ofNat ((otpWord j).toNat / 2 ^ (8 * i)))
      ((relocatedBytes_otp_text ι _ htext).trans (otp_byte_certificate j ⟨i, hi⟩))
    simpa only [codePC_toNat hram88 (show j.val ≤ 22 by omega), Nat.add_assoc,
      bitVec_of_importByte] using hlook
  · intro i hi
    have hlook := hbytes (80 + i)
      (UInt8.ofNat ((ι.importAddr "randombytes").toNat / 2 ^ (8 * i)))
      (relocatedBytes_otp_slot ι i hi)
    simpa only [codePC_toNat hram88 (show 20 ≤ 22 by decide), Nat.reduceMul, Nat.add_assoc,
      bitVec_of_importByte] using hlook

end MetrologyAsm.OTP
