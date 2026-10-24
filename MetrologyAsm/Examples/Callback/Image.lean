import MetrologyAsm.Examples.Callback.Placement
import MetrologyAsm.Examples.Callback.Source
import MetrologyAsm.ABI.Interface

/-! # Installing the actual relocated callback image -/

namespace MetrologyAsm

open ProbLang ProbLang.Asm
open UInt8 (ofNat)

/-- The emitted word at a certified callback-instruction index. -/
def importToyWord (i : Fin 10) : BitVec 32 := importToyCases[i].1

/-- Every emitted instruction byte agrees with the officially decoded source word. -/
theorem importToy_byte_certificate : ∀ j : Fin 10, ∀ i : Fin 4,
    importToyImage.bytes[4 * j.val + i.val]? =
      some (ofNat ((importToyWord j).toNat / 2 ^ (8 * i.val))) := by
  decide +kernel

variable (ι : Placement)

/-- Relocation preserves all forty text bytes and patches the eight-byte callback slot. -/
theorem relocatedBytes_importToy :
    relocatedBytes ι importToyImage = importToyImage.bytes.take 40 ++
      (List.range 8).map (fun i => ofNat ((ι.importAddr "cb").toNat / 2 ^ (8 * i))) := by
  rfl

/-- Relocation leaves every executable byte equal to its emitted source byte. -/
theorem relocatedBytes_importToy_text (i : Nat) (hi : i < 40) :
    (relocatedBytes ι importToyImage)[i]? = importToyImage.bytes[i]? := by
  rw [relocatedBytes_importToy, List.getElem?_append_left (by simpa using hi)]
  exact List.getElem?_take_of_lt hi

/-- The relocated slot exposes the corresponding byte of the callback's open address. -/
theorem relocatedBytes_importToy_slot (i : Nat) (hi : i < 8) :
    (relocatedBytes ι importToyImage)[40 + i]? =
      some (ofNat ((ι.importAddr "cb").toNat / 2 ^ (8 * i))) := by
  rw [relocatedBytes_importToy, List.getElem?_append_right (by simp)]
  simp [List.getElem?_range hi]

/-- A machine with the relocated callback image installed satisfies `ImportToyImageAt`. -/
theorem ImportToyImageAt.of_codeImage (s : Mach)
    (h : codeImage ι importToyCode [] s) : ImportToyImageAt s ι.codeBase (ι.importAddr "cb") := by
  obtain ⟨image, hi, hram, _, _, _, hbytes, _⟩ := h
  have heq : image = importToyImage := Except.ok.inj (hi.symm.trans assemble_importToyImage)
  subst image
  have hram48 : InUserRam ι.codeBase 48 := by
    simpa only [importToyImage_length] using hram
  have h40 : (importPC ι.codeBase 40).toNat = ι.codeBase.toNat + 40 :=
    importPC_toNat hram48 (by decide)
  have hwords (j : Fin 10) :
      Word32At s (importPC ι.codeBase (4 * j.val : Nat)) (importToyWord j) := by
    intro i hi
    have hj := j.isLt
    have htext : 4 * j.val + i < 40 := by omega
    have hlook := hbytes (4 * j.val + i) (ofNat ((importToyWord j).toNat / 2 ^ (8 * i)))
      ((relocatedBytes_importToy_text ι _ htext).trans (importToy_byte_certificate j ⟨i, hi⟩))
    simpa only [importPC_toNat hram48 (show 4 * j.val < 48 by omega), Nat.add_assoc,
      bitVec_of_importByte] using hlook
  refine ⟨by simpa [importToyWord, importToyCases] using hwords 0, hwords 1, hwords 2,
    hwords 3, hwords 4, hwords 5, hwords 6, hwords 7, hwords 8, hwords 9, ?_⟩
  intro i hi
  have hlook := hbytes (40 + i) (ofNat ((ι.importAddr "cb").toNat / 2 ^ (8 * i)))
    (relocatedBytes_importToy_slot ι i hi)
  simpa only [h40, Nat.add_assoc, bitVec_of_importByte] using hlook

end MetrologyAsm
