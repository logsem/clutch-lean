import MetrologyAsm.Examples.Callback.Placement
import MetrologyAsm.Examples.Support

/-! # A genuine compatible entry state for the callback source -/

set_option maxRecDepth 100000

namespace MetrologyAsm

open ProbLang ProbLang.Asm RiscvZkvm.Sail.Functions
open Sail.ConcurrencyInterfaceV1

/-- The callback witness uses distinct aligned code, callback, return, trap, and stack addresses. -/
def importWitnessPlacement : Placement := witnessPlacement 0

/-- Install the actual relocated callback image into the complete profiled register state. -/
noncomputable def importWitnessState : Mach :=
  { witnessRegisters with
    mem := witnessImageBytes (relocatedBytes importWitnessPlacement importToyImage)
      0x80000000 witnessRegisters.mem }

/-- The callback source has no logical pointer regions. -/
@[simp]
theorem importToy_callRegions : callRegions importToyCode [] = [] := by rfl

/-- The callback source owns no logical heap cells. -/
@[simp]
theorem importToy_callFootprint : callFootprint importToyCode [] = ∅ := by rfl

/-- The no-argument callback source accepts exactly the empty logical fragment. -/
theorem importToy_empty_valid : validFragment importToyCode [] ∅ := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · rw [importToy_callFootprint]
    symm
    apply Std.ExtTreeMap.ext_getElem?
    intro l
    simp
  · rfl

/-- Installing the relocated image preserves the formal user-mode register profile. -/
theorem importWitnessState_config : UserConfig importWitnessState :=
  witnessRegisters_config.of_regs_eq rfl

/-- The empty footprint has no physical storage obligations. -/
theorem importWitness_footprintPlacement :
    footprintPlacement importWitnessPlacement importToyCode [] := by
  simp [footprintPlacement]

/-- The concrete callback entry realizes its valid empty logical heap. -/
theorem importWitness_footprintContents :
    footprintContents importWitnessPlacement importToyCode [] ∅ importWitnessState := by
  refine ⟨importToy_empty_valid, ?_⟩
  simp

/-- No argument registers are constrained by the no-argument callback source. -/
theorem importWitness_argumentBindings :
    argumentBindings importWitnessPlacement [] importWitnessState := by
  intro i v hv
  simp at hv

/-- The source assembler's complete relocated callback image is installed. -/
theorem importWitness_codeImage :
    codeImage importWitnessPlacement importToyCode [] importWitnessState := by
  refine ⟨importToyImage, assemble_importToyImage, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [importToyImage_length]
    change InUserRam 0x80000000#64 48
    unfold InUserRam
    decide +kernel
  · change (0x80000000#64).toNat % 8 = 0
    decide +kernel
  · rw [importToyImage_entry, importToyImage_textLen]
    decide +kernel
  · simp [pc, importWitnessState, importWitnessPlacement, witnessPlacement,
      witnessRegisters, importToyImage_entry, Std.ExtDHashMap.get?_insert]
  · intro i byte hi
    exact witnessImageBytes_get _ _ _ _ _ hi
  · simp

/-- A byte above the complete source image cannot overlap the installed callback image. -/
theorem importWitness_not_imageByte (address : Nat) (hout : 0x80000000 + 48 ≤ address) :
    ¬ imageByte importWitnessPlacement importToyCode address := by
  rw [imageByte_importToy]
  change ¬(0x80000000 ≤ address ∧ address < 0x80000000 + 48)
  omega

/-- An address above the complete image cannot be an executable callback instruction. -/
theorem importWitness_not_codeRange (address : BitVec 64)
    (hout : 0x80000000 + 48 ≤ address.toNat) :
    ¬ codeRange importWitnessPlacement importToyCode address := by
  intro h
  exact importWitness_not_imageByte address.toNat hout (imageByte_of_codeRange_importToy _ _ h)

/-- The empty logical footprint has no physical bytes. -/
theorem importWitness_not_footprintByte (address : Nat) :
    ¬ footprintByte importWitnessPlacement importToyCode [] address := by
  simp [footprintByte]

/-- The single callback address is aligned and outside the full image and logical footprint. -/
theorem importWitness_importPlacement :
    importPlacement importWitnessPlacement importToyCode [] := by
  constructor
  · intro name sig hmem
    have heq : name = "cb" ∧ sig = ⟨[], .int 64⟩ := by simpa [importToyCode] using hmem
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨importWitness_not_imageByte _ (by decide +kernel),
      importWitness_not_footprintByte _, by decide +kernel⟩
  · intro n sig m ty hn hm hne
    have hn' : n = "cb" ∧ sig = ⟨[], .int 64⟩ := by simpa [importToyCode] using hn
    have hm' : m = "cb" ∧ ty = ⟨[], .int 64⟩ := by simpa [importToyCode] using hm
    exact (hne (hn'.1.trans hm'.1.symm)).elim

/-- The original return address is a separate aligned external stop. -/
theorem importWitness_returnPlacement :
    returnPlacement importWitnessPlacement importToyCode [] importWitnessState := by
  refine ⟨?_, ?_, ?_, importWitness_not_footprintByte _, ?_⟩
  · simp [importWitnessState, importWitnessPlacement, witnessPlacement,
      witnessRegisters, Std.ExtDHashMap.get?_insert]
  · change (0x80002000#64).toNat % 4 = 0
    decide +kernel
  · exact importWitness_not_imageByte _ (by decide +kernel)
  · intro name sig _
    change 0x80002000#64 ≠ 0x80005000#64
    decide +kernel

/-- The original scratch frame is mapped, aligned, and separate from image and stop addresses. -/
theorem importWitness_stackPlacement :
    stackPlacement importWitnessPlacement importToyCode [] importWitnessState := by
  refine ⟨0x80004000#64, ?_, by decide +kernel, ?_, ?_, ?_⟩
  · simp [importWitnessState, witnessRegisters, Std.ExtDHashMap.get?_insert]
  · change 16 ≤ (0x80004000#64).toNat
    decide +kernel
  · change InUserRam 0x80003ff0#64 16
    unfold InUserRam
    decide +kernel
  · intro address hs
    change 0x80003ff0 ≤ address ∧ address < 0x80004000 at hs
    refine ⟨importWitness_not_footprintByte _, importWitness_not_imageByte _ (by omega), ?_, ?_⟩
    · change address ≠ 0x80002000
      omega
    · intro name sig _
      change address ≠ 0x80005000
      omega

/-- The witness's direct trap vectors are separate from its executable code and both stops. -/
theorem importWitness_machineConfiguration :
    machineConfiguration importWitnessPlacement importToyCode importWitnessState := by
  refine ⟨importWitnessState_config, ?_⟩
  have hmt : importWitnessState.regs.get? Register.mtvec = some 0x80003000#64 := by
    simp [importWitnessState, witnessRegisters, Std.ExtDHashMap.get?_insert]
  have hst : importWitnessState.regs.get? Register.stvec = some 0x80003000#64 := by
    simp [importWitnessState, witnessRegisters]
  intro value hv
  simp only [hmt, hst, List.mem_cons, List.not_mem_nil, or_false, or_self] at hv
  subst value
  refine ⟨0x80003000#64, rfl, importWitness_not_codeRange _ (by decide +kernel), ?_, ?_⟩
  · change 0x80003000#64 ≠ 0x80002000#64
    decide +kernel
  · intro name sig _
    change 0x80003000#64 ≠ 0x80005000#64
    decide +kernel

/-- Every ABI entry facet is realized by actual profiled registers and relocated source bytes. -/
theorem importWitness_compatible :
    RVCompat importWitnessPlacement importToyCode [] ∅ importWitnessState := by
  exact ⟨importWitness_footprintPlacement, importWitness_footprintContents,
    importWitness_argumentBindings, importWitness_codeImage, importWitness_importPlacement,
    importWitness_returnPlacement, importWitness_stackPlacement, importWitness_machineConfiguration⟩

/-- The actual callback source has a genuine compatible Sail entry machine. -/
theorem importToy_compat_exists : ∃ ι s, RVCompat ι importToyCode [] ∅ s :=
  ⟨importWitnessPlacement, importWitnessState, importWitness_compatible⟩

end MetrologyAsm
