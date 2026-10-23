import MetrologyAsm.ImportImage
import MetrologyAsm.ImportObservation

/-! # The universal Sail callback specification -/

namespace MetrologyAsm

open ProbLang ProbLang.Asm RiscvZkvm.Sail.Functions

/-- The source calls the import and returns its reply for every compatible entry and resumption. -/
theorem importToy_rvspec : RVSpec importToyCode [] ∅ importToyTree := by
  intro ι origin hcompat
  change Mach at origin
  have hlayout := ImportToyPlacement.of_RVCompat ι origin ∅ hcompat
  obtain ⟨sp, hsp, layout⟩ := hlayout
  obtain ⟨hplacement, _, _, himage, himports, hreturn, hstack, hconfig⟩ := hcompat
  have hrawImage := ImportToyImageAt.of_codeImage ι origin himage
  have hcode := importToy_code_contains ι origin himage
  have hlower := importToy_stack_lower ι origin sp hstack hsp
  have houtCallback : ¬ codeRange ι importToyCode (ι.importAddr "cb") := by
    intro hp
    exact (himports.1 "cb" ⟨[], .int 64⟩ (by simp [importToyCode])).1
      (imageByte_of_codeRange_importToy ι _ hp)
  have houtReturn : ¬ codeRange ι importToyCode ι.retAddr := by
    intro hp
    exact hreturn.2.2.1 (imageByte_of_codeRange_importToy ι _ hp)
  have hprefix := importToy_runsTo_call hconfig.1 ι.codeBase sp ι.retAddr (ι.importAddr "cb")
    layout hrawImage (codeImage_importToy_pc ι origin himage) hsp hreturn.1
    (codeRange ι importToyCode) hcode houtCallback
  have hprefixFrame := importCallState_configurationFrame origin ι.codeBase sp
    ι.retAddr (ι.importAddr "cb")
  have hprefixMemory := importCallState_memoryFrame ι origin sp hsp hlower
    (importSavedAddress_toNat sp hlower)
  rw [importToy_footprint, importToyTree_eq]
  apply hprefix.mono
  intro paused hpaused
  subst paused
  refine ⟨?_, ?_⟩
  · refine ⟨?_, hprefixMemory, hprefixFrame, ?_, hplacement, rfl, ?_⟩
    · apply observe_importToy_call
      · exact importCallState_pc origin _ _ _ _
      · exact hreturn.2.2.2.2 "cb" ⟨[], .int 64⟩ (by simp [importToyCode])
    · exact machineConfiguration.of_configurationFrame ι importToyCode hconfig
        (hconfig.1.importCallState _ _ _ _) hprefixFrame
    · refine ⟨importPC ι.codeBase 16, importCallState_ra origin _ _ _ _, ?_⟩
      exact hcode _ (by simp [importToyPCs])
  · intro response heap hresponse current hresume
    change Mach at current
    obtain ⟨z, rfl, rfl, hrange⟩ := (importToy_response_iff response heap).mp hresponse
    rw [importToyNext_valid _ _ hresponse]
    obtain ⟨name, sig, link, word, _, _, hlink, _, hcurrentPC, hword, ha0, _, _,
      hprofile, hcallee, hresumeFrame, hresumeMemory⟩ := hresume
    have hlinkEq : link = importPC ι.codeBase 16 :=
      Option.some.inj (hlink.symm.trans (importCallState_ra origin _ _ _ _))
    subst link
    change word = BitVec.ofInt 64 z at hword
    subst word
    have hmemory : ∀ a, current.mem.get? a =
        (importCallState origin ι.codeBase sp ι.retAddr (ι.importAddr "cb")).mem.get? a := by
      intro a
      exact hresumeMemory a (by simp [footprintByte])
    have hcurrentSP : current.regs.get? .x2 = some (importReservedSP sp) :=
      (hcallee .x2 (by decide +kernel)).trans (importCallState_sp origin _ _ _ _)
    have hsaved : Word64At current (importSavedAddress sp) ι.retAddr := by
      intro i hi
      rw [hmemory]
      exact importCallState_saved origin _ _ _ _ i hi
    have hcontinued := (importCallState_image hrawImage layout).continuation.of_mem_get_eq hmemory
    have hreturnRun := importToy_runsTo_return hprofile ι.codeBase sp ι.retAddr (ι.importAddr "cb")
      layout hcontinued hcurrentPC hcurrentSP hsaved (codeRange ι importToyCode) hcode houtReturn
    apply hreturnRun.mono
    intro final hfinal
    subst final
    have hfinalFrame := (hprefixFrame.trans hresumeFrame).trans
      (importReturnState_configurationFrame current ι.codeBase sp ι.retAddr)
    refine ⟨?_, ?_, hfinalFrame, ?_, hplacement, rfl, ?_⟩
    · apply observe_importToy_ret ι _ z (importReturnState_pc current _ _ _) _ hrange
      exact (importReturnState_reg_other current _ _ _ .x10 (by decide +kernel)).trans ha0
    · obtain ⟨stack, hstack, hframe⟩ := hprefixMemory
      refine ⟨stack, hstack, ?_⟩
      intro a hfoot hstack
      rw [importReturnState_mem]
      exact (hmemory a).trans (hframe a hfoot hstack)
    · exact machineConfiguration.of_configurationFrame ι importToyCode hconfig
        (hprofile.importReturnState _ _ _) hfinalFrame
    · exact importReturnState_originalCallee origin current _ _ _ _ hsp hcallee

end MetrologyAsm
