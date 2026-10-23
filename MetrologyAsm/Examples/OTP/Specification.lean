import MetrologyAsm.Examples.OTP.Observation

/-! # The universal actual Sail specification for the compiled one-byte OTP -/

namespace MetrologyAsm.OTP

open ProbLang ProbLang.Asm Sail

/-- The compiled OTP calls randombytes and encrypts its fresh byte for every ABI-compatible run. -/
theorem otp_rvspec (message : Int) (pad : Loc) (initial : Int)
    (hm : 0 ≤ message ∧ message < 256) (hi : inRange false 8 initial = true) :
    RVSpec otpCode (otpArgs message pad) (padHeap pad initial) (otpTree message pad initial) := by
  intro ι origin hcompat
  change Mach at origin
  let a := entryInputs ι origin message pad
  have layout := entryInputs_layout ι origin message pad (padHeap pad initial) hcompat
  have hbindings := entryInputs_registers ι origin message pad hcompat.2.2.2.2.2.2.2.1
  have hplacement := hcompat.1
  have hcontents := hcompat.2.1
  have hreturn := hcompat.2.2.2.2.2.1
  have hconfig := hcompat.2.2.2.2.2.2.2
  have hprefix := entry_runsTo_call ι origin message pad (padHeap pad initial) hcompat
  have hprefixFrame := a.paused_configurationFrame origin
  have hprefixMemory := a.paused_memoryFrame ι origin message pad hbindings.1 layout.stackLower
  have hbytePrefix : (a.paused origin).mem.get? (ι.addr pad).toNat =
      some (BitVec.ofInt 8 initial) :=
    (a.paused_pad origin layout).trans (byte_of_footprintContents ι origin message pad initial
      hcontents)
  have hregisters := a.paused_registers origin
  rw [otp_footprint, otpTree_eq]
  apply hprefix.mono
  intro paused hpaused
  subst paused
  refine ⟨?_, ?_⟩
  · refine ⟨?_, hprefixMemory, hprefixFrame, ?_, hplacement,
      (otp_footprint message pad).symm, ?_⟩
    · exact observe_call ι _ message pad initial (a.paused_pc origin)
        (hreturn.2.2.2.2 "randombytes" ⟨[.array 8 (.arg 1), .uint 64], .unit⟩
          (by simp [otpCode, otpSig])) hregisters.2.2.2.2.1 hregisters.2.2.2.2.2 hi hbytePrefix
    · exact machineConfiguration.of_configurationFrame ι otpCode hconfig
        (a.config_paused hconfig.1) hprefixFrame
    · exact ⟨codePC a.base 10, hregisters.2.1,
        codeRange_codePC ι layout.codeRam (by decide)⟩
  · intro response heap hresponse current hresume
    change Mach at current
    obtain ⟨rfl, byte, rfl, _, hb⟩ := (otp_response_iff message pad response heap).mp hresponse
    rw [otpNext_valid _ _ _ _ hresponse, padValue_padHeap]
    obtain ⟨actualByte, hactual, _, hrun⟩ := resume_runsTo_return ι origin current message pad
      (padHeap pad initial) (padHeap pad byte) .unit hcompat hresume
    have hbyteEq : actualByte = byte := by simpa using hactual.symm
    subst actualByte
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hcurrentContents,
      hcurrentProfile, hcallee, hresumeFrame, hresumeMemory⟩ := hresume
    have hcurrentByte := byte_of_footprintContents ι current message pad byte hcurrentContents
    apply hrun.mono
    intro final hfinal
    subst final
    have hfinalFrame := (hprefixFrame.trans hresumeFrame).trans
      (returnState_configurationFrame current a.base a.sp a.message a.ret a.savedS0 a.savedS1
        (BitVec.ofInt 8 byte))
    have hfinalRegs := returnState_registers current a.base a.sp a.message a.ret a.savedS0
      a.savedS1 (BitVec.ofInt 8 byte)
    have hbBounds : 0 ≤ byte ∧ byte < 256 := by simpa [inRange] using hb
    have hcBounds := byteXor_range message byte
    have hcRange : inRange false 64 (byteXor message byte) = true := by
      simp [inRange]
      omega
    have hxor : (BitVec.ofInt 8 byte).setWidth 64 ^^^ a.message =
        BitVec.ofInt 64 (byteXor message byte) := by
      rw [byte_setWidth64 byte hb, BitVec.xor_comm]
      exact (byteXor_word64 message byte hm hbBounds).symm
    refine ⟨?_, ?_, hfinalFrame, ?_, hplacement, (otp_footprint message pad).symm, ?_⟩
    · exact observe_ret ι _ message pad byte (byteXor message byte)
        (returnState_pc _ _ _ _ _ _ _ _)
        (hfinalRegs.2.2.2.2.trans (congrArg some hxor)) hb hcRange hcurrentByte
    · obtain ⟨stack, hstack, hframe⟩ := hprefixMemory
      refine ⟨stack, hstack, ?_⟩
      intro address hfoot hstack
      rw [returnState_mem]
      exact (hresumeMemory address hfoot).trans (hframe address hfoot hstack)
    · exact machineConfiguration.of_configurationFrame ι otpCode hconfig
        (hcurrentProfile.otpReturnState _ _ _ _ _ _ _) hfinalFrame
    · exact a.return_originalCallee origin current (BitVec.ofInt 8 byte) hbindings.1
        hbindings.2.1 hbindings.2.2 hcallee

end MetrologyAsm.OTP
