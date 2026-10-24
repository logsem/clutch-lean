import MetrologyAsm.Examples.OTP.Execution

/-! # Physical frame preservation across the compiled OTP call and continuation -/

namespace MetrologyAsm.OTP

open ProbLang ProbLang.Asm Sail

/-- A list of scratch, callee-saved and bookkeeping registers avoids any frame register. -/
theorem notMem_of_frame (S : List Register)
    (hS : ∀ r ∈ S, r ∈ scratchRegisters ∨ r ∈ calleeSaved ∨
      r ∈ [Register.PC, .nextPC, .minstret_increment])
    (r : Register) (hscratch : r ∉ scratchRegisters) (hcallee : r ∉ calleeSaved)
    (hbookkeeping : r ∉ [Register.PC, .nextPC, .minstret_increment]) : r ∉ S :=
  fun h => by rcases hS r h with h | h | h <;> contradiction

/-- The import prefix preserves the full architectural configuration frame. -/
theorem CallInputs.paused_configurationFrame (a : CallInputs) (s : Mach) :
    configurationFrame s (a.paused s) := by
  have hf := a.paused_fields s
  exact ⟨fun r hs hc hb =>
    a.paused_reg_other s r (notMem_of_frame _ (by decide +kernel) r hs hc hb),
    hf.1, hf.2.1, hf.2.2.1, hf.2.2.2⟩

/-- The seven-instruction continuation preserves the full configuration frame. -/
theorem returnState_configurationFrame (s : Mach)
    (base sp message ret savedS0 savedS1 : BitVec 64) (byte : BitVec 8) :
    configurationFrame s (returnState s base sp message ret savedS0 savedS1 byte) := by
  have hf := returnState_fields s base sp message ret savedS0 savedS1 byte
  exact ⟨fun r hs hc hb => returnState_reg_other s base sp message ret savedS0 savedS1 byte r
    (notMem_of_frame _ (by decide +kernel) r hs hc hb),
    hf.1, hf.2.1, hf.2.2.1, hf.2.2.2⟩

/-- The prefix's scratch writes obey the original call's ABI memory frame. -/
theorem CallInputs.paused_memoryFrame (a : CallInputs) (ι : Placement) (s : Mach)
    (message : Int) (pad : Loc) (hsp : s.regs.get? .x2 = some a.sp)
    (hlower : 32 ≤ a.sp.toNat) :
    memoryFrame ι otpCode (otpArgs message pad) s (a.paused s) := by
  refine ⟨a.sp, hsp, ?_⟩
  intro address _ hstack
  apply a.paused_mem_outside s hlower
  change ¬inSpan (a.sp.toNat - 32) 32 address at hstack
  unfold inSpan at hstack
  omega

/-- The complete return restores the original callee-saved frame. -/
theorem CallInputs.return_originalCallee (a : CallInputs) (origin current : Mach)
    (byte : BitVec 8) (hsp : origin.regs.get? .x2 = some a.sp)
    (hs0 : origin.regs.get? .x8 = some a.savedS0) (hs1 : origin.regs.get? .x9 = some a.savedS1)
    (hresume : calleeSavedRestored (a.paused origin) current) :
    calleeSavedRestored origin
      (returnState current a.base a.sp a.message a.ret a.savedS0 a.savedS1 byte) := by
  have hregs := returnState_registers current a.base a.sp a.message a.ret a.savedS0 a.savedS1 byte
  intro r hr
  by_cases h2 : r = .x2
  · subst r
    exact hregs.1.trans hsp.symm
  by_cases h8 : r = .x8
  · subst r
    exact hregs.2.2.1.trans hs0.symm
  by_cases h9 : r = .x9
  · subst r
    exact hregs.2.2.2.1.trans hs1.symm
  have hcall : r ∉ [Register.PC, .nextPC, .minstret_increment, .x1, .x2,
      .x8, .x9, .x10, .x11, .x28] := fun hmem => by
    have key : ∀ r ∈ [Register.PC, .nextPC, .minstret_increment, .x1, .x2,
        .x8, .x9, .x10, .x11, .x28], r ∉ calleeSaved ∨ r = .x2 ∨ r = .x8 ∨ r = .x9 := by
      decide +kernel
    rcases key r hmem with h | h | h | h <;> contradiction
  have hreturn : r ∉ [Register.PC, .nextPC, .minstret_increment, .x1, .x2, .x8, .x9, .x10] :=
    fun hmem => hcall ((by decide +kernel :
      ∀ r ∈ [Register.PC, .nextPC, .minstret_increment, .x1, .x2, .x8, .x9, .x10],
        r ∈ [Register.PC, .nextPC, .minstret_increment, .x1, .x2, .x8, .x9, .x10, .x11, .x28])
      r hmem)
  exact (returnState_reg_other current a.base a.sp a.message a.ret a.savedS0 a.savedS1
    byte r hreturn).trans ((hresume r hr).trans (a.paused_reg_other origin r hcall))

end MetrologyAsm.OTP
