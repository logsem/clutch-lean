import MetrologyAsm.Examples.Callback.Boundary
import MetrologyAsm.Examples.Callback.Execution
import MetrologyAsm.Examples.Callback.Placement
import MetrologyAsm.ABI.Lemmas

/-! # Whole-call frame preservation around the callback -/

namespace MetrologyAsm

open ProbLang ProbLang.Asm RiscvZkvm.Sail.Functions

/-- The import prefix preserves the complete configuration frame. -/
theorem importCallState_configurationFrame (s : Mach) (base sp ra callback : BitVec 64) :
    configurationFrame s (importCallState s base sp ra callback) := by
  obtain ⟨h1, h2, h3, h4⟩ := importCallState_fields s base sp ra callback
  refine ⟨?_, h1, h2, h3, h4⟩
  intro r hscratch hcallee hbookkeeping
  apply importCallState_reg_other
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hbookkeeping ⊢
  refine ⟨hbookkeeping.1, hbookkeeping.2.1, hbookkeeping.2.2, ?_, ?_, ?_⟩
  · exact fun heq => hscratch (heq ▸ by decide +kernel)
  · exact fun heq => hcallee (heq ▸ by decide +kernel)
  · exact fun heq => hscratch (heq ▸ by decide +kernel)

/-- The post-callback continuation preserves the complete configuration frame. -/
theorem importReturnState_configurationFrame (s : Mach) (base sp ra : BitVec 64) :
    configurationFrame s (importReturnState s base sp ra) := by
  obtain ⟨h1, h2, h3, h4⟩ := importReturnState_fields s base sp ra
  refine ⟨?_, h1, h2, h3, h4⟩
  intro r hscratch hcallee hbookkeeping
  apply importReturnState_reg_other
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hbookkeeping ⊢
  refine ⟨hbookkeeping.1, hbookkeeping.2.1, hbookkeeping.2.2, ?_, ?_⟩
  · exact fun heq => hscratch (heq ▸ by decide +kernel)
  · exact fun heq => hcallee (heq ▸ by decide +kernel)

/-- Saving ra changes no byte outside the original call's scratch stack. -/
theorem importCallState_memoryFrame (ι : Placement) (s : Mach) (sp : BitVec 64)
    (hsp : s.regs.get? .x2 = some sp) (hlower : 16 ≤ sp.toNat)
    (hsaved : (importSavedAddress sp).toNat = sp.toNat - 8) :
    memoryFrame ι importToyCode [] s
      (importCallState s ι.codeBase sp ι.retAddr (ι.importAddr "cb")) := by
  refine ⟨sp, hsp, ?_⟩
  intro a _ hstack
  apply importCallState_mem_outside
  rw [hsaved]
  change ¬ inSpan (sp.toNat - 16) 16 a at hstack
  unfold inSpan at hstack
  omega

/-- Returning after a callee-saved-preserving callback restores the original callee-saved set. -/
theorem importReturnState_originalCallee (origin current : Mach)
    (base sp ra callback : BitVec 64) (hsp : origin.regs.get? .x2 = some sp)
    (hresume : calleeSavedRestored (importCallState origin base sp ra callback) current) :
    calleeSavedRestored origin (importReturnState current base sp ra) := by
  intro r hr
  by_cases heq : r = .x2
  · subst r
    exact (importReturnState_sp current base sp ra).trans hsp.symm
  · have hbase : r ∉ [Register.PC, .nextPC, .minstret_increment, .x1, .x28] :=
      (by decide +kernel : ∀ r ∈ calleeSaved,
        r ∉ [Register.PC, .nextPC, .minstret_increment, .x1, .x28]) r hr
    have hreturn : r ∉ [Register.PC, .nextPC, .minstret_increment, .x1, .x2] := by
      simp_all only [List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true]
    have hcall : r ∉ [Register.PC, .nextPC, .minstret_increment, .x1, .x2, .x28] := by
      simp_all only [List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true]
    exact (importReturnState_reg_other current base sp ra r hreturn).trans
      ((hresume r hr).trans (importCallState_reg_other origin base sp ra callback r hcall))

end MetrologyAsm
