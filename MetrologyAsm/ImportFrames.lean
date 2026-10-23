import MetrologyAsm.ImportBoundary
import MetrologyAsm.ImportExecution
import MetrologyAsm.ImportPlacement
import MetrologyAsm.RVProofs

/-! # Whole-call frame preservation around the callback -/

namespace MetrologyAsm

open ProbLang ProbLang.Asm RiscvZkvm.Sail.Functions

section RawFrames

variable (s : Mach) (base sp ra callback : BitVec 64)

/-- The import prefix preserves the complete configuration frame. -/
theorem importCallState_configurationFrame :
    configurationFrame s (importCallState s base sp ra callback) := by
  refine ⟨?_, (importCallState_fields s base sp ra callback).1,
    (importCallState_fields s base sp ra callback).2.1,
    (importCallState_fields s base sp ra callback).2.2.1,
    (importCallState_fields s base sp ra callback).2.2.2⟩
  intro r hscratch hcallee hbookkeeping
  apply importCallState_reg_other
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hbookkeeping ⊢
  refine ⟨hbookkeeping.1, hbookkeeping.2.1, hbookkeeping.2.2, ?_, ?_, ?_⟩
  · intro heq
    subst r
    exact hscratch (by decide +kernel)
  · intro heq
    subst r
    exact hcallee (by decide +kernel)
  · intro heq
    subst r
    exact hscratch (by decide +kernel)

/-- The post-callback continuation preserves the complete configuration frame. -/
theorem importReturnState_configurationFrame :
    configurationFrame s (importReturnState s base sp ra) := by
  refine ⟨?_, (importReturnState_fields s base sp ra).1,
    (importReturnState_fields s base sp ra).2.1,
    (importReturnState_fields s base sp ra).2.2.1,
    (importReturnState_fields s base sp ra).2.2.2⟩
  intro r hscratch hcallee hbookkeeping
  apply importReturnState_reg_other
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hbookkeeping ⊢
  refine ⟨hbookkeeping.1, hbookkeeping.2.1, hbookkeeping.2.2, ?_, ?_⟩
  · intro heq
    subst r
    exact hscratch (by decide +kernel)
  · intro heq
    subst r
    exact hcallee (by decide +kernel)

end RawFrames

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

/-- The complete callback execution restores the original integer callee-saved register frame. -/
theorem importReturnState_originalCallee (origin current : Mach)
    (base sp ra callback : BitVec 64) (hsp : origin.regs.get? .x2 = some sp)
    (hresume : calleeSavedRestored (importCallState origin base sp ra callback) current) :
    calleeSavedRestored origin (importReturnState current base sp ra) := by
  intro r hr
  by_cases heq : r = .x2
  · subst r
    exact (importReturnState_sp current base sp ra).trans hsp.symm
  · have hbase : r ∉ [Register.PC, .nextPC, .minstret_increment, .x1, .x28] := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    have hreturn : r ∉ [Register.PC, .nextPC, .minstret_increment, .x1, .x2] := by
      simp_all only [List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true]
    have hcall : r ∉ [Register.PC, .nextPC, .minstret_increment, .x1, .x2, .x28] := by
      simp_all only [List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true]
    exact (importReturnState_reg_other current base sp ra r hreturn).trans
      ((hresume r hr).trans (importCallState_reg_other origin base sp ra callback r hcall))

end MetrologyAsm
