import MetrologyAsm.RV

/-! # Concrete resumption witnesses for scalar callbacks -/

namespace MetrologyAsm

open ProbLang ProbLang.Asm RiscvZkvm.Sail.Functions

/-- Resume an integer callback at its saved return counter and install its scalar result. -/
def resumeIntState (s : Mach) (ra : BitVec 64) (z : Int) : Mach :=
  { s with regs := (s.regs.insert .PC ra).insert .x10 (BitVec.ofInt 64 z) }

/-- Integer resumption preserves the configured user-mode register profile. -/
theorem UserConfig.resumeIntState {s : Mach} (h : UserConfig s) (ra : BitVec 64) (z : Int) :
    UserConfig (MetrologyAsm.resumeIntState s ra z) :=
  (h.insert .PC ra trivial).insert .x10 (BitVec.ofInt 64 z) trivial

/-- Integer resumption preserves every register except the counter and return register. -/
theorem resumeIntState_reg_other (s : Mach) (ra : BitVec 64) (z : Int) (r : Register)
    (hpc : r ≠ .PC) (ha0 : r ≠ .x10) :
    (resumeIntState s ra z).regs.get? r = s.regs.get? r := by
  simp [resumeIntState, Std.ExtDHashMap.get?_insert, Ne.symm hpc, Ne.symm ha0]

/-- Integer resumption preserves every callee-saved integer register. -/
theorem resumeIntState_calleeSavedRestored (s : Mach) (ra : BitVec 64) (z : Int) :
    calleeSavedRestored s (resumeIntState s ra z) := by
  intro r hr
  apply resumeIntState_reg_other
  all_goals
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- Integer resumption preserves the architectural and model configuration frame. -/
theorem resumeIntState_configurationFrame (s : Mach) (ra : BitVec 64) (z : Int) :
    configurationFrame s (resumeIntState s ra z) := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  intro r hscratch _ hbookkeeping
  apply resumeIntState_reg_other
  · intro heq
    exact hbookkeeping (by simp [heq])
  · intro heq
    subst r
    exact hscratch (by decide +kernel)

/-- A callback with no pointer regions can always resume with an integer and the empty fragment. -/
theorem rv_resume_int_empty (ι : Placement) (code : Code) (args : List BoundaryValue)
    (F : Finset Loc) (s : Mach) (name : String) (sig : CallSig) (ra : BitVec 64) (z : Int)
    (hregions : callRegions code args = []) (hvalid : validFragment code args ∅)
    (hprofile : UserConfig s) (himport : (name, sig) ∈ code.sig.imports)
    (hpc : pc s = some (ι.importAddr name)) (hra : s.regs.get? .x1 = some ra)
    (hcode : codeRange ι code ra) (hF : F = callFootprint code args) :
    rv.Resume ι code args F s (.int z) ∅ (resumeIntState s ra z) := by
  refine ⟨name, sig, ra, BitVec.ofInt 64 z, himport, hpc, hra, hcode, ?_, rfl, ?_, hF,
    ⟨hvalid, ?_⟩, hprofile.resumeIntState ra z, resumeIntState_calleeSavedRestored s ra z,
    resumeIntState_configurationFrame s ra z, fun _ _ => rfl⟩
  · simp [pc, resumeIntState, Std.ExtDHashMap.get?_insert]
  · simp [resumeIntState]
  · intro r hr
    simp [hregions] at hr

end MetrologyAsm
