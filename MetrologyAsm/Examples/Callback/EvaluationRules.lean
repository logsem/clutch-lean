import MetrologyAsm.Examples.Callback.Boundary

/-! # Evaluating the callback tree from local Sail witnesses -/

namespace MetrologyAsm

open ProbLang ProbLang.Asm

/-- Observing the callback call identifies its actual external program counter. -/
theorem observe_importToy_call_pc (ι : Placement) (paused : Mach)
    (h : observe ι importToyCode [] ∅ paused = some (.call "cb" [] ∅)) :
    pc paused = some (ι.importAddr "cb") := by
  have hheap : decodeF ι importToyCode [] ∅ paused = some ∅ := by
    simp [decodeF, footprintLocations, Iris.Std.PartialMap.ofList]
  cases hp : pc paused with
  | none => simp [observe, hp] at h
  | some p =>
    by_cases hr : p = ι.retAddr
    · cases hw : argumentRegister paused 0 with
      | none => simp [observe, hp, hheap, hr, hw] at h
      | some word =>
        cases hv : decodeValue ι importToyCode [] importToyCode.sig.result word <;>
          simp [observe, hp, hheap, hr, hw, hv] at h
    · by_cases hc : p = ι.importAddr "cb"
      · simp only [hc]
      · simp [observe, hp, hr, importToyCode, hc] at h

/-- A callback exit carries the external counter of its observed call. -/
theorem exit_importToy_call_pc (ι : Placement) (origin paused : Mach)
    (h : rv.ExitCompat ι importToyCode [] ∅ origin paused (.call "cb" [] ∅)) :
    pc paused = some (ι.importAddr "cb") := observe_importToy_call_pc ι paused h.1

/-- Every valid response to an observed callback exit has a concrete local resumption. -/
theorem importToy_resume_nonempty (ι : Placement) (origin paused : Mach)
    (h : rv.ExitCompat ι importToyCode [] ∅ origin paused (.call "cb" [] ∅))
    (r : BoundaryValue) (heap : LocHeap BoundaryValue)
    (hr : rv.ResponseOK importToyCode [] ∅ "cb" r heap) :
    ∃ current, rv.Resume ι importToyCode [] ∅ paused r heap current := by
  have hpc := exit_importToy_call_pc ι origin paused h
  obtain ⟨_, _, _, hconfig, _, hF, ra, hra, hcode⟩ := h
  obtain ⟨z, rfl, rfl, _⟩ := (importToy_response_iff r heap).mp hr
  refine ⟨resumeIntState paused ra z, ?_⟩
  exact rv_resume_int_empty ι importToyCode [] paused "cb" ⟨[], .int 64⟩ ra z
    importToy_regions importToy_valid_empty hconfig.1 (by simp [importToyCode])
    hpc hra hcode hF

/-- A callback specification and a compatible entry give the canonical evaluation. -/
theorem importToy_eval_of_spec
    (hspec : RVSpec importToyCode [] ∅ importToyTree)
    (hentry : ∃ ι origin, RVCompat ι importToyCode [] ∅ origin) :
    rv.eval importToyCode [] ∅ ∅ = some importToyTree := by
  rw [importToyTree_eq]
  refine rv.eval_one_call_eq_some importToyCode [] ∅ ∅ "cb" [] ∅ importToyNext
    (fun ι t P Q => rv_runs_agree ι importToyCode t P Q)
    (fun ι origin paused s u => rv_exit_det ι importToyCode [] ∅ origin paused s u)
    hentry ?_ ?_ ?_ ?_
  · simpa only [importToyTree_eq] using importToyTree_canonical
  · simpa only [RVSpec, importToy_footprint, importToyTree_eq] using hspec
  · intro r heap hr
    exact ⟨r, heap, importToyNext_valid r heap hr⟩
  · intro ι origin paused _ hexit r heap hr
    exact importToy_resume_nonempty ι origin paused hexit r heap hr

end MetrologyAsm
