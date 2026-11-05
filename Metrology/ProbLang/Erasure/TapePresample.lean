module

public import Metrology.ProbLang.Erasure.Presample

@[expose] public section

/-! # Structural properties of tape presampling

Presampling changes only the selected tape and commutes with updates to the other state fields.
-/

noncomputable section

namespace ProbLang

open MeasureTheory MeasureTheory.Measure

variable {rT : Type} [MeasurableSpace rT] [ProbLangDist rT]
variable {σ : State rT} {α β : Loc} {k : ℕ}

/-! ## Facts about the resulting state -/

section

variable [LawfulProbLangℝ rT]

/-- Filling one tape position leaves the heap unchanged almost surely. -/
theorem tapePresampleAt_heap_eq {t : Tape rT} (ht : σ.tapes[α]? = some t) :
    ∀ᵐ σ' ∂tapePresampleAt σ α k, σ'.heap = σ.heap := by
  rcases hk : t.presamples k with _ | w
  · exact tapePresampleAt_ae ht hk (by measurability) fun _ => rfl
  · rw [tapePresampleAt_of_some ht hk]
    exact (ae_dirac_iff (by measurability)).mpr rfl

/-- Filling one tape position leaves the random variables unchanged almost surely. -/
theorem tapePresampleAt_rvs_eq {t : Tape rT} (ht : σ.tapes[α]? = some t) :
    ∀ᵐ σ' ∂tapePresampleAt σ α k, σ'.rvs = σ.rvs := by
  rcases hk : t.presamples k with _ | w
  · exact tapePresampleAt_ae ht hk (by measurability) fun _ => rfl
  · rw [tapePresampleAt_of_some ht hk]
    exact (ae_dirac_iff (by measurability)).mpr rfl

/-- Filling one position of `α` leaves every different tape unchanged almost surely. -/
theorem tapePresampleAt_tape_ne_ae {t : Tape rT} (ht : σ.tapes[α]? = some t)
    (hne : β ≠ α) :
    ∀ᵐ σ' ∂tapePresampleAt σ α k, σ'.tapes[β]? = σ.tapes[β]? := by
  rcases hk : t.presamples k with _ | w
  · exact tapePresampleAt_ae ht hk (by measurability) fun _ =>
      State.upd_diff_tape_tot hne
  · rw [tapePresampleAt_of_some ht hk]
    exact (ae_dirac_iff (by measurability)).mpr rfl

/-- Filling every tape hole leaves the heap unchanged almost surely. -/
theorem tapePresampleAll_heap_eq {t : Tape rT} (ht : σ.tapes[α]? = some t) :
    ∀ᵐ σ' ∂tapePresampleAll σ α, σ'.heap = σ.heap :=
  tapePresampleAll_ae ht (by measurability) fun _ => rfl

/-- Filling every tape hole leaves the random variables unchanged almost surely. -/
theorem tapePresampleAll_rvs_eq {t : Tape rT} (ht : σ.tapes[α]? = some t) :
    ∀ᵐ σ' ∂tapePresampleAll σ α, σ'.rvs = σ.rvs :=
  tapePresampleAll_ae ht (by measurability) fun _ => rfl

/-- Filling every hole of `α` leaves every different tape unchanged almost surely. -/
theorem tapePresampleAll_tape_ne_ae {t : Tape rT} (ht : σ.tapes[α]? = some t)
    (hne : β ≠ α) :
    ∀ᵐ σ' ∂tapePresampleAll σ α, σ'.tapes[β]? = σ.tapes[β]? :=
  tapePresampleAll_ae ht (by measurability) fun _ => State.upd_diff_tape_tot hne

end

/-! ## Commutation with state updates -/

/-- Filling one position commutes with a measurable heap update. -/
theorem tapePresampleAt_updateHeap_comm
    (f : LocHeap (Val rT) → LocHeap (Val rT)) (hf : Measurable f) :
    tapePresampleAt (σ.updateHeap f) α k =
      (tapePresampleAt σ α k).map (·.updateHeap f) := by
  have hmap : Measurable (fun σ' : State rT => σ'.updateHeap f) :=
    State.measurable_iff.mpr
      ⟨hf.comp State.measurable_heap, State.measurable_tapes, State.measurable_rvs⟩
  rcases ht : σ.tapes[α]? with _ | t
  · have ht' : (σ.updateHeap f).tapes[α]? = none := ht
    simp [tapePresampleAt, ht, ht']
  · rcases hk : t.presamples k with _ | w
    · rw [tapePresampleAt_eq_map (σ := σ.updateHeap f) ht hk,
        tapePresampleAt_eq_map ht hk,
        Measure.map_map hmap (State.measurable_fillAtTape σ α t k)]
      congr 1
    · rw [tapePresampleAt_of_some (σ := σ.updateHeap f) ht hk,
        tapePresampleAt_of_some ht hk, map_dirac' hmap]

/-- Filling every hole commutes with a measurable heap update. -/
theorem tapePresampleAll_updateHeap_comm
    (f : LocHeap (Val rT) → LocHeap (Val rT)) (hf : Measurable f) :
    tapePresampleAll (σ.updateHeap f) α =
      (tapePresampleAll σ α).map (·.updateHeap f) := by
  have hmap : Measurable (fun σ' : State rT => σ'.updateHeap f) :=
    State.measurable_iff.mpr
      ⟨hf.comp State.measurable_heap, State.measurable_tapes, State.measurable_rvs⟩
  rcases ht : σ.tapes[α]? with _ | t
  · have ht' : (σ.updateHeap f).tapes[α]? = none := ht
    simp [tapePresampleAll, ht, ht']
  · rw [tapePresampleAll_eq_map (σ := σ.updateHeap f) ht,
      tapePresampleAll_eq_map ht,
      Measure.map_map hmap (State.measurable_fillAllTape σ α t)]
    congr 1

/-- Filling one position commutes with replacing the random-variable map. -/
theorem tapePresampleAt_updateRvs_comm (r : LocHeap (RvCell rT)) :
    tapePresampleAt (σ.updateRvs fun _ => r) α k =
      (tapePresampleAt σ α k).map (·.updateRvs fun _ => r) := by
  have hmap : Measurable (fun σ' : State rT => σ'.updateRvs fun _ => r) :=
    State.measurable_iff.mpr
      ⟨State.measurable_heap, State.measurable_tapes, measurable_const⟩
  rcases ht : σ.tapes[α]? with _ | t
  · have ht' : (σ.updateRvs fun _ => r).tapes[α]? = none := ht
    simp [tapePresampleAt, ht, ht']
  · rcases hk : t.presamples k with _ | w
    · rw [tapePresampleAt_eq_map (σ := σ.updateRvs fun _ => r) ht hk,
        tapePresampleAt_eq_map ht hk,
        Measure.map_map hmap (State.measurable_fillAtTape σ α t k)]
      congr 1
    · rw [tapePresampleAt_of_some (σ := σ.updateRvs fun _ => r) ht hk,
        tapePresampleAt_of_some ht hk, map_dirac' hmap]

/-- Filling every hole commutes with replacing the random-variable map. -/
theorem tapePresampleAll_updateRvs_comm (r : LocHeap (RvCell rT)) :
    tapePresampleAll (σ.updateRvs fun _ => r) α =
      (tapePresampleAll σ α).map (·.updateRvs fun _ => r) := by
  have hmap : Measurable (fun σ' : State rT => σ'.updateRvs fun _ => r) :=
    State.measurable_iff.mpr
      ⟨State.measurable_heap, State.measurable_tapes, measurable_const⟩
  rcases ht : σ.tapes[α]? with _ | t
  · have ht' : (σ.updateRvs fun _ => r).tapes[α]? = none := ht
    simp [tapePresampleAll, ht, ht']
  · rw [tapePresampleAll_eq_map (σ := σ.updateRvs fun _ => r) ht,
      tapePresampleAll_eq_map ht,
      Measure.map_map hmap (State.measurable_fillAllTape σ α t)]
    congr 1

/-- Filling one position of `α` commutes with writing a different tape `β`. -/
theorem tapePresampleAt_updateTapes_ne_comm {u : Tape rT} (hne : β ≠ α) :
    tapePresampleAt (σ.updateTapes (·.insert β u)) α k =
      (tapePresampleAt σ α k).map (·.updateTapes (·.insert β u)) := by
  have hmap : Measurable (fun σ' : State rT => σ'.updateTapes (·.insert β u)) := by
    fun_prop
  rcases ht : σ.tapes[α]? with _ | t
  · have ht' : (σ.updateTapes (·.insert β u)).tapes[α]? = none :=
      (State.upd_diff_tape_tot (Ne.symm hne)).trans ht
    simp [tapePresampleAt, ht, ht']
  · rcases hk : t.presamples k with _ | w
    · have ht' : (σ.updateTapes (·.insert β u)).tapes[α]? = some t :=
        (State.upd_diff_tape_tot (Ne.symm hne)).trans ht
      rw [tapePresampleAt_eq_map ht' hk, tapePresampleAt_eq_map ht hk,
        Measure.map_map hmap (State.measurable_fillAtTape σ α t k)]
      congr 1
      funext x
      exact State.upd_diff_tape_comm (Ne.symm hne)
    · have ht' : (σ.updateTapes (·.insert β u)).tapes[α]? = some t :=
        (State.upd_diff_tape_tot (Ne.symm hne)).trans ht
      rw [tapePresampleAt_of_some ht' hk, tapePresampleAt_of_some ht hk,
        map_dirac' hmap]

/-- Filling every hole of `α` commutes with writing a different tape `β`. -/
theorem tapePresampleAll_updateTapes_ne_comm {u : Tape rT} (hne : β ≠ α) :
    tapePresampleAll (σ.updateTapes (·.insert β u)) α =
      (tapePresampleAll σ α).map (·.updateTapes (·.insert β u)) := by
  have hmap : Measurable (fun σ' : State rT => σ'.updateTapes (·.insert β u)) := by
    fun_prop
  rcases ht : σ.tapes[α]? with _ | t
  · have ht' : (σ.updateTapes (·.insert β u)).tapes[α]? = none :=
      (State.upd_diff_tape_tot (Ne.symm hne)).trans ht
    simp [tapePresampleAll, ht, ht']
  · have ht' : (σ.updateTapes (·.insert β u)).tapes[α]? = some t :=
      (State.upd_diff_tape_tot (Ne.symm hne)).trans ht
    rw [tapePresampleAll_eq_map ht', tapePresampleAll_eq_map ht,
      Measure.map_map hmap (State.measurable_fillAllTape σ α t)]
    congr 1
    funext ω
    exact State.upd_diff_tape_comm (Ne.symm hne)

/-! ## Integral forms -/

/-- Updating the heap after a one-position fill can be moved before the fill. -/
theorem tapePresampleAt_lintegral_updateHeap
    (g : LocHeap (Val rT) → LocHeap (Val rT)) (hg : Measurable g)
    (f : State rT → ENNReal) (hf : Measurable f) :
    ∫⁻ σ', f (σ'.updateHeap g) ∂tapePresampleAt σ α k =
      ∫⁻ τ, f τ ∂tapePresampleAt (σ.updateHeap g) α k := by
  have hmap : Measurable (fun σ' : State rT => σ'.updateHeap g) :=
    State.measurable_iff.mpr
      ⟨hg.comp State.measurable_heap, State.measurable_tapes, State.measurable_rvs⟩
  rw [tapePresampleAt_updateHeap_comm g hg, lintegral_map hf hmap]

/-- Updating the heap after a whole-stream fill can be moved before the fill. -/
theorem tapePresampleAll_lintegral_updateHeap
    (g : LocHeap (Val rT) → LocHeap (Val rT)) (hg : Measurable g)
    (f : State rT → ENNReal) (hf : Measurable f) :
    ∫⁻ σ', f (σ'.updateHeap g) ∂tapePresampleAll σ α =
      ∫⁻ τ, f τ ∂tapePresampleAll (σ.updateHeap g) α := by
  have hmap : Measurable (fun σ' : State rT => σ'.updateHeap g) :=
    State.measurable_iff.mpr
      ⟨hg.comp State.measurable_heap, State.measurable_tapes, State.measurable_rvs⟩
  rw [tapePresampleAll_updateHeap_comm g hg, lintegral_map hf hmap]

end ProbLang
