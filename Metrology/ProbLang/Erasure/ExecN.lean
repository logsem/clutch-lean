module

public import Metrology.ProbLang.Erasure.CaseClosers

@[expose] public section

/-! # Presampling invariance of bounded execution

The one-step identities lift through evaluation contexts and then through `execN`.
-/

noncomputable section

namespace ProbLang

open MeasureTheory MeasureTheory.Measure

variable {rT : Type} [MeasurableSpace rT] [ProbLangDist rT]
variable {σ : State rT} {α : Loc} {k : ℕ}

/-- Lifted presampling commutes with filling an evaluation context. -/
theorem Cfg.tapePresampleAt_map_fill (K : Ectx rT) (ρ : Cfg rT) :
    (Cfg.tapePresampleAt α k ρ).map K.fillCfg =
      Cfg.tapePresampleAt α k (K.fillCfg ρ) := by
  unfold Cfg.tapePresampleAt
  rw [Measure.map_map (μ := ProbLang.tapePresampleAt ρ.state α k)
    (f := fun σ' => (⟨ρ.expr, σ'⟩ : Cfg rT)) (g := K.fillCfg)
    (Ectx.fillCfg.measurable K)
    (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))]
  rfl

/-- Fixed-tape whole-stream presampling commutes with filling an evaluation context. -/
theorem Cfg.tapePresampleAllOf_map_fill (K : Ectx rT) (t : Tape rT)
    [IsProbabilityMeasure t.dist] (ρ : Cfg rT) :
    (Cfg.tapePresampleAllOf α t ρ).map K.fillCfg =
      Cfg.tapePresampleAllOf α t (K.fillCfg ρ) := by
  unfold Cfg.tapePresampleAllOf
  rw [Measure.map_map
    (μ := infinitePi fun _ : ℕ => t.dist)
    (f := fun ω => (⟨ρ.expr,
      ρ.state.updateTapes (·.insert α (t.fillAll ω))⟩ : Cfg rT))
    (g := K.fillCfg) (Ectx.fillCfg.measurable K)]
  · rfl
  · exact Cfg.measurable_mk.comp
      (measurable_const.prodMk (State.measurable_fillAllTape ρ.state α t))

variable [LawfulProbLangℝ rT] [ProbLangFFI rT] [ProbLangObs rT]

/-- A head-step transition with a remaining presample lifts to `primStep`. -/
theorem tapePresampleAt_bind_primStep_of_head {e : Exp rT} {j : ℕ}
    (hhead : (tapePresampleAt σ α k).bind (fun σ' =>
        headStep ⟨e.decomp.2, σ'⟩) =
      (headStep ⟨e.decomp.2, σ⟩).bind (Cfg.tapePresampleAt α j)) :
    (tapePresampleAt σ α k).bind (fun σ' => primStep ⟨e, σ'⟩) =
      (primStep ⟨e, σ⟩).bind (Cfg.tapePresampleAt α j) := by
  have hH : Measurable (fun σ' : State rT => headStep ⟨e.decomp.2, σ'⟩) :=
    headStep.measurable.comp
      (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
  have hfill := Ectx.fillCfg.measurable e.decomp.1
  simp only [primStep]
  rw [← Measure.map_bind hH.aemeasurable hfill.aemeasurable, hhead,
    Measure.map_bind (Cfg.tapePresampleAt.measurable α j).aemeasurable
      hfill.aemeasurable]
  simp_rw [Cfg.tapePresampleAt_map_fill]
  rw [← Measure.bind_map hfill.aemeasurable (Cfg.tapePresampleAt.measurable α j).aemeasurable]

/-- A head-step transition that consumes the presample lifts to `primStep`. -/
theorem tapePresampleAt_bind_primStep_of_head_zero {e : Exp rT}
    (hhead : (tapePresampleAt σ α k).bind (fun σ' =>
        headStep ⟨e.decomp.2, σ'⟩) = headStep ⟨e.decomp.2, σ⟩) :
    (tapePresampleAt σ α k).bind (fun σ' => primStep ⟨e, σ'⟩) =
      primStep ⟨e, σ⟩ := by
  have hH : Measurable (fun σ' : State rT => headStep ⟨e.decomp.2, σ'⟩) :=
    headStep.measurable.comp
      (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
  have hfill := Ectx.fillCfg.measurable e.decomp.1
  simp only [primStep]
  rw [← Measure.map_bind hH.aemeasurable hfill.aemeasurable, hhead]

/-- A whole-stream head-step transition lifts through its evaluation context. -/
theorem tapePresampleAll_bind_primStep_of_head {e : Exp rT} {t : Tape rT}
    [IsProbabilityMeasure t.dist]
    (hhead : (tapePresampleAll σ α).bind (fun σ' =>
        headStep ⟨e.decomp.2, σ'⟩) =
      (headStep ⟨e.decomp.2, σ⟩).bind (Cfg.tapePresampleAllOf α t)) :
    (tapePresampleAll σ α).bind (fun σ' => primStep ⟨e, σ'⟩) =
      (primStep ⟨e, σ⟩).bind (Cfg.tapePresampleAllOf α t) := by
  have hH : Measurable (fun σ' : State rT => headStep ⟨e.decomp.2, σ'⟩) :=
    headStep.measurable.comp
      (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
  have hfill := Ectx.fillCfg.measurable e.decomp.1
  simp only [primStep]
  rw [← Measure.map_bind hH.aemeasurable hfill.aemeasurable, hhead,
    Measure.map_bind (Cfg.tapePresampleAllOf.measurable α t).aemeasurable
      hfill.aemeasurable]
  simp_rw [Cfg.tapePresampleAllOf_map_fill]
  rw [← Measure.bind_map hfill.aemeasurable (Cfg.tapePresampleAllOf.measurable α t).aemeasurable]

/-- A consumed whole-stream head-step transition lifts through its evaluation context. -/
theorem tapePresampleAll_bind_primStep_of_head_zero {e : Exp rT}
    (hhead : (tapePresampleAll σ α).bind (fun σ' =>
        headStep ⟨e.decomp.2, σ'⟩) = headStep ⟨e.decomp.2, σ⟩) :
    (tapePresampleAll σ α).bind (fun σ' => primStep ⟨e, σ'⟩) =
      primStep ⟨e, σ⟩ := by
  have hH : Measurable (fun σ' : State rT => headStep ⟨e.decomp.2, σ'⟩) :=
    headStep.measurable.comp
      (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
  have hfill := Ectx.fillCfg.measurable e.decomp.1
  simp only [primStep]
  rw [← Measure.map_bind hH.aemeasurable hfill.aemeasurable, hhead]

/-- Fixed whole-stream presampling followed by execution is state filling then execution. -/
theorem Cfg.tapePresampleAllOf_bind_execN (m : ℕ) (α : Loc) (t : Tape rT)
    [IsProbabilityMeasure t.dist] (ρ : Cfg rT)
    (hρ : ρ.state.tapes[α]? = some t) :
    (Cfg.tapePresampleAllOf α t ρ).bind (execN m) =
      (tapePresampleAll ρ.state α).bind fun σ' => execN m ⟨ρ.expr, σ'⟩ := by
  rw [Cfg.tapePresampleAllOf_eq t ρ hρ]
  exact Measure.bind_map
    (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id)).aemeasurable
    (execN_measurable m).aemeasurable

/-- Lifted presampling followed by bounded execution is state presampling followed by execution. -/
theorem Cfg.tapePresampleAt_bind_execN (m : ℕ) (α : Loc) (k : ℕ) (ρ : Cfg rT) :
    (Cfg.tapePresampleAt α k ρ).bind (execN m) =
      (ProbLang.tapePresampleAt ρ.state α k).bind fun σ' =>
        execN m ⟨ρ.expr, σ'⟩ := by
  unfold Cfg.tapePresampleAt
  exact Measure.bind_map
    (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id)).aemeasurable
    (execN_measurable m).aemeasurable

/-- An almost-sure state property of a head step lifts through its evaluation context. -/
theorem ae_primStep_of_ae_headStep {e : Exp rT} {P : State rT → Prop}
    (hP : MeasurableSet {σ | P σ})
    (h : ∀ᵐ ρ ∂headStep ⟨e.decomp.2, σ⟩, P ρ.state) :
    ∀ᵐ ρ ∂primStep ⟨e, σ⟩, P ρ.state := by
  simp only [primStep]
  exact (ae_map_iff (Ectx.fillCfg.measurable e.decomp.1).aemeasurable
    (Cfg.measurable_state hP)).mpr h

/-- A primitive step whose redex does not read `α` keeps that tape. -/
theorem primStep_tape_persists_frame [ProbLangDist.IsIntValued rT]
    {e : Exp rT} {t : Tape rT} (ht : σ.tapes[α]? = some t)
    (hnot : ∀ n e', e.decomp.2 ≠ .sample n e' (.lit (.lbl α))) :
    ∀ᵐ ρ ∂primStep ⟨e, σ⟩, ρ.state.tapes[α]? = some t := by
  apply ae_primStep_of_ae_headStep (e := e)
    (P := fun τ => τ.tapes[α]? = some t)
  · exact (((LocHeap.measurable_getElem? α).comp State.measurable_tapes)
      (measurableSet_singleton _))
  · exact headStep_tape_persists_frame ht hnot

/-- A matching tape read leaves the shifted tape allocated almost surely. -/
theorem headStep_sample_tape_shift_ae {n : ℕ} {ea : Exp rT} {v : Val rT}
    {t : Tape rT} (hv : ea.toVal? = some v) (ht : σ.tapes[α]? = some t)
    (hfamily : t.name = n ∧ t.arg = v) :
    ∀ᵐ ρ ∂headStep ⟨.sample n ea (.lit (.lbl α)), σ⟩,
      ρ.state.tapes[α]? = some t.shift := by
  have hP : MeasurableSet {ρ : Cfg rT | ρ.state.tapes[α]? = some t.shift} :=
    (((LocHeap.measurable_getElem? α).comp State.measurable_tapes).comp
      Cfg.measurable_state) (measurableSet_singleton _)
  rcases hhead : t.head? with _ | w
  · rw [headStep_sample_tape_none hv ht hfamily hhead]
    exact (ae_map_iff
      (Cfg.measurable_mk.comp (Exp.ofVal.measurable.prodMk measurable_const)).aemeasurable hP).mpr
      (ae_of_all _ fun _ => State.upd_tape_some _ _ _)
  · rw [headStep_sample_tape_some hv ht hfamily hhead]
    exact (ae_dirac_iff hP).mpr (State.upd_tape_some _ _ _)

/-- A matching tape read leaves the shifted tape allocated after a primitive step. -/
theorem primStep_sample_tape_shift_ae {e : Exp rT} {n : ℕ} {ea : Exp rT}
    {v : Val rT} {t : Tape rT}
    (hred : e.decomp.2 = .sample n ea (.lit (.lbl α)))
    (hv : ea.toVal? = some v) (ht : σ.tapes[α]? = some t)
    (hfamily : t.name = n ∧ t.arg = v) :
    ∀ᵐ ρ ∂primStep ⟨e, σ⟩, ρ.state.tapes[α]? = some t.shift := by
  apply ae_primStep_of_ae_headStep (e := e)
    (P := fun τ => τ.tapes[α]? = some t.shift)
  · exact (((LocHeap.measurable_getElem? α).comp State.measurable_tapes)
      (measurableSet_singleton _))
  · simpa [hred] using headStep_sample_tape_shift_ae hv ht hfamily

/-- A tape read from another family leaves the tape allocated almost surely. -/
theorem headStep_sample_tape_other_persists_ae {n : ℕ} {ea : Exp rT}
    {v : Val rT} {t : Tape rT} (hv : ea.toVal? = some v)
    (ht : σ.tapes[α]? = some t) (hfamily : ¬(t.name = n ∧ t.arg = v)) :
    ∀ᵐ ρ ∂headStep ⟨.sample n ea (.lit (.lbl α)), σ⟩,
      ρ.state.tapes[α]? = some t := by
  have hP : MeasurableSet {ρ : Cfg rT | ρ.state.tapes[α]? = some t} :=
    (((LocHeap.measurable_getElem? α).comp State.measurable_tapes).comp
      Cfg.measurable_state) (measurableSet_singleton _)
  rw [headStep_sample_tape_other hv ht hfamily]
  exact (ae_map_iff
    (Cfg.measurable_mk.comp (Exp.ofVal.measurable.prodMk measurable_const)).aemeasurable hP).mpr
    (ae_of_all _ fun _ => ht)

/-- A tape read from another family preserves its tape after a primitive step. -/
theorem primStep_sample_tape_other_persists_ae {e : Exp rT} {n : ℕ}
    {ea : Exp rT} {v : Val rT} {t : Tape rT}
    (hred : e.decomp.2 = .sample n ea (.lit (.lbl α)))
    (hv : ea.toVal? = some v) (ht : σ.tapes[α]? = some t)
    (hfamily : ¬(t.name = n ∧ t.arg = v)) :
    ∀ᵐ ρ ∂primStep ⟨e, σ⟩, ρ.state.tapes[α]? = some t := by
  apply ae_primStep_of_ae_headStep (e := e)
    (P := fun τ => τ.tapes[α]? = some t)
  · exact (((LocHeap.measurable_getElem? α).comp State.measurable_tapes)
      (measurableSet_singleton _))
  · simpa [hred] using headStep_sample_tape_other_persists_ae hv ht hfamily

/-- A commuting one-step presample lifts through the remaining bounded execution. -/
theorem tapePresampleAt_bind_execN_of_primStep {e : Exp rT} {j m : ℕ}
    (hstep : (tapePresampleAt σ α k).bind (fun σ' => primStep ⟨e, σ'⟩) =
      (primStep ⟨e, σ⟩).bind (Cfg.tapePresampleAt α j))
    (hih : ∀ᵐ ρ ∂primStep ⟨e, σ⟩,
      asExpr ((Cfg.tapePresampleAt α j ρ).bind (execN m)) =
        asExpr (execN m ρ)) :
    asExpr ((tapePresampleAt σ α k).bind fun σ' =>
      (primStep ⟨e, σ'⟩).bind (execN m)) =
      asExpr ((primStep ⟨e, σ⟩).bind (execN m)) := by
  have hp : Measurable (fun σ' : State rT => primStep ⟨e, σ'⟩) :=
    primStep.measurable.comp
      (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
  have hpre : Measurable (fun ρ : Cfg rT =>
      (Cfg.tapePresampleAt α j ρ).bind (execN m)) :=
    (measurable_bind' (execN_measurable m)).comp
      (Cfg.tapePresampleAt.measurable α j)
  rw [← Measure.bind_bind hp.aemeasurable (execN_measurable m).aemeasurable,
    hstep, Measure.bind_bind (Cfg.tapePresampleAt.measurable α j).aemeasurable
      (execN_measurable m).aemeasurable,
    asExpr_bind _ _ hpre, asExpr_bind _ _ (execN_measurable m)]
  exact bind_congr_right hih

/-- A consumed one-step presample lifts through the remaining bounded execution. -/
theorem tapePresampleAt_bind_execN_of_primStep_zero {e : Exp rT} {m : ℕ}
    (hstep : (tapePresampleAt σ α k).bind (fun σ' => primStep ⟨e, σ'⟩) = primStep ⟨e, σ⟩) :
    (tapePresampleAt σ α k).bind (fun σ' =>
      (primStep ⟨e, σ'⟩).bind (execN m)) =
      (primStep ⟨e, σ⟩).bind (execN m) := by
  have hp : Measurable (fun σ' : State rT => primStep ⟨e, σ'⟩) :=
    primStep.measurable.comp
      (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
  rw [← Measure.bind_bind hp.aemeasurable (execN_measurable m).aemeasurable, hstep]

/-- A commuting whole-stream presample lifts through the remaining bounded execution. -/
theorem tapePresampleAll_bind_execN_of_primStep {e : Exp rT} {t : Tape rT}
    {m : ℕ} [IsProbabilityMeasure t.dist]
    (hstep : (tapePresampleAll σ α).bind (fun σ' => primStep ⟨e, σ'⟩) =
      (primStep ⟨e, σ⟩).bind (Cfg.tapePresampleAllOf α t))
    (hih : ∀ᵐ ρ ∂primStep ⟨e, σ⟩,
      asExpr ((Cfg.tapePresampleAllOf α t ρ).bind (execN m)) =
        asExpr (execN m ρ)) :
    asExpr ((tapePresampleAll σ α).bind fun σ' =>
      (primStep ⟨e, σ'⟩).bind (execN m)) =
      asExpr ((primStep ⟨e, σ⟩).bind (execN m)) := by
  have hp : Measurable (fun σ' : State rT => primStep ⟨e, σ'⟩) :=
    primStep.measurable.comp
      (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
  have hpre : Measurable (fun ρ : Cfg rT =>
      (Cfg.tapePresampleAllOf α t ρ).bind (execN m)) :=
    (measurable_bind' (execN_measurable m)).comp
      (Cfg.tapePresampleAllOf.measurable α t)
  rw [← Measure.bind_bind hp.aemeasurable (execN_measurable m).aemeasurable,
    hstep, Measure.bind_bind (Cfg.tapePresampleAllOf.measurable α t).aemeasurable
      (execN_measurable m).aemeasurable,
    asExpr_bind _ _ hpre, asExpr_bind _ _ (execN_measurable m)]
  exact bind_congr_right hih

/-- A consumed whole-stream presample lifts through the remaining bounded execution. -/
theorem tapePresampleAll_bind_execN_of_primStep_zero {e : Exp rT} {m : ℕ}
    (hstep : (tapePresampleAll σ α).bind (fun σ' => primStep ⟨e, σ'⟩) = primStep ⟨e, σ⟩) :
    (tapePresampleAll σ α).bind (fun σ' =>
      (primStep ⟨e, σ'⟩).bind (execN m)) =
      (primStep ⟨e, σ⟩).bind (execN m) := by
  have hp : Measurable (fun σ' : State rT => primStep ⟨e, σ'⟩) :=
    primStep.measurable.comp
      (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
  rw [← Measure.bind_bind hp.aemeasurable (execN_measurable m).aemeasurable, hstep]

/-- Filling one tape position does not change any bounded run's expression distribution. -/
theorem execN_tapePresampleAt_expr_eq [ProbLangDist.IsIntValued rT]
    {e : Exp rT} {t : Tape rT} {m : ℕ}
    (ht : σ.tapes[α]? = some t) (hd : t.dist ≠ 0) :
    asExpr ((tapePresampleAt σ α k).bind fun σ' => execN m ⟨e, σ'⟩) =
      asExpr (execN m ⟨e, σ⟩) := by
  rcases hk : t.presamples k with _ | w
  · induction m generalizing e σ t k with
    | zero => simp [execN]
    | succ m ih =>
      by_cases hv : e.isValue
      · have hrun : ∀ τ : State rT, execN (m + 1) ⟨e, τ⟩ = dirac ⟨e, τ⟩ :=
          fun τ => execN_succ_isValue hv m
        simp_rw [hrun]
        have hkdir : Measurable (fun τ : State rT =>
            dirac (⟨e, τ⟩ : Cfg rT)) :=
          measurable_dirac.comp
            (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
        unfold asExpr
        rw [bind_map_comm _ _ _ Cfg.measurable_expr hkdir.aemeasurable]
        have hker : (fun τ : State rT =>
            (dirac (⟨e, τ⟩ : Cfg rT)).map Cfg.expr) =
            fun _ => dirac e := by
          funext τ
          rw [map_dirac]
        rw [hker, map_dirac]
        let _ : IsProbabilityMeasure (tapePresampleAt σ α k) :=
          tapePresampleAt.isProbabilityMeasure ht hd
        refine ext fun S hS => ?_
        rw [bind_apply hS measurable_const.aemeasurable, lintegral_const,
          measure_univ, mul_one]
      · have hrun : ∀ τ : State rT,
            execN (m + 1) ⟨e, τ⟩ = (primStep ⟨e, τ⟩).bind (execN m) :=
          fun τ => execN_succ_not_isValue hv m
        simp_rw [hrun]
        by_cases htarget : ∃ n ea,
            e.decomp.2 = .sample n ea (.lit (.lbl α))
        · obtain ⟨n, ea, hred⟩ := htarget
          rcases harg : ea.toVal? with _ | v
          · have hhead :
                (tapePresampleAt σ α k).bind (fun τ =>
                    headStep ⟨e.decomp.2, τ⟩) =
                  headStep ⟨e.decomp.2, σ⟩ := by
              simp [hred, headStep, Exp.asValM, harg]
            have hprim := tapePresampleAt_bind_primStep_of_head_zero hhead
            exact congrArg asExpr
              (tapePresampleAt_bind_execN_of_primStep_zero hprim)
          · by_cases hfamily : t.name = n ∧ t.arg = v
            · cases k with
              | zero =>
                have hhead : t.head? = none := hk
                have hheadStep :=
                  tapePresampleAt_zero_bind_headStep harg ht hfamily hhead
                have hprim :=
                  tapePresampleAt_bind_primStep_of_head_zero (e := e) (by
                    simpa [hred] using hheadStep)
                exact congrArg asExpr
                  (tapePresampleAt_bind_execN_of_primStep_zero hprim)
              | succ j =>
                have hheadStep :=
                  tapePresampleAt_succ_bind_headStep harg ht hfamily hk
                have hprim := tapePresampleAt_bind_primStep_of_head (e := e) (by
                  simpa [hred] using hheadStep)
                apply tapePresampleAt_bind_execN_of_primStep hprim
                filter_upwards [primStep_sample_tape_shift_ae hred harg ht hfamily]
                  with ρ hρ
                rw [Cfg.tapePresampleAt_bind_execN]
                exact ih hρ hd hk
            · have hheadStep :=
                tapePresampleAt_bind_headStep_other harg ht hk hfamily
              have hprim := tapePresampleAt_bind_primStep_of_head (e := e) (by
                simpa [hred] using hheadStep)
              apply tapePresampleAt_bind_execN_of_primStep hprim
              filter_upwards [
                primStep_sample_tape_other_persists_ae hred harg ht hfamily]
                with ρ hρ
              rw [Cfg.tapePresampleAt_bind_execN]
              exact ih hρ hd hk
        · have hnot : ∀ n ea,
              e.decomp.2 ≠ .sample n ea (.lit (.lbl α)) := by
            intro n ea heq
            exact htarget ⟨n, ea, heq⟩
          have hhead := tapePresampleAt_bind_headStep_frame ht hk hnot
          have hprim := tapePresampleAt_bind_primStep_of_head (e := e) hhead
          apply tapePresampleAt_bind_execN_of_primStep hprim
          filter_upwards [primStep_tape_persists_frame ht hnot] with ρ hρ
          rw [Cfg.tapePresampleAt_bind_execN]
          exact ih hρ hd hk
  · rw [tapePresampleAt_of_some ht hk,
      dirac_bind (by fun_prop)]

/-- Filling every tape hole does not change any bounded run's expression distribution. -/
theorem execN_tapePresampleAll_expr_eq [ProbLangDist.IsIntValued rT]
    {e : Exp rT} {t : Tape rT} {m : ℕ}
    (ht : σ.tapes[α]? = some t) (hd : t.dist ≠ 0) :
    asExpr ((tapePresampleAll σ α).bind fun σ' => execN m ⟨e, σ'⟩) =
      asExpr (execN m ⟨e, σ⟩) := by
  induction m generalizing e σ t with
  | zero => simp [execN]
  | succ m ih =>
    let _ : IsProbabilityMeasure t.dist :=
      isProbabilityMeasure_of_ne_zero t.dist hd
    by_cases hv : e.isValue
    · have hrun : ∀ τ : State rT, execN (m + 1) ⟨e, τ⟩ = dirac ⟨e, τ⟩ :=
        fun τ => execN_succ_isValue hv m
      simp_rw [hrun]
      have hkdir : Measurable (fun τ : State rT =>
          dirac (⟨e, τ⟩ : Cfg rT)) :=
        measurable_dirac.comp
          (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
      unfold asExpr
      rw [bind_map_comm _ _ _ Cfg.measurable_expr hkdir.aemeasurable]
      have hker : (fun τ : State rT =>
          (dirac (⟨e, τ⟩ : Cfg rT)).map Cfg.expr) =
          fun _ => dirac e := by
        funext τ
        rw [map_dirac]
      rw [hker, map_dirac]
      let _ : IsProbabilityMeasure (tapePresampleAll σ α) :=
        tapePresampleAll.isProbabilityMeasure ht hd
      refine ext fun S hS => ?_
      rw [bind_apply hS measurable_const.aemeasurable, lintegral_const,
        measure_univ, mul_one]
    · have hrun : ∀ τ : State rT,
          execN (m + 1) ⟨e, τ⟩ = (primStep ⟨e, τ⟩).bind (execN m) :=
        fun τ => execN_succ_not_isValue hv m
      simp_rw [hrun]
      by_cases htarget : ∃ n ea,
          e.decomp.2 = .sample n ea (.lit (.lbl α))
      · obtain ⟨n, ea, hred⟩ := htarget
        rcases harg : ea.toVal? with _ | v
        · have hhead :
              (tapePresampleAll σ α).bind (fun τ =>
                  headStep ⟨e.decomp.2, τ⟩) =
                headStep ⟨e.decomp.2, σ⟩ := by
            simp [hred, headStep, Exp.asValM, harg]
          have hprim := tapePresampleAll_bind_primStep_of_head_zero hhead
          exact congrArg asExpr
            (tapePresampleAll_bind_execN_of_primStep_zero hprim)
        · by_cases hfamily : t.name = n ∧ t.arg = v
          · let _ : IsProbabilityMeasure t.shift.dist := by
              change IsProbabilityMeasure t.dist
              infer_instance
            have hheadStep := tapePresampleAll_bind_headStep harg ht hfamily
            have hprim := tapePresampleAll_bind_primStep_of_head (e := e) (by
              simpa [hred] using hheadStep)
            apply tapePresampleAll_bind_execN_of_primStep hprim
            filter_upwards [primStep_sample_tape_shift_ae hred harg ht hfamily]
              with ρ hρ
            rw [Cfg.tapePresampleAllOf_bind_execN m α t.shift ρ hρ]
            exact ih hρ hd
          · have hheadStep :=
              tapePresampleAll_bind_headStep_other harg ht hfamily
            have hprim := tapePresampleAll_bind_primStep_of_head (e := e) (by
              simpa [hred] using hheadStep)
            apply tapePresampleAll_bind_execN_of_primStep hprim
            filter_upwards [
              primStep_sample_tape_other_persists_ae hred harg ht hfamily]
              with ρ hρ
            rw [Cfg.tapePresampleAllOf_bind_execN m α t ρ hρ]
            exact ih hρ hd
      · have hnot : ∀ n ea,
            e.decomp.2 ≠ .sample n ea (.lit (.lbl α)) := by
          intro n ea heq
          exact htarget ⟨n, ea, heq⟩
        have hhead := tapePresampleAll_bind_headStep_frame ht hnot
        have hprim := tapePresampleAll_bind_primStep_of_head (e := e) hhead
        apply tapePresampleAll_bind_execN_of_primStep hprim
        filter_upwards [primStep_tape_persists_frame ht hnot] with ρ hρ
        rw [Cfg.tapePresampleAllOf_bind_execN m α t ρ hρ]
        exact ih hρ hd

end ProbLang
