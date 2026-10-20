module

public import Metrology.ProbLang.Erasure.ExecN

@[expose] public section

/-! Iterated presampling and erasability up to the expression projection. -/

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT]

open MeasureTheory MeasureTheory.Measure ProbLang.Measure

/-! ## `ErasableExpr` -/

/-- Erasability up to the expression projection, the analogue of `Erasable` (which compares full
configurations) that `tapePresample σ α` satisfies. -/
def ErasableExpr (μ : Measure (State rT)) (σ : State rT) : Prop :=
  ∀ (e : Exp rT) (m : Nat),
    asExpr (μ.bind (fun σ' => execN m ⟨e, σ'⟩)) =
      asExpr (execN m ⟨e, σ⟩)

namespace ErasableExpr

/-- Erasability implies erasability up to the expression projection. -/
theorem of_erasable {μ : Measure (State rT)} {σ : State rT} (h : Erasable μ σ) :
    ErasableExpr μ σ := by
  intro e m
  rw [h e m]

/-- An expression-erasable distribution has mass 1. -/
theorem mass {μ : Measure (State rT)} {σ : State rT} (h : ErasableExpr μ σ) :
    μ Set.univ = 1 := by
  -- run the value `()` one step: the LHS mass is `μ univ`, the RHS is 1
  have hv : IsVal (Exp.lit (rT := rT) .unit) := .lit
  have hstep : ∀ σ' : State rT,
      execN 1 ((⟨.lit .unit, σ'⟩ : Cfg rT)) = Measure.dirac (⟨.lit .unit, σ'⟩ : Cfg rT) :=
    fun σ' => execN_succ_isValue (ρ := ⟨.lit .unit, σ'⟩) hv.toIsValue 0
  have hexpr : ∀ ν : Measure (Cfg rT), asExpr ν Set.univ = ν Set.univ := fun ν => by
    rw [asExpr, Measure.map_apply Cfg.measurable_expr MeasurableSet.univ, Set.preimage_univ]
  have h1 := h (.lit .unit) 1
  have hboth := congrArg (fun ν => ν (Set.univ : Set (Exp rT))) h1
  simp only [hexpr] at hboth
  rw [hstep σ] at hboth
  rw [Measure.dirac_apply' _ .univ] at hboth
  simp at hboth
  rw [bind_apply .univ (Measurable.aemeasurable (by measurability))] at hboth
  simp_rw [hstep] at hboth
  simp_rw [Measure.dirac_apply' _ .univ] at hboth
  simp at hboth
  exact hboth

theorem isProbabilityMeasure {μ : Measure (State rT)} {σ : State rT} (h : ErasableExpr μ σ) :
    IsProbabilityMeasure μ :=
  ⟨h.mass⟩

/-- A Dirac state distribution is erasable. -/
theorem dret (σ : State rT) : ErasableExpr (Measure.dirac σ) σ :=
  of_erasable (Erasable.dret σ)

/-- Presampling a tape with positive bound is erasable up to expressions. -/
theorem tapePresample
    {σ : State rT} {α : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    ErasableExpr (tapePresample σ α) σ :=
  fun _ _ => execN_tape_presample_expr_eq h hN

/-- Sequencing preserves erasability; discreteness gives the measurability for free. -/
theorem dbind [Countable rT]
    {μ₁ : Measure (State rT)} {μ₂ : State rT → Measure (State rT)} {σ : State rT}
    (h₁ : ErasableExpr μ₁ σ) (h₂ : ∀ σ', ErasableExpr (μ₂ σ') σ') :
    ErasableExpr (μ₁.bind μ₂) σ := by
  intro e m
  unfold asExpr
  rw [Measure.bind_bind
        Measurable.of_discrete.aemeasurable
        Measurable.of_discrete.aemeasurable,
      Measure.bind_map_comm_of_discrete]
  have hker : (fun σ' : State rT =>
      Measure.map (·.expr : Cfg rT → Exp rT)
        ((μ₂ σ').bind (fun σ'' => execN m ⟨e, σ''⟩)))
      = (fun σ' : State rT =>
          Measure.map (·.expr) (execN m ⟨e, σ'⟩)) := by
    funext σ'
    have := h₂ σ' e m
    unfold asExpr at this
    exact this
  rw [hker, ← Measure.bind_map_comm_of_discrete]
  have := h₁ e m
  unfold asExpr at this
  exact this

/-- Erasability passes from every bounded run to the limit (monotone convergence). -/
theorem lim_exec
    {μ : Measure (State rT)} {σ : State rT} (h : ErasableExpr μ σ)
    (e : Exp rT) :
    asExpr (μ.bind (fun σ' => limExec ⟨e, σ'⟩)) =
      limExecV ⟨e, σ⟩ := by
  have hexpr : Measurable (·.expr : Cfg rT → Exp rT) := Cfg.measurable_expr
  have hmk : Measurable (fun σ' : State rT => (⟨e, σ'⟩ : Cfg rT)) := by fun_prop
  unfold asExpr limExecV asExpr
  -- as `Erasable.lim_exec`, on the event `(·.expr) ⁻¹' S`
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply hexpr hS, Measure.map_apply hexpr hS,
      Measure.bind_apply (hexpr hS)
        (show Measurable (fun σ' : State rT => limExec (⟨e, σ'⟩ : Cfg rT)) from
          limExec.measurable.comp hmk).aemeasurable]
  simp_rw [limExec_apply _ (hexpr hS)]
  rw [lintegral_iSup (fun n => ?measurable) ?mono]
  case measurable =>
    exact (Measure.measurable_coe (hexpr hS)).comp ((execN_measurable n).comp hmk)
  case mono => exact fun n m hnm a => execN_mono hnm ⟨e, a⟩ _
  suffices hbind : ∀ n, ∫⁻ σ', (execN n ⟨e, σ'⟩) ((·.expr) ⁻¹' S) ∂μ
      = (execN n ⟨e, σ⟩) ((·.expr) ⁻¹' S) by
    simp [hbind]
  intro n
  have hn := h e n
  unfold asExpr at hn
  have hval := congrArg (· S) hn
  rwa [Measure.map_apply hexpr hS, Measure.map_apply hexpr hS,
      Measure.bind_apply (hexpr hS)
        (show Measurable (fun σ' : State rT => execN n (⟨e, σ'⟩ : Cfg rT)) from
          (execN_measurable n).comp hmk).aemeasurable] at hval

end ErasableExpr

/-- Clutch `limprim_coupl_step_limprim` / `lim_exec_eq_erasure`, projected to expressions. -/
theorem limExec_tape_presample_expr_eq
    {σ : State rT} {α : Loc} {t : Tape} {e : Exp rT}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    asExpr ((tapePresample σ α).bind (fun σ' => limExec ⟨e, σ'⟩)) =
      limExecV ⟨e, σ⟩ :=
  (ErasableExpr.tapePresample h hN).lim_exec e

/-! ## Iterated presampling -/

/-- `n`-fold presampling on tape `α`; the `Nat.rec` in Clutch's `erasure.v` tape batching. -/
noncomputable def tapePresampleIter (α : Loc) (σ : State rT) : Nat → Measure (State rT)
  | 0 => Measure.dirac σ
  | n + 1 => (tapePresampleIter α σ n).bind (fun σ' => tapePresample σ' α)

theorem tapePresampleIter_tape_bound_ae [Countable rT]
    {σ : State rT} {α : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (n : Nat) :
    ∀ᵐ σ' ∂(tapePresampleIter α σ n),
      ∃ t' : Tape, σ'.tapes[α]? = some t' ∧ t'.bound = t.bound := by
  induction n with
  | zero =>
    show ∀ᵐ σ' ∂(Measure.dirac σ), _
    rw [MeasureTheory.ae_iff, Measure.dirac_apply' _ MeasurableSet.of_discrete,
        Set.indicator_of_notMem]
    simp only [Set.mem_ofPred_eq, not_not]
    exact ⟨t, h, rfl⟩
  | succ k ihk =>
    rw [tapePresampleIter, MeasureTheory.ae_iff,
        Measure.bind_apply MeasurableSet.of_discrete
          Measurable.of_discrete.aemeasurable]
    refine (lintegral_eq_zero_iff Measurable.of_discrete).mpr ?_
    filter_upwards [ihk] with σ'' ⟨t'', ht'', hbound⟩
    show tapePresample σ'' α _ = 0
    obtain ⟨Nb, bs⟩ := t''
    refine MeasureTheory.ae_iff.mp (tapePresample_ae ht'' MeasurableSet.of_discrete fun n' => ?_)
    exact ⟨⟨Nb, bs ++ [n']⟩, by simp [State.update_tapes], hbound⟩

theorem execN_tapePresampleIter_expr_eq [Countable rT]
    {σ : State rT} {α : Loc} {e : Exp rT} {m : Nat} {t : Tape} (n : Nat)
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    asExpr ((tapePresampleIter α σ n).bind (fun σ' => execN m ⟨e, σ'⟩)) =
      asExpr (execN m ⟨e, σ⟩) := by
  unfold asExpr
  induction n generalizing σ with
  | zero =>
    show ((Measure.dirac σ).bind (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr) = _
    rw [Measure.dirac_bind (f := _) Measurable.of_discrete]
  | succ k ih =>
    -- not `ErasableExpr.dbind`: tape α is present only a.e. after k presamples, so the IH is
    -- applied under `lintegral_congr_ae`
    show ((((tapePresampleIter α σ k).bind (fun σ' => tapePresample σ' α)).bind
            (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr)) = _
    rw [Measure.bind_bind
          Measurable.of_discrete.aemeasurable
          Measurable.of_discrete.aemeasurable,
        Measure.bind_map_comm_of_discrete]
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    calc ∫⁻ σ₁, ((tapePresample σ₁ α).bind (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr) S
            ∂(tapePresampleIter α σ k)
        = ∫⁻ σ₁, (execN m ⟨e, σ₁⟩).map (·.expr) S ∂(tapePresampleIter α σ k) := by
          refine lintegral_congr_ae ?_
          filter_upwards [tapePresampleIter_tape_bound_ae h k]
            with σ₁ ⟨t', ht', hbound⟩
          have h_eq := execN_tape_presample_expr_eq (e := e) (m := m) ht' (hbound ▸ hN)
          unfold asExpr at h_eq
          rw [h_eq]
      _ = ((tapePresampleIter α σ k).bind (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr) S := by
          rw [Measure.map_apply Measurable.of_discrete hS,
              Measure.bind_apply (Measurable.of_discrete hS)
                Measurable.of_discrete.aemeasurable]
          simp_rw [Measure.map_apply Measurable.of_discrete hS]
      _ = (execN m ⟨e, σ⟩).map (·.expr) S := by
          rw [ih h, Measure.map_apply Measurable.of_discrete hS]

end ProbLang
