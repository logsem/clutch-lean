module

public import Metrology.ProbLang.Erasure.ExecN

@[expose] public section

/-! # Erasability up to expressions

`ErasableExpr μ σ`: running from `μ` instead of `σ` leaves every `execN` expression distribution
unchanged. Main results: presampling a tape, once or `n` times, is erasable in this sense. -/

open Measurable (of_discrete)

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT]

open MeasureTheory MeasureTheory.Measure ProbLang.Measure
open Set
open Cfg (measurable_expr)

/-! ## `ErasableExpr` -/

/-- Erasability up to the expression projection, the analogue of `Erasable`. -/
def ErasableExpr (μ : Measure (State rT)) (σ : State rT) : Prop :=
  ∀ e m, asExpr (μ.bind (fun σ' => execN m ⟨e, σ'⟩)) = asExpr (execN m ⟨e, σ⟩)

namespace ErasableExpr

variable {μ : Measure (State rT)} {σ : State rT}

/-- Erasability implies erasability up to the expression projection. -/
theorem of_erasable (h : Erasable μ σ) : ErasableExpr μ σ := by
  intro e m
  rw [h e m]

/-- An expression-erasable distribution has mass 1. -/
theorem mass (h : ErasableExpr μ σ) : μ univ = 1 := by
  -- run the value `()` one step: the LHS mass is `μ univ`, the RHS is 1
  have hv : IsVal (Exp.lit (rT := rT) .unit) := .lit
  have hstep : ∀ σ' : State rT, execN 1 ⟨.lit .unit, σ'⟩ = dirac ⟨.lit .unit, σ'⟩ :=
    fun σ' => execN_succ_isValue hv.toIsValue 0
  have hexpr : ∀ ν : Measure (Cfg rT), asExpr ν univ = ν univ := fun ν => by
    rw [asExpr, map_apply measurable_expr .univ, preimage_univ]
  have h1 := h (.lit .unit) 1
  have hboth := congrArg (fun ν => ν (univ : Set (Exp rT))) h1
  simp only [hexpr] at hboth
  rw [hstep σ] at hboth
  rw [dirac_apply' _ .univ] at hboth
  simp only [mem_univ, indicator_of_mem, Pi.one_apply] at hboth
  rw [bind_apply .univ (Measurable.aemeasurable (by measurability))] at hboth
  simp_rw [hstep] at hboth
  simp_rw [dirac_apply' _ .univ] at hboth
  simp only [mem_univ, indicator_of_mem, Pi.one_apply, lintegral_const, one_mul] at hboth
  exact hboth

/-- An expression-erasable distribution is a probability measure. -/
theorem isProbabilityMeasure (h : ErasableExpr μ σ) : IsProbabilityMeasure μ :=
  ⟨h.mass⟩

/-- Presampling a tape with positive bound is erasable up to expressions. -/
theorem tapePresample {α : Loc} {t : Tape} (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    ErasableExpr (tapePresample σ α) σ :=
  fun _ _ => execN_tapePresample_expr_eq h hN

/-! ### Passage to the limit -/

/-- Erasability passes from every bounded run to the limit. -/
theorem lim_exec (h : ErasableExpr μ σ) (e : Exp rT) :
    asExpr (μ.bind (fun σ' => limExec ⟨e, σ'⟩)) = limExecV ⟨e, σ⟩ := by
  have hexpr : Measurable (·.expr : Cfg rT → Exp rT) := measurable_expr
  have hmk : Measurable (fun σ' : State rT => (⟨e, σ'⟩ : Cfg rT)) := by fun_prop
  unfold asExpr limExecV asExpr
  -- `limExec` is the sup of `execN n`: swap the sup with the integral, then use `h` at each `n`
  refine Measure.ext fun S hS => ?_
  rw [map_apply hexpr hS, map_apply hexpr hS,
    bind_apply (hexpr hS) (show Measurable (fun σ' : State rT => limExec (⟨e, σ'⟩ : Cfg rT)) from
      limExec.measurable.comp hmk).aemeasurable]
  simp_rw [limExec_apply _ (hexpr hS)]
  rw [lintegral_iSup (fun n => ?measurable) ?mono]
  case measurable =>
    exact (measurable_coe (hexpr hS)).comp ((execN_measurable n).comp hmk)
  case mono => exact fun n m hnm a => execN_mono hnm ⟨e, a⟩ _
  suffices hbind : ∀ n, ∫⁻ σ', (execN n ⟨e, σ'⟩) ((·.expr) ⁻¹' S) ∂μ =
      (execN n ⟨e, σ⟩) ((·.expr) ⁻¹' S) by
    simp [hbind]
  intro n
  have hn := h e n
  unfold asExpr at hn
  have hval := congrArg (· S) hn
  rwa [map_apply hexpr hS, map_apply hexpr hS,
    bind_apply (hexpr hS) (show Measurable (fun σ' : State rT => execN n (⟨e, σ'⟩ : Cfg rT)) from
      (execN_measurable n).comp hmk).aemeasurable] at hval

end ErasableExpr

/-- A Dirac state distribution is erasable. -/
theorem ErasableExpr.dret (σ : State rT) : ErasableExpr (dirac σ) σ :=
  .of_erasable (Erasable.dret σ)

/-- Presampling a tape leaves the limit expression distribution unchanged (Clutch
`lim_exec_eq_erasure`). -/
theorem limExec_tapePresample_expr_eq {σ : State rT} {α : Loc} {t : Tape} {e : Exp rT}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    asExpr ((tapePresample σ α).bind (fun σ' => limExec ⟨e, σ'⟩)) = limExecV ⟨e, σ⟩ :=
  (ErasableExpr.tapePresample h hN).lim_exec e

/-! ## Iterated presampling -/

/-- `n`-fold presampling on tape `α` (Clutch `erasure.v` tape batching). -/
noncomputable def tapePresampleIter (α : Loc) (σ : State rT) : Nat → Measure (State rT)
  | 0 => dirac σ
  | n + 1 => (tapePresampleIter α σ n).bind (fun σ' => tapePresample σ' α)

section

variable [Countable rT] {σ : State rT} {α : Loc} {t : Tape}

/-- After `n` presamples, tape `α` still exists almost surely, with its original bound. -/
theorem tapePresampleIter_tape_bound_ae (h : σ.tapes[α]? = some t) (n : Nat) :
    ∀ᵐ σ' ∂(tapePresampleIter α σ n),
      ∃ t' : Tape, σ'.tapes[α]? = some t' ∧ t'.bound = t.bound := by
  induction n with
  | zero =>
    show ∀ᵐ σ' ∂(dirac σ), _
    rw [ae_iff, dirac_apply' _ .of_discrete, indicator_of_notMem]
    simp only [mem_ofPred_eq, not_not]
    exact ⟨t, h, rfl⟩
  | succ k ihk =>
    rw [tapePresampleIter, ae_iff, bind_apply .of_discrete of_discrete.aemeasurable]
    refine (lintegral_eq_zero_iff of_discrete).mpr ?_
    filter_upwards [ihk] with σ'' ⟨t'', ht'', hbound⟩
    show tapePresample σ'' α _ = 0
    obtain ⟨Nb, bs⟩ := t''
    refine ae_iff.mp (tapePresample_ae ht'' .of_discrete fun n' => ?_)
    exact ⟨⟨Nb, bs ++ [n']⟩, by simp [State.update_tapes], hbound⟩

/-- `n`-fold presampling of a tape leaves every `execN` expression distribution unchanged. -/
theorem execN_tapePresampleIter_expr_eq {e : Exp rT} {m : Nat} (n : Nat)
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    asExpr ((tapePresampleIter α σ n).bind (fun σ' => execN m ⟨e, σ'⟩)) =
      asExpr (execN m ⟨e, σ⟩) := by
  unfold asExpr
  induction n generalizing σ with
  | zero =>
    show ((dirac σ).bind (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr) = _
    rw [dirac_bind of_discrete]
  | succ k ih =>
    -- the IH is applied under `lintegral_congr_ae`: tape α is present only a.e. after k presamples
    show ((((tapePresampleIter α σ k).bind (fun σ' => tapePresample σ' α)).bind
      (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr)) = _
    rw [bind_bind of_discrete.aemeasurable of_discrete.aemeasurable,
      bind_map_comm_of_discrete]
    refine Measure.ext fun S hS => ?_
    rw [bind_apply hS of_discrete.aemeasurable]
    calc ∫⁻ σ₁, ((tapePresample σ₁ α).bind (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr) S
            ∂(tapePresampleIter α σ k)
        = ∫⁻ σ₁, (execN m ⟨e, σ₁⟩).map (·.expr) S ∂(tapePresampleIter α σ k) := by
          refine lintegral_congr_ae ?_
          filter_upwards [tapePresampleIter_tape_bound_ae h k] with σ₁ ⟨t', ht', hbound⟩
          have h_eq := execN_tapePresample_expr_eq (e := e) (m := m) ht' (hbound ▸ hN)
          unfold asExpr at h_eq
          rw [h_eq]
      _ = ((tapePresampleIter α σ k).bind (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr) S := by
          rw [map_apply of_discrete hS,
            bind_apply (of_discrete hS) of_discrete.aemeasurable]
          simp_rw [map_apply of_discrete hS]
      _ = (execN m ⟨e, σ⟩).map (·.expr) S := by
          rw [ih h, map_apply of_discrete hS]

end

end ProbLang
