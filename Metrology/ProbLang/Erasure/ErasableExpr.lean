module

public import Metrology.ProbLang.Erasure.ExecN

@[expose] public section

/-! # Erasability up to expressions

`ErasableExpr μ σ`: sampling the state from `μ` leaves every `execN` expression distribution
unchanged. -/

namespace ProbLang

variable {rT : Type} [MeasurableSpace rT] {α : Loc}

open MeasureTheory MeasureTheory.Measure
open Set
open Cfg (measurable_expr)

variable [LawfulProbLangℝ rT] [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]

/-! ## `ErasableExpr` -/

/-- Sampling the initial state from `μ` leaves the expression distribution of `execN m`
unchanged. -/
def ErasableExpr (μ : Measure (State rT)) (σ : State rT) : Prop :=
  ∀ e m, asExpr (μ.bind (fun σ' => execN m ⟨e, σ'⟩)) = asExpr (execN m ⟨e, σ⟩)

namespace ErasableExpr

variable {μ : Measure (State rT)} {σ : State rT}

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

/-! ### Passage to the limit -/

/-- Erasability passes from every bounded run to the limit. -/
theorem lim_exec (h : ErasableExpr μ σ) (e : Exp rT) :
    asExpr (μ.bind (fun σ' => limExec ⟨e, σ'⟩)) = limExecV ⟨e, σ⟩ := by
  have hexpr : Measurable (·.expr : Cfg rT → Exp rT) := measurable_expr
  have hmk : Measurable (fun σ' : State rT => (⟨e, σ'⟩ : Cfg rT)) := by fun_prop
  unfold asExpr limExecV asExpr
  -- `limExec` is the sup of `execN n`: swap the sup with the integral, then use `h` at each `n`
  refine ext fun S hS => ?_
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
theorem ErasableExpr.dret (σ : State rT) : ErasableExpr (dirac σ) σ := by
  intro e m
  rw [dirac_bind (by measurability)]

/-! ## Erasure of one-position presampling -/

section

variable {σ : State rT}

/-- Binding an erasable distribution with almost surely erasable continuations is erasable. -/
theorem ErasableExpr.bind {μ : Measure (State rT)} {ν : State rT → Measure (State rT)}
    (hμ : ErasableExpr μ σ) (hν : Measurable ν) (h : ∀ᵐ σ' ∂μ, ErasableExpr (ν σ') σ') :
    ErasableExpr (μ.bind ν) σ := by
  intro e m
  have hK : Measurable (fun σ' : State rT => execN m (⟨e, σ'⟩ : Cfg rT)) := by fun_prop
  have hKb : Measurable (fun σ' => (ν σ').bind fun σ'' => execN m (⟨e, σ''⟩ : Cfg rT)) :=
    (measurable_bind' hK).comp hν
  rw [← hμ e m, bind_bind hν.aemeasurable hK.aemeasurable, asExpr, asExpr,
    bind_map_comm _ _ _ measurable_expr hKb.aemeasurable,
    bind_map_comm _ _ _ measurable_expr hK.aemeasurable]
  exact bind_congr_right (h.mono fun σ' hσ' => hσ' e m)

section

variable [ProbLangDist.IsIntValued rT] {t : Tape rT} (ht : σ.tapes[α]? = some t) (hd : t.dist ≠ 0)

include ht hd

/-- Filling one tape position is erasable up to expressions. -/
theorem ErasableExpr.tapePresampleAt (k : ℕ) :
    ErasableExpr (tapePresampleAt σ α k) σ :=
  fun _ _ => execN_tapePresampleAt_expr_eq ht hd

/-- Filling one tape position leaves the limit expression distribution unchanged. -/
theorem limExec_tapePresampleAt_expr_eq {e : Exp rT} (k : ℕ) :
    asExpr ((tapePresampleAt σ α k).bind fun σ' => limExec ⟨e, σ'⟩) =
      limExecV ⟨e, σ⟩ :=
  (ErasableExpr.tapePresampleAt ht hd k).lim_exec e

/-- Filling every tape hole is erasable up to expressions. -/
theorem ErasableExpr.tapePresampleAll :
    ErasableExpr (tapePresampleAll σ α) σ :=
  fun _ _ => execN_tapePresampleAll_expr_eq ht hd

/-- Filling every tape hole leaves the limit expression distribution unchanged. -/
theorem limExec_tapePresampleAll_expr_eq {e : Exp rT} :
    asExpr ((tapePresampleAll σ α).bind fun σ' => limExec ⟨e, σ'⟩) =
      limExecV ⟨e, σ⟩ :=
  (ErasableExpr.tapePresampleAll ht hd).lim_exec e

end

end

end ProbLang
