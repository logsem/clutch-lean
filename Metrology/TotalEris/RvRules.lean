module

public import Metrology.TotalEris.ErrorRules
public import Metrology.Iris.RvPointsTo
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Random-variable rules

Allocating a random variable and testing it, with and without error credits. -/

open Iris Iris.Std Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS
  Possible HeadStepSupport
open Std.ExtTreeMap (insert_eq_PartialMap_insert)
open Exp (toVal?_ofVal toVal?_lit)
open RvCell (predictive fresh exists_post_fiber_ne_zero post_fresh_ne_zero post_observe_ne_zero
  post_observe_ne_zero_of_predictive predictive_null predictive_singleton)
open MeasureTheory (lintegral_map lintegral_add_left lintegral_const measure_mono_null)
open MeasureTheory.Measure (map_apply)
open scoped ENNReal AppGS

namespace ProbLang.TotalEris

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
  {E : CoPset} {Φ : Val rT → IProp GF} {l : Loc}

local bi (IProp GF)
open ErrorCredit

/-- The law of a test's result. -/
local notation "pred" => predictive ProbLangDist.dist

/-- Allocating a random variable with prior `n` at `v` returns a fresh label owning it. -/
theorem twp_randvar [ProbLangDist.IsIntValued rT] {n : ℕ} {v : Val rT}
    (hd : ProbLangDist.dist n v ≠ 0) :
    iprop(∀ l, l ↦ᵣ fresh n v -∗ Φ (.lbl l)) ⊢ tglWp E (.randvar n (.ofVal v)) Φ := by
  iintro HΦ
  iapply twp_lift_atomic_head_step solve_not_value (by is_lc)
  iintro %σ₁ Hσ !>
  have hred : HeadReducible (.randvar n (.ofVal v)) σ₁ :=
    (RandvarS (toVal?_ofVal v) rfl rfl).ne_zero
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases headStepSupport Hstep with
  | RandvarS hv hl hσ =>
    rw [toVal?_ofVal, Option.some_inj] at hv
    subst hv hl hσ
    imod app_state_rv_alloc (post_fresh_ne_zero hd) $$ Hσ with ⟨Hσ', Hl⟩
    imodintro
    isimp only [erisWpGS_stateInterp_eq, insert_eq_PartialMap_insert, toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ %σ₁.rvs.fresh Hl

variable {k : ℕ} {a : Val rT} {c : RvCell rT}

/-- Testing a random variable returns a result of positive predictive mass and records the
observation. -/
theorem twp_test [ProbLangDist.IsIntValued rT] :
    iprop(l ↦ᵣ c ∗ ∀ y, ⌜pred k a c {y} ≠ 0⌝ -∗ l ↦ᵣ c.observe k a y -∗ Φ (.int y)) ⊢
      tglWp E (.test k (.lit (.lbl l)) (.ofVal a)) Φ := by
  iintro ⟨Hl, HΦ⟩
  ihave %hc := appRv_post_ne_zero $$ Hl
  iapply twp_lift_atomic_head_step solve_not_value (by is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_rv $$ Hσ Hl
  imodintro
  obtain ⟨y, hy⟩ := exists_post_fiber_ne_zero hc
  have hred : HeadReducible (.test k (.lit (.lbl l)) (.ofVal a)) σ₁ :=
    (TestS (toVal?_ofVal a) hlook hy).ne_zero
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases headStepSupport Hstep with
  | TestS hv hc' hy' =>
    rw [toVal?_ofVal, Option.some_inj] at hv
    subst hv
    rw [hlook, Option.some_inj] at hc'
    subst hc'
    imod app_state_update_rv (post_observe_ne_zero hy') $$ Hσ Hl with ⟨Hσ', Hl'⟩
    imodintro
    isimp only [erisWpGS_stateInterp_eq, insert_eq_PartialMap_insert, toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ %_ %(by rwa [predictive_singleton]) Hl'

/-- Spend `↯ε₁` on a test, giving result `y` the credit `ε₂ y` when the `ε₂` integrate to at most
`ε₁` against the posterior predictive. -/
theorem twp_test_exp {ε₁ : ℝ≥0∞} {ε₂ : Int → ℝ≥0∞} (hε : ∫⁻ y, ε₂ y ∂pred k a c ≤ ε₁) :
    iprop(↯ε₁ ∗ l ↦ᵣ c ∗ ∀ y, ↯(ε₂ y) -∗ l ↦ᵣ c.observe k a y -∗ Φ (.int y)) ⊢
      tglWp E (.test k (.lit (.lbl l)) (.ofVal a)) Φ := by
  iintro ⟨Herr, Hl, Hcont⟩
  ihave %hc := appRv_post_ne_zero $$ Hl
  iapply twp_lift_step_fupd_glm solve_not_value
  iintro %σ₁ %ε_now ⟨Hσ, Hε_now⟩
  ihave %hlook := app_state_lookup_rv $$ Hσ Hl
  imod (BIFUpdate.subset Std.LawfulSet.empty_subset) with Hclose
  imodintro
  ihave ⟨Hε_now, Herr, %hLe⟩ := errInterp_supply_bound $$ [$Hε_now $Herr]
  iapply glm'_prim_step
  set g := Cfg.testOutcome k a l σ₁ c
  have hhead : HeadReducible (.test k (.lit (.lbl l)) (.ofVal a)) σ₁ := by
    obtain ⟨y, hy⟩ := exists_post_fiber_ne_zero hc
    exact (TestS (toVal?_ofVal a) hlook hy).ne_zero
  have hprim : primStep ⟨.test k (.lit (.lbl l)) (.ofVal a), σ₁⟩ =
      (pred k a c).map g := by
    rw [primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible (by is_lc) hhead),
      headStep_test, Cfg.test_eq_map_predictive hlook]
  set f : Cfg rT → ℝ≥0∞ := fun ρ => match ρ.expr with | .lit (.int y) => ε₂ y | _ => 0
  have hf : Measurable f := (measurable_litInt_elim ε₂).comp Cfg.measurable_expr
  -- the reachable results: those of positive predictive mass
  set T := g '' {y | pred k a c {y} ≠ 0}
  have hR : MeasurableSet {ρ | ρ ∈ T} := ((Set.to_countable _).image g).measurableSet
  have hpgl : Pgl 0 (· ∈ T) (primStep ⟨.test k (.lit (.lbl l)) (.ofVal a), σ₁⟩) := by
    show primStep _ {ρ | ρ ∈ T}ᶜ ≤ 0
    rw [hprim, map_apply .of_discrete hR.compl, nonpos_iff_eq_zero]
    refine measure_mono_null (fun y hy => ?_) (predictive_null k a c)
    by_contra h
    exact hy ⟨y, h, rfl⟩
  have hint : ∫⁻ ρ, f ρ ∂primStep ⟨.test k (.lit (.lbl l)) (.ofVal a), σ₁⟩ ≤ ε₁ := by
    rw [hprim, lintegral_map hf .of_discrete]
    exact hε
  have hexp : 0 + ∫⁻ ρ, ((ε_now - ε₁) + f ρ)
      ∂primStep ⟨.test k (.lit (.lbl l)) (.ofVal a), σ₁⟩ ≤ ε_now := by
    rw [zero_add, lintegral_add_left measurable_const, lintegral_const]
    calc _ ≤ (ε_now - ε₁) * 1 + ε₁ := by gcongr; exact primStep_univ_le_one _
      _ = ε_now := by rw [mul_one]; exact tsub_add_cancel_of_le hLe
  have hred := reducible_of_headReducible (by is_lc) hhead
  iexists (· ∈ T), 0, (fun ρ => (ε_now - ε₁) + f ρ)
  iframe %hred %hR %hexp %hpgl
  iintro %ρ %⟨y, hy, rfl⟩
  imod errInterp_supply_decrease $$ [$Hε_now $Herr] with Hε_minus
  imodintro
  by_cases hlt : (ε_now - ε₁) + f (g y) < 1
  case neg =>
    push Not at hlt
    iapply execStutter_spend hlt
  case pos =>
    iapply execStutter_free
    imod errInterp_supply_increase hlt $$ Hε_minus with ⟨Hε_new, Hcr⟩
    imod app_state_update_rv (post_observe_ne_zero_of_predictive hy) $$ Hσ Hl with ⟨Hσ', Hl'⟩
    imod Hclose with -
    imodintro
    isimp only [erisWpGS_stateInterp_eq, insert_eq_PartialMap_insert, g, Cfg.testOutcome]
    iframe Hσ' Hε_new
    iapply (tglWp_value_of_toVal rfl)
    iapply Hcont $$ %y Hcr Hl'

end ProbLang.TotalEris
