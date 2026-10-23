module

public import Metrology.Micrometer.AppWeakestpre
import Metrology.Iris.LocalBI

/-! # Further lifting rules

Coupled-step rules for `wp` that keep the per-pair leftover `R`, and `wp_couple_erasables` for
presampling both sides at cost `0` (Rocq `approxis/lifting.v`). -/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

namespace ProbLang.MicrometerWpGS

variable {B : Type} [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B}
  {GF : BundledGFunctors} [MicrometerWpGS (rT := rT) GF] [BudgetGS B GF] {E : CoPset}
  {e₁ : Exp rT} {Φ : Val rT → IProp GF}
local bi IProp GF
open SpecUpdateGS

/-! ## Coupled steps with a leftover `R` -/

/-- Lift a coupled program and spec step whose leftover `R` is the new budget at each pair. -/
theorem wp_lift_prim_steps_coupl_adv' [Add B] [L.IsLawful] [L.HasBind] [L.IsSupportLocal]
    (hv : e₁.toVal? = none) : iprop%
    (∀ σ₁ e₁' σ₁' (b : B), stateInterp σ₁ ∗ specInterp ⟨e₁', σ₁'⟩ ∗
        budgetInterp b -∗ |={E, ∅}=>
        ∃ (R : Cfg rT → Cfg rT → B),
          ⌜Reducible e₁ σ₁⌝ ∗
          ⌜Reducible e₁' σ₁'⌝ ∗
          ⌜L b R (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)⌝ ∗
          (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ ▷ |={∅, E}=>
            stateInterp σ₂ ∗ specInterp ⟨e₂', σ₂'⟩ ∗
              budgetInterp (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) ∗ wp L E e₂ Φ)) ⊢
      wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_step_prog_couple hv
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  imod H $$ %σ₁ %e₁' %σ₁' %b [$Hσ $Hs $Hb] with ⟨%R, %hred, %hred', %hcpl, H⟩
  imodintro
  iapply progCoupl_steps_adv' hred hred' hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %hR !>
  iapply H $$ %e₂ %σ₂ %e₂' %σ₂' %hR

variable [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsTopAbsorbing] [L.HasBind]
  [L.IsSupportLocal]

/-- Lift a program step coupled with a spec step within `b₁`, adding `b₂` to every leftover
(Rocq `wp_lift_step_couple_adv`). -/
theorem wp_lift_prim_steps_coupl_adv (hv : e₁.toVal? = none) : iprop%
    (∀ σ₁ e₁' σ₁' (b : B), stateInterp σ₁ ∗ specInterp ⟨e₁', σ₁'⟩ ∗
        budgetInterp b -∗ |={E, ∅}=>
        ∃ (R : Cfg rT → Cfg rT → B) (b₁ b₂ : B),
          ⌜b₁ + b₂ ≤ b⌝ ∗
          ⌜Reducible e₁ σ₁⌝ ∗
          ⌜Reducible e₁' σ₁'⌝ ∗
          ⌜L b₁ R (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)⌝ ∗
          (∀ e₂ σ₂ e₂' σ₂', ⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂ < (⊤ : B)⌝ -∗ ▷ |={∅, E}=>
            stateInterp σ₂ ∗ specInterp ⟨e₂', σ₂'⟩ ∗
              budgetInterp (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂) ∗ wp L E e₂ Φ)) ⊢
      wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_step_prog_couple hv
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  imod H $$ %σ₁ %e₁' %σ₁' %b [$Hσ $Hs $Hb] with ⟨%R, %b₁, %b₂, %hb, %hred, %hred', %hcpl, H⟩
  imodintro
  iapply progCoupl_steps_adv hb hred hred' hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %hR !>
  iapply H $$ %e₂ %σ₂ %e₂' %σ₂' %hR

/-! ## Absorbing exit and presampling -/

/-- Budget-splitting coupled step whose continuation may exit with an absorbing budget instead of
proving `wp` (Rocq `wp_lift_step_couple_adv_err_le_1`, whose `1 ≤ ε` exit is
`L.Absorbing b`). -/
theorem wp_lift_prim_steps_coupl_adv_absorbing (hv : e₁.toVal? = none) : iprop%
    (∀ σ₁ e₁' σ₁' (b : B), stateInterp σ₁ ∗ specInterp ⟨e₁', σ₁'⟩ ∗
        budgetInterp b -∗ |={E, ∅}=>
        ∃ (R : Cfg rT → Cfg rT → B) (b₁ b₂ : B),
          ⌜b₁ + b₂ ≤ b⌝ ∗
          ⌜Reducible e₁ σ₁⌝ ∗
          ⌜Reducible e₁' σ₁'⌝ ∗
          ⌜L b₁ R (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)⌝ ∗
          (∀ e₂ σ₂ e₂' σ₂', ▷ |={∅, E}=>
            ⌜L.Absorbing (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂)⌝ ∨
            (stateInterp σ₂ ∗ specInterp ⟨e₂', σ₂'⟩ ∗
              budgetInterp (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂) ∗ wp L E e₂ Φ))) ⊢
      wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  imod H $$ %σ₁ %e₁' %σ₁' %b [$Hσ $Hs $Hb] with ⟨%R, %b₁, %b₂, %hb, %hred, %hred', %hcpl, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [hv]
  iapply progCoupl_steps_adv hb hred hred' hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %hR !> !>
  -- decide absorption before opening `H`: it picks the `specCoupl` disjunct
  by_cases habs : L.Absorbing (R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + b₂)
  · iapply specCoupl_absorbing habs
  · iapply specCoupl_ret
    imod H $$ %e₂ %σ₂ %e₂' %σ₂' with (%hge | H)
    · exact (habs hge).elim
    · icases H with ⟨Hσ', Hs', Hb', Hwp⟩
      imodintro
      iframe

/-- Presample both sides: couple erasable distributions of the program and spec states at cost
`0` (Rocq `wp_couple_erasables`). -/
theorem wp_couple_erasables : iprop%
    (∀ σ₁ e₁' σ₁' (b : B), stateInterp σ₁ ∗ specInterp ⟨e₁', σ₁'⟩ ∗
        budgetInterp b -∗ |={E, ∅}=>
        ∃ (R : State rT → State rT → Prop) (μ₁ μ₁' : MeasureTheory.Measure (State rT)),
          ⌜ErasableExpr μ₁ σ₁⌝ ∗ ⌜ErasableExpr μ₁' σ₁'⌝ ∗
          ⌜L.Rel 0 R μ₁ μ₁'⌝ ∗
          (∀ σ₂ σ₂', ⌜R σ₂ σ₂'⌝ -∗ |={∅, E}=>
            stateInterp σ₂ ∗ specInterp ⟨e₁', σ₂'⟩ ∗ budgetInterp b ∗
              wp L E e₁ Φ)) ⊢
      wp L E e₁ Φ := by
  iintro H
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  imod H $$ %σ₁ %e₁' %σ₁' %b [$Hσ $Hs $Hb] with ⟨%R, %μ₁, %μ₁', %her, %her', %hcpl, H⟩
  imodintro
  iapply specCoupl_erasables (by rw [zero_add]) hcpl her her'
  iintro %σ₂ %σ₂' %hR !>
  iapply specCoupl_ret
  imod H $$ %σ₂ %σ₂' %hR with ⟨Hσ', Hs', Hb', Hwp⟩
  imodintro
  iframe

end ProbLang.MicrometerWpGS
