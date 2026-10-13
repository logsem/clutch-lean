module

public import Metrology.Approxis.AppWeakestpre

@[expose] public section

/-! # Lifting lemmas translating operational semantics rules into program-logic rules. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS

variable {rT : Type} [ProbLang.LawfulProbLangℝ rT]

namespace ProbLang.ApproxisWpGS

variable {ι : Type} [Monoid ι] {Δ : GradedDivergence.{0} ι} {GF : BundledGFunctors}
  [ApproxisWpGS (rT := rT) Δ GF]

theorem wp_lift_prim_steps_coupl_adv {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (hv : e₁.toVal? = none) : iprop%
    (∀ σ₁ e₁' σ₁' ε, stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗
      errInterp (rT := rT) ε -∗ |={E, ∅}=>
      ∃ (X : Cfg rT → Cfg rT → ENNReal) (ε₁ ε₂ : ENNReal),
        ⌜ε₁ + ε₂ ≤ ε⌝ ∗
        ⌜Reducible e₁ σ₁⌝ ∗
        ⌜Reducible e₁' σ₁'⌝ ∗
        ⌜∀ ρ₁ ρ₂, X ρ₁ ρ₂ ≤ 1⌝ ∗
        ⌜Δ.CodensityE 1 ε₁ X (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)⌝ ∗
        (∀ e₂ σ₂ e₂' σ₂', ▷ |={∅, E}=>
          stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₂', σ₂'⟩ ∗
            errInterp (rT := rT) (X ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + ε₂) ∗ wp E e₂ Φ)) ⊢
    wp E e₁ Φ := by
  iintro H
  iapply wp_lift_step_prog_couple hv
  iintro %σ₁ %e₁' %σ₁' %ε Hpre
  imod H $$ %σ₁ %e₁' %σ₁' %ε Hpre with ⟨%X, %ε₁, %ε₂, %hεsum, %hred, %hred', %hbnd, %hcpl, H⟩
  imodintro
  iapply progCoupl_steps_adv hεsum hred hred' hbnd hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' !> !>
  iapply H $$ %e₂ %σ₂ %e₂' %σ₂'

theorem wp_lift_prim_steps_coupl_adv' {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (hv : e₁.toVal? = none) : iprop%
    (∀ σ₁ e₁' σ₁' ε, stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗
      errInterp (rT := rT) ε -∗ |={E, ∅}=>
      ∃ (X : Cfg rT → Cfg rT → ENNReal),
        ⌜Reducible e₁ σ₁⌝ ∗
        ⌜Reducible e₁' σ₁'⌝ ∗
        ⌜∀ ρ₁ ρ₂, X ρ₁ ρ₂ ≤ 1⌝ ∗
        ⌜Δ.CodensityE 1 ε X (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)⌝ ∗
        (∀ e₂ σ₂ e₂' σ₂', ▷ |={∅, E}=>
          stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₂', σ₂'⟩ ∗
            errInterp (rT := rT) (X ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) ∗ wp E e₂ Φ)) ⊢
    wp E e₁ Φ := by
  iintro H
  iapply wp_lift_step_prog_couple hv
  iintro %σ₁ %e₁' %σ₁' %ε Hpre
  imod H $$ %σ₁ %e₁' %σ₁' %ε Hpre with ⟨%X, %hred, %hred', %hbnd, %hcpl, H⟩
  imodintro
  iapply progCoupl_steps_adv' hred hred' hbnd hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' !> !>
  iapply H $$ %e₂ %σ₂ %e₂' %σ₂'

theorem wp_lift_prim_steps_coupl_adv_err_le_1 {E : CoPset} {e₁ : Exp rT}
    {Φ : Val rT → IProp GF} (hv : e₁.toVal? = none) : iprop%
    (∀ σ₁ e₁' σ₁' ε, stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗
      errInterp (rT := rT) ε -∗ |={E, ∅}=>
      ∃ (X : Cfg rT → Cfg rT → ENNReal) (ε₁ ε₂ : ENNReal),
        ⌜ε₁ + ε₂ ≤ ε⌝ ∗
        ⌜Reducible e₁ σ₁⌝ ∗
        ⌜Reducible e₁' σ₁'⌝ ∗
        ⌜∀ ρ₁ ρ₂, X ρ₁ ρ₂ ≤ 1⌝ ∗
        ⌜Δ.CodensityE 1 ε₁ X (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)⌝ ∗
        (∀ e₂ σ₂ e₂' σ₂', ▷ |={∅, E}=>
          ⌜1 ≤ X ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + ε₂⌝ ∨
          (stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₂', σ₂'⟩ ∗
            errInterp (rT := rT) (X ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + ε₂) ∗ wp E e₂ Φ))) ⊢
    wp E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %ε Hpre
  imod H $$ %σ₁ %e₁' %σ₁' %ε Hpre with ⟨%X, %ε₁, %ε₂, %hεsum, %hred, %hred', %hbnd, %hcpl, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [hv]
  iapply progCoupl_steps_adv hεsum hred hred' hbnd hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' !> !>
  ispecialize H $$ %e₂ %σ₂ %e₂' %σ₂'
  by_cases hle : X ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + ε₂ < 1
  · iapply specCoupl_ret
    imod H with (%hge | H)
    · exact absurd hle (_root_.not_lt.mpr hge)
    · imodintro; iexact H
  · iapply specCoupl_err_ge_1 (_root_.not_lt.mp hle)

theorem wp_couple_erasables {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} : iprop%
    (∀ σ₁ e₁' σ₁' ε, stateInterp σ₁ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₁'⟩ ∗
      errInterp (rT := rT) ε -∗ |={E, ∅}=>
      ∃ (R : State rT → State rT → Prop) (μ₁ μ₁' : MeasureTheory.Measure (State rT)),
        ⌜ErasableExpr μ₁ σ₁⌝ ∗ ⌜ErasableExpr μ₁' σ₁'⌝ ∗
        ⌜Δ.Codensity 1 0 {p | R p.1 p.2} μ₁ μ₁'⌝ ∗
        (∀ σ₂ σ₂', ⌜R σ₂ σ₂'⌝ -∗ |={∅, E}=>
          stateInterp σ₂ ∗ SpecUpdateGS.specInterp ⟨e₁', σ₂'⟩ ∗ errInterp (rT := rT) ε ∗
            wp E e Φ)) ⊢
    wp E e Φ := by
  iintro H
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %ε Hpre
  imod H $$ %σ₁ %e₁' %σ₁' %ε Hpre with ⟨%R, %μ₁, %μ₁', %her, %her', %hcpl, H⟩
  imodintro
  iapply specCoupl_erasables (by rw [zero_add]) hcpl her her'
  iintro %σ₂ %σ₂' %hR !>
  iapply specCoupl_ret
  iapply H $$ %σ₂ %σ₂' %hR

end ProbLang.ApproxisWpGS
