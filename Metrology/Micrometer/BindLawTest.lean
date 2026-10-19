module

public import Metrology.Micrometer.AppWeakestpre
public import Metrology.Couplings.BindLaws

@[expose] public section

/-! # Smoke tests for non-canonical bind laws in Micrometer steps -/

open Iris Iris.BI Iris.ProofMode GradedLifting GradedDivergence ProbLang.MicrometerWpGS
open scoped ENNReal

namespace ProbLang
namespace BindLawTest

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT] {GF : BundledGFunctors}
  [MicrometerWpGS (rT := rT) GF]

open Classical in
/-- A program step coupled with a spec step by right-keyed adaptive DP composition: the head DP
lifting of `S` costs `(ε₁, δ₁)`, and each related pair continues at `(ε₂, D ρ')`, paid as
`(ε₁ + ε₂, δ₁ + e^{ε₁} E[D])` (Rocq `GBL_DP_rhs`). -/
theorem progCoupl_dpRhs {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε₁ ε₂ δ₁ : ℝ≥0∞} {D : Cfg rT → ℝ≥0∞} {S : Cfg rT → Cfg rT → Prop}
    {Z : Exp rT → State rT → Exp rT → State rT → ℝ≥0∞ × ℝ≥0∞ → IProp GF}
    (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁') (hD : Measurable D)
    (hS : (codensity dp).Rel (ε₁, δ₁) S (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜S ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝ -∗ |={∅}=> Z e₂ σ₂ e₂' σ₂' (ε₂, D ⟨e₂', σ₂'⟩)) ⊢
    progCoupl (codensity dp) e₁ σ₁ e₁' σ₁'
      (ε₁ + ε₂, δ₁ + expBudget ε₁ * ∫⁻ ρ, D ρ ∂primStep ⟨e₁', σ₁'⟩) Z := by
  have := prim_step_mass Hred
  have := prim_step_mass Hred'
  let R : Cfg rT → Cfg rT → ℝ≥0∞ × ℝ≥0∞ := fun ρ ρ' => if S ρ ρ' then (ε₂, D ρ') else ⊤
  iintro H
  iapply progCoupl_steps_law (R := R) BindLaw.dpRhs Hred Hred'
    ⟨ε₁, ε₂, δ₁, D, S, hD, inferInstance, inferInstance, hS, fun _ _ h => by simp [R, h], le_rfl⟩
    (.of_forall fun _ _ => trivial)
  iintro %e₂ %σ₂ %e₂' %σ₂' %hR
  by_cases hS' : S ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩
  · simp only [R, hS', ↓reduceIte]
    iapply H $$ %e₂ %σ₂ %e₂' %σ₂' %hS'
  · simp [R, hS'] at hR

end BindLawTest
end ProbLang
