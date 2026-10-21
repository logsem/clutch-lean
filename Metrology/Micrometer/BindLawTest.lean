module

public import Metrology.Micrometer.AppWeakestpre
public import Metrology.Couplings.BindLaws
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Smoke tests: program steps under non-canonical DP bind laws

Instantiates the generic `progCoupl_steps_law` / `progCoupl_steps_spend_law` with
`BindLaw.dpRhs` and `BindLaw.dpChoice`. -/

open Iris Iris.BI Iris.ProofMode GradedLifting GradedDivergence ProbLang.MicrometerWpGS
open scoped ENNReal

namespace ProbLang
namespace BindLawTest

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT] {GF : BundledGFunctors}
  [MicrometerWpGS (rT := rT) GF]
local bi IProp GF

variable {e₁ e₁' : Exp rT} {σ₁ σ₁' : State rT}
  {Z : Exp rT → State rT → Exp rT → State rT → ℝ≥0∞ × ℝ≥0∞ → IProp GF}

open Classical in
/-- A program step coupled with a spec step by right-keyed adaptive DP composition: the head DP
lifting of `S` costs `(ε₁, δ₁)`, and each related pair continues at `(ε₂, D ρ')`, paid as
`(ε₁ + ε₂, δ₁ + e^{ε₁} E[D])` (Rocq `GBL_DP_rhs`). -/
theorem progCoupl_dpRhs {ε₁ ε₂ δ₁ : ℝ≥0∞} {D : Cfg rT → ℝ≥0∞} {S : Cfg rT → Cfg rT → Prop}
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
  · simp [R, hS'] at hR  -- unrelated pairs carry budget `⊤`, which `hR` rules out

open Classical in
/-- A program step coupled by the DP choice rule while `c` of the budget rides through it on every
leftover, so the head spends only part of `b`
(Rocq `GBL_DP_choice_head_shift`, `wp_couple_spend`). -/
theorem progCoupl_dpChoice_spend {ε₁ δ₁ ε₁' δ₁' ε₂ ε₂' δ₂ : ℝ≥0∞} {c b : ℝ≥0∞ × ℝ≥0∞}
    {S₁ S₂ : Cfg rT → Cfg rT → Prop} {P T : Set (Cfg rT)}
    (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁') (hP : MeasurableSet P)
    (hT : MeasurableSet T)
    (h₁ : (codensity dp).Rel (ε₁, δ₁) S₁ (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩))
    (h₂ : (codensity dp).Rel (ε₁', δ₁') S₂ (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩))
    (hPT₁ : ∀ ρ ρ', ρ ∈ P → S₁ ρ ρ' → ρ' ∈ T) (hPT₂ : ∀ ρ ρ', ρ ∉ P → S₂ ρ ρ' → ρ' ∉ T)
    (hc : c < (⊤ : ℝ≥0∞ × ℝ≥0∞)) (hb : (max (ε₁ + ε₂) (ε₁' + ε₂'), δ₁ + δ₁' + δ₂) + c ≤ b) : iprop%
    (∀ e₂ σ₂ e₂' σ₂', ⌜S₁ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ ∨ S₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝ -∗ |={∅}=>
      Z e₂ σ₂ e₂' σ₂' ((if (⟨e₂, σ₂⟩ : Cfg rT) ∈ P then (ε₂, δ₂) else (ε₂', δ₂)) + c)) ⊢
    progCoupl (codensity dp) e₁ σ₁ e₁' σ₁' b Z := by
  have := prim_step_mass Hred
  have := prim_step_mass Hred'
  let R : Cfg rT → Cfg rT → ℝ≥0∞ × ℝ≥0∞ := fun ρ ρ' =>
    if S₁ ρ ρ' ∨ S₂ ρ ρ' then (if ρ ∈ P then (ε₂, δ₂) else (ε₂', δ₂))
    else (⊤ : ℝ≥0∞ × ℝ≥0∞)
  iintro H
  iapply progCoupl_steps_spend_law (R := R) BindLaw.dpChoice hb hc Hred Hred'
    ⟨ε₁, δ₁, ε₁', δ₁', ε₂, ε₂', δ₂, S₁, S₂, P, T, hP, hT, inferInstance, inferInstance, h₁, h₂,
      hPT₁, hPT₂, fun _ _ hx h => by simp [R, hx, h], fun _ _ hx h => by simp [R, hx, h], le_rfl⟩
    (.of_forall fun _ _ => trivial)
  iintro %e₂ %σ₂ %e₂' %σ₂' %hR
  by_cases hS : S₁ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ ∨ S₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩
  · simp only [R, hS, ↓reduceIte]
    iapply H $$ %e₂ %σ₂ %e₂' %σ₂' %hS
  · simp only [R, hS, ↓reduceIte] at hR
    -- unrelated pairs carry budget `⊤`, which `hR` rules out
    have htop : (⊤ : ℝ≥0∞ × ℝ≥0∞) + c = (⊤ : ℝ≥0∞ × ℝ≥0∞) :=
      Prod.ext (top_add c.1) (top_add c.2)
    exact absurd htop hR.ne

end BindLawTest
end ProbLang
