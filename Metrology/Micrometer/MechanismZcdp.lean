module

public import Metrology.Micrometer.Mechanism
public import Metrology.Couplings.Divergences.PureDpZcdp
import Metrology.Iris.LocalBI

/-! # Pure DP programs are zCDP

A terminating program family refining in both directions from `↯b (ε, 0)` in `codensity dp` is
`(0, ε² / 2)`-zCDP (`progMech_zCDP_of_dp`), hence `(ε, δ)`-DP through zCDP. -/

@[expose] public section

open scoped ENNReal NNReal

namespace ProbabilityTheory.Kernel

open Real

/-- An `(0, ε² / 2)`-zCDP mechanism is `(ε² / 2 + 2 √(ε² / 2 · log (1 / δ)), δ)`-DP. -/
theorem DP_of_zCDP_sq {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {m : Kernel X Y}
    [IsFiniteKernel m] {adj : Adjacency X} {ε : ℝ≥0} {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1)
    (h : m.zCDP adj 0 (ENNReal.ofReal (ε ^ 2 / 2))) :
    m.DP adj (ENNReal.ofReal (ε ^ 2 / 2 + 2 * √(ε ^ 2 / 2 * log (1 / δ)))) (ENNReal.ofReal δ) := by
  have := DP_of_zCDP hδ hδ₁ h
  rwa [zero_add, ENNReal.toReal_ofReal (by positivity), ← ENNReal.ofReal_add (by positivity)
    (by positivity)] at this

end ProbabilityTheory.Kernel

namespace ProbLang

open Iris Iris.BI ProbabilityTheory GradedDivergence Real

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT] {X : Type}
  [MeasurableSpace X] (GF : BundledGFunctors) [RefinesPreGS rT (ℝ≥0∞ × ℝ≥0∞) GF]
  (p : X → Exp rT) (σ : State rT) {hp : Measurable fun x ↦ (⟨p x, σ⟩ : Cfg rT)}
  [IsMarkovKernel (progMech p σ hp)] {adj : Adjacency X} (ε : ℝ≥0)
  (A : ∀ (_ : MicrometerRGS rT .hasNoLC GF) (_ : BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF), lrel rT GF)
  (HA : ∀ IR IBC v v', ⊢ (A IR IBC).car v v' -∗ ⌜v = v'⌝)
  (Hlog : ∀ x x', adj x x' → ∀ (IR : MicrometerRGS rT .hasNoLC GF)
    (IBC : BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF),
    ⊢ ↯b ((ε : ℝ≥0∞), (0 : ℝ≥0∞)) -∗ refines (codensity dp) ⊤ (p x) (p x') (A IR IBC))
  (Hlog' : ∀ x x', adj x x' → ∀ (IR : MicrometerRGS rT .hasNoLC GF)
    (IBC : BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF),
    ⊢ ↯b ((ε : ℝ≥0∞), (0 : ℝ≥0∞)) -∗ refines (codensity dp) ⊤ (p x') (p x) (A IR IBC))
include HA Hlog Hlog'
local bi IProp GF

/-- A terminating program family whose members on adjacent inputs refine each other in both
directions at equal results from `↯b (ε, 0)` is `(0, ε² / 2)`-zCDP (Bun–Steinke 2016,
Prop. 3.3). -/
theorem progMech_zCDP_of_dp : (progMech p σ hp).zCDP adj 0 (ENNReal.ofReal (ε ^ 2 / 2)) :=
  fun _ _ hx ↦ zcdp_of_dp_two_sided (progMech_isPrivate GF p σ _ A HA Hlog hx)
    (progMech_isPrivate GF p σ _ A HA (fun x x' hx ↦ Hlog' x' x hx) hx)

/-- A terminating program family refining in both directions from `↯b (ε, 0)` is
`(ε² / 2 + 2 √(ε² / 2 · log (1 / δ)), δ)`-DP at every slack `0 < δ < 1`, through zCDP. -/
theorem progMech_DP_of_dp_sqrt {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) :
    (progMech p σ hp).DP adj (ENNReal.ofReal (ε ^ 2 / 2 + 2 * √(ε ^ 2 / 2 * log (1 / δ))))
      (ENNReal.ofReal δ) :=
  Kernel.DP_of_zCDP_sq hδ hδ₁ (progMech_zCDP_of_dp GF p σ ε A HA Hlog Hlog')

end ProbLang
