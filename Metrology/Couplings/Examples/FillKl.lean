module

public import Metrology.Couplings.Codensity
public import Metrology.Couplings.Divergences.FillKl
public import Metrology.Couplings.Divergences.FillHellinger

/-! # The filled-KL codensity lifting

`codensity (fill klDivergence)` has every lifting law the program logic asks for, by the generic
codensity instances (`codensity_fill_kl_laws`), and lifts of equality read back as KL bounds
(`klDiv_le_of_codensity_fill_kl`). Filled `α`-Hellinger has the same laws
(`codensity_fill_hellinger_laws`). -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory InformationTheory
open scoped ENNReal

namespace GradedDivergence

variable {X : Type u} [MeasurableSpace X] {μ ν : Measure X} {b : ℝ≥0∞}

/-- The codensity lifting of filled KL is lawful, binds, is reflexive, support local, top absorbing,
zero-left, left continuous, sound, complete and budget closed. -/
theorem codensity_fill_kl_laws :
    (codensity (fill klDivergence.{u})).IsLawful ∧ (codensity (fill klDivergence.{u})).HasBind ∧
      GradedLifting.IsReflexive (codensity (fill klDivergence.{u})) ∧
      (codensity (fill klDivergence.{u})).IsSupportLocal ∧
      (codensity (fill klDivergence.{u})).IsTopAbsorbing ∧
      GradedLifting.IsZeroLeft (codensity (fill klDivergence.{u})) ∧
      GradedLifting.IsLeftContinuous (codensity (fill klDivergence.{u})) ∧
      (codensity (fill klDivergence.{u})).IsSound (fill klDivergence) ∧
      (codensity (fill klDivergence.{u})).IsComplete (fill klDivergence) ∧
      GradedLifting.IsBudgetClosed (codensity (fill klDivergence.{u})) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The filled-KL lifting of equality is filled KL. -/
theorem codensity_fill_kl_rel_eq_iff [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    (codensity (fill klDivergence)).Rel b (· = ·) μ ν ↔ fill klDivergence b μ ν :=
  codensity_rel_eq_iff

/-- Between probability measures, the filled-KL lifting of equality is KL. -/
theorem codensity_fill_kl_rel_eq_iff_of_isProbabilityMeasure [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    (codensity (fill klDivergence)).Rel b (· = ·) μ ν ↔ klDivergence b μ ν :=
  codensity_fill_kl_rel_eq_iff.trans fill_kl_iff_of_isProbabilityMeasure

/-- A filled-KL lifting of equality from a terminating program bounds Mathlib's KL divergence
(compare `klDiv_le_of_markovCodensity`). -/
theorem klDiv_le_of_codensity_fill_kl [IsProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    (h : (codensity (fill klDivergence)).Rel b (· = ·) μ ν) : klDiv μ ν ≤ b :=
  klDiv_le_of_fill (codensity_sound h)

/-- The codensity lifting of filled `α`-Hellinger has the same laws as filled KL. -/
theorem codensity_fill_hellinger_laws (α : ℝ) [Fact (α ∈ Set.Ioo (0 : ℝ) 1)] :
    (codensity (fill (hellingerDivergence.{u} α))).IsLawful ∧
      (codensity (fill (hellingerDivergence.{u} α))).HasBind ∧
      GradedLifting.IsReflexive (codensity (fill (hellingerDivergence.{u} α))) ∧
      (codensity (fill (hellingerDivergence.{u} α))).IsSupportLocal ∧
      (codensity (fill (hellingerDivergence.{u} α))).IsTopAbsorbing ∧
      GradedLifting.IsZeroLeft (codensity (fill (hellingerDivergence.{u} α))) ∧
      GradedLifting.IsLeftContinuous (codensity (fill (hellingerDivergence.{u} α))) ∧
      (codensity (fill (hellingerDivergence.{u} α))).IsSound (fill (hellingerDivergence α)) ∧
      (codensity (fill (hellingerDivergence.{u} α))).IsComplete (fill (hellingerDivergence α)) ∧
      GradedLifting.IsBudgetClosed (codensity (fill (hellingerDivergence.{u} α))) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance⟩

end GradedDivergence
