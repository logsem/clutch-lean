module

public import Metrology.Couplings.Divergences.Laplace
public import Metrology.ForSampCert.PureDPzCDP

/-! # Pure DP gives zCDP

Two-sided pure DP gives zCDP (Bun–Steinke 2016, Prop. 3.3), via `ForSampCert.ofDP_bound`. -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal NNReal
open ENNReal

namespace GradedDivergence

variable {X : Type u} [MeasurableSpace X] {μ ν : Measure X} {ε : ℝ≥0} {α : ℝ}

/-- The perspective of `t ↦ t ^ α` at finite masses is `a ^ α * b ^ (1 - α)`. -/
theorem persp_rpow_toReal (hα : 1 < α) {a b : ℝ≥0∞} (hb : b ≠ ⊤) (hab : b = 0 → a = 0) :
    persp (· ^ α) a.toReal b.toReal = (((a ^ α * b ^ (1 - α)).toReal : ℝ) : EReal) := by
  rcases eq_or_ne b 0 with rfl | hb0
  · simp [hab rfl, persp_rpow_zero_left (zero_lt_one.trans hα) le_rfl,
      zero_rpow_of_pos (zero_lt_one.trans hα)]
  have hb' : 0 < b.toReal := toReal_pos hb0 hb
  rw [persp_rpow_of_pos α hb', EReal.coe_eq_coe_iff, toReal_mul,
    ← toReal_rpow, ← toReal_rpow,
    Real.div_rpow toReal_nonneg hb'.le, Real.rpow_sub hb', Real.rpow_one]
  field_simp

/-- Two-sided pure `ε`-DP bounds the Rényi moment of probability measures on a finite space by
`e^{(α - 1) α ε² / 2}` (SampCert `ofDP_bound`). -/
theorem fDiv_rpow_le_of_dp_of_finite {I : Type*} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] {ρ₁ ρ₂ : Measure I} [IsProbabilityMeasure ρ₁]
    [IsProbabilityMeasure ρ₂] (hα : 1 < α) (h : dp (ε, 0) ρ₁ ρ₂) (h' : dp (ε, 0) ρ₂ ρ₁) :
    fDiv (· ^ α) ρ₁ ρ₂ ≤ ((Real.exp ((α - 1) * (α * ε ^ 2 / 2)) : ℝ) : EReal) := by
  have hratio {ρ ρ' : Measure I} (h : dp (ε, 0) ρ ρ') (i : I) :
      ρ {i} / ρ' {i} ≤ ENNReal.ofReal (Real.exp ε) := by
    refine div_le_of_le_mul ?_
    simpa [expBudget_of_ne_top coe_ne_top] using
      (dp_iff coe_ne_top).1 h {i} (measurableSet_singleton i)
  have hac (i : I) : ρ₂ {i} = 0 → ρ₁ {i} = 0 :=
    ForSampCert.ACNeighbour_of_DP ε ρ₁.toPMF ρ₂.toPMF (hratio h) i
  have hsum := ForSampCert.ofDP_bound ε ρ₁.toPMF ρ₂.toPMF (hratio h) (hratio h') α hα
  simp only [toPMF_apply, tsum_fintype] at hsum
  rw [fDiv_eq_sum (convexOn_rpow hα.le) (continuousWithinAt_rpow_zero (zero_lt_one.trans hα)),
    Finset.sum_congr rfl fun i _ ↦ persp_rpow_toReal hα (by finiteness) (hac i),
    ← EReal.coe_finset_sum, EReal.coe_le_coe_iff,
    ← toReal_sum fun i _ ↦ ne_top_of_le_ne_top ofReal_ne_top
      ((Finset.single_le_sum (fun j _ ↦ zero_le) (Finset.mem_univ i)).trans hsum)]
  calc (∑ i, ρ₁ {i} ^ α * ρ₂ {i} ^ (1 - α)).toReal
    _ ≤ Real.exp ((α - 1) * (1 / 2 * ε ^ 2 * α)) := toReal_le_of_le_ofReal (Real.exp_pos _).le hsum
    _ = Real.exp ((α - 1) * (α * ε ^ 2 / 2)) := by ring_nf

/-- Two-sided pure `ε`-DP bounds the Rényi divergence of order `α` by `α ε² / 2`
(Bun–Steinke 2016, Prop. 3.3). -/
theorem renyi_of_dp_two_sided [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hα : 1 < α)
    (h : dp (ε, 0) μ ν) (h' : dp (ε, 0) ν μ) :
    renyiDivergence α (ENNReal.ofReal (α * ε ^ 2 / 2)) μ ν := by
  rw [renyiDivergence_iff_of_ne_top hα.le ofReal_ne_top,
    toReal_ofReal (by positivity), fDiv_eq_iSup_map (convexOn_rpow hα.le)
      (continuousWithinAt_rpow_zero (zero_lt_one.trans hα))]
  refine iSup_le fun n ↦ iSup_le fun k ↦ iSup_le fun hk ↦ ?_
  exact fDiv_rpow_le_of_dp_of_finite hα (dp_map h hk) (dp_map h' hk)

/-- Two-sided pure `ε`-DP gives `(0, ε² / 2)`-zCDP (Bun–Steinke 2016, Prop. 3.3). -/
theorem zcdp_of_dp_two_sided [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : dp (ε, 0) μ ν) (h' : dp (ε, 0) ν μ) :
    zcdpDivergence (0, ENNReal.ofReal (ε ^ 2 / 2)) μ ν :=
  zcdpDivergence_iff.2 fun α hα ↦ by
    rw [zero_add, ← ofReal_mul (by linarith), ← mul_div_assoc]
    exact renyi_of_dp_two_sided hα h h'

end GradedDivergence

namespace ProbabilityTheory.Kernel

variable {X : Type*} {Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {m : Kernel X Y}
  {adj : Adjacency X} {ε : ℝ≥0}

/-- A pure `ε`-DP mechanism for a symmetric adjacency is `(0, ε² / 2)`-zCDP
(Bun–Steinke 2016, Prop. 3.3). -/
theorem zCDP_of_DP_of_symm [IsMarkovKernel m] [Std.Symm adj] (h : m.DP adj ε 0) :
    m.zCDP adj 0 (ENNReal.ofReal (ε ^ 2 / 2)) :=
  fun _ _ hx ↦ GradedDivergence.zcdp_of_dp_two_sided (h hx) (h (Std.Symm.symm _ _ hx))

end ProbabilityTheory.Kernel

namespace Mechanism

/-- The Laplace mechanism with scale `b` is `(0, (r / b)² / 2)`-zCDP for inputs at distance at
most `r`. -/
theorem zCDP_laplaceMech {r : ℝ} (hr : 0 ≤ r) (b : ℝ≥0) [Fact (0 < b)] :
    (laplaceMech b).zCDP (fun a a' ↦ |a - a'| ≤ r) 0 (ENNReal.ofReal ((r / b) ^ 2 / 2)) := by
  have : Std.Symm fun a a' : ℝ ↦ |a - a'| ≤ r := ⟨fun a a' (h : |a - a'| ≤ r) ↦ by
    rwa [abs_sub_comm]⟩
  have h := Kernel.zCDP_of_DP_of_symm (ε := (r / b).toNNReal) (DP_laplaceMech r b)
  rwa [Real.coe_toNNReal _ (by positivity)] at h

end Mechanism
