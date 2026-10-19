module

public import Metrology.Couplings.BindLaws

/-! Escort heads shift: scaling the right measure by `e^{-c}` costs `c` in every Rényi
divergence, so the escort law spends from credits (Rocq `gbl_head_shift`). -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory GradedLifting GradedDivergence Real
open scoped ENNReal

namespace GradedDivergence

variable {X : Type u} [MeasurableSpace X] {α : ℝ} {ρ : ℝ≥0∞} {μ ν : Measure X}

/-- Scaling the right measure by `e^{-c}` raises the Rényi divergence by at most `c`. -/
theorem renyiDivergence_smul_inv_expBudget (hα : 1 < α) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : renyiDivergence α ρ μ ν) :
    renyiDivergence α (ρ + c) μ ((expBudget c)⁻¹ • ν) := by
  rcases eq_or_ne ρ ⊤ with rfl | hρ
  · simpa using renyiDivergence_top hα μ ((expBudget c)⁻¹ • ν)
  have : IsFiniteMeasure ((expBudget c)⁻¹ • ν) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (zero_lt_one.trans_le (one_le_expBudget c)))
      (measure_lt_top ν _)⟩
  have hf := convexOn_rpow hα.le
  have hf0 := continuousWithinAt_rpow_zero (zero_lt_one.trans hα)
  rw [renyiDivergence_iff_of_ne_top hα.le hρ, fDiv_eq_iSup_partition hf hf0] at h
  rw [renyiDivergence_iff_of_ne_top hα.le (by finiteness), fDiv_eq_iSup_partition hf hf0]
  refine iSup_le fun n ↦ iSup_le fun k ↦ iSup_le fun hk ↦ ?_
  set p : Fin n → ℝ := fun i ↦ (μ (k ⁻¹' {i})).toReal
  set q : Fin n → ℝ := fun i ↦ (ν (k ⁻¹' {i})).toReal
  have hsum : ∑ i, persp (· ^ α) (p i) (q i) ≤ _ :=
    (le_iSup₂_of_le (f := fun n (k : X → Fin n) ↦ ⨆ (_ : Measurable k),
      ∑ i, persp (· ^ α) (μ (k ⁻¹' {i})).toReal (ν (k ⁻¹' {i})).toReal) n k
      (le_iSup_of_le hk le_rfl)).trans h
  have hs : ((expBudget c)⁻¹).toReal = exp (-c.toReal) := by
    rw [expBudget_of_ne_top hc, ← ENNReal.ofReal_inv_of_pos (exp_pos _),
      ENNReal.toReal_ofReal (by positivity), exp_neg]
  have hfin (i : Fin n) :
      ((persp (· ^ α) (p i) (q i)).toReal : EReal) = persp (· ^ α) (p i) (q i) :=
    have hnn (j : Fin n) : 0 ≤ persp (· ^ α) (p j) (q j) :=
      persp_rpow_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _)
      ((Finset.single_le_sum (fun j _ ↦ hnn j) (Finset.mem_univ i)).trans hsum))
      (ne_bot_of_le_ne_bot EReal.zero_ne_bot (hnn i))
  -- each cell costs `e^{(α - 1) c}` times more
  have hcell (i : Fin n) : persp (· ^ α) (p i) (((expBudget c)⁻¹ • ν) (k ⁻¹' {i})).toReal =
      ((exp ((α - 1) * c.toReal) * (persp (· ^ α) (p i) (q i)).toReal : ℝ) : EReal) := by
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, hs, ← one_mul (p i),
      persp_rpow_mul hα zero_le_one (exp_pos _).le ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      persp_rpow_of_pos α (exp_pos _), one_mul, ← hfin i, ← EReal.coe_mul, EReal.coe_eq_coe_iff,
      one_div, ← exp_neg, neg_neg, ← exp_mul, ← exp_add, EReal.toReal_coe]
    ring_nf
  have hreal : ∑ i, (persp (· ^ α) (p i) (q i)).toReal ≤ exp ((α - 1) * ρ.toReal) := by
    rw [← EReal.coe_le_coe_iff, EReal.coe_finset_sum]
    simpa only [hfin] using hsum
  rw [Finset.sum_congr rfl fun i _ ↦ hcell i]
  rw [← EReal.coe_finset_sum, EReal.coe_le_coe_iff, ← Finset.mul_sum,
    ENNReal.toReal_add hρ hc, mul_add, exp_add, mul_comm (exp ((α - 1) * ρ.toReal))]
  gcongr

end GradedDivergence

namespace GradedLifting.BindLaw

/-- Escort heads shift: the escort continues at `ρ₂ + c` against the right measure reweighted by
another `e^{-c}`, which costs `c` more. -/
instance headShift_escort (α : ℝ) [hα : Fact (1 < α)] : (escort.{u} α).HeadShift where
  shift := by
    rintro _ _ _ _ _ c _ μ ν hc ⟨S, ρ₂, r, A, hr, hρ₂, hA, hμA, hμ, hν, hrS, hR, h⟩
    refine ⟨S, fun x ↦ ρ₂ x + c, r, A, hr, hρ₂.add_const c, hA, hμA, hμ, hν, hrS,
      fun x y hx hxy ↦ by simp only [hR x y hx hxy], ?_⟩
    have hw : (fun x ↦ (expBudget (ρ₂ x + c))⁻¹) =
        (expBudget c)⁻¹ • fun x ↦ (expBudget (ρ₂ x))⁻¹ := by
      ext x
      rw [expBudget_add, Pi.smul_apply, smul_eq_mul, mul_comm,
        ENNReal.mul_inv (.inl (zero_lt_one.trans_le (one_le_expBudget _)).ne')
        (.inr (zero_lt_one.trans_le (one_le_expBudget _)).ne')]
    rw [hw, withDensity_smul _ (f := fun x ↦ (expBudget (ρ₂ x))⁻¹)
      (measurable_expBudget.comp hρ₂).inv]
    exact renyiDivergence_smul_inv_expBudget hα.out hc.ne h

end GradedLifting.BindLaw
