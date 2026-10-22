module

public import Mathlib.Probability.Kernel.Composition.WithDensity
public import Metrology.Couplings.Divergences.RenyiStrassen

/-! # Adaptive Rényi composition

Rényi liftings compose when the second budget `ρ₂ x` depends on the first outcome; paying the
plain average budget is unsound (Rocq `renyi_escort_adaptive.v`, `renyi_expcomp_unsound.v`). -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory GradedLifting
open scoped ENNReal
open ENNReal

namespace GradedDivergence

variable {X Y X' Y' : Type u} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X']
  [MeasurableSpace Y'] {α : ℝ} {ρ : ℝ≥0∞} {μ : Measure X} {ν : Measure Y}

/-! ## Reweighting by `e^{-ε}` (support for the escort rule) -/

/-- Reweighting by `e^{-ε}` keeps a measure sub-probability. -/
instance isSubProbabilityMeasure_withDensity_inv_expBudget (μ : Measure X)
    [IsSubProbabilityMeasure μ] (ε : X → ℝ≥0∞) :
    IsSubProbabilityMeasure (μ.withDensity fun x ↦ (expBudget (ε x))⁻¹) :=
  isSubProbabilityMeasure_withDensity_of_le_one μ fun _ ↦ ENNReal.inv_le_one.2 (one_le_expBudget _)

open Real in
/-- Scaling the right measure by `e^{-c}` raises the Rényi divergence by at most `c`. -/
theorem renyiDivergence_smul_inv_expBudget (hα : 1 < α) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : renyiDivergence α ρ μ ν) :
    renyiDivergence α (ρ + c) μ ((expBudget c)⁻¹ • ν) := by
  rcases eq_or_ne ρ ⊤ with rfl | hρ
  · simpa using renyiDivergence_top hα μ ((expBudget c)⁻¹ • ν)
  have : IsFiniteMeasure ((expBudget c)⁻¹ • ν) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact mul_lt_top (inv_lt_top.2 (zero_lt_one.trans_le (one_le_expBudget c)))
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
    rw [expBudget_of_ne_top hc, ← ofReal_inv_of_pos (exp_pos _),
      toReal_ofReal (by positivity), exp_neg]
  -- every cell is finite (the sum is bounded by `h`), so we can work in ℝ
  have hfin (i : Fin n) :
      ((persp (· ^ α) (p i) (q i)).toReal : EReal) = persp (· ^ α) (p i) (q i) :=
    have hnn (j : Fin n) : 0 ≤ persp (· ^ α) (p j) (q j) :=
      persp_rpow_nonneg toReal_nonneg toReal_nonneg
    EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _)
      ((Finset.single_le_sum (fun j _ ↦ hnn j) (Finset.mem_univ i)).trans hsum))
      (ne_bot_of_le_ne_bot EReal.zero_ne_bot (hnn i))
  -- each cell costs `e^{(α - 1) c}` times more
  have hcell (i : Fin n) : persp (· ^ α) (p i) (((expBudget c)⁻¹ • ν) (k ⁻¹' {i})).toReal =
      ((exp ((α - 1) * c.toReal) * (persp (· ^ α) (p i) (q i)).toReal : ℝ) : EReal) := by
    rw [Measure.smul_apply, smul_eq_mul, toReal_mul, hs, ← one_mul (p i),
      persp_rpow_mul hα zero_le_one (exp_pos _).le toReal_nonneg toReal_nonneg,
      persp_rpow_of_pos α (exp_pos _), one_mul, ← hfin i, ← EReal.coe_mul, EReal.coe_eq_coe_iff,
      one_div, ← exp_neg, neg_neg, ← exp_mul, ← exp_add, EReal.toReal_coe]
    ring_nf
  have hreal : ∑ i, (persp (· ^ α) (p i) (q i)).toReal ≤ exp ((α - 1) * ρ.toReal) := by
    rw [← EReal.coe_le_coe_iff, EReal.coe_finset_sum]
    simpa only [hfin] using hsum
  rw [Finset.sum_congr rfl fun i _ ↦ hcell i]
  rw [← EReal.coe_finset_sum, EReal.coe_le_coe_iff, ← Finset.mul_sum,
    toReal_add hρ hc, mul_add, exp_add, mul_comm (exp ((α - 1) * ρ.toReal))]
  gcongr

/-! ## The escort rule -/

/-- Adaptive Rényi composition: if `μ` is within budget `ρ` of the `e^{-ρ₂}`-weighted reduct of an
`S`-supported kernel `r`, the composite lifts at `ρ` (Rocq `escort_adaptive`). -/
theorem codensity_renyi_bind_escort [Fact (1 < α)] [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] {R : X' → Y' → ℝ≥0∞} {κ : Kernel X X'} {η : Kernel Y Y'}
    [IsSubMarkovKernel κ] [IsSubMarkovKernel η] {S : X → Y → Prop} {ρ₂ : X → ℝ≥0∞}
    (hρ₂ : Measurable ρ₂) (r : Kernel Y X) [IsSubMarkovKernel r] (hr : ∀ y, ∀ᵐ x ∂r y, S x y)
    (hκη : ∀ x y, S x y → (renyiDivergence α).codensity (ρ₂ x) R (κ x) (η y))
    (h : renyiDivergence α ρ μ ((r ∘ₘ ν).withDensity fun x ↦ (expBudget (ρ₂ x))⁻¹)) :
    (renyiDivergence α).codensity ρ R (κ ∘ₘ μ) (η ∘ₘ ν) := by
  classical
  -- With `ν₀ = r ∘ₘ ν`, `h` is the moment bound `∫ (dμ/dν₀)^α e^{(α - 1) ρ₂} dν₀ ≤ e^{(α - 1) ρ}`.
  -- It holds at `ρ₁ + (α - 1)⁻¹ log E_π[e^{(α - 1) ρ₂}]` for the `α`-escort `π ∝ (dμ/dν₀)^α ν₀`
  -- (Rocq `escort_moment_eq`); the same mean under `μ`, or the plain average, is unsound
  -- (`exists_not_codensity_renyi_bind_lintegral`).
  have hw : Measurable fun x ↦ (expBudget (ρ₂ x))⁻¹ := by fun_prop
  set w : X → ℝ≥0∞ := fun x ↦ (expBudget (ρ₂ x))⁻¹
  set r' := r.withDensity fun _ ↦ w
  have hr' (y : Y) : r' y = (r y).withDensity w := Kernel.withDensity_apply _ (by fun_prop) y
  have : IsSubMarkovKernel r' := ⟨fun y ↦ hr' y ▸ inferInstance⟩
  -- the leftover of the witness: `ρ₂ x` on `S`, `⊤` off it
  set E : X → Y → ℝ≥0∞ := fun x y ↦ if S x y then ρ₂ x else ⊤
  have hE : (renyiDivergence α).codensity ρ E μ ν := by
    refine codensity_renyi_of_witness r' (fun y ↦ ?_) (fun y ↦ ?_) ?_
    · rw [hr', ae_withDensity_iff hw]
      filter_upwards [hr y] with x hS hx
      simp only [E, hS, ↓reduceIte]
      exact expBudget_lt_top_iff.1 (lt_top_iff_ne_top.2 (by simpa [w] using hx))
    · rw [hr']
      -- the weight `e^{-ρ₂}` cancels `e^E = e^{ρ₂}` on `S`
      calc ∫⁻ x, expBudget (E x y) ∂(r y).withDensity w
          ≤ ∫⁻ x, w x * expBudget (E x y) ∂r y := lintegral_withDensity_le_lintegral_mul _ hw _
        _ ≤ ∫⁻ _, 1 ∂r y := lintegral_mono_ae <| (hr y).mono fun x hS ↦ by
            simp [E, hS, w]
        _ ≤ 1 := IsSubProbabilityMeasure.lintegral_le_one fun _ ↦ le_rfl
    · rwa [← withDensity_comp hw]
  refine HasBind.bind (L := codensity _) hE fun x y hxy ↦ ?_
  by_cases hS : S x y
  · simpa [E, hS] using hκη x y hS
  · simp [E, hS] at hxy

/-! ## Paying the average budget is unsound -/

/-- Paying the average of the per-outcome budgets is unsound (Rocq
`expcomp_expectation_rule_unsound`). -/
theorem exists_not_codensity_renyi_bind_lintegral :
    ∃ (μ : Measure Bool) (κ η : Kernel Bool (Fin 3)) (ρ₂ : Bool → ℝ≥0∞),
      IsProbabilityMeasure μ ∧ IsMarkovKernel κ ∧ IsMarkovKernel η ∧
      (∀ x, (codensity (renyiDivergence 2)).Rel (ρ₂ x) (· = ·) (κ x) (η x)) ∧
      ¬(codensity (renyiDivergence 2)).Rel (∫⁻ x, ρ₂ x ∂μ) (· = ·) (κ ∘ₘ μ) (η ∘ₘ μ) := by
  have hhalf {Z : Type} [MeasurableSpace Z] (a b : Z) :
      IsProbabilityMeasure ((2⁻¹ : ℝ≥0∞) • (dirac a + dirac b)) :=
    ⟨by simp [← two_mul, ENNReal.mul_inv_cancel two_ne_zero ofNat_ne_top]⟩
  set μ : Measure Bool := (2⁻¹ : ℝ≥0∞) • (dirac false + dirac true)
  set κ : Kernel Bool (Fin 3) := ⟨fun x ↦ cond x (dirac 1) (dirac 0), .of_discrete⟩
  set η : Kernel Bool (Fin 3) :=
    ⟨fun x ↦ cond x ((2⁻¹ : ℝ≥0∞) • (dirac 1 + dirac 2)) (dirac 0), .of_discrete⟩
  have : IsProbabilityMeasure μ := hhalf _ _
  have : IsMarkovKernel κ := ⟨by
    rintro (_ | _) <;> exact inferInstanceAs (IsProbabilityMeasure (dirac _))⟩
  have : IsMarkovKernel η := ⟨by
    rintro (_ | _)
    · exact inferInstanceAs (IsProbabilityMeasure (dirac _))
    · exact hhalf _ _⟩
  have hcomp (f : Kernel Bool (Fin 3)) (i : Fin 3) :
      (f ∘ₘ μ) {i} = 2⁻¹ * (f false {i} + f true {i}) := by
    rw [bind_apply (measurableSet_singleton i) f.aemeasurable]
    simp [μ, lintegral_smul_measure, lintegral_add_measure, mul_add]
  refine ⟨μ, κ, η, fun x ↦ cond x (ENNReal.ofReal (Real.log 2)) 0, inferInstance, inferInstance,
    inferInstance, fun x ↦ ?_, fun h ↦ ?_⟩
  · refine codensity_complete ?_
    cases x
    · exact IsReflexive.refl _
    -- the second moment of the `true` branch is `2 = e^{log 2}`
    change renyiDivergence 2 (ENNReal.ofReal (Real.log 2)) (κ true) (η true)
    rw [renyiDivergence_iff_of_ne_top one_le_two ofReal_ne_top,
      fDiv_eq_sum (convexOn_rpow one_le_two) (continuousWithinAt_rpow_zero two_pos)]
    simp [κ, η, Fin.sum_univ_three]
    rw [persp_of_ne_zero (by norm_num), persp_of_ne_zero (by norm_num), ← EReal.coe_add,
      toReal_ofReal (Real.log_nonneg one_le_two), EReal.coe_le_coe_iff]
    norm_num [Real.exp_log]
  -- the composite's second moment is `3 / 2`, above `e^{(log 2) / 2} = √2`
  have hbud : ∫⁻ x, cond x (ENNReal.ofReal (Real.log 2)) 0 ∂μ =
      ENNReal.ofReal (Real.log 2 / 2) := by
    simp [μ, lintegral_smul_measure, lintegral_add_measure, div_eq_inv_mul]
  have := codensity_sound h
  rw [hbud, renyiDivergence_iff_of_ne_top one_le_two ofReal_ne_top,
    fDiv_eq_sum (convexOn_rpow one_le_two) (continuousWithinAt_rpow_zero two_pos)] at this
  simp only [Fin.sum_univ_three, hcomp] at this
  simp [κ, η] at this
  rw [persp_of_ne_zero (by norm_num), persp_of_ne_zero (by norm_num),
    persp_of_ne_zero (by norm_num), ← EReal.coe_add, ← EReal.coe_add,
    toReal_ofReal (by positivity), EReal.coe_le_coe_iff] at this
  norm_num at this
  have hsq : Real.exp (Real.log 2 / 2) ^ 2 = 2 := by
    rw [sq, ← Real.exp_add, add_halves, Real.exp_log two_pos]
  nlinarith [Real.exp_pos (Real.log 2 / 2)]

end GradedDivergence
