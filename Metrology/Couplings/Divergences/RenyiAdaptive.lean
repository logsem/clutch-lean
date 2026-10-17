module

public import Mathlib.Probability.Kernel.Composition.WithDensity
public import Metrology.Couplings.Divergences.RenyiCodensity

/-! Adaptive Rényi composition at outcome-dependent budgets, paid through a witness kernel; paying
the average budget instead is unsound (Rocq `renyi_witness_adaptive.v`,
`renyi_escort_adaptive.v`, `renyi_expcomp_unsound.v`). -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory GradedLifting
open scoped ENNReal

namespace GradedDivergence

variable {X Y X' Y' : Type u} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X']
  [MeasurableSpace Y'] {α : ℝ} {ρ : ℝ≥0∞} {μ : Measure X} {ν : Measure Y}

/-! ## The multiplier `e^ε` -/

theorem measurable_expBudget : Measurable expBudget :=
  expBudget_mono.measurable

theorem expBudget_rpow {p : ℝ} (hp : 0 < p) (ε : ℝ≥0∞) :
    expBudget ε ^ p = expBudget (ENNReal.ofReal p * ε) := by
  rcases eq_or_ne ε ⊤ with rfl | hε
  · simp [ENNReal.mul_top (ENNReal.ofReal_pos.2 hp).ne', ENNReal.top_rpow_of_pos hp]
  rw [expBudget_of_ne_top hε, expBudget_of_ne_top (by finiteness),
    ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hp.le, ← Real.exp_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hp.le, mul_comm]

/-! ## Witness kernels -/

/-- A witness kernel gives the Rényi codensity lifting: if the rows of `r` pay for the leftover,
`∫ e^{R x y} d(r y) ≤ 1`, and the reduct `r ∘ₘ ν` is within budget `ρ` of `μ`, then `μ` and `ν`
lift `R` at `ρ` (Rocq `witness_adaptive` at `Cr = 1`). -/
theorem codensity_renyi_of_witness [hα : Fact (1 < α)] [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] {R : X → Y → ℝ≥0∞} (r : Kernel Y X) [IsSubMarkovKernel r]
    (hR : ∀ y, ∀ᵐ x ∂r y, R x y < ⊤) (hr : ∀ y, ∫⁻ x, expBudget (R x y) ∂r y ≤ 1)
    (h : renyiDivergence α ρ μ (r ∘ₘ ν)) : (renyiDivergence α).codensity ρ R μ ν := by
  rcases eq_or_ne ρ ⊤ with rfl | hρ
  · intro I _ c hc
    simp at hc
  refine codensity_renyi_of_slackHolder fun f g hf hg hfg ↦ ?_
  have hα0 : 0 < α := zero_lt_one.trans hα.out
  have hα1 : 0 < α - 1 := sub_pos.2 hα.out
  have hq : 0 < α / (α - 1) := div_pos hα0 hα1
  have hcq : ENNReal.ofReal (α / (α - 1)) * ENNReal.ofReal ((α - 1) / α) = 1 := by
    rw [← ENNReal.ofReal_mul hq.le, div_mul_div_cancel₀ hα1.ne', div_self hα0.ne',
      ENNReal.ofReal_one]
  -- each row of `r` carries at most the right test's moment
  have hrow (y : Y) : ∫⁻ x, f x ^ (α / (α - 1)) ∂r y ≤ g y ^ (α / (α - 1)) := by
    rcases eq_or_ne (g y) ⊤ with hg | hg
    · simp [hg, ENNReal.top_rpow_of_pos hq]
    calc ∫⁻ x, f x ^ (α / (α - 1)) ∂r y
        ≤ ∫⁻ x, g y ^ (α / (α - 1)) * expBudget (R x y) ∂r y := by
          refine lintegral_mono_ae ((hR y).mono fun x hx ↦ ?_)
          calc f x ^ (α / (α - 1))
              ≤ (expBudget (ENNReal.ofReal ((α - 1) / α) * R x y) * g y) ^ (α / (α - 1)) := by
                gcongr
                exact hfg x y hx
            _ = g y ^ (α / (α - 1)) * expBudget (R x y) := by
                rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, expBudget_rpow hq, ← mul_assoc, hcq,
                  one_mul, mul_comm]
      _ = g y ^ (α / (α - 1)) * ∫⁻ x, expBudget (R x y) ∂r y :=
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le hg)
      _ ≤ g y ^ (α / (α - 1)) := mul_le_of_le_one_right' (hr y)
  -- Hölder against the reduct, then average the rows
  have hcpl := (rdpCoupl_iff_codensity hρ).2
    (IsComplete.complete (L := codensity (renyiDivergence α)) h)
  calc ∫⁻ x, f x ∂μ
      ≤ expBudget (ENNReal.ofReal ((α - 1) / α) * ρ) *
          (∫⁻ x, f x ^ (α / (α - 1)) ∂(r ∘ₘ ν)) ^ ((α - 1) / α) :=
        hcpl hf hf fun _ _ hxy ↦ hxy ▸ le_rfl
    _ = expBudget (ENNReal.ofReal ((α - 1) / α) * ρ) *
          (∫⁻ y, ∫⁻ x, f x ^ (α / (α - 1)) ∂r y ∂ν) ^ ((α - 1) / α) := by
        rw [lintegral_bind r.aemeasurable (by fun_prop)]
    _ ≤ expBudget (ENNReal.ofReal ((α - 1) / α) * ρ) *
          (∫⁻ y, g y ^ (α / (α - 1)) ∂ν) ^ ((α - 1) / α) := by
        gcongr with y
        exact hrow y

/-! ## The escort rule -/

/-- Adaptive Rényi composition at budgets `ρ₂ x` that depend on the left outcome: weight the
reduct of an `S`-supported kernel `r` by `e^{-ρ₂}`; if `μ` is within budget `ρ` of the weighted
reduct, the composite lifts at `ρ` (Rocq `escort_adaptive`).

With `ν₀ = r ∘ₘ ν` the hypothesis is the moment bound
`∫ (dμ/dν₀)^α e^{(α - 1) ρ₂} dν₀ ≤ e^{(α - 1) ρ}`. If `D_α(μ ‖ ν₀) = ρ₁`, it holds at
`ρ = ρ₁ + (α - 1)⁻¹ log E_π[e^{(α - 1) ρ₂}]`, the exponential mean of `ρ₂` under the `α`-escort
`π ∝ (dμ/dν₀)^α ν₀` (Rocq `escort_moment_eq`). The same mean under `μ` is unsound (Rocq
`lq_adaptive_unsound`), and so is the plain average `ρ₁ + E_μ[ρ₂]`
(`exists_not_codensity_renyi_bind_lintegral`). -/
theorem codensity_renyi_bind_escort [Fact (1 < α)] [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] {R : X' → Y' → ℝ≥0∞} {κ : Kernel X X'} {η : Kernel Y Y'}
    [IsSubMarkovKernel κ] [IsSubMarkovKernel η] {S : X → Y → Prop} {ρ₂ : X → ℝ≥0∞}
    (hρ₂ : Measurable ρ₂) (r : Kernel Y X) [IsSubMarkovKernel r] (hr : ∀ y, ∀ᵐ x ∂r y, S x y)
    (hκη : ∀ x y, S x y → (renyiDivergence α).codensity (ρ₂ x) R (κ x) (η y))
    (h : renyiDivergence α ρ μ ((r ∘ₘ ν).withDensity fun x ↦ (expBudget (ρ₂ x))⁻¹)) :
    (renyiDivergence α).codensity ρ R (κ ∘ₘ μ) (η ∘ₘ ν) := by
  classical
  have hw : Measurable fun x ↦ (expBudget (ρ₂ x))⁻¹ := (measurable_expBudget.comp hρ₂).inv
  set w : X → ℝ≥0∞ := fun x ↦ (expBudget (ρ₂ x))⁻¹
  set r' := r.withDensity fun _ ↦ w
  have hr' (y : Y) : r' y = (r y).withDensity w := Kernel.withDensity_apply _ (by fun_prop) y
  have : IsSubMarkovKernel r' := ⟨fun y ↦ ⟨by
    rw [hr', withDensity_apply _ .univ, setLIntegral_univ]
    exact IsSubProbabilityMeasure.lintegral_le_one fun x ↦ ENNReal.inv_le_one.2
      (one_le_expBudget _)⟩⟩
  -- the leftover of the witness: `ρ₂ x` on `S`, `⊤` off it
  set E : X → Y → ℝ≥0∞ := fun x y ↦ if S x y then ρ₂ x else ⊤
  have hE : (renyiDivergence α).codensity ρ E μ ν := by
    refine codensity_renyi_of_witness r' (fun y ↦ ?_) (fun y ↦ ?_) ?_
    · rw [hr', ae_withDensity_iff hw]
      filter_upwards [hr y] with x hS hx
      simp only [E, hS, ↓reduceIte]
      exact expBudget_lt_top_iff.1 (lt_top_iff_ne_top.2 (by simpa [w] using hx))
    · rw [hr']
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

/-- Paying the average of the per-outcome budgets is unsound: at `α = 2`, with `μ` a fair coin on
both sides (so the head costs `0`), the branches lift equality at budgets `0` and `log 2`, but the
composite does not lift it at their average `(log 2) / 2`. Its second moment is `3 / 2 > √2`
(Rocq `expcomp_expectation_rule_unsound`). -/
theorem exists_not_codensity_renyi_bind_lintegral :
    ∃ (μ : Measure Bool) (κ η : Kernel Bool (Fin 3)) (ρ₂ : Bool → ℝ≥0∞),
      IsProbabilityMeasure μ ∧ IsMarkovKernel κ ∧ IsMarkovKernel η ∧
      (∀ x, (codensity (renyiDivergence 2)).Rel (ρ₂ x) (· = ·) (κ x) (η x)) ∧
      ¬(codensity (renyiDivergence 2)).Rel (∫⁻ x, ρ₂ x ∂μ) (· = ·) (κ ∘ₘ μ) (η ∘ₘ μ) := by
  have : Fact (1 < (2 : ℝ)) := ⟨one_lt_two⟩
  have hhalf {Z : Type} [MeasurableSpace Z] (a b : Z) :
      IsProbabilityMeasure ((2⁻¹ : ℝ≥0∞) • (dirac a + dirac b)) :=
    ⟨by simp [← two_mul, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩
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
  · refine IsComplete.complete (L := codensity (renyiDivergence 2)) (D := renyiDivergence 2) ?_
    cases x
    · exact IsReflexive.refl _
    -- the second moment of the `true` branch is `2 = e^{log 2}`
    change renyiDivergence 2 (ENNReal.ofReal (Real.log 2)) (κ true) (η true)
    rw [renyiDivergence_iff_of_ne_top one_le_two ENNReal.ofReal_ne_top,
      fDiv_eq_sum (convexOn_rpow one_le_two) (continuousWithinAt_rpow_zero two_pos)]
    simp [κ, η, Fin.sum_univ_three]
    rw [persp_of_ne_zero (by norm_num), persp_of_ne_zero (by norm_num), ← EReal.coe_add,
      ENNReal.toReal_ofReal (Real.log_nonneg one_le_two), EReal.coe_le_coe_iff]
    norm_num [Real.exp_log]
  -- the composite's second moment is `3 / 2`, above `e^{(log 2) / 2} = √2`
  have hbud : ∫⁻ x, cond x (ENNReal.ofReal (Real.log 2)) 0 ∂μ =
      ENNReal.ofReal (Real.log 2 / 2) := by
    simp [μ, lintegral_smul_measure, lintegral_add_measure, div_eq_inv_mul]
  have := IsSound.sound (L := codensity (renyiDivergence 2)) (D := renyiDivergence 2) h
  rw [hbud, renyiDivergence_iff_of_ne_top one_le_two ENNReal.ofReal_ne_top,
    fDiv_eq_sum (convexOn_rpow one_le_two) (continuousWithinAt_rpow_zero two_pos)] at this
  simp only [Fin.sum_univ_three, hcomp] at this
  simp [κ, η] at this
  rw [persp_of_ne_zero (by norm_num), persp_of_ne_zero (by norm_num),
    persp_of_ne_zero (by norm_num), ← EReal.coe_add, ← EReal.coe_add,
    ENNReal.toReal_ofReal (by positivity), EReal.coe_le_coe_iff] at this
  norm_num at this
  have hsq : Real.exp (Real.log 2 / 2) ^ 2 = 2 := by
    rw [sq, ← Real.exp_add, add_halves, Real.exp_log two_pos]
  nlinarith [Real.exp_pos (Real.log 2 / 2)]

end GradedDivergence
