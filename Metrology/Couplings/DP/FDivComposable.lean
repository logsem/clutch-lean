module

public import Metrology.Couplings.DP.FDivergence

/-! A sufficient condition for composability of `f`-divergences (Sato–Katsumata, Prop. 1). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set GradedDivergence
open scoped ENNReal

universe u

theorem EReal.toENNReal_sum {ι : Type*} (s : Finset ι) {x : ι → EReal} (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s, x i).toENNReal = ∑ i ∈ s, (x i).toENNReal := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, EReal.toENNReal_add (hx j (by simp))
      (Finset.sum_nonneg fun i hi ↦ hx i (by simp [hi])), ih fun i hi ↦ hx i (by simp [hi])]

/-- Every set has real mass in `[0, 1]` under a subprobability measure. -/
theorem MeasureTheory.IsSubProbabilityMeasure.toReal_mem_Icc {X : Type*} [MeasurableSpace X]
    (ρ : Measure X) [IsSubProbabilityMeasure ρ] (s : Set X) : (ρ s).toReal ∈ Icc (0 : ℝ) 1 :=
  ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one
    (ENNReal.ofReal_one ▸ IsSubProbabilityMeasure.measure_le_one s)⟩

namespace WeightFunction

variable {f : WeightFunction}

theorem slopeAtTop_nonneg (hf : ∀ t, 0 ≤ t → 0 ≤ f t) : 0 ≤ f.slopeAtTop :=
  Filter.le_limsup_of_frequently_le (Filter.Eventually.frequently <|
    (Filter.eventually_ge_atTop 0).mono fun t ht ↦ EReal.coe_nonneg.2 (div_nonneg (hf t ht) ht))

theorem persp_nonneg (hf : ∀ t, 0 ≤ t → 0 ≤ f t) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ f.persp a b := by
  unfold persp
  split_ifs
  · exact le_rfl
  · exact EReal.mul_nonneg (EReal.coe_nonneg.2 ha) (slopeAtTop_nonneg hf)
  · exact EReal.coe_nonneg.2 (mul_nonneg hb (hf _ (div_nonneg ha hb)))

end WeightFunction

/-- The perspective of `f` at a product splits into the perspectives of `f₁` and `f₂`, weighted
by convex combinations with coefficients `β, β'` (condition (A') of Sato–Katsumata, Prop. 1). -/
def WeightFunction.PerspSplit (f f₁ f₂ : WeightFunction) (β β' : ℝ) : Prop :=
  ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (0 : ℝ) 1,
    f.persp (z * w) (x * y) ≤ ((β * w + (1 - β) * y : ℝ) : EReal) * f₁.persp z x +
      ((β' * z + (1 - β') * x : ℝ) : EReal) * f₂.persp w y

namespace WeightFunction

variable {f f₁ f₂ : WeightFunction} {β β' : ℝ}

open IsSubProbabilityMeasure in
/-- Under condition (A'), the `f`-divergence of two compositions on finite spaces is at most the
`f₁`-divergence of the inputs plus the largest `f₂`-divergence of the kernels (Sato–Katsumata,
Prop. 1). -/
theorem fDiv_comp_le (hf : ConvexOn ℝ (Ici 0) f) (hf₁ : ConvexOn ℝ (Ici 0) f₁)
    (hf₂ : ConvexOn ℝ (Ici 0) f₂) (hf₀ : ∀ t, 0 ≤ t → 0 ≤ f t) (hf₁₀ : ∀ t, 0 ≤ t → 0 ≤ f₁ t)
    (hf₂₀ : ∀ t, 0 ≤ t → 0 ≤ f₂ t) (hβ : β ∈ Icc (0 : ℝ) 1) (hβ' : β' ∈ Icc (0 : ℝ) 1)
    (hA : f.PerspSplit f₁ f₂ β β') {M N : ℕ} (μ₁ μ₂ : Measure (ULift.{u} (Fin M)))
    [IsSubProbabilityMeasure μ₁] [IsSubProbabilityMeasure μ₂]
    (κ η : Kernel (ULift.{u} (Fin M)) (ULift.{u} (Fin N))) [IsSubMarkovKernel κ]
    [IsSubMarkovKernel η] :
    (fDiv f (κ ∘ₘ μ₁) (η ∘ₘ μ₂)).toENNReal ≤
      (fDiv f₁ μ₁ μ₂).toENNReal + ⨆ j, (fDiv f₂ (κ j) (η j)).toENNReal := by
  have hb (μ : Measure (ULift.{u} (Fin M))) [IsSubProbabilityMeasure μ]
      (κ : Kernel (ULift.{u} (Fin M)) (ULift.{u} (Fin N))) [IsSubMarkovKernel κ]
      (i : ULift.{u} (Fin N)) :
      ((κ ∘ₘ μ) {i}).toReal = ∑ j, (μ {j}).toReal * (κ j {i}).toReal := by
    rw [Measure.bind_apply (ULift.measurableSet_fin _) κ.measurable.aemeasurable,
      lintegral_fintype, ENNReal.toReal_sum fun _ _ ↦ by finiteness]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [ENNReal.toReal_mul, mul_comm]
  have hw {γ : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1) {a b : ℝ≥0∞} : 0 ≤ γ * a.toReal + (1 - γ) * b.toReal :=
    add_nonneg (mul_nonneg hγ.1 ENNReal.toReal_nonneg)
      (mul_nonneg (sub_nonneg.2 hγ.2) ENNReal.toReal_nonneg)
  -- the sum of the coefficients of a convex combination of two kernels is at most one
  have hc (γ : ℝ) (hγ : γ ∈ Icc (0 : ℝ) 1) {K : ℕ} (ρ ρ' : Measure (ULift.{u} (Fin K)))
      [IsSubProbabilityMeasure ρ] [IsSubProbabilityMeasure ρ'] :
      ∑ i, ENNReal.ofReal (γ * (ρ {i}).toReal + (1 - γ) * (ρ' {i}).toReal) ≤ 1 := by
    have hsum (ρ : Measure (ULift.{u} (Fin K))) [IsSubProbabilityMeasure ρ] :
        ∑ i, (ρ {i}).toReal ≤ 1 := by
      rw [← ENNReal.toReal_sum fun _ _ ↦ by finiteness, sum_measure_singleton]
      exact (toReal_mem_Icc ρ _).2
    rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ hw hγ, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ENNReal.ofReal_le_one]
    nlinarith [hsum ρ, hsum ρ', hγ.1, hγ.2]
  have hp {g : WeightFunction} (hg : ∀ t, 0 ≤ t → 0 ≤ g t) {a b : ℝ≥0∞} :
      0 ≤ g.persp a.toReal b.toReal :=
    persp_nonneg hg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  set S := ⨆ j, (fDiv f₂ (κ j) (η j)).toENNReal
  rw [fDiv_eq_sum hf, fDiv_eq_sum hf₁]
  simp_rw [hb]
  calc (∑ i, f.persp (∑ j, (μ₁ {j}).toReal * (κ j {i}).toReal)
        (∑ j, (μ₂ {j}).toReal * (η j {i}).toReal)).toENNReal
      ≤ (∑ i, ∑ j, f.persp ((μ₁ {j}).toReal * (κ j {i}).toReal)
          ((μ₂ {j}).toReal * (η j {i}).toReal)).toENNReal :=
        EReal.toENNReal_le_toENNReal <| Finset.sum_le_sum fun i _ ↦ persp_sum_le hf _
          (fun _ _ ↦ by positivity) fun _ _ ↦ by positivity
    _ = ∑ i, ∑ j, (f.persp ((μ₁ {j}).toReal * (κ j {i}).toReal)
          ((μ₂ {j}).toReal * (η j {i}).toReal)).toENNReal := by
        rw [EReal.toENNReal_sum _ fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
          persp_nonneg hf₀ (by positivity) (by positivity)]
        exact Finset.sum_congr rfl fun i _ ↦
          EReal.toENNReal_sum _ fun _ _ ↦ persp_nonneg hf₀ (by positivity) (by positivity)
    _ ≤ ∑ i, ∑ j, (ENNReal.ofReal (β * (κ j {i}).toReal + (1 - β) * (η j {i}).toReal) *
            (f₁.persp (μ₁ {j}).toReal (μ₂ {j}).toReal).toENNReal +
          ENNReal.ofReal (β' * (μ₁ {j}).toReal + (1 - β') * (μ₂ {j}).toReal) *
            (f₂.persp (κ j {i}).toReal (η j {i}).toReal).toENNReal) := by
        refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
        refine (EReal.toENNReal_le_toENNReal (hA _ (toReal_mem_Icc μ₂ _) _
          (toReal_mem_Icc (η j) _) _ (toReal_mem_Icc μ₁ _) _ (toReal_mem_Icc (κ j) _))).trans_eq ?_
        rw [EReal.toENNReal_add
          (EReal.mul_nonneg (EReal.coe_nonneg.2 (hw hβ)) (hp hf₁₀))
          (EReal.mul_nonneg (EReal.coe_nonneg.2 (hw hβ')) (hp hf₂₀)),
          EReal.toENNReal_mul (EReal.coe_nonneg.2 (hw hβ)),
          EReal.toENNReal_mul (EReal.coe_nonneg.2 (hw hβ')),
          EReal.real_coe_toENNReal, EReal.real_coe_toENNReal]
    _ = ∑ j, ((∑ i, ENNReal.ofReal (β * (κ j {i}).toReal + (1 - β) * (η j {i}).toReal)) *
            (f₁.persp (μ₁ {j}).toReal (μ₂ {j}).toReal).toENNReal +
          ENNReal.ofReal (β' * (μ₁ {j}).toReal + (1 - β') * (μ₂ {j}).toReal) *
            ∑ i, (f₂.persp (κ j {i}).toReal (η j {i}).toReal).toENNReal) := by
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    _ ≤ ∑ j, ((f₁.persp (μ₁ {j}).toReal (μ₂ {j}).toReal).toENNReal +
          ENNReal.ofReal (β' * (μ₁ {j}).toReal + (1 - β') * (μ₂ {j}).toReal) * S) := by
        gcongr with j
        · exact mul_le_of_le_one_left zero_le (hc β hβ (κ j) (η j))
        rw [← EReal.toENNReal_sum _ fun _ _ ↦ hp hf₂₀, ← fDiv_eq_sum hf₂]
        exact le_iSup (fun j ↦ (fDiv f₂ (κ j) (η j)).toENNReal) j
    _ ≤ (∑ j, f₁.persp (μ₁ {j}).toReal (μ₂ {j}).toReal).toENNReal + S := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, EReal.toENNReal_sum _ fun _ _ ↦ hp hf₁₀]
        exact add_le_add le_rfl (mul_le_of_le_one_left zero_le (hc β' hβ' μ₁ μ₂))

end WeightFunction

namespace fDivFamily

variable {ι : Type*} [Mul ι] (F : ι → WeightFunction) {β β' : ℝ}

/-- A family of nonnegative convex weights satisfying condition (A') composes between finite
spaces (Prop. 1 of Sato–Katsumata). -/
theorem isFiniteComposable_of_perspSplit (hF : ∀ a, ConvexOn ℝ (Ici 0) (F a))
    (hF₀ : ∀ a t, 0 ≤ t → 0 ≤ F a t) (hβ : β ∈ Icc (0 : ℝ) 1) (hβ' : β' ∈ Icc (0 : ℝ) 1)
    (hA : ∀ a b, (F (a * b)).PerspSplit (F a) (F b) β β') :
    (fDivFamily F : GradedDivergence.{u} ι).IsFiniteComposable where
  bind_le a b _ _ μ₁ μ₂ _ _ κ η _ _ := WeightFunction.fDiv_comp_le (hF _) (hF a) (hF b)
    (hF₀ _) (hF₀ a) (hF₀ b) hβ hβ' (hA a b) μ₁ μ₂ κ η

/-- A family of nonnegative convex weights satisfying condition (A') composes (Prop. 1 of
Sato–Katsumata). -/
theorem isComposable_of_perspSplit (hF : ∀ a, ConvexOn ℝ (Ici 0) (F a))
    (hF₀ : ∀ a t, 0 ≤ t → 0 ≤ F a t) (hβ : β ∈ Icc (0 : ℝ) 1) (hβ' : β' ∈ Icc (0 : ℝ) 1)
    (hA : ∀ a b, (F (a * b)).PerspSplit (F a) (F b) β β') :
    (fDivFamily F : GradedDivergence.{u} ι).IsComposable :=
  have := isFiniteComposable_of_perspSplit F hF hF₀ hβ hβ' hA
  isComposable_of_isFiniteComposable F hF

end fDivFamily
