module

public import Metrology.Couplings.Divergences.Dp
public import Metrology.Couplings.Divergences.Tv

/-! The DP bind shapes beyond uniform composition, as DP codensity liftings (Rocq
`instances_dp.v`). -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory GradedLifting Set
open scoped ENNReal

namespace GradedDivergence

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  {ε ε₁ ε₂ δ δ₁ δ₂ : ℝ≥0∞} {S : X → Y → Prop}

open Classical in
/-- Adaptive composition keyed on the right outcome: after a DP lifting of `S`, the budgets
`(ε₂, D y)` on `S` cost `(ε₁ + ε₂, δ₁ + e^{ε₁} E_ν[D])` (Rocq `dp_rhs_head`). -/
theorem codensity_dp_rhs [IsSubProbabilityMeasure μ] (h : (codensity dp).Rel (ε₁, δ₁) S μ ν)
    {D : Y → ℝ≥0∞} (hD : Measurable D) :
    dp.codensity (ε₁ + ε₂, δ₁ + expBudget ε₁ * ∫⁻ y, D y ∂ν)
      (fun x y ↦ if S x y then (ε₂, D y) else ⊤) μ ν := by
  rcases eq_or_ne (ε₁ + ε₂) ⊤ with hε | hε
  · exact hε ▸ codensity_dp_top_left
  obtain ⟨hε₁, hε₂⟩ := ENNReal.add_ne_top.1 hε
  refine codensity_dp_of_lintegral_le fun f g hf hg hf1 _ hfg ↦ ?_
  calc ∫⁻ x, f x ∂μ
      ≤ expBudget ε₁ * ∫⁻ y, min 1 (expBudget ε₂ * g y + D y) ∂ν + δ₁ :=
        (codensity_dp_rel_iff hε₁).1 h _ _ hf (by fun_prop) hf1 (fun _ ↦ min_le_left _ _)
          fun x y hS ↦ le_min (hf1 x) (by simpa [hS, hε₂.lt_top] using hfg x y)
    _ ≤ expBudget ε₁ * (expBudget ε₂ * ∫⁻ y, g y ∂ν + ∫⁻ y, D y ∂ν) + δ₁ := by
        rw [← lintegral_const_mul _ hg, ← lintegral_add_left (hg.const_mul _)]
        gcongr
        exact min_le_right _ _
    _ = expBudget (ε₁ + ε₂) * ∫⁻ y, g y ∂ν + (δ₁ + expBudget ε₁ * ∫⁻ y, D y ∂ν) := by
        rw [expBudget_add]
        ring

open Classical in
/-- Adaptive composition keyed on the right outcome after a total variation lifting: no
multiplier is spent on the head (Rocq `dp_rhs_head_of_AR`). -/
theorem codensity_dp_rhs_of_tv [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    (h : (codensity tv).Rel δ₁ S μ ν) {D : Y → ℝ≥0∞} (hD : Measurable D) :
    dp.codensity (ε₂, δ₁ + ∫⁻ y, D y ∂ν) (fun x y ↦ if S x y then (ε₂, D y) else ⊤) μ ν := by
  simpa using codensity_dp_rhs (ε₂ := ε₂) (codensity_tv_rel_iff_dp.1 h) hD

open Classical in
/-- Adaptive composition keyed on the left outcome: after a DP lifting of `S`, the budgets
`(ε₂, D x)` on `S` cost `(ε₁ + ε₂, δ₁ + E_μ[D])` (Rocq `dp_lhs_head`). -/
theorem codensity_dp_lhs [IsSubProbabilityMeasure μ] (h : (codensity dp).Rel (ε₁, δ₁) S μ ν)
    {D : X → ℝ≥0∞} (hD : Measurable D) :
    dp.codensity (ε₁ + ε₂, δ₁ + ∫⁻ x, D x ∂μ) (fun x y ↦ if S x y then (ε₂, D x) else ⊤) μ ν := by
  rcases eq_or_ne (ε₁ + ε₂) ⊤ with hε | hε
  · exact hε ▸ codensity_dp_top_left
  obtain ⟨hε₁, hε₂⟩ := ENNReal.add_ne_top.1 hε
  refine codensity_dp_of_lintegral_le fun f g hf hg hf1 _ hfg ↦ ?_
  have hf1' (x : X) : f x - D x ≤ 1 := tsub_le_self.trans (hf1 x)
  calc ∫⁻ x, f x ∂μ
      ≤ ∫⁻ x, (f x - D x) + D x ∂μ := lintegral_mono fun _ ↦ le_tsub_add
    _ = ∫⁻ x, f x - D x ∂μ + ∫⁻ x, D x ∂μ := lintegral_add_right _ hD
    _ ≤ expBudget ε₁ * ∫⁻ y, min 1 (expBudget ε₂ * g y) ∂ν + δ₁ + ∫⁻ x, D x ∂μ := by
        gcongr
        refine (codensity_dp_rel_iff hε₁).1 h _ _ (hf.sub hD) (by fun_prop) hf1'
          (fun _ ↦ min_le_left _ _) fun x y hS ↦ le_min (hf1' x) (tsub_le_iff_right.2 ?_)
        simpa [hS, hε₂.lt_top] using hfg x y
    _ ≤ expBudget ε₁ * (expBudget ε₂ * ∫⁻ y, g y ∂ν) + δ₁ + ∫⁻ x, D x ∂μ := by
        rw [← lintegral_const_mul _ hg]
        gcongr
        exact min_le_right _ _
    _ = expBudget (ε₁ + ε₂) * ∫⁻ y, g y ∂ν + (δ₁ + ∫⁻ x, D x ∂μ) := by
        rw [expBudget_add]
        ring

open Classical in
/-- Per-pair budgets `E` on `S` with no head lifting: a transfer of `[0, 1]`-valued tests gives the
DP codensity lifting (Rocq `dp_kanto_head`). -/
theorem codensity_dp_of_kanto [IsSubProbabilityMeasure μ] {E : X → Y → ℝ≥0∞ × ℝ≥0∞}
    (h : ∀ f g, Measurable f → Measurable g → (∀ x, f x ≤ 1) → (∀ y, g y ≤ 1) →
      (∀ x y, S x y → (E x y).1 < ⊤ → f x ≤ expBudget (E x y).1 * g y + (E x y).2) →
      ∫⁻ x, f x ∂μ ≤ expBudget ε * ∫⁻ y, g y ∂ν + δ) :
    dp.codensity (ε, δ) (fun x y ↦ if S x y then E x y else ⊤) μ ν :=
  codensity_dp_of_lintegral_le fun f g hf hg hf1 hg1 hfg ↦
    h f g hf hg hf1 hg1 fun x y hS ↦ by simpa [hS] using hfg x y

/-- One branch of the choice rule: on `P`, a DP lifting of `S` that sends `P` into `T` moves the
continuation's slack `δ₂` out of the test. -/
theorem setLIntegral_le_of_codensity_dp [IsSubProbabilityMeasure μ] (hε₁ : ε₁ ≠ ⊤)
    (h : (codensity dp).Rel (ε₁, δ₁) S μ ν) {P : Set X} {T : Set Y} (hP : MeasurableSet P)
    (hT : MeasurableSet T) (hPT : ∀ x y, x ∈ P → S x y → y ∈ T) {f : X → ℝ≥0∞} {g : Y → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hf1 : ∀ x, f x ≤ 1)
    (hfg : ∀ x y, x ∈ P → S x y → f x ≤ expBudget ε₂ * g y + δ₂) :
    ∫⁻ x in P, f x - δ₂ ∂μ ≤ expBudget (ε₁ + ε₂) * ∫⁻ y in T, g y ∂ν + δ₁ := by
  have hf1' (x : X) : P.indicator (fun x ↦ f x - δ₂) x ≤ 1 :=
    (indicator_le_self' (fun _ _ ↦ zero_le) x).trans (tsub_le_self.trans (hf1 x))
  calc ∫⁻ x in P, f x - δ₂ ∂μ
      = ∫⁻ x, P.indicator (fun x ↦ f x - δ₂) x ∂μ := (lintegral_indicator hP _).symm
    _ ≤ expBudget ε₁ * ∫⁻ y, min 1 (expBudget ε₂ * T.indicator g y) ∂ν + δ₁ := by
        refine (codensity_dp_rel_iff hε₁).1 h _ _ ((hf.sub_const δ₂).indicator hP)
          (by fun_prop (disch := exact hT)) hf1' (fun _ ↦ min_le_left _ _) fun x y hS ↦ ?_
        by_cases hx : x ∈ P
        · rw [indicator_of_mem hx, indicator_of_mem (hPT x y hx hS)]
          exact le_min (tsub_le_self.trans (hf1 x)) (tsub_le_iff_right.2 (hfg x y hx hS))
        · simp [hx]
    _ ≤ expBudget ε₁ * (expBudget ε₂ * ∫⁻ y in T, g y ∂ν) + δ₁ := by
        rw [← lintegral_indicator hT, ← lintegral_const_mul _ (hg.indicator hT)]
        gcongr
        exact min_le_right _ _
    _ = expBudget (ε₁ + ε₂) * ∫⁻ y in T, g y ∂ν + δ₁ := by
        rw [expBudget_add, mul_assoc]

open Classical in
/-- The choice rule: two DP liftings of the same pair, chosen by a measurable left predicate `P`
whose two sides the relations send to the two sides of a measurable `T` (Rocq
`dp_kanto_head_choice`). -/
theorem codensity_dp_choice [IsSubProbabilityMeasure μ] {S₁ S₂ : X → Y → Prop}
    {ε₁' ε₂' δ₁' : ℝ≥0∞} (h₁ : (codensity dp).Rel (ε₁, δ₁) S₁ μ ν)
    (h₂ : (codensity dp).Rel (ε₁', δ₁') S₂ μ ν) {P : Set X} {T : Set Y} (hP : MeasurableSet P)
    (hT : MeasurableSet T) (hPT₁ : ∀ x y, x ∈ P → S₁ x y → y ∈ T)
    (hPT₂ : ∀ x y, x ∉ P → S₂ x y → y ∉ T) :
    dp.codensity (max (ε₁ + ε₂) (ε₁' + ε₂'), δ₁ + δ₁' + δ₂)
      (fun x y ↦ if x ∈ P then (if S₁ x y then (ε₂, δ₂) else ⊤)
        else if S₂ x y then (ε₂', δ₂) else ⊤) μ ν := by
  set ε := max (ε₁ + ε₂) (ε₁' + ε₂')
  rcases eq_or_ne ε ⊤ with hε | hε
  · exact hε ▸ codensity_dp_top_left
  obtain ⟨hε₁, hε₂⟩ := ENNReal.add_ne_top.1 (ne_top_of_le_ne_top hε (le_max_left _ _))
  obtain ⟨hε₁', hε₂'⟩ := ENNReal.add_ne_top.1 (ne_top_of_le_ne_top hε (le_max_right _ _))
  refine codensity_dp_of_lintegral_le fun f g hf hg hf1 _ hfg ↦ ?_
  have hb₁ := setLIntegral_le_of_codensity_dp (ε₂ := ε₂) (δ₂ := δ₂) hε₁ h₁ hP hT hPT₁ hf hg hf1
    fun x y hx hS ↦ by simpa [hx, hS, hε₂.lt_top] using hfg x y
  have hb₂ := setLIntegral_le_of_codensity_dp (ε₂ := ε₂') (δ₂ := δ₂) hε₁' h₂ hP.compl hT.compl
    hPT₂ hf hg hf1 fun x y hx hS ↦ by simpa [show x ∉ P from hx, hS, hε₂'.lt_top] using hfg x y
  calc ∫⁻ x, f x ∂μ
      ≤ ∫⁻ x, f x - δ₂ ∂μ + δ₂ := IsSubProbabilityMeasure.lintegral_le_tsub_add _ _
    _ = ∫⁻ x in P, f x - δ₂ ∂μ + ∫⁻ x in Pᶜ, f x - δ₂ ∂μ + δ₂ := by
        rw [lintegral_add_compl _ hP]
    _ ≤ (expBudget ε * ∫⁻ y in T, g y ∂ν + δ₁) + (expBudget ε * ∫⁻ y in Tᶜ, g y ∂ν + δ₁') +
          δ₂ := by
        gcongr
        · exact hb₁.trans (by gcongr; exact le_max_left _ _)
        · exact hb₂.trans (by gcongr; exact le_max_right _ _)
    _ = expBudget ε * ∫⁻ y, g y ∂ν + (δ₁ + δ₁' + δ₂) := by
        rw [← lintegral_add_compl (μ := ν) g hT]
        ring

open Classical in
/-- The choice rule on a countable right space: no right outcome may be related to both sides of
`P` (Rocq `dp_kanto_head_choice`). -/
theorem codensity_dp_choice_of_countable [Countable Y] [MeasurableSingletonClass Y]
    [IsSubProbabilityMeasure μ] {S₁ S₂ : X → Y → Prop} {ε₁' ε₂' δ₁' : ℝ≥0∞}
    (h₁ : (codensity dp).Rel (ε₁, δ₁) S₁ μ ν) (h₂ : (codensity dp).Rel (ε₁', δ₁') S₂ μ ν)
    {P : Set X} (hP : MeasurableSet P)
    (hS : ∀ x x' y, x ∈ P → x' ∉ P → ¬(S₁ x y ∧ S₂ x' y)) :
    dp.codensity (max (ε₁ + ε₂) (ε₁' + ε₂'), δ₁ + δ₁' + δ₂)
      (fun x y ↦ if x ∈ P then (if S₁ x y then (ε₂, δ₂) else ⊤)
        else if S₂ x y then (ε₂', δ₂) else ⊤) μ ν :=
  codensity_dp_choice (T := {y | ∃ x ∈ P, S₁ x y}) h₁ h₂ hP (to_countable _).measurableSet
    (fun x _ hx hS ↦ ⟨x, hx, hS⟩) fun x' y hx' hS₂ ⟨x, hx, hS₁⟩ ↦ hS x x' y hx hx' ⟨hS₁, hS₂⟩

end GradedDivergence
