module

public import Metrology.Couplings.Divergences.Dp

/-! One-sided total variation as a graded divergence: DP at multiplier `1`. -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory GradedLifting
open scoped ENNReal

namespace GradedDivergence

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {δ : ℝ≥0∞}

/-- One-sided total variation within `δ`: every event gains at most `δ` from `ν` to `μ`. -/
noncomputable def tv : GradedDivergence.{u} ℝ≥0∞ :=
  fun δ ↦ dp (0, δ)

theorem tv_iff {μ ν : Measure X} : tv δ μ ν ↔ ∀ S, MeasurableSet S → μ S ≤ ν S + δ := by
  simp [tv, dp_iff]

/-- Point masses within total variation `δ` differ in mass by at most `δ`. -/
theorem tv_smul_dirac_iff {a a' : ℝ≥0∞} :
    tv δ (a • dirac PUnit.unit.{u + 1}) (a' • dirac PUnit.unit) ↔ a ≤ a' + δ := by
  simp [tv, dp_smul_dirac_iff]

/-! ## Instances -/

instance isGraded_tv : tv.{u}.IsGraded where
  mono _ _ hb := IsGraded.mono (D := dp) (Prod.mk_le_mk.2 ⟨le_rfl, hb⟩)
  top _ _ := tv_iff.2 fun _ _ ↦ by simp

instance isReflexive_tv : tv.{u}.IsReflexive where
  refl μ _ := IsReflexive.refl (D := dp) μ

instance isComposable_tv : tv.{u}.IsComposable where
  comp _ _ := fun h hκη ↦ by simpa [tv] using IsComposable.comp (D := dp) h hκη

instance isZeroLeft_tv : tv.{u}.IsZeroLeft where
  zero_left δ := IsZeroLeft.zero_left (D := dp) (0, δ)

instance isLeftContinuous_tv : tv.{u}.IsLeftContinuous where
  iSup_left δ := IsLeftContinuous.iSup_left (D := dp) (b := (0, δ))

instance isRightMonotone_tv : tv.{u}.IsRightMonotone where
  right_mono δ := IsRightMonotone.right_mono (D := dp) (b := (0, δ))

instance isLeftAntitone_tv : tv.{u}.IsLeftAntitone where
  left_anti δ := IsLeftAntitone.left_anti (D := dp) (b := (0, δ))

instance isBudgetClosed_tv : tv.{u}.IsBudgetClosed where
  of_forall_gt {δ} _ _ _ _ _ _ h :=
    tv_iff.2 fun S hS ↦ by
      simpa using Bound.of_forall_lt (c := 1) (fun δ' hδ' S hS ↦ by
        simpa using tv_iff.1 (h δ' hδ') S hS) S hS

instance hasSlack_tv : tv.{u}.HasSlack (OrderAddMonoidHom.id ℝ≥0∞) where
  of_forall_le h := tv_iff.2 h

instance isMassDetecting_tv : tv.{u}.IsMassDetecting (OrderAddMonoidHom.id ℝ≥0∞) where
  le_add_of _ _ := tv_smul_dirac_iff.1

/-! ## The total variation codensity lifting -/

variable {μ : Measure X} {ν : Measure Y} {E : X → Y → ℝ≥0∞} {S : X → Y → Prop}

/-- Reading a total variation codensity lifting on `[0, 1]`-valued test functions through mass
kernels. -/
theorem lintegral_le_of_codensity_tv (h : tv.codensity δ E μ ν) {f : X → ℝ≥0∞} {g : Y → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ y, g y ≤ 1)
    (hfg : ∀ x y, f x ≤ g y + E x y) : ∫⁻ x, f x ∂μ ≤ ∫⁻ y, g y ∂ν + δ := by
  rcases eq_or_ne δ ⊤ with rfl | hδ
  · simp
  have := Kernel.isSubMarkovKernel_mass.{u} hf hf1
  have := Kernel.isSubMarkovKernel_mass.{u} hg hg1
  have hc := h (c := 0) (k := Kernel.mass.{u} hf) (l := Kernel.mass.{u} hg)
    (by simpa using hδ.lt_top) fun x y ↦ by
      simpa [Kernel.mass_apply, tv_smul_dirac_iff] using hfg x y
  simpa [Kernel.mass_comp, tv_smul_dirac_iff] using hc

/-- `[0, 1]`-valued test functions that the leftover relates give a total variation codensity
lifting: a test passed with slack `c` becomes a test function once `c` is cut off. -/
theorem codensity_tv_of_lintegral_le [IsSubProbabilityMeasure μ]
    (h : ∀ f g, Measurable f → Measurable g → (∀ x, f x ≤ 1) → (∀ y, g y ≤ 1) →
      (∀ x y, f x ≤ g y + E x y) → ∫⁻ x, f x ∂μ ≤ ∫⁻ y, g y ∂ν + δ) :
    tv.codensity δ E μ ν := by
  intro I _ c _ k l _ _ hkl
  refine tv_iff.2 fun S hS ↦ ?_
  have hkS := k.measurable_coe hS
  have hfg := h (fun x ↦ k x S - c) (fun y ↦ l y S) (hkS.sub measurable_const)
    (l.measurable_coe hS) (fun _ ↦ tsub_le_self.trans (IsSubProbabilityMeasure.measure_le_one S))
    (fun _ ↦ IsSubProbabilityMeasure.measure_le_one S)
    fun x y ↦ tsub_le_iff_right.2 <| (tv_iff.1 (hkl x y) S hS).trans_eq (by ring)
  rw [bind_apply hS k.measurable.aemeasurable, bind_apply hS l.measurable.aemeasurable]
  calc ∫⁻ x, k x S ∂μ
      ≤ ∫⁻ x, (k x S - c) + c ∂μ := lintegral_mono fun _ ↦ le_tsub_add
    _ ≤ ∫⁻ x, k x S - c ∂μ + c := IsSubProbabilityMeasure.lintegral_add_const_le _ _
    _ ≤ ∫⁻ y, l y S ∂ν + (δ + c) := by
        rw [← add_assoc]
        gcongr

/-- The total variation codensity lifting is decided by `[0, 1]`-valued test functions. -/
theorem codensity_tv_iff [IsSubProbabilityMeasure μ] :
    tv.codensity δ E μ ν ↔ ∀ f g, Measurable f → Measurable g → (∀ x, f x ≤ 1) →
      (∀ y, g y ≤ 1) → (∀ x y, f x ≤ g y + E x y) → ∫⁻ x, f x ∂μ ≤ ∫⁻ y, g y ∂ν + δ :=
  ⟨fun h _ _ ↦ lintegral_le_of_codensity_tv h, codensity_tv_of_lintegral_le⟩

/-- A leftover keyed on the right sample is paid in expectation; this uses linearity of the
tests, so it is specific to total variation. -/
instance isExpectationAdditive_codensity_tv :
    (codensity tv.{u}).IsExpectationAdditive (OrderAddMonoidHom.id ℝ≥0∞) where
  add_right {_ _} _ _ b R μ ν _ _ c hc h := by
    simp only [OrderAddMonoidHom.coe_id, id]
    refine codensity_tv_of_lintegral_le fun f g hf hg hf1 _ hfg ↦ ?_
    calc ∫⁻ x, f x ∂μ
        ≤ ∫⁻ y, min (g y + c y) 1 ∂ν + b := by
          refine lintegral_le_of_codensity_tv h hf ((hg.add hc).min measurable_const) hf1
            (fun _ ↦ min_le_right _ _) fun x y ↦ ?_
          rcases le_total (g y + c y) 1 with hle | hle
          · rw [min_eq_left hle]
            exact (hfg x y).trans_eq (by ring)
          · exact (hf1 x).trans (le_add_right (le_min hle le_rfl))
      _ ≤ ∫⁻ y, g y + c y ∂ν + b := by gcongr with y; exact min_le_left _ _
      _ = ∫⁻ y, g y ∂ν + (b + ∫⁻ y, c y ∂ν) := by
          rw [lintegral_add_right _ hc]
          ring

/-- At slack at least `1`, every sub-probability measure is related to any measure. -/
theorem codensity_tv_of_one_le [IsSubProbabilityMeasure μ] (hδ : 1 ≤ δ) :
    tv.codensity δ E μ ν := by
  intro I _ c _ k l _ _ _
  refine tv_iff.2 fun S _ ↦ ?_
  calc (k ∘ₘ μ) S ≤ 1 := IsSubProbabilityMeasure.measure_le_one S
    _ ≤ (l ∘ₘ ν) S + (δ + c) := le_add_left (hδ.trans le_self_add)

/-- Slack `1` relates every pair of sub-probability measures (Rocq `GCFTop_AR`). -/
theorem absorbing_codensity_tv_one : (codensity tv.{u}).Absorbing 1 :=
  fun _ _ _ _ _ ↦ codensity_tv_of_one_le le_rfl

/-- A total variation lifting at slack `δ` bounds an event by its image, up to `δ`. -/
theorem tv_measure_le_add (h : (codensity tv).Rel δ S μ ν) {T : Set X} {T' : Set Y}
    (hT : MeasurableSet T) (hT' : MeasurableSet T') (hS : ∀ x y, S x y → x ∈ T → y ∈ T') :
    μ T ≤ ν T' + δ := by
  have hfg (x : X) (y : Y) :
      T.indicator (1 : X → ℝ≥0∞) x ≤ T'.indicator 1 y + relCost S x y := by
    by_cases hxy : S x y
    · by_cases hx : x ∈ T <;> simp [hxy, hx, hS x y hxy]
    · simp [hxy]
  simpa [lintegral_indicator_const, hT, hT'] using lintegral_le_of_codensity_tv h
    (measurable_const.indicator hT) (measurable_const.indicator hT')
    (fun _ ↦ Set.indicator_le_self' (by simp) _) (fun _ ↦ Set.indicator_le_self' (by simp) _) hfg

/-- A total variation lifting of equality at slack `δ` bounds every event up to `δ`. -/
theorem tv_le_add_of_rel {μ ν : Measure X} (h : (codensity tv).Rel δ (· = ·) μ ν) {S : Set X}
    (hS : MeasurableSet S) : μ S ≤ ν S + δ :=
  tv_measure_le_add h hS hS fun _ _ hxy hx ↦ hxy ▸ hx

/-- Exact total variation liftings of equality in both directions give equal measures. -/
theorem tv_eq_of_rel {μ ν : Measure X} (h₁ : (codensity tv).Rel 0 (· = ·) μ ν)
    (h₂ : (codensity tv).Rel 0 (· = ·) ν μ) : μ = ν :=
  ext fun S hS ↦ le_antisymm (by simpa using tv_le_add_of_rel h₁ hS)
    (by simpa using tv_le_add_of_rel h₂ hS)

/-- Two point masses are related along the empty relation exactly at slack at least `1` (Rocq
`GCF_AR_top_exact`). -/
theorem codensity_tv_rel_false_iff :
    (codensity tv).Rel δ (fun _ _ ↦ False) (dirac PUnit.unit.{u + 1})
      (dirac PUnit.unit.{u + 1}) ↔ 1 ≤ δ :=
  ⟨fun h ↦ by simpa using tv_measure_le_add h .univ .empty fun _ _ ↦ False.elim,
    fun h ↦ absorbing_codensity_tv_one.mono h _ _ _⟩

/-- Total variation liftings are DP liftings at multiplier `1`, leftovers included (Rocq
`CM_AR_DP`). -/
theorem codensity_tv_iff_dp [IsSubProbabilityMeasure μ] :
    tv.codensity δ E μ ν ↔ dp.codensity (0, δ) (fun x y ↦ dpSlack (E x y)) μ ν := by
  rw [codensity_dp_iff ENNReal.zero_ne_top, codensity_tv_iff]
  simp

/-- Total variation liftings of a relation are DP liftings at multiplier `1`. -/
theorem codensity_tv_rel_iff_dp [IsSubProbabilityMeasure μ] :
    (codensity tv).Rel δ S μ ν ↔ (codensity dp).Rel (0, δ) S μ ν := by
  rw [codensity_dp_rel_iff ENNReal.zero_ne_top, GradedLifting.Rel, codensity_tv_iff]
  refine forall₂_congr fun f g ↦ forall₄_congr fun _ _ _ _ ↦ ?_
  simp only [expBudget_zero, one_mul]
  refine imp_congr_left (forall₂_congr fun x y ↦ ?_)
  by_cases hS : S x y <;> simp [hS]

end GradedDivergence
