module

public import Mathlib.Algebra.Order.Monoid.Lex
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.MeasureTheory.Integral.Layercake
public import Metrology.Couplings.Codensity

/-! `(ε, δ)`-differential privacy as a graded divergence (Approximate Span Liftings, §4.3). -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory GradedLifting Set
open scoped ENNReal

/-! ## Kernels into a point -/

section massKernel

variable {X : Type*} [MeasurableSpace X] {f : X → ℝ≥0∞}

/-- A measurable function as a kernel into a point: the point with that mass. -/
noncomputable def massKernel (hf : Measurable f) : Kernel X PUnit.{v + 1} :=
  ⟨fun x ↦ f x • dirac PUnit.unit, hf.smul_measure _⟩

theorem massKernel_apply (hf : Measurable f) (x : X) :
    massKernel.{v} hf x = f x • dirac PUnit.unit :=
  rfl

theorem isSubMarkovKernel_massKernel (hf : Measurable f) (hf1 : ∀ x, f x ≤ 1) :
    IsSubMarkovKernel (massKernel.{v} hf) where
  isSubProbabilityMeasure x := ⟨by simpa [massKernel_apply] using hf1 x⟩

/-- Composing with a mass kernel integrates its function. -/
theorem massKernel_comp (hf : Measurable f) (μ : Measure X) :
    massKernel.{v} hf ∘ₘ μ = (∫⁻ x, f x ∂μ) • dirac PUnit.unit := by
  ext s hs
  rw [bind_apply hs (massKernel hf).measurable.aemeasurable]
  simp [massKernel_apply, lintegral_mul_const _ hf]

end massKernel

namespace GradedDivergence

/-! ## The DP inequality -/

section Bound

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {c c' δ δ' : ℝ≥0∞}
  {μ ν : Measure X}

/-- The DP inequality `μ S ≤ c ν S + δ` on every measurable event. -/
def Bound (c δ : ℝ≥0∞) (μ ν : Measure X) : Prop :=
  ∀ S, MeasurableSet S → μ S ≤ c * ν S + δ

theorem Bound.mono (h : Bound c δ μ ν) (hc : c ≤ c') (hδ : δ ≤ δ') : Bound c' δ' μ ν :=
  fun S hS ↦ (h S hS).trans (by gcongr)

theorem bound_zero_left (c δ : ℝ≥0∞) (ν : Measure X) : Bound c δ 0 ν :=
  fun _ _ ↦ by simp

/-- DP inequalities are preserved by measurable post-processing. -/
theorem Bound.map (h : Bound c δ μ ν) {f : X → Y} (hf : Measurable f := by fun_prop) :
    Bound c δ (μ.map f) (ν.map f) := fun S hS ↦ by
  simpa only [map_apply hf hS] using h _ (hf hS)

/-- A DP inequality on events transfers to `[0, 1]`-valued test functions (by the layer cake
formula). -/
theorem Bound.lintegral_le (h : Bound c δ μ ν) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hf1 : ∀ x, f x ≤ 1) : ∫⁻ x, f x ∂μ ≤ c * ∫⁻ x, f x ∂ν + δ := by
  have hfr : ∀ x, ENNReal.ofReal (f x).toReal = f x :=
    fun x ↦ ENNReal.ofReal_toReal ((hf1 x).trans_lt ENNReal.one_lt_top).ne
  have hm : Measurable fun x ↦ (f x).toReal := hf.ennreal_toReal
  have hcake (ρ : Measure X) :
      ∫⁻ x, f x ∂ρ = ∫⁻ t in Ioi 0, ρ {x | t < (f x).toReal} := by
    rw [← lintegral_eq_lintegral_meas_lt ρ (.of_forall fun _ ↦ ENNReal.toReal_nonneg)
      hm.aemeasurable]
    simp only [hfr]
  have hanti : Measurable fun t : ℝ ↦ ν {x | t < (f x).toReal} :=
    Antitone.measurable fun s t hst ↦ measure_mono fun x (hx : t < _) ↦ hst.trans_lt hx
  rw [hcake μ, hcake ν, ← lintegral_const_mul _ hanti]
  calc ∫⁻ t in Ioi 0, μ {x | t < (f x).toReal}
      ≤ ∫⁻ t in Ioi 0, (c * ν {x | t < (f x).toReal} + (Iic 1).indicator (fun _ ↦ δ) t) := by
        refine lintegral_mono fun t ↦ ?_
        by_cases ht : t ≤ 1
        · simpa [ht] using h _ (measurableSet_lt measurable_const hm)
        · have : {x | t < (f x).toReal} = ∅ := eq_empty_of_forall_notMem fun x hx ↦
            (not_le.2 hx) ((ENNReal.toReal_le_of_le_ofReal zero_le_one
              ((hf1 x).trans ENNReal.ofReal_one.ge)).trans (not_le.1 ht).le)
          simp [this]
    _ ≤ (∫⁻ t in Ioi 0, c * ν {x | t < (f x).toReal}) + δ := by
        rw [lintegral_add_right _ (measurable_const.indicator measurableSet_Iic)]
        gcongr
        rw [lintegral_indicator_const measurableSet_Iic, Measure.restrict_apply measurableSet_Iic,
          inter_comm, Ioi_inter_Iic, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]

/-- DP inequalities compose along kernels (DP composition). -/
theorem Bound.bind {c₁ c₂ δ₁ δ₂ : ℝ≥0∞} {μ₁ μ₂ : Measure X} [IsSubProbabilityMeasure μ₁]
    (h₁ : Bound c₁ δ₁ μ₁ μ₂) {f g : X → Measure Y} (hf : Measurable f) (hg : Measurable g)
    [∀ x, IsSubProbabilityMeasure (f x)] (h₂ : ∀ x, Bound c₂ δ₂ (f x) (g x)) :
    Bound (c₁ * c₂) (δ₁ + δ₂) (μ₁.bind f) (μ₂.bind g) := by
  intro S hS
  have hgS : Measurable fun x ↦ g x S := (measurable_coe hS).comp hg
  have hpt (x : X) : f x S ≤ min 1 (c₂ * g x S) + δ₂ := by
    rcases le_total (c₂ * g x S) 1 with h | h
    · rw [min_eq_right h]
      exact h₂ x S hS
    · rw [min_eq_left h]
      exact (IsSubProbabilityMeasure.measure_le_one S).trans le_self_add
  rw [bind_apply hS hf.aemeasurable, bind_apply hS hg.aemeasurable]
  calc ∫⁻ x, f x S ∂μ₁
      ≤ ∫⁻ x, min 1 (c₂ * g x S) + δ₂ ∂μ₁ := lintegral_mono hpt
    _ ≤ ∫⁻ x, min 1 (c₂ * g x S) ∂μ₁ + δ₂ := IsSubProbabilityMeasure.lintegral_add_const_le _ _
    _ ≤ c₁ * ∫⁻ x, min 1 (c₂ * g x S) ∂μ₂ + δ₁ + δ₂ := by
        gcongr
        exact h₁.lintegral_le (measurable_const.min (measurable_const.mul hgS))
          fun _ ↦ min_le_left _ _
    _ ≤ c₁ * c₂ * ∫⁻ x, g x S ∂μ₂ + (δ₁ + δ₂) := by
        rw [mul_assoc, ← lintegral_const_mul _ hgS, add_assoc]
        gcongr
        exact min_le_right _ _

/-- DP inequalities chain (group privacy). -/
theorem Bound.trans {c₁ c₂ δ₁ δ₂ : ℝ≥0∞} {μ₁ μ₂ μ₃ : Measure X} (h₁ : Bound c₁ δ₁ μ₁ μ₂)
    (h₂ : Bound c₂ δ₂ μ₂ μ₃) : Bound (c₁ * c₂) (c₁ * δ₂ + δ₁) μ₁ μ₃ := fun S hS ↦
  calc μ₁ S ≤ c₁ * μ₂ S + δ₁ := h₁ S hS
    _ ≤ c₁ * (c₂ * μ₃ S + δ₂) + δ₁ := by grw [h₂ S hS]
    _ = c₁ * c₂ * μ₃ S + (c₁ * δ₂ + δ₁) := by ring

end Bound

/-! ## The multiplier `e^ε` -/

section expBudget

variable {ε ε' : ℝ≥0∞}

/-- The multiplier `e^ε`, `⊤` at `ε = ⊤`. -/
noncomputable def expBudget (ε : ℝ≥0∞) : ℝ≥0∞ :=
  if ε = ⊤ then ⊤ else ENNReal.ofReal (Real.exp ε.toReal)

@[simp]
theorem expBudget_top : expBudget ⊤ = ⊤ := by
  simp [expBudget]

theorem expBudget_of_ne_top (hε : ε ≠ ⊤) : expBudget ε = ENNReal.ofReal (Real.exp ε.toReal) := by
  simp [expBudget, hε]

@[simp]
theorem expBudget_zero : expBudget 0 = 1 := by
  simp [expBudget_of_ne_top]

theorem one_le_expBudget (ε : ℝ≥0∞) : 1 ≤ expBudget ε := by
  rcases eq_or_ne ε ⊤ with rfl | hε
  · simp
  · simp [expBudget_of_ne_top hε, Real.one_le_exp ENNReal.toReal_nonneg]

theorem expBudget_lt_top_iff : expBudget ε < ⊤ ↔ ε < ⊤ := by
  rcases eq_or_ne ε ⊤ with rfl | hε
  · simp
  · simp [expBudget_of_ne_top hε, hε.lt_top]

@[gcongr]
theorem expBudget_le_expBudget (h : ε ≤ ε') : expBudget ε ≤ expBudget ε' := by
  rcases eq_or_ne ε' ⊤ with rfl | hε'
  · simp
  rw [expBudget_of_ne_top (ne_top_of_le_ne_top hε' h), expBudget_of_ne_top hε']
  gcongr

theorem expBudget_mono : Monotone expBudget :=
  fun _ _ ↦ expBudget_le_expBudget

theorem expBudget_add (ε ε' : ℝ≥0∞) : expBudget (ε + ε') = expBudget ε * expBudget ε' := by
  rcases eq_or_ne ε ⊤ with rfl | hε
  · simp [ENNReal.top_mul (one_pos.trans_le (one_le_expBudget ε')).ne']
  rcases eq_or_ne ε' ⊤ with rfl | hε'
  · simp [ENNReal.mul_top (one_pos.trans_le (one_le_expBudget ε)).ne']
  rw [expBudget_of_ne_top (ENNReal.add_ne_top.2 ⟨hε, hε'⟩), expBudget_of_ne_top hε,
    expBudget_of_ne_top hε', ENNReal.toReal_add hε hε', Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_pos _).le]

end expBudget

/-! ## The DP divergence -/

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {ε ε' δ : ℝ≥0∞}

section dp

variable {b : ℝ≥0∞ × ℝ≥0∞} {μ ν : Measure X}

/-- `(ε, δ)`-DP between measures; at `ε = ⊤` it always holds. -/
noncomputable def dp : GradedDivergence.{u} (ℝ≥0∞ × ℝ≥0∞) :=
  fun b _ _ μ ν ↦ b.1 < ⊤ → Bound (expBudget b.1) b.2 μ ν

theorem dp_iff (hε : ε ≠ ⊤) :
    dp (ε, δ) μ ν ↔ ∀ S, MeasurableSet S → μ S ≤ expBudget ε * ν S + δ :=
  ⟨fun h ↦ h hε.lt_top, fun h _ ↦ h⟩

theorem dp_top_left : dp (⊤, δ) μ ν :=
  fun h ↦ (lt_irrefl _ h).elim

theorem dp_mono_left (h : ε ≤ ε') (hd : dp (ε, δ) μ ν) : dp (ε', δ) μ ν :=
  fun hε' ↦ (hd (h.trans_lt hε')).mono (expBudget_mono h) le_rfl

/-- Point masses within a DP budget compare their masses. -/
theorem dp_smul_dirac_iff {a a' : ℝ≥0∞} :
    dp b (a • dirac PUnit.unit.{u + 1}) (a' • dirac PUnit.unit) ↔
      (b.1 < ⊤ → a ≤ expBudget b.1 * a' + b.2) := by
  refine imp_congr_right fun _ ↦ ⟨fun h ↦ by simpa using h univ .univ, fun h S _ ↦ ?_⟩
  rcases S.eq_empty_or_nonempty with rfl | ⟨⟨⟩, hS⟩
  · simp
  · simpa [hS] using h

theorem dp_map (h : dp b μ ν) {f : X → Y} (hf : Measurable f := by fun_prop) :
    dp b (μ.map f) (ν.map f) :=
  fun hb ↦ (h hb).map hf

/-- DP chains, multiplying the second slack by the first multiplier (group privacy). -/
theorem dp_trans {μ₁ μ₂ μ₃ : Measure X} {ε₁ ε₂ δ₁ δ₂ : ℝ≥0∞} (h₁ : dp (ε₁, δ₁) μ₁ μ₂)
    (h₂ : dp (ε₂, δ₂) μ₂ μ₃) : dp (ε₁ + ε₂, expBudget ε₁ * δ₂ + δ₁) μ₁ μ₃ := fun h ↦ by
  obtain ⟨h₁', h₂'⟩ := ENNReal.add_lt_top.1 h
  simpa only [expBudget_add] using (h₁ h₁').trans (h₂ h₂')

/-! ## Instances -/

instance isGraded_dp : dp.{u}.IsGraded where
  mono _ _ hb := fun h hb' ↦ (h (hb.1.trans_lt hb')).mono (expBudget_mono hb.1) hb.2
  top _ _ := fun h ↦ (lt_irrefl _ h).elim

instance isReflexive_dp : dp.{u}.IsReflexive where
  refl _ := fun _ _ _ ↦ by simp

/-- Adaptive composition multiplies the multipliers and adds the slacks (DP composition). -/
instance isComposable_dp : dp.{u}.IsComposable where
  comp _ _ := fun h hκη hbc ↦ by
    obtain ⟨hb, hc⟩ := ENNReal.add_lt_top.1 hbc
    simpa only [Prod.fst_add, Prod.snd_add, expBudget_add] using
      (h hb).bind (Kernel.measurable _) (Kernel.measurable _) fun x ↦ hκη x hc

instance isZeroLeft_dp : dp.{u}.IsZeroLeft where
  zero_left _ _ _ ν _ _ := bound_zero_left _ _ ν

instance isLeftContinuous_dp : dp.{u}.IsLeftContinuous where
  iSup_left _ _ _ _ _ hμ _ _ h hb S hS := by
    rw [iSup_apply_of_monotone hμ hS]
    exact iSup_le fun n ↦ h n hb S hS

instance isRightMonotone_dp : dp.{u}.IsRightMonotone where
  right_mono _ _ _ _ _ _ _ _ hν h hb S hS := (h hb S hS).trans (by grw [le_iff'.1 hν S])

instance isLeftAntitone_dp : dp.{u}.IsLeftAntitone where
  left_anti _ _ _ _ _ _ _ _ hμ h hb S hS := (le_iff'.1 hμ S).trans (h hb S hS)

/-- A bound at every larger slack is a bound at the slack. -/
instance isBudgetClosed_dp : dp.{u}.IsBudgetClosed where
  of_forall_gt {b} _ _ _ _ _ _ h hb S hS := by
    rcases eq_or_ne b.2 ⊤ with htop | htop
    · simp [htop]
    refine ENNReal.le_of_forall_pos_le_add fun η hη _ ↦ ?_
    rw [add_assoc]
    refine h (b.1, b.2 + η) (Prod.lt_iff.2 (.inr ⟨le_rfl, ?_⟩)) hb S hS
    exact ENNReal.lt_add_right htop (by simpa using hη.ne')

/-- The slack `δ ↦ (0, δ)` through which an event gap enters a DP budget. -/
noncomputable def dpSlack : ℝ≥0∞ →+o ℝ≥0∞ × ℝ≥0∞ :=
  OrderAddMonoidHom.inr ℝ≥0∞ ℝ≥0∞

@[simp]
theorem dpSlack_apply (δ : ℝ≥0∞) : dpSlack δ = (0, δ) :=
  rfl

instance hasSlack_dp : dp.{u}.HasSlack dpSlack where
  of_forall_le h _ S hS := by simpa using h S hS

instance isMassDetecting_dp : dp.{u}.IsMassDetecting dpSlack where
  le_add_of _ _ h := by simpa [dp_smul_dirac_iff] using h

end dp

/-! ## The DP codensity lifting -/

variable {μ : Measure X} {ν : Measure Y} {R : X → Y → ℝ≥0∞ × ℝ≥0∞} {S : X → Y → Prop}

theorem codensity_dp_top_left : dp.codensity (⊤, δ) R μ ν := by
  intro I _ c _ k l _ _ _ h
  simp at h

/-- Reading a DP codensity lifting on `[0, 1]`-valued test functions through mass kernels. -/
theorem lintegral_le_of_codensity_dp (hε : ε ≠ ⊤) (h : dp.codensity (ε, δ) R μ ν)
    {f : X → ℝ≥0∞} {g : Y → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hf1 : ∀ x, f x ≤ 1)
    (hg1 : ∀ y, g y ≤ 1)
    (hfg : ∀ x y, (R x y).1 < ⊤ → f x ≤ expBudget (R x y).1 * g y + (R x y).2) :
    ∫⁻ x, f x ∂μ ≤ expBudget ε * ∫⁻ y, g y ∂ν + δ := by
  have := isSubMarkovKernel_massKernel.{u} hf hf1
  have := isSubMarkovKernel_massKernel.{u} hg hg1
  have hc := h (c := 0) (k := massKernel.{u} hf) (l := massKernel.{u} hg)
    (by simpa [Prod.lt_iff] using Or.inl hε.lt_top) fun x y ↦ by
      simpa [massKernel_apply, dp_smul_dirac_iff] using hfg x y
  simpa [massKernel_comp, dp_smul_dirac_iff, hε.lt_top] using hc

/-- `[0, 1]`-valued test functions that the leftover relates give a DP codensity lifting: a
test passed with slack `c` becomes a test function once `c.2` is cut off. -/
theorem codensity_dp_of_lintegral_le [IsSubProbabilityMeasure μ]
    (h : ∀ f g, Measurable f → Measurable g → (∀ x, f x ≤ 1) → (∀ y, g y ≤ 1) →
      (∀ x y, (R x y).1 < ⊤ → f x ≤ expBudget (R x y).1 * g y + (R x y).2) →
      ∫⁻ x, f x ∂μ ≤ expBudget ε * ∫⁻ y, g y ∂ν + δ) :
    dp.codensity (ε, δ) R μ ν := by
  intro I _ c _ k l _ _ hkl hεc S hS
  simp only [Prod.fst_add, Prod.snd_add] at hεc ⊢
  obtain ⟨-, hc⟩ := ENNReal.add_lt_top.1 hεc
  have hkS := k.measurable_coe hS
  have hlS := l.measurable_coe hS
  have hfg := h (fun x ↦ k x S - c.2) (fun y ↦ min 1 (expBudget c.1 * l y S))
    (hkS.sub measurable_const) (measurable_const.min (measurable_const.mul hlS))
    (fun _ ↦ tsub_le_self.trans (IsSubProbabilityMeasure.measure_le_one S))
    (fun _ ↦ min_le_left _ _) fun x y hR ↦ by
      rw [tsub_le_iff_right]
      rcases le_total (expBudget c.1 * l y S) 1 with h1 | h1
      · have := hkl x y (ENNReal.add_lt_top.2 ⟨hR, hc⟩) S hS
        rw [min_eq_right h1]
        simpa only [Prod.fst_add, Prod.snd_add, expBudget_add, mul_assoc, add_assoc] using this
      · rw [min_eq_left h1, mul_one]
        exact le_add_right (le_add_right
          ((IsSubProbabilityMeasure.measure_le_one S).trans (one_le_expBudget _)))
  rw [bind_apply hS k.measurable.aemeasurable, bind_apply hS l.measurable.aemeasurable,
    expBudget_add]
  calc ∫⁻ x, k x S ∂μ
      ≤ ∫⁻ x, (k x S - c.2) + c.2 ∂μ := lintegral_mono fun _ ↦ le_tsub_add
    _ ≤ ∫⁻ x, k x S - c.2 ∂μ + c.2 := IsSubProbabilityMeasure.lintegral_add_const_le _ _
    _ ≤ expBudget ε * ∫⁻ y, min 1 (expBudget c.1 * l y S) ∂ν + δ + c.2 := by gcongr
    _ ≤ expBudget ε * expBudget c.1 * ∫⁻ y, l y S ∂ν + (δ + c.2) := by
        rw [mul_assoc, ← lintegral_const_mul _ hlS, add_assoc]
        gcongr
        exact min_le_right _ _

/-- At a finite multiplier, the DP codensity lifting is decided by `[0, 1]`-valued test
functions. -/
theorem codensity_dp_iff [IsSubProbabilityMeasure μ] (hε : ε ≠ ⊤) :
    dp.codensity (ε, δ) R μ ν ↔ ∀ f g, Measurable f → Measurable g → (∀ x, f x ≤ 1) →
      (∀ y, g y ≤ 1) →
      (∀ x y, (R x y).1 < ⊤ → f x ≤ expBudget (R x y).1 * g y + (R x y).2) →
      ∫⁻ x, f x ∂μ ≤ expBudget ε * ∫⁻ y, g y ∂ν + δ :=
  ⟨fun h _ _ ↦ lintegral_le_of_codensity_dp hε h, codensity_dp_of_lintegral_le⟩

/-- The relational form of `codensity_dp_iff`: test functions ordered on the relation. -/
theorem codensity_dp_rel_iff [IsSubProbabilityMeasure μ] (hε : ε ≠ ⊤) :
    (codensity dp).Rel (ε, δ) S μ ν ↔ ∀ f g, Measurable f → Measurable g → (∀ x, f x ≤ 1) →
      (∀ y, g y ≤ 1) → (∀ x y, S x y → f x ≤ g y) →
      ∫⁻ x, f x ∂μ ≤ expBudget ε * ∫⁻ y, g y ∂ν + δ := by
  have (f : X → ℝ≥0∞) (g : Y → ℝ≥0∞) (x : X) (y : Y) :
      ((relCost S x y : ℝ≥0∞ × ℝ≥0∞).1 < ⊤ →
        f x ≤ expBudget (relCost S x y : ℝ≥0∞ × ℝ≥0∞).1 * g y +
          (relCost S x y : ℝ≥0∞ × ℝ≥0∞).2) ↔
      (S x y → f x ≤ g y) := by
    by_cases hS : S x y <;> simp [hS]
  simp only [GradedLifting.Rel, codensity_dp_iff hε, this]

/-- Countable fibers with a pointwise DP bound give a DP codensity lifting of equal images
(clutch-dp `randomized_response.v`). -/
theorem codensity_dp_of_fiber {Z : Type*} [MeasurableSpace Z] [Countable Z]
    [MeasurableSingletonClass Z] {f : X → Z} {g : Y → Z} (hf : Measurable f) (hg : Measurable g)
    [IsSubProbabilityMeasure μ] (h : ∀ z, μ (f ⁻¹' {z}) ≤ expBudget ε * ν (g ⁻¹' {z})) :
    (codensity dp).Rel (ε, 0) (fun x y ↦ f x = g y) μ ν := by
  rcases eq_or_ne ε ⊤ with rfl | hε
  · exact codensity_dp_top_left
  refine (codensity_dp_rel_iff hε).2 fun h₁ h₂ _ _ _ _ h₁₂ ↦ ?_
  let m : Z → ℝ≥0∞ := fun z ↦ ⨅ y ∈ g ⁻¹' {z}, h₂ y
  have hm : Measurable m := .of_discrete
  have hint (κ : Measure Z) : ∫⁻ z, m z ∂κ = ∑' z, m z * κ {z} := lintegral_countable' _
  calc ∫⁻ x, h₁ x ∂μ
      ≤ ∫⁻ x, m (f x) ∂μ := lintegral_mono fun x ↦ le_iInf₂ fun _ hy ↦ h₁₂ _ _ hy.symm
    _ = ∑' z, m z * μ (f ⁻¹' {z}) := by
        simp [← lintegral_map hm hf, hint, map_apply hf (measurableSet_singleton _)]
    _ ≤ ∑' z, m z * (expBudget ε * ν (g ⁻¹' {z})) := ENNReal.tsum_le_tsum fun z ↦ by grw [h z]
    _ = expBudget ε * ∫⁻ y, m (g y) ∂ν := by
        simp [← lintegral_map hm hg, hint, map_apply hg (measurableSet_singleton _),
          ← ENNReal.tsum_mul_left, mul_left_comm]
    _ ≤ expBudget ε * ∫⁻ y, h₂ y ∂ν + 0 := by
        rw [add_zero]
        gcongr with y
        exact biInf_le h₂ rfl

/-- Slack `1` relates every pair of sub-probability measures. -/
theorem absorbing_codensity_dp : (codensity dp.{u}).Absorbing (0, 1) :=
  absorbing_codensity_of_hasSlack (s := dpSlack)

/-- At a finite multiplier, two point masses are related along the empty relation exactly at
slack at least `1`. -/
theorem codensity_dp_rel_false_iff (hε : ε ≠ ⊤) :
    (codensity dp).Rel (ε, δ) (fun _ _ ↦ False) (dirac PUnit.unit.{u + 1})
      (dirac PUnit.unit.{u + 1}) ↔ 1 ≤ δ := by
  refine ⟨fun h ↦ ?_, fun h ↦ absorbing_codensity_dp.mono (Prod.mk_le_mk.2 ⟨zero_le, h⟩) _ _ _⟩
  simpa using (codensity_dp_rel_iff hε).1 h (fun _ ↦ 1) (fun _ ↦ 0) measurable_const
    measurable_const (fun _ ↦ le_rfl) (fun _ ↦ zero_le) fun _ _ ↦ False.elim

end GradedDivergence
