module

public import Mathlib.Algebra.Order.Monoid.Lex
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
public import Metrology.Couplings.Codensity

/-! `(ε, δ)`-differential privacy as a graded divergence (Approximate Span Liftings, §4.3). -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory GradedLifting Set Filter Topology Real
open ENNReal

namespace GradedDivergence

/-! ## The DP inequality -/

section Bound

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {c c' δ δ' : ℝ≥0∞}
  {μ ν : Measure X}

/-- The DP inequality `μ S ≤ c ν S + δ` on every measurable event. -/
def Bound (c δ : ℝ≥0∞) (μ ν : Measure X) : Prop :=
  ∀ S, MeasurableSet S → μ S ≤ c * ν S + δ

/-- A bound at every larger slack is a bound at the slack. -/
theorem Bound.of_forall_lt (h : ∀ δ', δ < δ' → Bound c δ' μ ν) : Bound c δ μ ν := fun S hS ↦ by
  rcases eq_or_ne δ ⊤ with rfl | hδ
  · simp
  refine le_of_forall_pos_le_add fun η hη _ ↦ ?_
  rw [add_assoc]
  exact h _ (lt_add_right hδ (by simpa using hη.ne')) S hS

/-- DP inequalities at multipliers converging to `e^{e₀}` give the one at `e^{e₀}`. -/
theorem Bound.of_tendsto {e : ℕ → ℝ} {e₀ : ℝ} (he : Tendsto e atTop (𝓝 e₀))
    (h : ∀ n, Bound (ENNReal.ofReal (exp (e n))) δ μ ν) :
    Bound (ENNReal.ofReal (exp e₀)) δ μ ν := fun S hS ↦
  ge_of_tendsto' ((ENNReal.Tendsto.mul_const
    (tendsto_ofReal ((continuous_exp.tendsto e₀).comp he))
    (.inl (ofReal_pos.2 (exp_pos _)).ne')).add_const δ) fun n ↦ h n S hS

/-- Increasing the parameters `c` and `δ` preserves the `(c, δ)` DP bound between `μ` and `ν`. -/
theorem Bound.mono (h : Bound c δ μ ν) (hc : c ≤ c') (hδ : δ ≤ δ') : Bound c' δ' μ ν :=
  fun S hS ↦ (h S hS).trans (by gcongr)

theorem bound_zero_left (c δ : ℝ≥0∞) (ν : Measure X) : Bound c δ 0 ν :=
  fun _ _ ↦ by simp

/-- DP inequalities are preserved by measurable post-processing. -/
theorem Bound.map (h : Bound c δ μ ν) {f : X → Y} (hf : Measurable f := by fun_prop) :
    Bound c δ (μ.map f) (ν.map f) := fun S hS ↦ by
  simpa only [map_apply hf hS] using h _ (hf hS)

/-- A function bounded by `1` has an empty strict superlevel set above height `1`. -/
theorem setOf_lt_toReal_eq_empty {f : X → ℝ≥0∞} (hf1 : ∀ x, f x ≤ 1) {t : ℝ} (ht : 1 < t) :
    {x | t < (f x).toReal} = ∅ :=
  eq_empty_of_forall_notMem fun x hx ↦
    (not_le.2 hx) ((toReal_le_of_le_ofReal zero_le_one
      ((hf1 x).trans ofReal_one.ge)).trans ht.le)

/-- A DP inequality on events transfers to `[0, 1]`-valued test functions (by the layer cake
formula). -/
theorem Bound.lintegral_le (h : Bound c δ μ ν) {f : X → ℝ≥0∞} (hf : Measurable f)
    (hf1 : ∀ x, f x ≤ 1) : ∫⁻ x, f x ∂μ ≤ c * ∫⁻ x, f x ∂ν + δ := by
  have hm : Measurable fun x ↦ (f x).toReal := hf.ennreal_toReal
  have hcake (ρ : Measure X) :
      ∫⁻ x, f x ∂ρ = ∫⁻ t in Ioi 0, ρ {x | t < (f x).toReal} := by
    rw [← lintegral_eq_lintegral_meas_lt ρ (.of_forall fun _ ↦ toReal_nonneg)
      hm.aemeasurable]
    simp only [fun x ↦ ofReal_toReal ((hf1 x).trans_lt one_lt_top).ne]
  have hanti : Measurable fun t : ℝ ↦ ν {x | t < (f x).toReal} :=
    Antitone.measurable fun s t hst ↦ measure_mono fun x (hx : t < _) ↦ hst.trans_lt hx
  rw [hcake μ, hcake ν, ← lintegral_const_mul _ hanti]
  calc ∫⁻ t in Ioi 0, μ {x | t < (f x).toReal}
      ≤ ∫⁻ t in Ioi 0, (c * ν {x | t < (f x).toReal} + (Iic 1).indicator (fun _ ↦ δ) t) := by
        refine lintegral_mono fun t ↦ ?_
        by_cases ht : t ≤ 1
        · simpa [ht] using h _ (measurableSet_lt measurable_const hm)
        · simp [setOf_lt_toReal_eq_empty hf1 (not_le.1 ht)]
    _ ≤ (∫⁻ t in Ioi 0, c * ν {x | t < (f x).toReal}) + δ := by
        rw [lintegral_add_right _ (measurable_const.indicator measurableSet_Iic)]
        gcongr
        rw [lintegral_indicator_const measurableSet_Iic, Measure.restrict_apply measurableSet_Iic,
          inter_comm, Ioi_inter_Iic, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]

/-- A DP bound on a sub-probability measure `μ` also bounds `μ S` by `min 1 (c * ν S) + δ`. -/
theorem Bound.apply_le_min_add [IsSubProbabilityMeasure μ] (h : Bound c δ μ ν) {S : Set X}
    (hS : MeasurableSet S) : μ S ≤ min 1 (c * ν S) + δ := by
  rcases le_total (c * ν S) 1 with h' | h'
  · rw [min_eq_right h']; exact h S hS
  · rw [min_eq_left h']; exact (IsSubProbabilityMeasure.measure_le_one S).trans le_self_add

/-- DP inequalities compose along kernels (DP composition). -/
theorem Bound.bind {c₁ c₂ δ₁ δ₂ : ℝ≥0∞} {μ₁ μ₂ : Measure X} [IsSubProbabilityMeasure μ₁]
    (h₁ : Bound c₁ δ₁ μ₁ μ₂) {f g : X → Measure Y} (hf : Measurable f) (hg : Measurable g)
    [∀ x, IsSubProbabilityMeasure (f x)] (h₂ : ∀ x, Bound c₂ δ₂ (f x) (g x)) :
    Bound (c₁ * c₂) (δ₁ + δ₂) (μ₁.bind f) (μ₂.bind g) := by
  intro S hS
  have hgS : Measurable fun x ↦ g x S := (measurable_coe hS).comp hg
  rw [bind_apply hS hf.aemeasurable, bind_apply hS hg.aemeasurable]
  calc ∫⁻ x, f x S ∂μ₁
      ≤ ∫⁻ x, min 1 (c₂ * g x S) + δ₂ ∂μ₁ :=
        lintegral_mono fun x ↦ Bound.apply_le_min_add (h₂ x) hS
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
  (ε : EReal).exp

@[simp]
theorem expBudget_top : expBudget ⊤ = ⊤ := by
  simp [expBudget]

/-- For finite `ε`, the exponential budget is `exp ε` as a nonnegative extended real. -/
theorem expBudget_of_ne_top (hε : ε ≠ ⊤) : expBudget ε = ENNReal.ofReal (exp ε.toReal) := by
  rw [expBudget, ← EReal.coe_ennreal_toReal hε, EReal.exp_coe]

/-- The budget exponential of a nonnegative real `x` is `exp x`. -/
theorem expBudget_ofReal {x : ℝ} (hx : 0 ≤ x) :
    expBudget (ENNReal.ofReal x) = ENNReal.ofReal (exp x) := by
  rw [expBudget_of_ne_top ofReal_ne_top, toReal_ofReal hx]

@[simp]
theorem expBudget_zero : expBudget 0 = 1 := by
  simp [expBudget]

/-- The exponentiated privacy budget `exp ε` is at least `1`. -/
theorem one_le_expBudget (ε : ℝ≥0∞) : 1 ≤ expBudget ε :=
  EReal.one_le_exp_iff.2 (EReal.coe_ennreal_nonneg ε)

/-- The exponential budget of `ε` is finite exactly when `ε` is finite. -/
theorem expBudget_lt_top_iff : expBudget ε < ⊤ ↔ ε < ⊤ := by
  simp [expBudget, lt_top_iff_ne_top, EReal.coe_ennreal_eq_top_iff]

theorem expBudget_mono : Monotone expBudget :=
  fun _ _ h ↦ EReal.exp_monotone (EReal.coe_ennreal_le_coe_ennreal_iff.2 h)

@[fun_prop]
theorem measurable_expBudget : Measurable expBudget :=
  expBudget_mono.measurable

@[gcongr]
theorem expBudget_le_expBudget (h : ε ≤ ε') : expBudget ε ≤ expBudget ε' :=
  expBudget_mono h

/-- The exponential budget is multiplicative: `expBudget (ε + ε') = expBudget ε * expBudget ε'`. -/
theorem expBudget_add (ε ε' : ℝ≥0∞) : expBudget (ε + ε') = expBudget ε * expBudget ε' := by
  simp [expBudget, EReal.coe_ennreal_add, EReal.exp_add]

/-- The `p`-th power of the exponential budget of `ε` is the exponential budget of `p * ε`. -/
theorem expBudget_rpow {p : ℝ} (hp : 0 < p) (ε : ℝ≥0∞) :
    expBudget ε ^ p = expBudget (ENNReal.ofReal p * ε) := by
  rcases eq_or_ne ε ⊤ with rfl | hε
  · simp [mul_top (ofReal_pos.2 hp).ne', top_rpow_of_pos hp]
  rw [expBudget_of_ne_top hε, expBudget_of_ne_top (by finiteness),
    ofReal_rpow_of_nonneg (exp_pos _).le hp.le, ← exp_mul, toReal_mul, toReal_ofReal hp.le,
    mul_comm]

end expBudget

/-! ## The DP divergence -/

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {ε ε' δ : ℝ≥0∞}

section dp

variable {b : ℝ≥0∞ × ℝ≥0∞} {μ ν : Measure X}

/-- `(ε, δ)`-DP between measures; at `ε = ⊤` it always holds. -/
noncomputable def dp : GradedDivergence.{u} (ℝ≥0∞ × ℝ≥0∞) :=
  fun b _ _ μ ν ↦ b.1 < ⊤ → Bound (expBudget b.1) b.2 μ ν

/-- `(ε, δ)`-differential privacy for finite `ε` is the inequality `μ S ≤ exp ε * ν S + δ` on
every measurable set `S`. -/
theorem dp_iff (hε : ε ≠ ⊤) :
    dp (ε, δ) μ ν ↔ ∀ S, MeasurableSet S → μ S ≤ expBudget ε * ν S + δ :=
  ⟨fun h ↦ h hε.lt_top, fun h _ ↦ h⟩

/-- A pointwise bound `μ S ≤ exp ε * ν S` on measurable sets gives `(ε, 0)`-differential privacy. -/
theorem dp_of_forall_le (h : ∀ S, MeasurableSet S → μ S ≤ expBudget ε * ν S) : dp (ε, 0) μ ν :=
  fun _ S hS ↦ (h S hS).trans le_self_add

/-- Differential privacy with infinite `ε` holds vacuously. -/
theorem dp_top_left : dp (⊤, δ) μ ν :=
  fun h ↦ (lt_irrefl _ h).elim

/-- The `(ε, δ)`-DP inequality is monotone in the budget. -/
theorem dp_mono {b' : ℝ≥0∞ × ℝ≥0∞} (hb : b ≤ b') (h : dp b μ ν) : dp b' μ ν :=
  fun hb' ↦ (h (hb.1.trans_lt hb')).mono (expBudget_mono hb.1) hb.2

theorem dp_mono_left (h : ε ≤ ε') (hd : dp (ε, δ) μ ν) : dp (ε', δ) μ ν :=
  dp_mono (Prod.mk_le_mk.2 ⟨h, le_rfl⟩) hd

/-- Point masses within a DP budget compare their masses. -/
theorem dp_smul_dirac_iff {a a' : ℝ≥0∞} :
    dp b (a • dirac PUnit.unit.{u + 1}) (a' • dirac PUnit.unit) ↔
      (b.1 < ⊤ → a ≤ expBudget b.1 * a' + b.2) := by
  refine imp_congr_right fun _ ↦ ⟨fun h ↦ by simpa using h univ .univ, fun h S _ ↦ ?_⟩
  rcases S.eq_empty_or_nonempty with rfl | ⟨⟨⟩, hS⟩
  · simp
  · simpa [hS] using h

/-- DP at every larger multiplier is DP at the multiplier. -/
theorem dp_of_forall_gt_left (h : ∀ ε', ε < ε' → dp (ε', δ) μ ν) : dp (ε, δ) μ ν := by
  intro (hε : ε < ⊤)
  have key (n : ℕ) : Bound (ENNReal.ofReal (exp (ε.toReal + 1 / (n + 1)))) δ μ ν := by
    have hfin := add_lt_top.2 ⟨hε, ofReal_lt_top (r := 1 / (n + 1))⟩
    have : Bound (expBudget (ε + ENNReal.ofReal (1 / (n + 1)))) δ μ ν :=
      h _ (ENNReal.lt_add_right hε.ne (by simp; positivity)) hfin
    rwa [expBudget_of_ne_top hfin.ne, toReal_add hε.ne ofReal_ne_top,
      toReal_ofReal (by positivity)] at this
  rw [expBudget_of_ne_top hε.ne]
  exact .of_tendsto (by simpa using
    (tendsto_const_nhds (x := ε.toReal)).add tendsto_one_div_add_atTop_nhds_zero_nat) key

/-- DP at a family of multipliers is DP at their infimum. -/
theorem dp_iInf_left {ι : Sort*} [Nonempty ι] {ε : ι → ℝ≥0∞} (h : ∀ i, dp (ε i, δ) μ ν) :
    dp (⨅ i, ε i, δ) μ ν :=
  dp_of_forall_gt_left fun _ h' ↦ by
    obtain ⟨i, hi⟩ := iInf_lt_iff.1 h'
    exact dp_mono_left hi.le (h i)

/-- Differential privacy is preserved under pushforward by a measurable map. -/
theorem dp_map (h : dp b μ ν) {f : X → Y} (hf : Measurable f := by fun_prop) :
    dp b (μ.map f) (ν.map f) :=
  fun hb ↦ (h hb).map hf

/-- DP chains, multiplying the second slack by the first multiplier (group privacy). -/
theorem dp_trans {μ₁ μ₂ μ₃ : Measure X} {ε₁ ε₂ δ₁ δ₂ : ℝ≥0∞} (h₁ : dp (ε₁, δ₁) μ₁ μ₂)
    (h₂ : dp (ε₂, δ₂) μ₂ μ₃) : dp (ε₁ + ε₂, expBudget ε₁ * δ₂ + δ₁) μ₁ μ₃ := fun h ↦ by
  obtain ⟨h₁', h₂'⟩ := add_lt_top.1 h
  simpa only [expBudget_add] using (h₁ h₁').trans (h₂ h₂')

/-! ## Instances -/

/-- DP is a graded divergence: monotone in the budget, trivial at `⊤`. -/
instance isGraded_dp : dp.{u}.IsGraded where
  mono _ _ hb := dp_mono hb
  top _ _ := dp_top_left

/-- DP is reflexive at every budget. -/
instance isReflexive_dp : dp.{u}.IsReflexive where
  refl _ := fun _ _ _ ↦ by simp

/-- Adaptive composition multiplies the multipliers and adds the slacks (DP composition). -/
instance isComposable_dp : dp.{u}.IsComposable where
  comp _ _ := fun h hκη hbc ↦ by
    obtain ⟨hb, hc⟩ := ENNReal.add_lt_top.1 hbc
    simpa only [Prod.fst_add, Prod.snd_add, expBudget_add] using
      (h hb).bind (Kernel.measurable _) (Kernel.measurable _) fun x ↦ hκη x hc

/-- The zero measure is DP-bounded by any measure. -/
instance isZeroLeft_dp : dp.{u}.IsZeroLeft where
  zero_left _ _ _ ν _ _ := bound_zero_left _ _ ν

/-- DP is continuous in the left measure along monotone suprema. -/
instance isLeftContinuous_dp : dp.{u}.IsLeftContinuous where
  iSup_left _ := fun hμ _ _ h hb S hS ↦ by
    rw [iSup_apply_of_monotone hμ hS]
    exact iSup_le fun n ↦ h n hb S hS

/-- DP is monotone in the right measure. -/
instance isRightMonotone_dp : dp.{u}.IsRightMonotone where
  right_mono _ := fun hν h hb S hS ↦ (h hb S hS).trans (by grw [le_iff'.1 hν S])

/-- DP is antitone in the left measure. -/
instance isLeftAntitone_dp : dp.{u}.IsLeftAntitone where
  left_anti _ := fun hμ h hb S hS ↦ (le_iff'.1 hμ S).trans (h hb S hS)

/-- DP budgets are closed from above. -/
instance isBudgetClosed_dp : dp.{u}.IsBudgetClosed where
  of_forall_gt {b} := fun h hb ↦
    .of_forall_lt fun δ' hδ' ↦ h (b.1, δ') (Prod.lt_iff.2 (.inr ⟨le_rfl, hδ'⟩)) hb

/-- The slack `δ ↦ (0, δ)` through which an event gap enters a DP budget. -/
noncomputable def dpSlack : ℝ≥0∞ →+o ℝ≥0∞ × ℝ≥0∞ :=
  OrderAddMonoidHom.inr ℝ≥0∞ ℝ≥0∞

@[simp]
theorem dpSlack_apply (δ : ℝ≥0∞) : dpSlack δ = (0, δ) :=
  rfl

/-- An event gap `δ` gives DP at budget `(0, δ)`. -/
instance hasSlack_dp : dp.{u}.HasSlack dpSlack where
  of_forall_le h _ S hS := by simpa using h S hS

/-- Point masses that are DP-close at `(0, δ)` differ in mass by at most `δ`. -/
instance isMassDetecting_dp : dp.{u}.IsMassDetecting dpSlack where
  le_add_of _ _ h := by simpa [dp_smul_dirac_iff] using h

end dp

/-! ## The DP codensity lifting -/

variable {μ : Measure X} {ν : Measure Y} {R : X → Y → ℝ≥0∞ × ℝ≥0∞} {S : X → Y → Prop}

/-- With infinite multiplicative budget, the `(ε, δ)`-DP codensity holds for any `δ`. -/
theorem codensity_dp_top_left : dp.codensity (⊤, δ) R μ ν := by
  intro I _ c _ k l _ _ _ h
  simp at h

/-- The codensity of the DP divergence absorbs any grade with first component `⊤`. -/
theorem absorbing_codensity_dp_top_left : (codensity dp.{u}).Absorbing (⊤, δ) :=
  fun _ _ _ _ _ ↦ codensity_dp_top_left

/-- A DP codensity lifting bounds `∫⁻ f ∂μ` by `expBudget ε * ∫⁻ g ∂ν + δ` for `[0, 1]`-valued
test functions. -/
theorem lintegral_le_of_codensity_dp (hε : ε ≠ ⊤) (h : dp.codensity (ε, δ) R μ ν)
    {f : X → ℝ≥0∞} {g : Y → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hf1 : ∀ x, f x ≤ 1)
    (hg1 : ∀ y, g y ≤ 1)
    (hfg : ∀ x y, (R x y).1 < ⊤ → f x ≤ expBudget (R x y).1 * g y + (R x y).2) :
    ∫⁻ x, f x ∂μ ≤ expBudget ε * ∫⁻ y, g y ∂ν + δ := by
  have := Kernel.isSubMarkovKernel_mass.{u} hf hf1
  have := Kernel.isSubMarkovKernel_mass.{u} hg hg1
  simpa [Kernel.mass_comp, dp_smul_dirac_iff, hε.lt_top] using
    h (c := 0) (k := Kernel.mass.{u} hf) (l := Kernel.mass.{u} hg)
      (by simpa [Prod.lt_iff] using Or.inl hε.lt_top) fun x y ↦ by
        simpa [Kernel.mass_apply, dp_smul_dirac_iff] using hfg x y

/-- If the budgeted bound holds when the test is not truncated, it holds for the truncated one. -/
theorem le_add_of_min_expBudget_mul_le {k l r₁ r₂ c₁ c₂ : ℝ≥0∞} (hk : k ≤ 1)
    (hkl : k ≤ expBudget r₁ * (expBudget c₁ * l) + (r₂ + c₂)) :
    k ≤ expBudget r₁ * min 1 (expBudget c₁ * l) + r₂ + c₂ := by
  rcases le_total (expBudget c₁ * l) 1 with h1 | h1
  · rwa [min_eq_right h1, add_assoc]
  · rw [min_eq_left h1, mul_one]
    exact le_add_right (le_add_right (hk.trans (one_le_expBudget _)))

/-- `[0, 1]`-valued test functions that the leftover relates give a DP codensity lifting: a
test passed with slack `c` becomes a test function once `c.2` is cut off. -/
theorem codensity_dp_of_lintegral_le [IsSubProbabilityMeasure μ]
    (h : ∀ f g, Measurable f → Measurable g → (∀ x, f x ≤ 1) → (∀ y, g y ≤ 1) →
      (∀ x y, (R x y).1 < ⊤ → f x ≤ expBudget (R x y).1 * g y + (R x y).2) →
      ∫⁻ x, f x ∂μ ≤ expBudget ε * ∫⁻ y, g y ∂ν + δ) :
    dp.codensity (ε, δ) R μ ν := by
  intro I _ c _ k l _ _ hkl hεc S hS
  simp only [Prod.fst_add, Prod.snd_add] at hεc ⊢
  obtain ⟨-, hc⟩ := add_lt_top.1 hεc
  have hlS := l.measurable_coe hS
  have hfg := h (fun x ↦ k x S - c.2) (fun y ↦ min 1 (expBudget c.1 * l y S))
    ((k.measurable_coe hS).sub measurable_const) (measurable_const.min (measurable_const.mul hlS))
    (fun _ ↦ tsub_le_self.trans (IsSubProbabilityMeasure.measure_le_one S))
    (fun _ ↦ min_le_left _ _) fun x y hR ↦
      tsub_le_iff_right.2 <| le_add_of_min_expBudget_mul_le
        (IsSubProbabilityMeasure.measure_le_one S)
        (by
          simpa only [Prod.fst_add, Prod.snd_add, expBudget_add, mul_assoc, add_assoc]
            using hkl x y (add_lt_top.2 ⟨hR, hc⟩) S hS)
  rw [bind_apply hS k.measurable.aemeasurable, bind_apply hS l.measurable.aemeasurable,
    expBudget_add]
  calc ∫⁻ x, k x S ∂μ
      ≤ ∫⁻ x, k x S - c.2 ∂μ + c.2 := IsSubProbabilityMeasure.lintegral_le_tsub_add _ _
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
  rw [GradedLifting.Rel, codensity_dp_iff hε]
  refine forall₂_congr fun f g ↦ forall₄_congr fun _ _ _ _ ↦ imp_congr_left <|
    forall₂_congr fun x y ↦ ?_
  by_cases hS : S x y <;> simp [hS]

/-- On pairs of finite cost related by `S`, the indicator of `T` is bounded by the cost-weighted
indicator of `T'`, plus the additive cost. -/
theorem indicator_le_relCost {S : X → Y → Prop} {T : Set X} {T' : Set Y}
    (hS : ∀ x y, S x y → x ∈ T → y ∈ T') {x : X} {y : Y}
    (hxy : (relCost (B := ℝ≥0∞ × ℝ≥0∞) S x y).1 < ⊤) :
    T.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤
      expBudget (relCost (B := ℝ≥0∞ × ℝ≥0∞) S x y).1 * T'.indicator (fun _ ↦ (1 : ℝ≥0∞)) y +
        (relCost (B := ℝ≥0∞ × ℝ≥0∞) S x y).2 := by
  have hxy' : S x y := (relCost_lt_top_iff (B := ℝ≥0∞ × ℝ≥0∞)).1
    (by simpa [Prod.lt_iff] using Or.inl hxy)
  by_cases hx : x ∈ T <;> simp [hxy', hx, hS x y hxy']

/-- A DP lifting at a finite multiplier bounds an event by `e^ε` times its image, plus `δ`. -/
theorem dp_measure_le_add (hε : ε ≠ ⊤) (h : (codensity dp).Rel (ε, δ) S μ ν) {T : Set X}
    {T' : Set Y} (hT : MeasurableSet T) (hT' : MeasurableSet T')
    (hS : ∀ x y, S x y → x ∈ T → y ∈ T') : μ T ≤ expBudget ε * ν T' + δ := by
  simpa [lintegral_indicator_const, hT, hT'] using lintegral_le_of_codensity_dp hε h
    (measurable_const.indicator hT) (measurable_const.indicator hT')
    (fun _ ↦ indicator_le_self' (by simp) _) (fun _ ↦ indicator_le_self' (by simp) _)
    fun _ _ hxy ↦ indicator_le_relCost hS hxy

/-- Countable fibers with a pointwise DP bound give a DP codensity lifting of equal images. -/
theorem codensity_dp_of_fiber {Z : Type*} [MeasurableSpace Z] [Countable Z]
    [MeasurableSingletonClass Z] {f : X → Z} {g : Y → Z} (hf : Measurable f) (hg : Measurable g)
    [IsSubProbabilityMeasure μ] (h : ∀ z, μ (f ⁻¹' {z}) ≤ expBudget ε * ν (g ⁻¹' {z})) :
    (codensity dp).Rel (ε, 0) (fun x y ↦ f x = g y) μ ν := by
  rcases eq_or_ne ε ⊤ with rfl | hε
  · exact codensity_dp_top_left
  refine (codensity_dp_rel_iff hε).2 fun h₁ h₂ _ _ _ _ h₁₂ ↦ ?_
  let m : Z → ℝ≥0∞ := fun z ↦ ⨅ y ∈ g ⁻¹' {z}, h₂ y
  have hint (κ : Measure Z) : ∫⁻ z, m z ∂κ = ∑' z, m z * κ {z} := lintegral_countable' _
  calc ∫⁻ x, h₁ x ∂μ
      ≤ ∫⁻ x, m (f x) ∂μ := lintegral_mono fun x ↦ le_iInf₂ fun _ hy ↦ h₁₂ _ _ hy.symm
    _ = ∑' z, m z * μ (f ⁻¹' {z}) := by
        simp [← lintegral_map (f := m) .of_discrete hf, hint,
          map_apply hf (measurableSet_singleton _)]
    _ ≤ ∑' z, m z * (expBudget ε * ν (g ⁻¹' {z})) := ENNReal.tsum_le_tsum fun z ↦ by grw [h z]
    _ = expBudget ε * ∫⁻ y, m (g y) ∂ν := by
        simp [← lintegral_map (f := m) .of_discrete hg, hint,
          map_apply hg (measurableSet_singleton _), ← ENNReal.tsum_mul_left, mul_left_comm]
    _ ≤ expBudget ε * ∫⁻ y, h₂ y ∂ν + 0 := by
        rw [add_zero]; gcongr with y; exact biInf_le h₂ rfl

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
