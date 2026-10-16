module

public import Metrology.Couplings.Divergences.FDivBound

/-! The Rényi divergence as a graded divergence (Approximate Span Liftings, Def. 2.2, Thm. 4.11,
App. C.4). -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory GradedLifting Set Filter Topology
open scoped ENNReal

theorem EReal.mul_finset_sum_of_nonneg {ι : Type*} (s : Finset ι) (c : EReal) {x : ι → EReal}
    (hx : ∀ i ∈ s, 0 ≤ x i) : c * ∑ i ∈ s, x i = ∑ i ∈ s, c * x i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, EReal.left_distrib_of_nonneg (hx j (by simp))
      (Finset.sum_nonneg fun i hi ↦ hx i (by simp [hi])), ih fun i hi ↦ hx i (by simp [hi])]

namespace ProbabilityTheory

variable {X : Type*} [MeasurableSpace X] {f : ℝ → ℝ}

/-- Against the zero measure the `f`-divergence is the mass times the slope at infinity. -/
theorem fDiv_zero_right_eq (μ : Measure X) : fDiv f μ 0 = derivAtTop f * μ univ := by
  simp [fDiv_of_integrable integrable_zero_measure]

/-! ## The weight `t ↦ t ^ α` -/

variable {α : ℝ}

theorem continuousWithinAt_rpow_zero (hα : 0 < α) :
    ContinuousWithinAt (· ^ α : ℝ → ℝ) (Ici 0) 0 :=
  (Real.continuousAt_rpow_const 0 α (.inr hα.le)).continuousWithinAt

theorem derivAtTop_rpow (hα : 1 < α) : derivAtTop (· ^ α) = ⊤ := by
  refine Tendsto.limsup_eq (EReal.tendsto_coe_atTop.comp ?_)
  refine (tendsto_rpow_atTop (sub_pos.2 hα)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  exact Real.rpow_sub_one ht.ne' α

theorem persp_rpow_of_pos (α : ℝ) {p q : ℝ} (hq : 0 < q) :
    persp (· ^ α) p q = ((q * (p / q) ^ α : ℝ) : EReal) :=
  persp_of_ne_zero hq.ne'

theorem persp_rpow_zero_right (hα : 1 < α) {p : ℝ} (hp : 0 < p) : persp (· ^ α) p 0 = ⊤ := by
  rw [persp_zero_right, derivAtTop_rpow hα, EReal.coe_mul_top_of_pos hp]

theorem persp_rpow_zero_left (hα : 0 < α) {q : ℝ} (hq : 0 ≤ q) : persp (· ^ α) 0 q = 0 := by
  rcases hq.eq_or_lt with rfl | hq
  · simp
  · simp [persp_rpow_of_pos α hq, Real.zero_rpow hα.ne']

theorem persp_rpow_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) : 0 ≤ persp (· ^ α) p q :=
  persp_nonneg (fun _ ht ↦ Real.rpow_nonneg ht α) hp hq

/-- The perspective of `t ↦ t ^ α` is multiplicative. -/
theorem persp_rpow_mul (hα : 1 < α) {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) : persp (· ^ α) (a * c) (b * d) = persp (· ^ α) a b * persp (· ^ α) c d := by
  have hα0 : 0 < α := by linarith
  rcases ha.eq_or_lt with rfl | ha
  · simp [persp_rpow_zero_left hα0 (mul_nonneg hb hd), persp_rpow_zero_left hα0 hb]
  rcases hc.eq_or_lt with rfl | hc
  · simp [persp_rpow_zero_left hα0 (mul_nonneg hb hd), persp_rpow_zero_left hα0 hd]
  have hpos {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) : 0 < persp (· ^ α) x y := by
    rcases hy.eq_or_lt with rfl | hy
    · simp [persp_rpow_zero_right hα hx]
    · rw [persp_rpow_of_pos α hy]
      exact EReal.coe_pos.2 (mul_pos hy (Real.rpow_pos_of_pos (div_pos hx hy) _))
  rcases hb.eq_or_lt with rfl | hb
  · rw [zero_mul, persp_rpow_zero_right hα (mul_pos ha hc), persp_rpow_zero_right hα ha,
      EReal.top_mul_of_pos (hpos hc hd)]
  rcases hd.eq_or_lt with rfl | hd
  · rw [mul_zero, persp_rpow_zero_right hα (mul_pos ha hc), persp_rpow_zero_right hα hc,
      EReal.mul_top_of_pos (hpos ha hb.le)]
  rw [persp_rpow_of_pos α (mul_pos hb hd), persp_rpow_of_pos α hb, persp_rpow_of_pos α hd,
    ← EReal.coe_mul, EReal.coe_eq_coe_iff, mul_div_mul_comm,
    Real.mul_rpow (div_pos ha hb).le (div_pos hc hd).le]
  ring

theorem persp_rpow_anti_right (hα : 1 < α) {p q q' : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (h : q ≤ q') :
    persp (· ^ α) p q' ≤ persp (· ^ α) p q := by
  rcases hq.eq_or_lt with rfl | hq
  · rcases hp.eq_or_lt with rfl | hp
    · rw [persp_rpow_zero_left (zero_lt_one.trans hα) h]
      exact persp_rpow_nonneg le_rfl le_rfl
    · rw [persp_rpow_zero_right hα hp]
      exact le_top
  have hpow (r : ℝ) (hr : 0 < r) : r * (p / r) ^ α = p ^ α * r ^ (1 - α) := by
    rw [Real.div_rpow hp hr.le, Real.rpow_sub hr, Real.rpow_one]
    field_simp
  rw [persp_rpow_of_pos α (hq.trans_le h), persp_rpow_of_pos α hq, EReal.coe_le_coe_iff,
    hpow _ (hq.trans_le h), hpow _ hq]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hq h (by linarith))
    (Real.rpow_nonneg hp α)

theorem persp_rpow_mono_left (hα : 1 < α) {p p' q : ℝ} (hp : 0 ≤ p) (h : p ≤ p') (hq : 0 ≤ q) :
    persp (· ^ α) p q ≤ persp (· ^ α) p' q := by
  rcases hq.eq_or_lt with rfl | hq
  · rcases hp.eq_or_lt with rfl | hp
    · rw [persp_rpow_zero_left (zero_lt_one.trans hα) le_rfl]
      exact persp_rpow_nonneg h le_rfl
    · rw [persp_rpow_zero_right hα (hp.trans_le h)]
      exact le_top
  rw [persp_rpow_of_pos α hq, persp_rpow_of_pos α hq, EReal.coe_le_coe_iff]
  gcongr

theorem fDiv_rpow_nonneg {μ ν : Measure X} : 0 ≤ fDiv (· ^ α) μ ν :=
  fDiv_nonneg_of_nonneg fun _ ht ↦ Real.rpow_nonneg ht α

/-- Growing the right measure does not increase the `t ↦ t ^ α` divergence. -/
theorem fDiv_rpow_anti_right (hα : 1 < α) {μ ν ν' : Measure X} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν'] (h : ν ≤ ν') : fDiv (· ^ α) μ ν' ≤ fDiv (· ^ α) μ ν := by
  have := isFiniteMeasure_of_le ν' h
  have hf := convexOn_rpow hα.le
  have hf_cont := continuousWithinAt_rpow_zero (zero_lt_one.trans hα)
  rw [fDiv_eq_iSup_partition hf hf_cont, fDiv_eq_iSup_partition hf hf_cont]
  exact iSup_mono fun n ↦ iSup_mono fun k ↦ iSup_mono fun _ ↦ Finset.sum_le_sum fun i _ ↦
    persp_rpow_anti_right hα ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      (ENNReal.toReal_mono (measure_ne_top ν' _) (Measure.le_iff'.1 h _))

/-- Growing the left measure does not decrease the `t ↦ t ^ α` divergence. -/
theorem fDiv_rpow_mono_left (hα : 1 < α) {μ μ' ν : Measure X} [IsFiniteMeasure μ']
    [IsFiniteMeasure ν] (h : μ ≤ μ') : fDiv (· ^ α) μ ν ≤ fDiv (· ^ α) μ' ν := by
  have := isFiniteMeasure_of_le μ' h
  have hf := convexOn_rpow hα.le
  have hf_cont := continuousWithinAt_rpow_zero (zero_lt_one.trans hα)
  rw [fDiv_eq_iSup_partition hf hf_cont, fDiv_eq_iSup_partition hf hf_cont]
  exact iSup_mono fun n ↦ iSup_mono fun k ↦ iSup_mono fun _ ↦ Finset.sum_le_sum fun i _ ↦
    persp_rpow_mono_left hα ENNReal.toReal_nonneg
      (ENNReal.toReal_mono (measure_ne_top μ' _) (Measure.le_iff'.1 h _)) ENNReal.toReal_nonneg

/-- Between finite spaces the `t ↦ t ^ α` divergence of two compositions is at most that of the
inputs times the largest one of the kernels (App. C.4, by Jensen's inequality). -/
theorem fDiv_rpow_comp_le (hα : 1 < α) {M N : ℕ} (μ₁ μ₂ : Measure (ULift.{u} (Fin M)))
    [IsSubProbabilityMeasure μ₁] [IsSubProbabilityMeasure μ₂]
    (κ η : Kernel (ULift.{u} (Fin M)) (ULift.{u} (Fin N))) [IsSubMarkovKernel κ]
    [IsSubMarkovKernel η] :
    fDiv (· ^ α) (κ ∘ₘ μ₁) (η ∘ₘ μ₂) ≤ fDiv (· ^ α) μ₁ μ₂ * ⨆ j, fDiv (· ^ α) (κ j) (η j) := by
  have hf := convexOn_rpow hα.le
  have hf_cont := continuousWithinAt_rpow_zero (zero_lt_one.trans hα)
  have hb (μ : Measure (ULift.{u} (Fin M))) [IsSubProbabilityMeasure μ]
      (κ : Kernel (ULift.{u} (Fin M)) (ULift.{u} (Fin N))) [IsSubMarkovKernel κ]
      (i : ULift.{u} (Fin N)) :
      ((κ ∘ₘ μ) {i}).toReal = ∑ j, (μ {j}).toReal * (κ j {i}).toReal := by
    rw [Measure.bind_apply (ULift.measurableSet_fin _) κ.measurable.aemeasurable,
      lintegral_fintype, ENNReal.toReal_sum fun _ _ ↦ by finiteness]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [ENNReal.toReal_mul, mul_comm]
  have hP {a b : ℝ≥0∞} : 0 ≤ persp (· ^ α) a.toReal b.toReal :=
    persp_rpow_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  rw [fDiv_eq_sum hf hf_cont, fDiv_eq_sum hf hf_cont]
  simp_rw [hb]
  calc ∑ i, persp (· ^ α) (∑ j, (μ₁ {j}).toReal * (κ j {i}).toReal)
        (∑ j, (μ₂ {j}).toReal * (η j {i}).toReal)
      ≤ ∑ i, ∑ j, persp (· ^ α) ((μ₁ {j}).toReal * (κ j {i}).toReal)
          ((μ₂ {j}).toReal * (η j {i}).toReal) :=
        Finset.sum_le_sum fun i _ ↦ persp_sum_le hf _ (fun _ _ ↦ by positivity)
          fun _ _ ↦ by positivity
    _ = ∑ j, persp (· ^ α) (μ₁ {j}).toReal (μ₂ {j}).toReal *
          ∑ i, persp (· ^ α) (κ j {i}).toReal (η j {i}).toReal := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [EReal.mul_finset_sum_of_nonneg _ _ fun _ _ ↦ hP]
        exact Finset.sum_congr rfl fun i _ ↦ persp_rpow_mul hα ENNReal.toReal_nonneg
          ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    _ ≤ ∑ j, persp (· ^ α) (μ₁ {j}).toReal (μ₂ {j}).toReal *
          ⨆ j, fDiv (· ^ α) (κ j) (η j) := by
        refine Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left ?_ hP
        rw [← fDiv_eq_sum hf hf_cont]
        exact le_iSup (fun j ↦ fDiv (· ^ α) (κ j) (η j)) j
    _ = (∑ j, persp (· ^ α) (μ₁ {j}).toReal (μ₂ {j}).toReal) *
          ⨆ j, fDiv (· ^ α) (κ j) (η j) := by
        rw [mul_comm, EReal.mul_finset_sum_of_nonneg _ _ fun _ _ ↦ hP]
        simp_rw [mul_comm]

end ProbabilityTheory

namespace GradedDivergence

/-! ## The Rényi divergence -/

section renyiThresh

variable {α : ℝ} {ρ : ℝ≥0∞}

/-- The moment threshold `exp ((α - 1) ρ)`, `⊤` at `ρ = ⊤`. -/
noncomputable def renyiThresh (α : ℝ) (ρ : ℝ≥0∞) : EReal :=
  expBudget (ENNReal.ofReal (α - 1) * ρ)

theorem renyiThresh_of_ne_top (hα : 1 ≤ α) (hρ : ρ ≠ ⊤) :
    renyiThresh α ρ = ((Real.exp ((α - 1) * ρ.toReal) : ℝ) : EReal) := by
  rw [renyiThresh, expBudget_of_ne_top (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.2 hα), EReal.coe_ennreal_ofReal,
    max_eq_left (Real.exp_pos _).le]

theorem renyiThresh_top (hα : 1 < α) : renyiThresh α ⊤ = ⊤ := by
  simp [renyiThresh, ENNReal.mul_top (ENNReal.ofReal_pos.2 (sub_pos.2 hα)).ne']

@[simp]
theorem renyiThresh_zero : renyiThresh α 0 = 1 := by
  simp [renyiThresh]

theorem renyiThresh_mono : Monotone (renyiThresh α) := fun _ _ h ↦
  EReal.coe_ennreal_le_coe_ennreal_iff.2 (expBudget_mono (by gcongr))

theorem renyiThresh_add (ρ ρ' : ℝ≥0∞) :
    renyiThresh α (ρ + ρ') = renyiThresh α ρ * renyiThresh α ρ' := by
  rw [renyiThresh, mul_add, expBudget_add, EReal.coe_ennreal_mul, renyiThresh, renyiThresh]

/-- The threshold is right continuous in the budget. -/
theorem le_renyiThresh_of_forall_lt (hα : 1 < α) {x : EReal}
    (h : ∀ ρ', ρ < ρ' → x ≤ renyiThresh α ρ') : x ≤ renyiThresh α ρ := by
  rcases eq_or_ne ρ ⊤ with rfl | hρ
  · simp [renyiThresh_top hα]
  have hlim : Tendsto (fun s : ℝ ↦ ((Real.exp ((α - 1) * (ρ.toReal + s)) : ℝ) : EReal))
      (𝓝[>] 0) (𝓝 ((Real.exp ((α - 1) * (ρ.toReal + 0)) : ℝ) : EReal)) :=
    ((continuous_coe_real_ereal.comp (by fun_prop)).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [renyiThresh_of_ne_top hα.le hρ, ← add_zero ρ.toReal]
  refine ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun s (hs : 0 < s) ↦ ?_)
  have := h (ρ + ENNReal.ofReal s) (ENNReal.lt_add_right hρ (by simpa using hs))
  rwa [renyiThresh_of_ne_top hα.le (by finiteness), ENNReal.toReal_add hρ ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hs.le] at this

end renyiThresh

/-- `D_α(μ ‖ ν) ≤ ρ`, as the moment bound `∫ (dμ/dν)^α dν ≤ e^{(α - 1) ρ}` (Def. 2.2). -/
noncomputable def renyiDivergence (α : ℝ) : GradedDivergence.{u} ℝ≥0∞ :=
  fDivBound Unit (fun _ _ t ↦ t ^ α) fun ρ _ ↦ renyiThresh α ρ

variable {X : Type u} [MeasurableSpace X] {α : ℝ} {ρ : ℝ≥0∞} {μ ν : Measure X}

theorem renyiDivergence_iff : renyiDivergence α ρ μ ν ↔ fDiv (· ^ α) μ ν ≤ renyiThresh α ρ :=
  ⟨fun h ↦ h (), fun h _ ↦ h⟩

/-- At a finite budget, the Rényi divergence bounds the `α`-th moment (Rocq
`codensity_div_form`). -/
theorem renyiDivergence_iff_of_ne_top (hα : 1 ≤ α) (hρ : ρ ≠ ⊤) :
    renyiDivergence α ρ μ ν ↔ fDiv (· ^ α) μ ν ≤ ((Real.exp ((α - 1) * ρ.toReal) : ℝ) : EReal) := by
  rw [renyiDivergence_iff, renyiThresh_of_ne_top hα hρ]

theorem renyiDivergence_top (hα : 1 < α) (μ ν : Measure X) : renyiDivergence α ⊤ μ ν :=
  renyiDivergence_iff.2 (renyiThresh_top hα ▸ le_top)

/-- Point masses with ordered masses are within budget zero. -/
theorem renyiDivergence_zero_smul_dirac (hα : 1 < α) {a a' : ℝ≥0∞} (h : a ≤ a') (ha' : a' ≤ 1) :
    renyiDivergence α 0 (a • dirac PUnit.unit.{u + 1}) (a' • dirac PUnit.unit) := by
  have hα0 : 0 < α := zero_lt_one.trans hα
  have ha'₁ : a' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha'
  have : IsFiniteMeasure (a • dirac PUnit.unit.{u + 1}) := ⟨by simpa using h.trans_lt ha'₁.lt_top⟩
  have : IsFiniteMeasure (a' • dirac PUnit.unit.{u + 1}) := ⟨by simpa using ha'₁.lt_top⟩
  rw [renyiDivergence_iff, renyiThresh_zero,
    fDiv_eq_sum (convexOn_rpow hα.le) (continuousWithinAt_rpow_zero hα0)]
  simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton, Measure.smul_apply,
    dirac_apply_of_mem (mem_singleton _), smul_eq_mul, mul_one]
  have hq : a'.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using ha')
  have hpq : a.toReal ≤ a'.toReal := ENNReal.toReal_mono ha'₁ h
  rcases (ENNReal.toReal_nonneg (a := a')).eq_or_lt with hq0 | hq0
  · rw [← hq0, le_antisymm (hq0 ▸ hpq) ENNReal.toReal_nonneg,
      persp_rpow_zero_left hα0 le_rfl]
    exact zero_le_one
  rw [persp_rpow_of_pos α hq0, ← EReal.coe_one, EReal.coe_le_coe_iff]
  calc a'.toReal * (a.toReal / a'.toReal) ^ α ≤ a'.toReal * 1 := by
        gcongr
        exact Real.rpow_le_one (by positivity) ((div_le_one hq0).2 hpq) hα0.le
    _ ≤ 1 := by rwa [mul_one]

/-! ## Instances -/

section Instances

variable (α) [hα : Fact (1 < α)]

instance isGraded_renyi : (renyiDivergence.{u} α).IsGraded :=
  isGraded_fDivBound (fun _ _ ↦ convexOn_rpow hα.out.le)
    (fun _ _ ↦ continuousWithinAt_rpow_zero (zero_lt_one.trans hα.out))
    (fun _ _ _ _ _ _ ↦ le_rfl) (fun _ _ h _ ↦ renyiThresh_mono h) fun _ ↦ renyiThresh_top hα.out

instance isReflexive_renyi : (renyiDivergence.{u} α).IsReflexive :=
  isReflexive_fDivBound fun _ ↦ by simp

instance isZeroLeft_renyi : (renyiDivergence.{u} α).IsZeroLeft :=
  isZeroLeft_fDivBound fun _ _ ↦ by
    simp [Real.zero_rpow (zero_lt_one.trans hα.out).ne', renyiThresh, EReal.coe_ennreal_nonneg]

/-- The Rényi divergence is left continuous (Rocq `GCFamLim_RDP`). -/
instance isLeftContinuous_renyi : (renyiDivergence.{u} α).IsLeftContinuous :=
  isLeftContinuous_fDivBound (fun _ _ ↦ convexOn_rpow hα.out.le)
    fun _ _ ↦ continuousWithinAt_rpow_zero (zero_lt_one.trans hα.out)

instance isRightMonotone_renyi : (renyiDivergence.{u} α).IsRightMonotone where
  right_mono _ _ _ _ _ _ _ _ hν h :=
    renyiDivergence_iff.2 ((fDiv_rpow_anti_right hα.out hν).trans (renyiDivergence_iff.1 h))

instance isLeftAntitone_renyi : (renyiDivergence.{u} α).IsLeftAntitone where
  left_anti _ _ _ _ _ _ _ _ hμ h :=
    renyiDivergence_iff.2 ((fDiv_rpow_mono_left hα.out hμ).trans (renyiDivergence_iff.1 h))

instance isBudgetClosed_renyi : (renyiDivergence.{u} α).IsBudgetClosed :=
  isBudgetClosed_fDivBound (fun _ _ _ ↦ rfl) fun _ _ _ h ↦ le_renyiThresh_of_forall_lt hα.out h

/-- Moments multiply under composition, so Rényi budgets add (Thm. 4.11, by Thm. 4.6). -/
instance isComposable_renyi : (renyiDivergence.{u} α).IsComposable :=
  isComposable_fDivBound_of_finite (fun _ _ ↦ convexOn_rpow hα.out.le)
    (fun _ _ ↦ continuousWithinAt_rpow_zero (zero_lt_one.trans hα.out))
    (chain := fun a c ↦ ((a.toENNReal * c.toENNReal : ℝ≥0∞) : EReal))
    (fun _ _ _ _ ha hc ↦ EReal.coe_ennreal_le_coe_ennreal_iff.2
      (mul_le_mul' (EReal.toENNReal_le_toENNReal ha) (EReal.toENNReal_le_toENNReal hc)))
    (fun _ _ _ M N _ μ₁ μ₂ _ _ κ η _ _ ↦ by
      have : Nonempty (ULift.{u} (Fin M)) := ⟨⟨0⟩⟩
      have hS : 0 ≤ ⨆ i, fDiv (· ^ α) (κ i) (η i) :=
        le_iSup_of_le (Classical.arbitrary _) fDiv_rpow_nonneg
      rw [EReal.coe_ennreal_mul, EReal.coe_toENNReal fDiv_rpow_nonneg, EReal.coe_toENNReal hS]
      exact fDiv_rpow_comp_le hα.out μ₁ μ₂ κ η)
    (fun b c _ ↦ by rw [renyiThresh_add]; simp [renyiThresh, EReal.coe_ennreal_mul])
    fun _ _ ↦ EReal.coe_ennreal_nonneg _

end Instances

/-! ## The Rényi codensity lifting -/

/-- Below `⊤` no Rényi budget relates a point mass to the zero measure, so none is absorbing
(Rocq `no_GCFTop_RDP`). -/
theorem not_absorbing_codensity_renyi (hα : 1 < α) (hρ : ρ < ⊤) :
    ¬(codensity (renyiDivergence.{u} α)).Absorbing ρ := by
  have : Fact (1 < α) := ⟨hα⟩
  refine not_absorbing_of_refutes fun h ↦ ?_
  have := renyiDivergence_iff.1 <| h (I := PUnit.{u + 1}) (c := 0) (by rwa [add_zero])
    (k := Kernel.id) (l := 0) fun _ _ ↦ by simpa using IsGraded.top (D := renyiDivergence α) _ _
  simp [fDiv_zero_right_eq, derivAtTop_rpow hα, renyiThresh_of_ne_top hα.le hρ.ne] at this

end GradedDivergence
