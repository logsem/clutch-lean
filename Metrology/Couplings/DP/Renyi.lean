module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Metrology.Couplings.DP.FDivergence

/-! The Rényi divergence as a graded divergence (Approximate Span Liftings, Def. 2.2, Thm. 4.11,
App. C.4). -/

@[expose] public section

open MeasureTheory Set Filter Topology Real GradedDivergence
open scoped ENNReal NNReal

universe u

namespace Renyi

variable {X : Type*} [MeasurableSpace X]

/-! ### The Rényi weight -/

theorem convexOn_rpow {α : ℝ} (hα : 1 ≤ α) : ConvexOn ℝ (Ici 0) (WeightFunction.rpow α) :=
  _root_.convexOn_rpow hα

theorem slopeAtTop_rpow {α : ℝ} (hα : 1 < α) : (WeightFunction.rpow α).slopeAtTop = ⊤ := by
  refine Tendsto.limsup_eq (EReal.tendsto_coe_atTop.comp ?_)
  refine (tendsto_rpow_atTop (sub_pos.2 hα)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [WeightFunction.rpow, Real.rpow_sub_one ht.ne']

theorem persp_rpow_of_pos (α : ℝ) {p q : ℝ} (hq : 0 < q) :
    (WeightFunction.rpow α).persp p q = ((q * (p / q) ^ α : ℝ) : EReal) := by
  simp [WeightFunction.persp, hq.ne', WeightFunction.rpow]

theorem persp_rpow_of_zero {α : ℝ} (hα : 1 < α) {p : ℝ} (hp : 0 < p) :
    (WeightFunction.rpow α).persp p 0 = ⊤ := by
  simp [WeightFunction.persp, hp.ne', slopeAtTop_rpow hα, EReal.coe_mul_top_of_pos hp]

theorem persp_rpow_nonneg {α : ℝ} (hα : 1 < α) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    0 ≤ (WeightFunction.rpow α).persp p q := by
  rcases hq.eq_or_lt with rfl | hq
  · rcases hp.eq_or_lt with rfl | hp
    · simp [WeightFunction.persp]
    · simp [persp_rpow_of_zero hα hp]
  · rw [persp_rpow_of_pos α hq]
    exact EReal.coe_nonneg.2 (by positivity)

theorem coe_mul_le_iff {c : ℝ} (hc : 0 < c) {L : EReal} {d : ℝ} :
    (c : EReal) * L ≤ d ↔ L ≤ ((d / c : ℝ) : EReal) := by
  induction L with
  | bot => simp [EReal.coe_mul_bot_of_pos hc]
  | top => simp [EReal.coe_mul_top_of_pos hc]
  | coe l => rw [← EReal.coe_mul, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff, le_div_iff₀ hc,
      mul_comm]

/-- A Rényi divergence bound is a bound on the `t ↦ t ^ α` divergence. -/
theorem renyiDiv_le_iff {α : ℝ} (hα : 1 < α) (μ ν : Measure X) (d : ℝ) :
    renyiDiv α μ ν ≤ d ↔
      (fDiv (.rpow α) μ ν).toENNReal ≤ ENNReal.ofReal (exp ((α - 1) * d)) := by
  rw [renyiDiv, coe_mul_le_iff (inv_pos.2 (sub_pos.2 hα)), ← ENNReal.log_le_log_iff,
    ENNReal.log_ofReal_of_pos (exp_pos _), log_exp, div_inv_eq_mul, mul_comm]

theorem le_coe_toENNReal (x : EReal) : x ≤ (x.toENNReal : EReal) :=
  EReal.coe_toENNReal_eq_max ▸ le_max_right 0 x

theorem persp_rpow_zero_left (α : ℝ) {q : ℝ} (hq : 0 ≤ q) (hα : 0 < α) :
    (WeightFunction.rpow α).persp 0 q = 0 := by
  rcases hq.eq_or_lt with rfl | hq
  · simp [WeightFunction.persp]
  · simp [persp_rpow_of_pos α hq, Real.zero_rpow hα.ne']

/-- The perspective of `t ↦ t ^ α` is multiplicative. -/
theorem persp_rpow_mul {α : ℝ} (hα : 1 < α) {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (WeightFunction.rpow α).persp (a * c) (b * d) =
      (WeightFunction.rpow α).persp a b * (WeightFunction.rpow α).persp c d := by
  have hα0 : 0 < α := by linarith
  rcases ha.eq_or_lt with rfl | ha
  · simp [persp_rpow_zero_left α (mul_nonneg hb hd) hα0, persp_rpow_zero_left α hb hα0]
  rcases hc.eq_or_lt with rfl | hc
  · simp [persp_rpow_zero_left α (mul_nonneg hb hd) hα0, persp_rpow_zero_left α hd hα0]
  have hpos {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) : 0 < (WeightFunction.rpow α).persp x y := by
    rcases hy.eq_or_lt with rfl | hy
    · simp [persp_rpow_of_zero hα hx]
    · rw [persp_rpow_of_pos α hy]
      exact EReal.coe_pos.2 (mul_pos hy (Real.rpow_pos_of_pos (div_pos hx hy) _))
  rcases hb.eq_or_lt with rfl | hb
  · rw [zero_mul, persp_rpow_of_zero hα (mul_pos ha hc), persp_rpow_of_zero hα ha,
      EReal.top_mul_of_pos (hpos hc hd)]
  rcases hd.eq_or_lt with rfl | hd
  · rw [mul_zero, persp_rpow_of_zero hα (mul_pos ha hc), persp_rpow_of_zero hα hc,
      EReal.mul_top_of_pos (hpos ha hb.le)]
  rw [persp_rpow_of_pos α (mul_pos hb hd), persp_rpow_of_pos α hb, persp_rpow_of_pos α hd,
    ← EReal.coe_mul, EReal.coe_eq_coe_iff, mul_div_mul_comm,
    Real.mul_rpow (div_pos ha hb).le (div_pos hc hd).le]
  ring

/-- Multiplication by a nonzero real is continuous on `EReal`. -/
theorem _root_.EReal.continuous_coe_mul {c : ℝ} (hc : c ≠ 0) :
    Continuous fun y : EReal ↦ (c : EReal) * y := by
  have hc : (c : EReal) ≠ 0 := by exact_mod_cast hc
  exact continuous_iff_continuousAt.2 fun y ↦ (EReal.continuousAt_mul (p := (_, y)) (Or.inl hc)
    (Or.inl hc) (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).comp
    (continuous_const.prodMk continuous_id).continuousAt

/-! ### The Rényi transform `x ↦ log x / (α - 1)` -/

/-- The map `x ↦ log x / (α - 1)` turning the `t ↦ t ^ α` divergence into the Rényi
divergence. -/
noncomputable def transform (α : ℝ) (x : EReal) : EReal :=
  ((α - 1)⁻¹ : ℝ) * ENNReal.log x.toENNReal

theorem renyiDiv_eq (α : ℝ) (μ ν : Measure X) :
    renyiDiv α μ ν = transform α (fDiv (.rpow α) μ ν) := rfl

variable {α : ℝ}

theorem monotone_transform (hα : 1 < α) : Monotone (transform α) := fun _ _ h ↦
  mul_le_mul_of_nonneg_left (ENNReal.log_monotone (EReal.toENNReal_le_toENNReal h))
    (EReal.coe_nonneg.2 (inv_nonneg.2 (sub_pos.2 hα).le))

theorem continuous_transform (hα : 1 < α) : Continuous (transform α) :=
  (EReal.continuous_coe_mul (inv_ne_zero (sub_pos.2 hα).ne')).comp
    (ENNReal.continuous_log.comp EReal.continuous_toENNReal)

theorem transform_bot (hα : 1 < α) : transform α ⊥ = ⊥ := by
  simp [transform, EReal.coe_mul_bot_of_pos (inv_pos.2 (sub_pos.2 hα))]

theorem transform_iSup (hα : 1 < α) {ι : Sort*} (g : ι → EReal) :
    transform α (⨆ i, g i) = ⨆ i, transform α (g i) :=
  (monotone_transform hα).map_iSup_of_continuousAt (continuous_transform hα).continuousAt
    (transform_bot hα)

theorem transform_coe_toENNReal (x : EReal) : transform α x.toENNReal = transform α x := by
  simp [transform]

/-- The Rényi transform turns products of nonnegative values into sums. -/
theorem transform_mul (hα : 1 < α) {x y : EReal} (hx : 0 ≤ x) :
    transform α (x * y) = transform α x + transform α y := by
  rw [transform, EReal.toENNReal_mul hx, ENNReal.log_mul_add,
    EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.2 (inv_nonneg.2 (sub_pos.2 hα).le))
      (EReal.coe_ne_top _)]
  rfl

/-! ### Finite spaces -/

/-- On finite spaces, binding is a finite weighted sum. -/
theorem bind_singleton {M N : ℕ} (d : Measure (ULift.{u} (Fin M)))
    (h : ULift.{u} (Fin M) → Measure (ULift.{u} (Fin N))) (i : ULift.{u} (Fin N)) :
    (d.bind h) {i} = ∑ j, h j {i} * d {j} := by
  rw [Measure.bind_apply (ULift.measurableSet_fin _)
    (measurable_of_countable h).aemeasurable, lintegral_fintype]

/-- The `t ↦ t ^ α` divergence of two binds on finite spaces is at most the divergence of the
inputs times the largest divergence of the kernels (App. C.4, by Jensen's inequality). -/
theorem fDiv_rpow_bind_le (hα : 1 < α) {M N : ℕ} (d₁ d₂ : Measure (ULift.{u} (Fin M)))
    [IsSubProbabilityMeasure d₁] [IsSubProbabilityMeasure d₂]
    (h k : ULift.{u} (Fin M) → Measure (ULift.{u} (Fin N))) [∀ j, IsSubProbabilityMeasure (h j)]
    [∀ j, IsSubProbabilityMeasure (k j)] :
    fDiv (.rpow α) (d₁.bind h) (d₂.bind k) ≤
      fDiv (.rpow α) d₁ d₂ * ⨆ j, fDiv (.rpow α) (h j) (k j) := by
  have hcvx := convexOn_rpow hα.le
  have := isSubProbabilityMeasure_bind d₁ h (measurable_of_countable h).aemeasurable
  have := isSubProbabilityMeasure_bind d₂ k (measurable_of_countable k).aemeasurable
  have hb (d : Measure (ULift.{u} (Fin M))) [IsSubProbabilityMeasure d]
      (h : ULift.{u} (Fin M) → Measure (ULift.{u} (Fin N))) [∀ j, IsSubProbabilityMeasure (h j)]
      (i : ULift.{u} (Fin N)) :
      ((d.bind h) {i}).toReal = ∑ j, (d {j}).toReal * (h j {i}).toReal := by
    rw [bind_singleton, ENNReal.toReal_sum fun _ _ ↦ by finiteness]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [ENNReal.toReal_mul, mul_comm]
  set P := WeightFunction.rpow α
  have hP {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ P.persp a b := persp_rpow_nonneg hα ha hb
  rw [fDiv_eq_sum hcvx, fDiv_eq_sum hcvx]
  simp_rw [hb]
  calc ∑ i, P.persp (∑ j, (d₁ {j}).toReal * (h j {i}).toReal)
        (∑ j, (d₂ {j}).toReal * (k j {i}).toReal)
      ≤ ∑ i, ∑ j, P.persp ((d₁ {j}).toReal * (h j {i}).toReal)
          ((d₂ {j}).toReal * (k j {i}).toReal) :=
        Finset.sum_le_sum fun i _ ↦ WeightFunction.persp_sum_le hcvx _
          (fun _ _ ↦ by positivity) fun _ _ ↦ by positivity
    _ = ∑ j, P.persp (d₁ {j}).toReal (d₂ {j}).toReal *
          ∑ i, P.persp (h j {i}).toReal (k j {i}).toReal := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [EReal.mul_finset_sum_of_nonneg _ _ fun _ _ ↦ hP ENNReal.toReal_nonneg
          ENNReal.toReal_nonneg]
        exact Finset.sum_congr rfl fun i _ ↦ persp_rpow_mul hα ENNReal.toReal_nonneg
          ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    _ ≤ ∑ j, P.persp (d₁ {j}).toReal (d₂ {j}).toReal * ⨆ j, fDiv P (h j) (k j) := by
        refine Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left ?_
          (hP ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
        rw [← fDiv_eq_sum hcvx]
        exact le_iSup (fun j ↦ fDiv P (h j) (k j)) j
    _ = (∑ j, P.persp (d₁ {j}).toReal (d₂ {j}).toReal) * ⨆ j, fDiv P (h j) (k j) := by
        rw [mul_comm, EReal.mul_finset_sum_of_nonneg _ _ fun _ _ ↦ hP ENNReal.toReal_nonneg
          ENNReal.toReal_nonneg]
        simp_rw [mul_comm]

theorem fDiv_rpow_nonneg (hα : 1 < α) (μ ν : Measure X) : 0 ≤ fDiv (.rpow α) μ ν :=
  le_iSup₂_of_le 1 (fun _ ↦ 0) <| le_iSup_of_le measurable_const <| Finset.sum_nonneg fun _ _ ↦
    persp_rpow_nonneg hα ENNReal.toReal_nonneg ENNReal.toReal_nonneg

end Renyi

/-! ### The Rényi divergence as a graded divergence -/

open Renyi

/-- The Rényi divergence of order `α`, as a singly graded divergence (Def. 2.2), truncated at
zero. Negative values, possible for subprobability measures, are lost, as in SampCert. -/
noncomputable def renyiDivergence (α : ℝ) : GradedDivergence.{u} Unit :=
  fun _ {_} _ μ ν ↦ (renyiDiv α μ ν).toENNReal

namespace renyiDivergence

variable (α : ℝ)

instance isGraded : (renyiDivergence.{u} α).IsGraded where
  anti _ _ _ _ _ _ _ _ _ := le_rfl

variable {α} in
theorem le_coe_iff {X : Type u} [MeasurableSpace X] {μ ν : Measure X} {ρ : ℝ≥0} :
    renyiDivergence α () μ ν ≤ ρ ↔ renyiDiv α μ ν ≤ (ρ : ℝ) :=
  EReal.toENNReal_le_iff_le_coe.trans (by rw [EReal.coe_nnreal_eq_coe_real])

variable [hα : Fact (1 < α)]

/-- Deterministic post-processing does not increase the Rényi divergence. -/
instance isFunctorial : (renyiDivergence.{u} α).IsFunctorial where
  map_le _ _ _ _ _ _ μ ν _ _ hk :=
    EReal.toENNReal_le_toENNReal (monotone_transform hα.out (fDiv_map_le _ hk μ ν))

/-- A measure is at Rényi divergence zero from itself (Thm. 4.11). -/
instance isReflexive : (renyiDivergence.{u} α).IsReflexive where
  self_le_zero μ _ := by
    refine EReal.toENNReal_le_iff_le_coe.2 ?_
    change transform α (fDiv (.rpow α) μ μ) ≤ (0 : ℝ≥0∞)
    rw [EReal.coe_ennreal_zero, fDiv_self, WeightFunction.rpow, Real.one_rpow, mul_one,
      transform, EReal.real_coe_toENNReal]
    refine mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.2 (inv_nonneg.2 (sub_pos.2 hα.out).le))
      (ENNReal.log_le_zero_iff.2 ?_)
    exact ENNReal.ofReal_le_one.2 (IsSubProbabilityMeasure.toReal_mem_Icc univ).2

/-- The Rényi divergence is the supremum of its pushforwards to finite spaces (Thm. 4.11). -/
instance isContinuous : (renyiDivergence.{u} α).IsContinuous where
  eq_iSup _ X _ μ ν _ _ := by
    simp_rw [renyiDivergence, renyiDiv_eq, fDiv_eq_iSup_map _ μ, transform_iSup hα.out,
      EReal.toENNReal_iSup]

/-- The Rényi divergence is approximable (Thm. 4.11). -/
instance isApproximable : (renyiDivergence.{u} α).IsApproximable where
  tendsto _ X _ N f g _ _ μ₁ μ₂ _ _ hf hg := by
    obtain ⟨J, d, e, hd, he, h⟩ := (fDivFamily.isApproximable (ι := Unit) (fun _ ↦ .rpow α)
      fun _ ↦ Renyi.convexOn_rpow hα.out.le).tendsto () N μ₁ μ₂ hf hg
    refine ⟨J, d, e, hd, he, ?_⟩
    simp only [renyiDivergence, renyiDiv_eq]
    have := ((EReal.continuous_toENNReal.comp ((continuous_transform hα.out).comp
      continuous_coe_ennreal_ereal)).tendsto _).comp h
    simpa only [Function.comp_def, fDivFamily, transform_coe_toENNReal] using this

/-- The Rényi divergence composes between finite spaces (App. C.4). -/
instance isFiniteComposable : (renyiDivergence.{u} α).IsFiniteComposable where
  bind_le _ _ M N μ₁ μ₂ _ _ κ η _ _ := by
    refine (EReal.toENNReal_le_toENNReal ?_).trans <|
      EReal.toENNReal_add_le.trans_eq (congrArg _ (EReal.toENNReal_iSup _))
    change transform α _ ≤ transform α _ + ⨆ i, transform α _
    rw [← transform_iSup hα.out, ← transform_mul hα.out (fDiv_rpow_nonneg hα.out _ _)]
    exact monotone_transform hα.out (fDiv_rpow_bind_le hα.out μ₁ μ₂ κ η)

/-- The Rényi divergence composes adaptively (Thm. 4.11, by Thm. 4.6). -/
instance isComposable : (renyiDivergence.{u} α).IsComposable :=
  IsComposable.of_finite _

end renyiDivergence
