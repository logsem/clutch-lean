module

public import Metrology.Couplings.DP.Renyi

/-! Concentrated differential privacy as graded divergences (Approximate Span Liftings, Eqs. 6
and 7, Thms. 4.12 and 4.13).

The zCDP and tCDP divergences are both suprema of shifted, rescaled Rényi divergences
`(D_α - ξ) / α` over a range `A` of orders: all `α > 1` for zCDP, and `1 < α < ω` for tCDP. Their
properties follow from those of the Rényi divergences, order by order. -/

@[expose] public section

open MeasureTheory Set GradedDivergence Renyi
open scoped ENNReal NNReal

universe u

namespace EReal

variable {c : ℝ} (ξ : ℝ)

theorem monotone_coe_mul_sub (hc : 0 ≤ c) : Monotone fun x : EReal ↦ (c : EReal) * (x - ξ) :=
  fun _ _ h ↦ mul_le_mul_of_nonneg_left (EReal.sub_le_sub h le_rfl) (EReal.coe_nonneg.2 hc)

theorem continuous_coe_mul_sub (hc : c ≠ 0) : Continuous fun x : EReal ↦ (c : EReal) * (x - ξ) := by
  have hsub : Continuous fun x : EReal ↦ x + ((-ξ : ℝ) : EReal) :=
    continuous_iff_continuousAt.2 fun x ↦ (EReal.continuousAt_add (p := (x, ((-ξ : ℝ) : EReal)))
      (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))).comp
      (f := fun y : EReal ↦ (y, ((-ξ : ℝ) : EReal))) (by fun_prop)
  convert (continuous_coe_mul hc).comp hsub using 3
  rw [Function.comp_apply, sub_eq_add_neg, EReal.coe_neg]

theorem coe_mul_sub_iSup (hc : 0 < c) {ι : Sort*} (g : ι → EReal) :
    (c : EReal) * ((⨆ i, g i) - ξ) = ⨆ i, (c : EReal) * (g i - ξ) :=
  (monotone_coe_mul_sub ξ hc.le).map_iSup_of_continuousAt
    (continuous_coe_mul_sub ξ hc.ne').continuousAt (by simp [EReal.coe_mul_bot_of_pos hc])

theorem coe_mul_sub_add_le (hc : 0 ≤ c) {x a b : EReal} (h : x ≤ a + b) (ξ₁ ξ₂ : ℝ) :
    (c : EReal) * (x - ((ξ₁ + ξ₂ : ℝ) : EReal)) ≤ c * (a - ξ₁) + c * (b - ξ₂) := by
  rw [← EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.2 hc) (EReal.coe_ne_top c)]
  refine (monotone_coe_mul_sub _ hc h).trans_eq (congrArg _ ?_)
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, ← EReal.coe_neg, ← EReal.coe_neg,
    ← EReal.coe_neg, _root_.neg_add, EReal.coe_add, add_add_add_comm]

end EReal

/-- Rescaled Rényi divergences `(D_α - ξ) / α`, maximized over the orders `α ∈ A` and graded
additively by the shift `ξ ≥ 0`. -/
noncomputable def concentratedDivergence (A : Set ℝ) :
    GradedDivergence.{u} (Multiplicative ℝ≥0) :=
  fun ξ {_} _ μ ν ↦ ⨆ α ∈ A, ((α⁻¹ : ℝ) : EReal) * (renyiDiv α μ ν - (ξ.toAdd : ℝ))

/-- The zCDP divergences, graded by `ξ` (Eq. 6). -/
noncomputable abbrev zcdpDivergence : GradedDivergence.{u} (Multiplicative ℝ≥0) :=
  concentratedDivergence (Ioi 1)

/-- The `ω`-tCDP divergence (Eq. 7). -/
noncomputable def tcdpDivergence (ω : ℝ) : GradedDivergence.{u} Unit :=
  fun _ ↦ concentratedDivergence (Ioo 1 ω) 1

namespace concentratedDivergence

variable {A : Set ℝ} {X : Type u} [MeasurableSpace X]

/-- A concentrated divergence bound is a Rényi bound `ξ + α ρ` at every order `α ∈ A`. -/
theorem le_iff (hA : A ⊆ Ioi 1) (ξ : ℝ≥0) {μ ν : Measure X} {ρ : ℝ} :
    concentratedDivergence A (.ofAdd ξ) μ ν ≤ ρ ↔
      ∀ α ∈ A, renyiDiv α μ ν ≤ ((ξ + α * ρ : ℝ) : EReal) := by
  refine iSup₂_le_iff.trans (forall₂_congr fun α hα ↦ ?_)
  have hα : 0 < α := lt_trans one_pos (hA hα)
  rw [toAdd_ofAdd, coe_mul_le_iff (inv_pos.2 hα),
    EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _)),
    ← EReal.coe_add, div_inv_eq_mul, add_comm, mul_comm]

variable (A) (hA : A ⊆ Ioi 1)
include hA

theorem isGraded : (concentratedDivergence.{u} A).IsGraded where
  anti _ _ h _ _ _ _ _ _ := iSup₂_mono fun _ hα ↦ mul_le_mul_of_nonneg_left
    (EReal.sub_le_sub le_rfl (EReal.coe_le_coe_iff.2 (NNReal.coe_le_coe.2 h)))
    (EReal.coe_nonneg.2 (inv_nonneg.2 (lt_trans one_pos (hA hα)).le))

theorem isReflexive : (concentratedDivergence.{u} A).IsReflexive where
  self_le_zero μ _ := iSup₂_le fun α hα ↦ by
    have : Fact (1 < α) := ⟨hA hα⟩
    rw [toAdd_one, NNReal.coe_zero, EReal.coe_zero, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos
      (EReal.coe_nonneg.2 (inv_nonneg.2 (lt_trans one_pos (hA hα)).le))
      (IsReflexive.self_le_zero (Δ := renyiDivergence.{u} α) μ)

theorem isFunctorial : (concentratedDivergence.{u} A).IsFunctorial where
  map_le ξ _ _ _ _ _ μ ν _ _ hk := iSup₂_mono fun α hα ↦ by
    have : Fact (1 < α) := ⟨hA hα⟩
    exact EReal.monotone_coe_mul_sub _ (inv_nonneg.2 (lt_trans one_pos (hA hα)).le)
      (IsFunctorial.map_le (Δ := renyiDivergence.{u} α) () μ ν hk)

theorem isContinuous : (concentratedDivergence.{u} A).IsContinuous where
  eq_iSup ξ _ _ μ ν _ _ := by
    have := isFunctorial A hA
    refine le_antisymm (iSup₂_le fun α hα ↦ ?_)
      (iSup_le fun _ ↦ iSup₂_le fun _ hk ↦ IsFunctorial.map_le ξ μ ν hk)
    have : Fact (1 < α) := ⟨hA hα⟩
    have hα' : 0 < α⁻¹ := inv_pos.2 (lt_trans one_pos (hA hα))
    change _ * (renyiDivergence α () μ ν - _) ≤ _
    simp_rw [IsContinuous.eq_iSup (Δ := renyiDivergence.{u} α) () μ ν,
      EReal.coe_mul_sub_iSup _ hα']
    exact iSup_mono fun _ ↦ iSup₂_mono fun k _ ↦ le_iSup₂_of_le
      (f := fun α _ ↦ ((α⁻¹ : ℝ) : EReal) * (renyiDiv α (μ.map k) (ν.map k) - _)) α hα le_rfl

theorem isComposable : (concentratedDivergence.{u} A).IsComposable where
  bind_le ξ₁ ξ₂ _ _ _ _ μ₁ μ₂ _ _ f g _ _ hf hg := iSup₂_le fun α hα ↦ by
    have : Fact (1 < α) := ⟨hA hα⟩
    have hα' : 0 < α⁻¹ := inv_pos.2 (lt_trans one_pos (hA hα))
    refine (EReal.coe_mul_sub_add_le hα'.le
      (IsComposable.bind_le (Δ := renyiDivergence.{u} α) () () μ₁ μ₂ hf hg) _ _).trans ?_
    rw [EReal.coe_mul_sub_iSup _ hα']
    exact add_le_add (le_iSup₂_of_le α hα le_rfl)
      (iSup_mono fun x ↦ le_iSup₂_of_le (f := fun α _ ↦ ((α⁻¹ : ℝ) : EReal) *
        (renyiDiv α (f x) (g x) - _)) α hα le_rfl)

end concentratedDivergence

/-! ### zCDP -/

namespace zcdpDivergence

/-- A zCDP divergence bound is a Rényi bound `ξ + α ρ` at every order `α > 1`. -/
theorem le_iff {X : Type u} [MeasurableSpace X] (ξ : ℝ≥0) {μ ν : Measure X} {ρ : ℝ} :
    zcdpDivergence (.ofAdd ξ) μ ν ≤ ρ ↔ ∀ α, 1 < α → renyiDiv α μ ν ≤ ((ξ + α * ρ : ℝ) : EReal) :=
  concentratedDivergence.le_iff subset_rfl ξ

instance isGraded : zcdpDivergence.{u}.IsGraded := concentratedDivergence.isGraded _ subset_rfl
instance isReflexive : zcdpDivergence.{u}.IsReflexive :=
  concentratedDivergence.isReflexive _ subset_rfl
instance isFunctorial : zcdpDivergence.{u}.IsFunctorial :=
  concentratedDivergence.isFunctorial _ subset_rfl
instance isContinuous : zcdpDivergence.{u}.IsContinuous :=
  concentratedDivergence.isContinuous _ subset_rfl

/-- The zCDP divergences are reflexive, continuous, composable and additive (Thm. 4.12). -/
instance isComposable : zcdpDivergence.{u}.IsComposable :=
  concentratedDivergence.isComposable _ subset_rfl

end zcdpDivergence

/-! ### tCDP -/

namespace tcdpDivergence

/-- A tCDP divergence bound is a Rényi bound `α ρ` at every order `1 < α < ω`. -/
theorem le_iff {X : Type u} [MeasurableSpace X] {ω : ℝ} {μ ν : Measure X} {ρ : ℝ} :
    tcdpDivergence ω () μ ν ≤ ρ ↔ ∀ α, 1 < α → α < ω → renyiDiv α μ ν ≤ ((α * ρ : ℝ) : EReal) := by
  refine (concentratedDivergence.le_iff Ioo_subset_Ioi_self 0).trans ?_
  simp only [NNReal.coe_zero, zero_add, mem_Ioo, and_imp]

variable (ω : ℝ)

instance isGraded : (tcdpDivergence.{u} ω).IsGraded where
  anti _ _ _ _ _ _ _ _ _ := le_rfl

instance isReflexive : (tcdpDivergence.{u} ω).IsReflexive where
  self_le_zero := (concentratedDivergence.isReflexive _ Ioo_subset_Ioi_self).self_le_zero

instance isFunctorial : (tcdpDivergence.{u} ω).IsFunctorial where
  map_le _ _ _ _ _ _ μ ν _ _ hk :=
    (concentratedDivergence.isFunctorial _ Ioo_subset_Ioi_self).map_le 1 μ ν hk

instance isContinuous : (tcdpDivergence.{u} ω).IsContinuous where
  eq_iSup _ := (concentratedDivergence.isContinuous _ Ioo_subset_Ioi_self).eq_iSup 1

/-- The tCDP divergences are reflexive, continuous, composable and additive (Thm. 4.13). -/
instance isComposable : (tcdpDivergence.{u} ω).IsComposable where
  bind_le _ _ _ _ _ _ μ₁ μ₂ _ _ _ _ _ _ hf hg := by
    have := (concentratedDivergence.isComposable (Ioo 1 ω) Ioo_subset_Ioi_self).bind_le 1 1 μ₁ μ₂
      hf hg
    rwa [mul_one] at this

end tcdpDivergence
