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

/-- Rescaled Rényi divergences `(D_α - ξ) / α`, maximized over the orders `α ∈ A` and graded
additively by the shift `ξ ≥ 0`. The Rényi divergences are truncated at zero, so negative values
are lost, as in SampCert. -/
noncomputable def concentratedDivergence (A : Set ℝ) :
    GradedDivergence.{u} (Multiplicative ℝ≥0) :=
  fun ξ {_} _ μ ν ↦ ⨆ α ∈ A, (ENNReal.ofReal α)⁻¹ * (renyiDivergence α () μ ν - ξ.toAdd)

/-- The zCDP divergences, graded by `ξ` (Eq. 6). -/
noncomputable abbrev zcdpDivergence : GradedDivergence.{u} (Multiplicative ℝ≥0) :=
  concentratedDivergence (Ioi 1)

/-- The `ω`-tCDP divergence (Eq. 7). -/
noncomputable def tcdpDivergence (ω : ℝ) : GradedDivergence.{u} Unit :=
  fun _ ↦ concentratedDivergence (Ioo 1 ω) 1

namespace concentratedDivergence

variable {A : Set ℝ} {X : Type u} [MeasurableSpace X]

/-- A concentrated divergence bound is a Rényi bound `ξ + α ρ` at every order `α ∈ A`. -/
theorem le_iff (hA : A ⊆ Ioi 1) (ξ : ℝ≥0) {μ ν : Measure X} {ρ : ℝ≥0} :
    concentratedDivergence A (.ofAdd ξ) μ ν ≤ ρ ↔
      ∀ α ∈ A, renyiDiv α μ ν ≤ ((ξ + α * ρ : ℝ) : EReal) := by
  refine iSup₂_le_iff.trans (forall₂_congr fun α hα ↦ ?_)
  have hα : 0 < α := lt_trans one_pos (hA hα)
  have h : (ξ : ℝ≥0∞) + ENNReal.ofReal α * ρ = ENNReal.ofReal (ξ + α * ρ) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hα.le,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  rw [toAdd_ofAdd, ENNReal.inv_mul_le_iff (by simpa) ENNReal.ofReal_ne_top, tsub_le_iff_left, h]
  exact EReal.toENNReal_le_iff_le_coe.trans (by
    rw [EReal.coe_ennreal_ofReal, max_eq_left (by positivity)])

variable (A)

theorem isGraded : (concentratedDivergence.{u} A).IsGraded where
  anti _ _ h _ _ _ _ _ _ := iSup₂_mono fun _ _ ↦
    mul_le_mul_right (tsub_le_tsub_left (ENNReal.coe_le_coe.2 h) _) _

variable (hA : A ⊆ Ioi 1)
include hA

theorem isReflexive : (concentratedDivergence.{u} A).IsReflexive where
  self_le_zero μ _ := iSup₂_le fun α hα ↦ by
    have : Fact (1 < α) := ⟨hA hα⟩
    simp [nonpos_iff_eq_zero.1 (IsReflexive.self_le_zero (Δ := renyiDivergence.{u} α) μ)]

theorem isFunctorial : (concentratedDivergence.{u} A).IsFunctorial where
  map_le ξ _ _ _ _ _ μ ν _ _ hk := iSup₂_mono fun α hα ↦ by
    have : Fact (1 < α) := ⟨hA hα⟩
    exact mul_le_mul_right (tsub_le_tsub_right
      (IsFunctorial.map_le (Δ := renyiDivergence.{u} α) () μ ν hk) _) _

theorem isContinuous : (concentratedDivergence.{u} A).IsContinuous where
  eq_iSup ξ _ _ μ ν _ _ := by
    have := isFunctorial A hA
    refine le_antisymm (iSup₂_le fun α hα ↦ ?_)
      (iSup_le fun _ ↦ iSup₂_le fun _ hk ↦ IsFunctorial.map_le ξ μ ν hk)
    have : Fact (1 < α) := ⟨hA hα⟩
    simp_rw [IsContinuous.eq_iSup (Δ := renyiDivergence.{u} α) () μ ν, ENNReal.iSup_sub,
      ENNReal.mul_iSup]
    exact iSup_mono fun _ ↦ iSup₂_mono fun k _ ↦ le_iSup₂_of_le (f := fun α _ ↦
      (ENNReal.ofReal α)⁻¹ * (renyiDivergence α () (μ.map k) (ν.map k) - _)) α hα le_rfl

theorem isComposable : (concentratedDivergence.{u} A).IsComposable where
  bind_le ξ₁ ξ₂ _ _ _ _ μ₁ μ₂ _ _ κ η _ _ := iSup₂_le fun α hα ↦ by
    have : Fact (1 < α) := ⟨hA hα⟩
    rw [toAdd_mul, ENNReal.coe_add]
    have h := IsComposable.bind_le (Δ := renyiDivergence.{u} α) () () μ₁ μ₂ κ η
    refine (mul_le_mul_right ((tsub_le_tsub_right h _).trans
      add_tsub_add_le_tsub_add_tsub) _).trans ?_
    rw [mul_add, ENNReal.iSup_sub, ENNReal.mul_iSup]
    exact add_le_add (le_iSup₂_of_le α hα le_rfl)
      (iSup_mono fun x ↦ le_iSup₂_of_le (f := fun α _ ↦ (ENNReal.ofReal α)⁻¹ *
        (renyiDivergence α () (κ x) (η x) - _)) α hα le_rfl)

end concentratedDivergence

/-! ### zCDP -/

namespace zcdpDivergence

/-- A zCDP divergence bound is a Rényi bound `ξ + α ρ` at every order `α > 1`. -/
theorem le_iff {X : Type u} [MeasurableSpace X] (ξ : ℝ≥0) {μ ν : Measure X} {ρ : ℝ≥0} :
    zcdpDivergence (.ofAdd ξ) μ ν ≤ ρ ↔ ∀ α, 1 < α → renyiDiv α μ ν ≤ ((ξ + α * ρ : ℝ) : EReal) :=
  concentratedDivergence.le_iff subset_rfl ξ

instance isGraded : zcdpDivergence.{u}.IsGraded := concentratedDivergence.isGraded _
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
theorem le_iff {X : Type u} [MeasurableSpace X] {ω : ℝ} {μ ν : Measure X} {ρ : ℝ≥0} :
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
  bind_le _ _ _ _ _ _ μ₁ μ₂ _ _ κ η _ _ := by
    have := (concentratedDivergence.isComposable (Ioo 1 ω) Ioo_subset_Ioi_self).bind_le 1 1 μ₁ μ₂
      κ η
    rwa [mul_one] at this

end tcdpDivergence
