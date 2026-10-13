module

public import Metrology.Couplings.DP.Basic

/-! The graded family of DP divergences and its basic properties (Approximate Span Liftings,
Thm. 4.10). -/

@[expose] public section

open MeasureTheory Set GradedDivergence
open scoped ENNReal NNReal

namespace DPDiv

universe u

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]

/-- The DP divergences `{Δ^{DP(ε)}}`, graded additively by `ε ≥ 0` (§4.3). -/
noncomputable def dp : GradedDivergence.{u} (Multiplicative ℝ≥0) :=
  fun ε {_} _ μ ν ↦ gap ((Multiplicative.toAdd ε : ℝ≥0) : ℝ) μ ν

variable {ε : Multiplicative ℝ≥0} {μ ν : Measure X}

theorem dp_apply : dp ε μ ν = gap ((Multiplicative.toAdd ε : ℝ≥0) : ℝ) μ ν := rfl

/-- A DP divergence bound is the DP inequality on events. -/
theorem dp_le_iff {δ : ℝ≥0∞} :
    dp ε μ ν ≤ δ ↔
      Bound (ENNReal.ofReal (Real.exp ((Multiplicative.toAdd ε : ℝ≥0) : ℝ))) δ μ ν :=
  gap_le_iff

theorem gap_anti {ε ε' : ℝ} (h : ε ≤ ε') (μ ν : Measure X) : gap ε' μ ν ≤ gap ε μ ν :=
  iSup₂_mono fun _ _ ↦ tsub_le_tsub_left
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 h)) _) _

/-- A larger privacy budget gives a smaller divergence. -/
instance isGraded_dp : (dp.{u}).IsGraded where
  anti _ _ h _ _ μ ν _ _ := gap_anti (NNReal.coe_le_coe.2 (Multiplicative.toAdd_le.2 h)) μ ν

/-- A measure is at DP divergence zero from itself at budget zero. -/
instance isReflexive_dp : (dp.{u}).IsReflexive where
  self_le_zero μ _ := by simp [dp_apply, gap]

/-- Deterministic post-processing does not increase the DP divergence. -/
instance isFunctorial_dp : (dp.{u}).IsFunctorial where
  map_le α X Y _ _ k μ ν _ _ hk := iSup₂_le fun S hS ↦ le_iSup₂_of_le (k ⁻¹' S) (hk hS) <| by
    rw [Measure.map_apply hk hS, Measure.map_apply hk hS]

/-- Adaptive composition adds DP budgets and slacks (DP composition). -/
instance isComposable_dp : (dp.{u}).IsComposable where
  bind_le α β X Y _ _ μ₁ μ₂ _ _ κ η _ _ := by
    have h₂ (x : X) : Bound (ENNReal.ofReal (Real.exp ((Multiplicative.toAdd β : ℝ≥0) : ℝ)))
        (⨆ x, dp β (κ x) (η x)) (κ x) (η x) :=
      gap_le_iff.1 (le_iSup (fun x ↦ dp β (κ x) (η x)) x)
    have hbind := (bound_gap ((Multiplicative.toAdd α : ℝ≥0) : ℝ) μ₁ μ₂).bind κ.measurable
      η.measurable h₂
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add] at hbind
    rw [dp_apply, toAdd_mul, NNReal.coe_add]
    exact gap_le_iff.2 hbind

/-- The DP divergence is the supremum of its pushforwards to finite spaces. -/
instance isContinuous_dp : (dp.{u}).IsContinuous where
  eq_iSup α X _ μ ν _ _ := by
    refine le_antisymm (iSup₂_le fun S hS ↦ ?_)
      (iSup_le fun n ↦ iSup_le fun k ↦ iSup_le fun hk ↦ IsFunctorial.map_le α μ ν hk)
    classical
    let k : X → ULift.{u} (Fin 2) := fun x ↦ if x ∈ S then ⟨0⟩ else ⟨1⟩
    have hk : Measurable k := measurable_const.ite hS measurable_const
    have hT : MeasurableSet ({⟨0⟩} : Set (ULift.{u} (Fin 2))) :=
      (measurable_down : Measurable (ULift.down : ULift.{u} (Fin 2) → Fin 2))
        (measurableSet_singleton 0)
    have hpre : k ⁻¹' {⟨0⟩} = S := by ext x; by_cases hx : x ∈ S <;> simp [k, hx]
    refine le_iSup_of_le 2 <| le_iSup_of_le k <| le_iSup_of_le hk <| le_iSup₂_of_le _ hT ?_
    rw [Measure.map_apply hk hT, Measure.map_apply hk hT, hpre]

end DPDiv
