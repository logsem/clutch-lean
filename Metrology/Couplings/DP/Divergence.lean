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

/-- The DP divergences `{Δ^{DP(ε)}}`, graded additively by `ε ≥ 0` (§4.3). The zero measure is at
divergence `⊥` from everything, as for the Rényi divergence. -/
noncomputable def dp : GradedDivergence.{u} (Multiplicative ℝ≥0) := by
  classical
  exact fun ε {_} _ μ ν ↦
    if μ = 0 then ⊥ else (gap ((Multiplicative.toAdd ε : ℝ≥0) : ℝ) μ ν : EReal)

variable {ε : Multiplicative ℝ≥0} {μ ν : Measure X}

@[simp] theorem dp_zero (ν : Measure X) : dp ε 0 ν = ⊥ := by simp [dp]

theorem dp_of_ne_zero (h : μ ≠ 0) : dp ε μ ν = gap ((Multiplicative.toAdd ε : ℝ≥0) : ℝ) μ ν := by
  simp [dp, h]

/-- A DP divergence bound is the DP inequality on events. -/
theorem dp_le_iff {δ : ℝ≥0∞} :
    dp ε μ ν ≤ δ ↔
      Bound (ENNReal.ofReal (Real.exp ((Multiplicative.toAdd ε : ℝ≥0) : ℝ))) δ μ ν := by
  rcases eq_or_ne μ 0 with rfl | h
  · simp [bound_zero_left]
  · rw [dp_of_ne_zero h, EReal.coe_ennreal_le_coe_ennreal_iff, gap_le_iff]

theorem gap_anti {ε ε' : ℝ} (h : ε ≤ ε') (μ ν : Measure X) : gap ε' μ ν ≤ gap ε μ ν :=
  iSup₂_mono fun _ _ ↦ tsub_le_tsub_left
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 h)) _) _

/-- A larger privacy budget gives a smaller divergence. -/
instance : (dp.{u}).IsGraded where
  anti α β h X _ μ ν _ _ := by
    rcases eq_or_ne μ 0 with rfl | hμ
    · simp
    · rw [dp_of_ne_zero hμ, dp_of_ne_zero hμ, EReal.coe_ennreal_le_coe_ennreal_iff]
      exact gap_anti (NNReal.coe_le_coe.2 (Multiplicative.toAdd_le.2 h)) μ ν

/-- A measure is at DP divergence at most zero from itself at budget zero. -/
instance : (dp.{u}).IsReflexive where
  self_le_zero μ _ := by
    rcases eq_or_ne μ 0 with rfl | hμ
    · simp
    · rw [dp_of_ne_zero hμ, toAdd_one, NNReal.coe_zero]
      simp [gap]

/-- Deterministic post-processing does not increase the DP divergence. -/
instance : (dp.{u}).IsFunctorial where
  map_le α X Y _ _ k μ ν _ _ hk := by
    rcases eq_or_ne (μ.map k) 0 with h | h
    · simp [h]
    have hμ : μ ≠ 0 := fun h0 ↦ h (by simp [h0])
    rw [dp_of_ne_zero h, dp_of_ne_zero hμ, EReal.coe_ennreal_le_coe_ennreal_iff]
    refine iSup₂_le fun S hS ↦ le_iSup₂_of_le (k ⁻¹' S) (hk hS) ?_
    rw [Measure.map_apply hk hS, Measure.map_apply hk hS]

/-- Adaptive composition adds DP budgets and slacks (DP composition). -/
instance : (dp.{u}).IsComposable where
  bind_le α β X Y _ _ μ₁ μ₂ _ _ f g _ _ hf hg := by
    rcases eq_or_ne (μ₁.bind f) 0 with h0 | h0
    · simp [h0]
    have hμ₁ : μ₁ ≠ 0 := fun h ↦ h0 (by simp [h])
    obtain ⟨x₀, hx₀⟩ : ∃ x, f x ≠ 0 := by
      by_contra! h
      exact h0 (by simp [funext h])
    set B := ⨆ x, dp β (f x) (g x)
    have hB : 0 ≤ B :=
      le_iSup_of_le x₀ (by rw [dp_of_ne_zero hx₀]; exact EReal.coe_ennreal_nonneg _)
    have h₂ (x : X) :
        Bound (ENNReal.ofReal (Real.exp ((Multiplicative.toAdd β : ℝ≥0) : ℝ))) B.toENNReal
        (f x) (g x) := by
      rcases eq_or_ne (f x) 0 with hx | hx
      · rw [hx]
        exact bound_zero_left _ _ _
      · refine gap_le_iff.1 ?_
        rw [← EReal.toENNReal_coe (x := gap _ _ _), ← dp_of_ne_zero hx]
        exact EReal.toENNReal_le_toENNReal (le_iSup (fun x ↦ dp β (f x) (g x)) x)
    have hbind := (bound_gap ((Multiplicative.toAdd α : ℝ≥0) : ℝ) μ₁ μ₂).bind hf hg h₂
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add] at hbind
    rw [dp_of_ne_zero h0, dp_of_ne_zero hμ₁, ← EReal.coe_toENNReal hB, ← EReal.coe_ennreal_add,
      EReal.coe_ennreal_le_coe_ennreal_iff, toAdd_mul, NNReal.coe_add]
    exact gap_le_iff.2 hbind

/-- The DP divergence is the supremum of its pushforwards to finite spaces. -/
instance : (dp.{u}).IsContinuous where
  eq_iSup α X _ μ ν _ _ := by
    rcases eq_or_ne μ 0 with rfl | hμ
    · simp
    apply le_antisymm
    · classical
      set R := ⨆ (n : ℕ) (k : X → ULift.{u} (Fin n)) (_ : Measurable k),
        dp α (μ.map k) (ν.map k)
      have hS (S : Set X) (hS : MeasurableSet S) :
          ((μ S - ENNReal.ofReal (Real.exp ((Multiplicative.toAdd α : ℝ≥0) : ℝ)) * ν S :
            ℝ≥0∞) : EReal) ≤ R := by
        let k : X → ULift.{u} (Fin 2) := fun x ↦ if x ∈ S then ⟨0⟩ else ⟨1⟩
        have hk : Measurable k := measurable_const.ite hS measurable_const
        have hT : MeasurableSet ({⟨0⟩} : Set (ULift.{u} (Fin 2))) :=
          (measurable_down : Measurable (ULift.down : ULift.{u} (Fin 2) → Fin 2))
            (measurableSet_singleton 0)
        have hpre : k ⁻¹' {⟨0⟩} = S := by ext x; by_cases hx : x ∈ S <;> simp [k, hx]
        refine le_iSup_of_le 2 <| le_iSup_of_le k <| le_iSup_of_le hk ?_
        rw [dp_of_ne_zero ((Measure.map_ne_zero_iff hk.aemeasurable).2 hμ),
          EReal.coe_ennreal_le_coe_ennreal_iff]
        refine le_iSup₂_of_le _ hT ?_
        rw [Measure.map_apply hk hT, Measure.map_apply hk hT, hpre]
      have hR : 0 ≤ R := (EReal.coe_ennreal_nonneg _).trans (hS ∅ .empty)
      rw [dp_of_ne_zero hμ, ← EReal.coe_toENNReal hR, EReal.coe_ennreal_le_coe_ennreal_iff]
      refine iSup₂_le fun S hS' ↦ ?_
      rw [← EReal.toENNReal_coe (x := μ S - _)]
      exact EReal.toENNReal_le_toENNReal (hS S hS')
    · exact iSup_le fun n ↦ iSup_le fun k ↦ iSup_le fun hk ↦ IsFunctorial.map_le α μ ν hk

end DPDiv
