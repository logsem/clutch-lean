module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Metrology.Couplings.DifferentialPrivacy

/-! The `(ε, δ)`-DP inequality between measures, and the largest event gap it bounds. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace DPDiv

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The DP inequality `μ S ≤ c ν S + δ` on every measurable event. -/
def Bound (c δ : ℝ≥0∞) (μ ν : Measure X) : Prop :=
  ∀ S, MeasurableSet S → μ S ≤ c * ν S + δ

/-- The largest gap `μ S - e^ε ν S` over measurable events. -/
noncomputable def gap (ε : ℝ) (μ ν : Measure X) : ℝ≥0∞ :=
  ⨆ (S : Set X) (_ : MeasurableSet S), μ S - ENNReal.ofReal (Real.exp ε) * ν S

theorem gap_le_iff {ε : ℝ} {δ : ℝ≥0∞} {μ ν : Measure X} :
    gap ε μ ν ≤ δ ↔ Bound (ENNReal.ofReal (Real.exp ε)) δ μ ν := by
  simp only [gap, iSup₂_le_iff, tsub_le_iff_right, Bound, add_comm]

theorem bound_gap (ε : ℝ) (μ ν : Measure X) :
    Bound (ENNReal.ofReal (Real.exp ε)) (gap ε μ ν) μ ν :=
  gap_le_iff.1 le_rfl

theorem Bound.mono {c c' δ δ' : ℝ≥0∞} {μ ν : Measure X} (h : Bound c δ μ ν) (hc : c ≤ c')
    (hδ : δ ≤ δ') : Bound c' δ' μ ν :=
  fun S hS ↦ (h S hS).trans (by gcongr)

theorem bound_zero_left (c δ : ℝ≥0∞) (ν : Measure X) : Bound c δ 0 ν :=
  fun _ _ ↦ by simp

/-- DP inequalities are preserved by measurable post-processing. -/
theorem Bound.map {c δ : ℝ≥0∞} {μ ν : Measure X} (h : Bound c δ μ ν) {f : X → Y}
    (hf : Measurable f) : Bound c δ (μ.map f) (ν.map f) := fun S hS ↦ by
  simpa only [Measure.map_apply hf hS] using h _ (hf hS)

/-- The gap equals the DP `f`-divergence on finite measures. -/
theorem fDiv_dp_eq_gap (ε : ℝ) (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv (.dp ε) μ ν = gap ε μ ν := by
  rw [fDiv_dp_eq_iSup]
  set R := ⨆ (S : Set X) (_ : MeasurableSet S),
    (((μ S).toReal - Real.exp ε * (ν S).toReal : ℝ) : EReal)
  have hR : 0 ≤ R := le_iSup₂_of_le ∅ .empty (by simp)
  have hterm (S : Set X) : ((μ S - ENNReal.ofReal (Real.exp ε) * ν S : ℝ≥0∞) : EReal) =
      ((max 0 ((μ S).toReal - Real.exp ε * (ν S).toReal) : ℝ) : EReal) := by
    rw [← EReal.coe_ennreal_toReal (by finiteness), EReal.coe_eq_coe_iff]
    rcases le_total (ENNReal.ofReal (Real.exp ε) * ν S) (μ S) with h | h
    · rw [ENNReal.toReal_sub_of_le h (by finiteness), ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (Real.exp_pos ε).le, max_eq_right]
      rw [sub_nonneg, ← ENNReal.toReal_ofReal (Real.exp_pos ε).le, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (by finiteness) h
    · rw [tsub_eq_zero_of_le h, max_eq_left, ENNReal.toReal_zero]
      rw [sub_nonpos, ← ENNReal.toReal_ofReal (Real.exp_pos ε).le, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (by finiteness) h
  apply le_antisymm
  · refine iSup₂_le fun S hS ↦ ?_
    refine (EReal.coe_le_coe_iff.2 (le_max_right 0 _)).trans ?_
    rw [← hterm]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.2 (le_iSup₂ (f := fun S (_ : MeasurableSet S) ↦
      μ S - ENNReal.ofReal (Real.exp ε) * ν S) S hS)
  · rw [← EReal.coe_toENNReal hR, EReal.coe_ennreal_le_coe_ennreal_iff]
    refine iSup₂_le fun S hS ↦ ?_
    rw [← EReal.toENNReal_coe (x := μ S - _), hterm]
    refine EReal.toENNReal_le_toENNReal (max_le hR (le_iSup₂_of_le S hS le_rfl))

/-- A DP inequality on events transfers to `[0, 1]`-valued test functions (by the layer cake
formula). -/
theorem Bound.lintegral_le {c δ : ℝ≥0∞} {μ ν : Measure X} (h : Bound c δ μ ν) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, f x ≤ 1) : ∫⁻ x, f x ∂μ ≤ c * ∫⁻ x, f x ∂ν + δ := by
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
  have hgS : Measurable fun x ↦ g x S := (Measure.measurable_coe hS).comp hg
  have hpt (x : X) : f x S ≤ min 1 (c₂ * g x S) + δ₂ := by
    rcases le_total (c₂ * g x S) 1 with h | h
    · rw [min_eq_right h]
      exact h₂ x S hS
    · rw [min_eq_left h]
      exact ((measure_mono (subset_univ S)).trans
        IsSubProbabilityMeasure.measure_univ_le_one).trans le_self_add
  rw [Measure.bind_apply hS hf.aemeasurable, Measure.bind_apply hS hg.aemeasurable]
  calc ∫⁻ x, f x S ∂μ₁
      ≤ ∫⁻ x, min 1 (c₂ * g x S) + δ₂ ∂μ₁ := lintegral_mono hpt
    _ ≤ ∫⁻ x, min 1 (c₂ * g x S) ∂μ₁ + δ₂ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
        gcongr
        exact mul_le_of_le_one_right' IsSubProbabilityMeasure.measure_univ_le_one
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
    _ ≤ c₁ * (c₂ * μ₃ S + δ₂) + δ₁ := by gcongr; exact h₂ S hS
    _ = c₁ * c₂ * μ₃ S + (c₁ * δ₂ + δ₁) := by ring

end DPDiv
