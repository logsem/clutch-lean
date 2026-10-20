module

public import Metrology.Couplings.Divergences.Fill
public import Metrology.Couplings.Divergences.Hellinger
public import Metrology.Couplings.Divergences.Kl

/-! # Filled KL

`fill klDivergence` (Rocq `FillDiv` at KL) is graded, reflexive, zero-left, composable, left
continuous and budget closed on all measurable spaces. The proofs avoid choosing fillings: a fill
bound is equivalent to the Donsker–Varadhan test bound `KlDualBound` (`fill_kl_iff`), whose tests
compose, pass to suprema and close. -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory Set Filter Topology InformationTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-! ## The test bound -/

/-- Every bounded nonnegative test `h` has `∫ h dm ≤ r + log ∫ exp h dQ`: the Donsker–Varadhan
bound for some probability measure above `m` (`exists_le_klDiv_le_of_klDualBound`). -/
def KlDualBound (r : ℝ≥0∞) (m Q : Measure Ω) : Prop :=
  ∀ ⦃h : Ω → ℝ⦄, Measurable h → (∀ ω, 0 ≤ h ω) → BddAbove (range h) →
    ∫⁻ ω, ENNReal.ofReal (h ω) ∂m ≤
      r + ENNReal.ofReal (Real.log (∫⁻ ω, ENNReal.ofReal (Real.exp (h ω)) ∂Q).toReal)

theorem KlDualBound.mono {r r' : ℝ≥0∞} {m Q : Measure Ω} (h : KlDualBound r m Q) (hr : r ≤ r') :
    KlDualBound r' m Q :=
  fun _ hm h0 hb ↦ (h hm h0 hb).trans (by gcongr)

theorem KlDualBound.mono_left {r : ℝ≥0∞} {m m' Q : Measure Ω} (h : KlDualBound r m' Q)
    (hm : m ≤ m') : KlDualBound r m Q :=
  fun _ hh h0 hb ↦ (lintegral_mono' hm le_rfl).trans (h hh h0 hb)

theorem klDualBound_zero_left (r : ℝ≥0∞) (Q : Measure Ω) : KlDualBound r 0 Q :=
  fun _ _ _ _ ↦ by simp

/-- Budgets of test bounds are closed from above. -/
theorem klDualBound_of_forall_gt {r : ℝ≥0∞} {m Q : Measure Ω}
    (h : ∀ r', r < r' → KlDualBound r' m Q) : KlDualBound r m Q := by
  intro g hg h0 hb
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt ↦ ?_
  have hr : r ≠ ⊤ := ne_top_of_le_ne_top hlt.ne le_self_add
  calc ∫⁻ ω, ENNReal.ofReal (g ω) ∂m
      ≤ (r + ε) + ENNReal.ofReal (Real.log (∫⁻ ω, ENNReal.ofReal (Real.exp (g ω)) ∂Q).toReal) :=
        h _ (ENNReal.lt_add_right hr (by exact_mod_cast hε.ne')) hg h0 hb
    _ = _ := by ring

/-- The exponential moment of a bounded test against a probability measure is finite and at
least `1`. -/
theorem one_le_lintegral_exp {Q : Measure Ω} [IsProbabilityMeasure Q] {h : Ω → ℝ}
    (h0 : ∀ ω, 0 ≤ h ω) : 1 ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (h ω)) ∂Q := by
  calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂Q := by simp
    _ ≤ _ := lintegral_mono fun ω ↦ by simpa using Real.one_le_exp (h0 ω)

theorem lintegral_exp_ne_top {Q : Measure Ω} [IsFiniteMeasure Q] {h : Ω → ℝ} {C : ℝ}
    (hC : ∀ ω, h ω ≤ C) : ∫⁻ ω, ENNReal.ofReal (Real.exp (h ω)) ∂Q ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal (Real.exp C) ∂Q) ?_ ?_
  · simp [lintegral_const, ENNReal.mul_ne_top, measure_ne_top]
  · exact lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hC ω))

/-! ## Donsker–Varadhan: KL bounds give test bounds -/

/-- Donsker–Varadhan inequality for bounded tests: `∫ h dP ≤ KL(P, Q) + log ∫ exp h dQ`. -/
theorem integral_le_toReal_klDiv_add_log {P Q : Measure Ω} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hint : Integrable (llr P Q) P) {h : Ω → ℝ}
    (hm : Measurable h) {C : ℝ} (hC : ∀ ω, |h ω| ≤ C) :
    ∫ ω, h ω ∂P ≤ (klDiv P Q).toReal + Real.log (∫ ω, Real.exp (h ω) ∂Q) := by
  have hhP : Integrable h P := Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hC)
  have hexp : Integrable (fun ω ↦ Real.exp (h ω)) Q :=
    Integrable.of_bound (by fun_prop) (Real.exp C) (ae_of_all _ fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 ((le_abs_self _).trans (hC ω)))
  have : IsProbabilityMeasure (Q.tilted h) := isProbabilityMeasure_tilted hexp
  have hPt : P ≪ Q.tilted h := hPQ.trans (absolutelyContinuous_tilted hexp)
  have h0 := integral_llr_add_sub_measure_univ_nonneg hPt
    (integrable_llr_tilted_right hPQ hhP hint hexp)
  rw [integral_llr_tilted_right hPQ hhP hexp hint] at h0
  rw [toReal_klDiv_of_measure_eq hPQ (by simp)]
  simp only [probReal_univ, add_sub_cancel_right] at h0
  linarith

/-- A probability measure above `m` within KL `klDiv P Q` of `Q` gives the test bound. -/
theorem klDualBound_of_le {m P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hmP : m ≤ P) : KlDualBound (klDiv P Q) m Q := by
  intro h hm h0 ⟨C, hC⟩
  simp only [mem_upperBounds, mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hC
  by_cases hkl : klDiv P Q = ⊤
  · simp [hkl]
  obtain ⟨hPQ, hint⟩ := klDiv_ne_top_iff.1 hkl
  have hb (ω : Ω) : |h ω| ≤ C := by rw [abs_of_nonneg (h0 ω)]; exact hC ω
  have hhP : Integrable h P := Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hb)
  have hexp : ∫ ω, Real.exp (h ω) ∂Q = (∫⁻ ω, ENNReal.ofReal (Real.exp (h ω)) ∂Q).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ (Real.exp_pos _).le) (by fun_prop)
  calc ∫⁻ ω, ENNReal.ofReal (h ω) ∂m
      ≤ ∫⁻ ω, ENNReal.ofReal (h ω) ∂P := lintegral_mono' hmP le_rfl
    _ = ENNReal.ofReal (∫ ω, h ω ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hhP (ae_of_all _ h0)).symm
    _ ≤ ENNReal.ofReal ((klDiv P Q).toReal +
          Real.log (∫⁻ ω, ENNReal.ofReal (Real.exp (h ω)) ∂Q).toReal) :=
        ENNReal.ofReal_le_ofReal (hexp ▸ integral_le_toReal_klDiv_add_log hPQ hint hm hb)
    _ ≤ _ := by
        refine ENNReal.ofReal_add_le.trans ?_
        rw [ENNReal.ofReal_toReal hkl]

end ProbabilityTheory
