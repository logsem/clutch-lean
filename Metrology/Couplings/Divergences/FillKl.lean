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

/-! ## Test bounds give KL bounds: the optimal filling -/

section Optimal

variable {r : ℝ≥0∞} {m Q : Measure Ω}

/-- A finite test bound puts no mass where `Q` has none: test with large multiples of the
indicator of a `Q`-null set. -/
theorem absolutelyContinuous_of_klDualBound [IsProbabilityMeasure Q] [IsFiniteMeasure m]
    (hr : r ≠ ⊤) (h : KlDualBound r m Q) : m ≪ Q := by
  refine AbsolutelyContinuous.mk fun s hs hQs ↦ ?_
  by_contra hne
  have key (n : ℕ) : (n : ℝ≥0∞) * m s ≤ r := by
    have hmeas : Measurable (s.indicator fun _ ↦ (n : ℝ)) := measurable_const.indicator hs
    have h1 := h hmeas (fun ω ↦ Set.indicator_nonneg (fun _ _ ↦ Nat.cast_nonneg n) ω)
      ⟨n, by rintro _ ⟨ω, rfl⟩; by_cases hω : ω ∈ s <;> simp [hω]⟩
    have hl : (fun ω ↦ ENNReal.ofReal (s.indicator (fun _ ↦ (n : ℝ)) ω)) =
        s.indicator fun _ ↦ (n : ℝ≥0∞) := by
      funext ω
      by_cases hω : ω ∈ s <;> simp [hω]
    have he : ∫⁻ ω, ENNReal.ofReal (Real.exp (s.indicator (fun _ ↦ (n : ℝ)) ω)) ∂Q = 1 := by
      rw [lintegral_congr_ae (g := fun _ ↦ 1), lintegral_one, measure_univ]
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hQs] with ω hω
      simp [hω]
    rwa [hl, lintegral_indicator_const hs, he, ENNReal.toReal_one, Real.log_one,
      ENNReal.ofReal_zero, add_zero] at h1
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top hr hne)
  rw [ENNReal.div_lt_iff (.inl hne) (.inl (measure_ne_top m s))] at hn
  exact (key n).not_gt hn

variable {p : Ω → ℝ}

/-- The test `log (max p t / t)`, truncated and passed to the limit, bounds `∫ p log (max p t / t)`
for a density `p` of `m`. -/
theorem lintegral_mul_log_le [IsProbabilityMeasure Q] (h : KlDualBound r m Q) (hpm : Measurable p)
    (hp0 : ∀ ω, 0 ≤ p ω) (hpint : Integrable p Q)
    (hmQ : m = Q.withDensity fun ω ↦ ENNReal.ofReal (p ω)) {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, ENNReal.ofReal (p ω * Real.log (max (p ω) t / t)) ∂Q ≤
      r + ENNReal.ofReal (Real.log ((∫ ω, max (p ω) t ∂Q) / t)) := by
  set φ : Ω → ℝ := fun ω ↦ Real.log (max (p ω) t / t)
  have hct (ω : Ω) : 0 < max (p ω) t / t := div_pos (ht.trans_le (le_max_right _ _)) ht
  have hφ0 (ω : Ω) : 0 ≤ φ ω :=
    Real.log_nonneg ((one_le_div ht).2 (le_max_right _ _))
  have hφm : Measurable φ := ((hpm.max measurable_const).div_const t).log
  have hcint : Integrable (fun ω ↦ max (p ω) t / t) Q :=
    (hpint.sup (integrable_const t)).div_const t
  -- the right side of the bound is the exponential moment of the untruncated test
  have hB : (∫⁻ ω, ENNReal.ofReal (max (p ω) t / t) ∂Q).toReal = (∫ ω, max (p ω) t ∂Q) / t := by
    rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω ↦ (hct ω).le)
      hcint.aestronglyMeasurable, integral_div]
  rw [← hB]
  calc ∫⁻ ω, ENNReal.ofReal (p ω * φ ω) ∂Q
      = ∫⁻ ω, ENNReal.ofReal (φ ω) ∂m := by
        rw [hmQ, lintegral_withDensity_eq_lintegral_mul _ hpm.ennreal_ofReal hφm.ennreal_ofReal]
        simp_rw [Pi.mul_apply, ← ENNReal.ofReal_mul (hp0 _)]
    _ = ⨆ n : ℕ, ∫⁻ ω, ENNReal.ofReal (min (φ ω) n) ∂m := by
        rw [← lintegral_iSup (fun n ↦ (hφm.min measurable_const).ennreal_ofReal)
          fun a b hab ω ↦ ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.2 hab))]
        refine lintegral_congr fun ω ↦ le_antisymm ?_ (iSup_le fun n ↦
          ENNReal.ofReal_le_ofReal (min_le_left _ _))
        exact le_iSup_of_le ⌈φ ω⌉₊ (by rw [min_eq_left (Nat.le_ceil _)])
    _ ≤ _ := iSup_le fun n ↦ by
        refine (h (hφm.min measurable_const) (fun ω ↦ le_min (hφ0 ω) (Nat.cast_nonneg n))
          ⟨n, by rintro _ ⟨ω, rfl⟩; exact min_le_right _ _⟩).trans ?_
        have hA1 := one_le_lintegral_exp (Q := Q) fun ω ↦ le_min (hφ0 ω) (Nat.cast_nonneg n)
        have hAt := lintegral_exp_ne_top (Q := Q) (h := fun ω ↦ min (φ ω) n) (C := n)
          fun ω ↦ min_le_right _ _
        refine add_le_add le_rfl (ENNReal.ofReal_le_ofReal (Real.log_le_log
          (ENNReal.toReal_pos (zero_lt_one.trans_le hA1).ne' hAt)
          (ENNReal.toReal_mono hcint.lintegral_lt_top.ne (lintegral_mono fun ω ↦
            ENNReal.ofReal_le_ofReal ?_))))
        calc Real.exp (min (φ ω) n) ≤ Real.exp (φ ω) := Real.exp_le_exp.2 (min_le_left _ _)
          _ = max (p ω) t / t := Real.exp_log (hct ω)

/-- The mass of `max p t` under `Q` is `1`-Lipschitz in `t`. -/
theorem lipschitzWith_integral_max [IsProbabilityMeasure Q] (hpint : Integrable p Q) :
    LipschitzWith 1 fun t : ℝ ↦ ∫ ω, max (p ω) t ∂Q := by
  refine LipschitzWith.of_dist_le_mul fun s t ↦ ?_
  have hs : Integrable (fun ω ↦ max (p ω) s) Q := hpint.sup (integrable_const s)
  have ht : Integrable (fun ω ↦ max (p ω) t) Q := hpint.sup (integrable_const t)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, ← integral_sub hs ht]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ ω, |max (p ω) s - max (p ω) t| ∂Q ≤ ∫ _, |s - t| ∂Q :=
        integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _) (integrable_const _)
          (ae_of_all _ fun ω ↦ by
            simpa only [max_comm (p ω)] using abs_max_sub_max_le_abs s t (p ω))
    _ = |s - t| := by simp

/-- A test bound for `m` is met by a probability measure above `m` within that KL budget: when
`m` loses mass, the optimal filling `max (dm/dQ) λ • Q` with total mass `1`; otherwise `m`
itself. -/
theorem exists_le_klDiv_le_of_klDualBound [IsProbabilityMeasure Q] [IsFiniteMeasure m]
    (hm1 : m univ ≤ 1) (h : KlDualBound r m Q) :
    ∃ P, IsProbabilityMeasure P ∧ m ≤ P ∧ klDiv P Q ≤ r := by
  rcases eq_or_ne r ⊤ with rfl | hr
  · refine ⟨m + (1 - m univ) • Q, ⟨?_⟩, Measure.le_add_right le_rfl, le_top⟩
    simp [add_tsub_cancel_of_le hm1]
  have hac := absolutelyContinuous_of_klDualBound hr h
  set p : Ω → ℝ := fun ω ↦ (m.rnDeriv Q ω).toReal with hp
  have hpm : Measurable p := (measurable_rnDeriv m Q).ennreal_toReal
  have hp0 (ω : Ω) : 0 ≤ p ω := ENNReal.toReal_nonneg
  have hpint : Integrable p Q := Measure.integrable_toReal_rnDeriv
  have hmQ : m = Q.withDensity fun ω ↦ ENNReal.ofReal (p ω) := by
    conv_lhs => rw [← withDensity_rnDeriv_eq m Q hac]
    refine withDensity_congr_ae ?_
    filter_upwards [rnDeriv_lt_top m Q] with ω hω
    exact (ENNReal.ofReal_toReal hω.ne).symm
  have hpm1 : ∫ ω, p ω ∂Q = m.real univ := integral_toReal_rnDeriv hac
  set F : ℝ → ℝ := fun t ↦ ∫ ω, max (p ω) t ∂Q
  have hF0 : F 0 = m.real univ := by simp only [F, max_eq_left (hp0 _), hpm1]
  have hF1 : 1 ≤ F 1 := by
    calc (1 : ℝ) = ∫ _, (1 : ℝ) ∂Q := by simp
      _ ≤ F 1 := integral_mono (integrable_const _) (hpint.sup (integrable_const 1))
          fun ω ↦ le_max_right _ _
  have hreal1 : m.real univ ≤ 1 := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hm1)
  obtain ⟨t, ⟨ht0, ht1⟩, hFt⟩ : ∃ t ∈ Icc (0 : ℝ) 1, F t = 1 :=
    intermediate_value_Icc zero_le_one (lipschitzWith_integral_max hpint).continuous.continuousOn
      ⟨hF0.trans_le hreal1, hF1⟩
  have hcint (s : ℝ) : Integrable (fun ω ↦ max (p ω) s) Q := hpint.sup (integrable_const s)
  have hklm : Measurable klFun := continuous_klFun.measurable
  rcases ht0.eq_or_lt with rfl | htpos
  · -- no lost mass: `m` itself, with the bound at every `s > 0` up to `log (1 + s)`
    have hmu : m univ = 1 := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top m univ), ← measureReal_def, ← hF0, hFt,
        ENNReal.ofReal_one]
    have : IsProbabilityMeasure m := ⟨hmu⟩
    refine ⟨m, this, le_rfl, ?_⟩
    rw [klDiv_eq_lintegral_klFun_of_ac hac]
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    set s : ℝ := min 1 ε
    have hs : 0 < s := lt_min one_pos hε
    have hs1 : s ≤ 1 := min_le_left _ _
    set φ : Ω → ℝ := fun ω ↦ Real.log (max (p ω) s / s)
    have hφ0 (ω : Ω) : 0 ≤ φ ω := Real.log_nonneg ((one_le_div hs).2 (le_max_right _ _))
    have hφm : Measurable φ := ((hpm.max measurable_const).div_const s).log
    have hL := lintegral_mul_log_le h hpm hp0 hpint hmQ hs
    have hpm1' : ∫ ω, p ω ∂Q = 1 := by rw [hpm1, measureReal_def, hmu, ENNReal.toReal_one]
    have hFs : F s ≤ 1 + s := by
      calc F s ≤ ∫ ω, (p ω + s) ∂Q := integral_mono (hcint s) (hpint.add (integrable_const s))
            fun ω ↦ max_le (le_add_of_nonneg_right hs.le) (le_add_of_nonneg_left (hp0 ω))
        _ = 1 + s := by rw [integral_add hpint (integrable_const s), hpm1']; simp
    have hFs' : s ≤ F s := by
      calc s = ∫ _, s ∂Q := by simp
        _ ≤ F s := integral_mono (integrable_const _) (hcint s) fun ω ↦ le_max_right _ _
    have hlog0 : 0 ≤ Real.log (F s / s) := Real.log_nonneg ((one_le_div hs).2 hFs')
    have hpφ : Integrable (fun ω ↦ p ω * φ ω) Q :=
      (lintegral_ofReal_ne_top_iff_integrable (hpm.mul hφm).aestronglyMeasurable
        (ae_of_all _ fun ω ↦ mul_nonneg (hp0 ω) (hφ0 ω))).1
        (ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hr, ENNReal.ofReal_ne_top⟩) hL)
    have hpφle : ∫ ω, p ω * φ ω ∂Q ≤ r.toReal + Real.log (F s / s) := by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω ↦ mul_nonneg (hp0 ω) (hφ0 ω))
        hpφ.aestronglyMeasurable, ← ENNReal.toReal_ofReal hlog0,
        ← ENNReal.toReal_add hr ENNReal.ofReal_ne_top]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hr, ENNReal.ofReal_ne_top⟩) hL
    set g : Ω → ℝ := fun ω ↦ p ω * φ ω + (Real.log s * p ω + (1 - p ω))
    have hA : Integrable (fun ω ↦ Real.log s * p ω) Q := hpint.const_mul _
    have hB : Integrable (fun ω ↦ 1 - p ω) Q := (integrable_const 1).sub hpint
    have hAB : Integrable (fun ω ↦ Real.log s * p ω + (1 - p ω)) Q := hA.add hB
    have hg : Integrable g Q := hpφ.add hAB
    have hkl (ω : Ω) : klFun (p ω) ≤ g ω := by
      have hc : 0 < max (p ω) s := hs.trans_le (le_max_right _ _)
      have hlog : p ω * Real.log (p ω) ≤ p ω * Real.log (max (p ω) s) := by
        rcases (hp0 ω).eq_or_lt with h0 | h0
        · simp [← h0]
        · exact mul_le_mul_of_nonneg_left (Real.log_le_log h0 (le_max_left _ _)) (hp0 ω)
      simp only [g, φ, klFun, Real.log_div hc.ne' hs.ne']
      nlinarith
    have hklint : Integrable (fun ω ↦ klFun (p ω)) Q :=
      hg.mono' (hklm.comp hpm).aestronglyMeasurable (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg (hp0 ω))]
        exact hkl ω)
    have hint : ∫ ω, klFun (p ω) ∂Q ≤ r.toReal + Real.log (1 + s) := by
      calc ∫ ω, klFun (p ω) ∂Q ≤ ∫ ω, g ω ∂Q := integral_mono hklint hg hkl
        _ = ∫ ω, p ω * φ ω ∂Q + Real.log s := by
          simp only [g]
          rw [integral_add hpφ hAB, integral_add hA hB, integral_const_mul,
            integral_sub (integrable_const 1) hpint, hpm1']
          simp
        _ ≤ r.toReal + Real.log (F s / s) + Real.log s := by linarith
        _ = r.toReal + Real.log (F s) := by
          rw [Real.log_div (hs.trans_le hFs').ne' hs.ne']
          ring
        _ ≤ r.toReal + Real.log (1 + s) := by
          gcongr
          exact hs.trans_le hFs'
    calc ∫⁻ ω, ENNReal.ofReal (klFun (m.rnDeriv Q ω).toReal) ∂Q
        = ENNReal.ofReal (∫ ω, klFun (p ω) ∂Q) :=
          (ofReal_integral_eq_lintegral_ofReal hklint
            (ae_of_all _ fun ω ↦ klFun_nonneg (hp0 ω))).symm
      _ ≤ ENNReal.ofReal (r.toReal + Real.log (1 + s)) := ENNReal.ofReal_le_ofReal hint
      _ ≤ r + ε := by
          refine ENNReal.ofReal_add_le.trans ?_
          rw [ENNReal.ofReal_toReal hr]
          refine add_le_add le_rfl ?_
          rw [← ENNReal.ofReal_coe_nnreal]
          refine ENNReal.ofReal_le_ofReal ?_
          calc Real.log (1 + s) ≤ 1 + s - 1 := Real.log_le_sub_one_of_pos (by linarith)
            _ ≤ ε := by simp [s]
  · -- lost mass: fill with `max p t • Q`, which has mass `1`
    set c : Ω → ℝ := fun ω ↦ max (p ω) t
    have hc0 (ω : Ω) : 0 ≤ c ω := (hp0 ω).trans (le_max_left _ _)
    have hcm : Measurable c := hpm.max measurable_const
    set P := Q.withDensity fun ω ↦ ENNReal.ofReal (c ω)
    have hP : IsProbabilityMeasure P := ⟨by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        ← ofReal_integral_eq_lintegral_ofReal (hcint t) (ae_of_all _ hc0)]
      rw [show (∫ ω, max (p ω) t ∂Q) = F t from rfl, hFt, ENNReal.ofReal_one]⟩
    refine ⟨P, hP, ?_, ?_⟩
    · rw [hmQ]
      exact withDensity_mono (ae_of_all _ fun ω ↦ ENNReal.ofReal_le_ofReal (le_max_left _ _))
    rw [klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous _ _)]
    have hrn := rnDeriv_withDensity Q hcm.ennreal_ofReal
    rw [lintegral_congr_ae (hrn.mono fun ω hω ↦ by
      rw [hω, ENNReal.toReal_ofReal (hc0 ω)])]
    set φ : Ω → ℝ := fun ω ↦ Real.log (c ω / t)
    have hφ0 (ω : Ω) : 0 ≤ φ ω := Real.log_nonneg ((one_le_div htpos).2 (le_max_right _ _))
    have hφm : Measurable φ := (hcm.div_const t).log
    have hL := lintegral_mul_log_le h hpm hp0 hpint hmQ htpos
    rw [show (∫ ω, max (p ω) t ∂Q) = F t from rfl, hFt, one_div, Real.log_inv] at hL
    have hlt : 0 ≤ -Real.log t := neg_nonneg.2 (Real.log_nonpos htpos.le ht1)
    have hpφ : Integrable (fun ω ↦ p ω * φ ω) Q :=
      (lintegral_ofReal_ne_top_iff_integrable (hpm.mul hφm).aestronglyMeasurable
        (ae_of_all _ fun ω ↦ mul_nonneg (hp0 ω) (hφ0 ω))).1
        (ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hr, ENNReal.ofReal_ne_top⟩) hL)
    have hpφle : ∫ ω, p ω * φ ω ∂Q ≤ r.toReal + -Real.log t := by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω ↦ mul_nonneg (hp0 ω) (hφ0 ω))
        hpφ.aestronglyMeasurable, ← ENNReal.toReal_ofReal hlt,
        ← ENNReal.toReal_add hr ENNReal.ofReal_ne_top]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hr, ENNReal.ofReal_ne_top⟩) hL
    -- `c log (c / t) = p log (c / t)`: where they differ, `c = t`
    have hkl (ω : Ω) :
        klFun (c ω) = p ω * φ ω + (Real.log t * c ω + (1 - c ω)) := by
      have hc : 0 < c ω := htpos.trans_le (le_max_right _ _)
      have hcp : c ω * φ ω = p ω * φ ω := by
        rcases le_total (p ω) t with hpt | hpt
        · simp [φ, c, max_eq_right hpt, div_self htpos.ne']
        · simp [c, max_eq_left hpt]
      simp only [φ, klFun_apply, Real.log_div hc.ne' htpos.ne'] at hcp ⊢
      linear_combination hcp
    have hA : Integrable (fun ω ↦ Real.log t * c ω) Q := (hcint t).const_mul _
    have hB : Integrable (fun ω ↦ 1 - c ω) Q := (integrable_const 1).sub (hcint t)
    have hrest : Integrable (fun ω ↦ Real.log t * c ω + (1 - c ω)) Q := hA.add hB
    have hklint : Integrable (fun ω ↦ klFun (c ω)) Q := by
      simp_rw [hkl]
      exact hpφ.add hrest
    have hint : ∫ ω, klFun (c ω) ∂Q ≤ r.toReal := by
      simp_rw [hkl]
      rw [integral_add hpφ hrest, integral_add hA hB, integral_const_mul,
        integral_sub (integrable_const 1) (hcint t)]
      rw [show (∫ ω, max (p ω) t ∂Q) = F t from rfl, hFt]
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, sub_self, add_zero]
      linarith
    calc ∫⁻ ω, ENNReal.ofReal (klFun (c ω)) ∂Q = ENNReal.ofReal (∫ ω, klFun (c ω) ∂Q) :=
          (ofReal_integral_eq_lintegral_ofReal hklint
            (ae_of_all _ fun ω ↦ klFun_nonneg (hc0 ω))).symm
      _ ≤ ENNReal.ofReal r.toReal := ENNReal.ofReal_le_ofReal hint
      _ = r := ENNReal.ofReal_toReal hr

end Optimal

/-! ## Test bounds compose -/

/-- Test bounds compose along a Markov right kernel: test the head with the log exponential moment
of the test under the right kernel. -/
theorem KlDualBound.comp {b c : ℝ≥0∞} {m₁ Q₁ : Measure Ω} [IsSubProbabilityMeasure m₁]
    {K L : Kernel Ω Ω'} [IsMarkovKernel L] (h₁ : KlDualBound b m₁ Q₁)
    (h₂ : ∀ ω, KlDualBound c (K ω) (L ω)) : KlDualBound (b + c) (K ∘ₘ m₁) (L ∘ₘ Q₁) := by
  intro h hm h0 hb
  obtain ⟨C, hC⟩ := hb
  have hC' (ω : Ω') : h ω ≤ C := hC ⟨ω, rfl⟩
  set G : Ω → ℝ≥0∞ := fun ω ↦ ∫⁻ ω', ENNReal.ofReal (Real.exp (h ω')) ∂(L ω)
  have hGm : Measurable G := (hm.exp.ennreal_ofReal).lintegral_kernel
  have hG1 (ω : Ω) : 1 ≤ G ω := one_le_lintegral_exp h0
  have hGt (ω : Ω) : G ω ≠ ⊤ := lintegral_exp_ne_top hC'
  have hGpos (ω : Ω) : 0 < (G ω).toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (hG1 ω)).ne' (hGt ω)
  set g : Ω → ℝ := fun ω ↦ Real.log (G ω).toReal
  have hg0 (ω : Ω) : 0 ≤ g ω :=
    Real.log_nonneg (ENNReal.toReal_one ▸ ENNReal.toReal_mono (hGt ω) (hG1 ω))
  have hgC (ω : Ω) : g ω ≤ C := by
    have hle : G ω ≤ ENNReal.ofReal (Real.exp C) :=
      (lintegral_mono fun ω' ↦ ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hC' ω'))).trans
        (by simp)
    calc g ω ≤ Real.log (Real.exp C) := Real.log_le_log (hGpos ω)
          ((ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans_eq
            (ENNReal.toReal_ofReal (Real.exp_pos C).le))
      _ = C := Real.log_exp C
  have hgm : Measurable g := hGm.ennreal_toReal.log
  have hexpg (ω : Ω) : ENNReal.ofReal (Real.exp (g ω)) = G ω := by
    rw [Real.exp_log (hGpos ω), ENNReal.ofReal_toReal (hGt ω)]
  calc ∫⁻ ω', ENNReal.ofReal (h ω') ∂(K ∘ₘ m₁)
      = ∫⁻ ω, ∫⁻ ω', ENNReal.ofReal (h ω') ∂(K ω) ∂m₁ :=
        Measure.lintegral_bind K.aemeasurable hm.ennreal_ofReal.aemeasurable
    _ ≤ ∫⁻ ω, (c + ENNReal.ofReal (g ω)) ∂m₁ :=
        lintegral_mono fun ω ↦ h₂ ω hm h0 ⟨C, hC⟩
    _ = c * m₁ univ + ∫⁻ ω, ENNReal.ofReal (g ω) ∂m₁ := by
        rw [lintegral_add_left measurable_const, lintegral_const]
    _ ≤ c + (b + ENNReal.ofReal (Real.log (∫⁻ ω, ENNReal.ofReal (Real.exp (g ω)) ∂Q₁).toReal)) :=
        add_le_add (mul_le_of_le_one_right' (IsSubProbabilityMeasure.measure_le_one _))
          (h₁ hgm hg0 ⟨C, by rintro _ ⟨ω, rfl⟩; exact hgC ω⟩)
    _ = (b + c) + ENNReal.ofReal
          (Real.log (∫⁻ ω', ENNReal.ofReal (Real.exp (h ω')) ∂(L ∘ₘ Q₁)).toReal) := by
        rw [Measure.lintegral_bind L.aemeasurable hm.exp.ennreal_ofReal.aemeasurable]
        simp_rw [hexpg]
        ring

end ProbabilityTheory

namespace GradedDivergence

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {μ ν : Measure X} {r : ℝ≥0∞}

/-! ## Filled KL is the test bound -/

theorem isSubProbabilityMeasure_map_some (μ : Measure X) [IsSubProbabilityMeasure μ] :
    IsSubProbabilityMeasure (μ.map some) :=
  ⟨by rw [map_apply measurable_some .univ]; exact IsSubProbabilityMeasure.measure_le_one _⟩

/-- A filled KL bound is the Donsker–Varadhan test bound of the relabelled left measure against the
filled right measure. -/
theorem fill_kl_iff [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    fill klDivergence r μ ν ↔ KlDualBound r (μ.map some) ν.withBot := by
  refine ⟨fun ⟨μ', hle, _, hD⟩ ↦ ?_, fun h ↦ ?_⟩
  · have hkl : klDiv μ'.withBot ν.withBot ≤ r := klDivergence_iff.1 hD
    exact (klDualBound_of_le ((map_mono hle measurable_some).trans
      (map_some_le_withBot μ'))).mono hkl
  · have : IsSubProbabilityMeasure (μ.map some) := isSubProbabilityMeasure_map_some μ
    obtain ⟨P, hP, hle, hkl⟩ := exists_le_klDiv_le_of_klDualBound
      (IsSubProbabilityMeasure.measure_le_one _) h
    refine ⟨Kernel.dropBot ∘ₘ P, Kernel.le_dropBot_comp hle, isSubProbabilityMeasure_bind _ _, ?_⟩
    change klDivergence r (Kernel.dropBot ∘ₘ P).withBot ν.withBot
    rw [Kernel.withBot_dropBot_comp]
    exact klDivergence_iff.2 hkl

/-! ## Filling before comparing composes for KL and Hellinger -/

/-- KL between filled measures composes: filled kernels are Markov. -/
instance isComposable_onWithBot_kl : (klDivergence.{u}).onWithBot.IsComposable :=
  isComposable_onWithBot fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ↦
    klDivergence_comp_of_mass_eq fun _ ↦ by simp

/-- `α`-Hellinger between filled measures composes: filled kernels are Markov. -/
instance isComposable_onWithBot_hellinger (α : ℝ) [hα : Fact (α ∈ Ioo (0 : ℝ) 1)] :
    (hellingerDivergence.{u} α).onWithBot.IsComposable :=
  isComposable_onWithBot fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ ↦
    hellingerDivergence_comp_of_mass_eq hα.out.1 hα.out.2 fun _ ↦ by simp

/-! ## Reading filled KL back -/

/-- A filled KL bound is a generalized KL bound for some completion of the left measure: forget
`none` by data processing. -/
theorem exists_le_klDivergence_of_fill [IsSubProbabilityMeasure ν]
    (h : fill klDivergence r μ ν) :
    ∃ μ', μ ≤ μ' ∧ IsSubProbabilityMeasure μ' ∧ klDivergence r μ' ν := by
  obtain ⟨μ', hle, hμ', hD⟩ := h
  refine ⟨μ', hle, hμ', ?_⟩
  have := klDivergence_comp_self Kernel.dropBot hD
  rwa [Kernel.dropBot_comp_withBot', Kernel.dropBot_comp_withBot'] at this

/-- Against a left probability measure, filled KL bounds Mathlib's KL divergence. -/
theorem klDiv_le_of_fill [IsProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    (h : fill klDivergence r μ ν) : klDiv μ ν ≤ r := by
  obtain ⟨μ', hle, hμ', hD⟩ := exists_le_klDivergence_of_fill h
  have h1 : μ' univ ≤ 1 := hμ'.measure_univ_le_one
  obtain rfl : μ = μ' := Measure.eq_of_le_of_measure_univ_eq hle
    (le_antisymm (by simpa using hle univ) (by simpa using h1))
  exact klDivergence_iff.1 hD

/-- Between probability measures (terminating programs), filled KL is KL. -/
theorem fill_kl_iff_of_isProbabilityMeasure [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    fill klDivergence r μ ν ↔ klDivergence r μ ν := by
  refine ⟨fun h ↦ klDivergence_iff.2 (klDiv_le_of_fill h), fun h ↦ ⟨μ, le_rfl, inferInstance, ?_⟩⟩
  change klDivergence r μ.withBot ν.withBot
  rw [withBot_of_isProbabilityMeasure, withBot_of_isProbabilityMeasure,
    ← deterministic_comp_eq_map measurable_some, ← deterministic_comp_eq_map measurable_some]
  exact klDivergence_comp_self _ h

/-! ## The laws of filled KL -/

/-- Filled KL composes: the test bounds of the fillings compose, so no filling of the kernel has
to be chosen (Rocq `FillDiv_composable`, which chooses one on the support of the head). -/
instance isComposable_fill_kl : (fill klDivergence.{u}).IsComposable where
  comp b c X Y _ _ μ₁ μ₂ _ _ κ η _ _ hμ hκ := by
    have : IsSubProbabilityMeasure (μ₁.map some) := isSubProbabilityMeasure_map_some μ₁
    have : IsSubProbabilityMeasure (κ ∘ₘ μ₁) := isSubProbabilityMeasure_bind μ₁ _
    have : IsSubProbabilityMeasure (η ∘ₘ μ₂) := isSubProbabilityMeasure_bind μ₂ _
    rw [fill_kl_iff] at hμ ⊢
    have hK : (κ ∘ₘ μ₁).map some = ((κ.map some) ∘ₖ Kernel.dropBot) ∘ₘ μ₁.map some := by
      rw [← Measure.comp_assoc, Kernel.dropBot_comp_map_some, Measure.map_comp _ _ measurable_some]
    rw [hK, Kernel.withBot_comp]
    refine KlDualBound.comp hμ fun o ↦ ?_
    cases o with
    | none =>
      simpa [Kernel.comp_apply, Kernel.dropBot] using klDualBound_zero_left _ _
    | some x =>
      have h := fill_kl_iff.1 (hκ x)
      simpa [Kernel.comp_apply, Kernel.dropBot, Kernel.map_apply _ measurable_some,
        Measure.dirac_bind (Kernel.measurable _)] using h

/-- Filled KL passes to the supremum of an increasing sequence on the left: tests pass to it by
monotone convergence (Rocq `FillDiv_lim`, which extracts a convergent subsequence of fillings). -/
instance isLeftContinuous_fill_kl : (fill klDivergence.{u}).IsLeftContinuous where
  iSup_left b X _ μ _ hμ ν _ h := by
    have : IsSubProbabilityMeasure (⨆ n, μ n) := ⟨by
      rw [iSup_apply_of_monotone hμ .univ]
      exact iSup_le fun n ↦ IsSubProbabilityMeasure.measure_le_one _⟩
    rw [fill_kl_iff]
    intro g hg h0 hb
    rw [lintegral_map hg.ennreal_ofReal measurable_some,
      lintegral_iSup_of_monotone hμ (f := fun x ↦ ENNReal.ofReal (g (some x)))
        (hg.comp measurable_some).ennreal_ofReal]
    refine iSup_le fun n ↦ ?_
    have := fill_kl_iff.1 (h n) hg h0 hb
    rwa [lintegral_map hg.ennreal_ofReal measurable_some] at this

/-- Filled KL has closed budgets: so do test bounds. -/
instance isBudgetClosed_fill_kl : (fill klDivergence.{u}).IsBudgetClosed where
  of_forall_gt h := fill_kl_iff.2 (klDualBound_of_forall_gt fun _ hr ↦ fill_kl_iff.1 (h _ hr))

end GradedDivergence
