module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Metrology.Couplings.Divergences.Bof

/-! Generalized KL on sub-probability measures, the Barthe–Olmedo divergence at `γ = 0`
(Barthe–Olmedo, ICALP 2013).
Main results: composition for kernels of equal mass (`klDivergence_comp_of_mass_eq`), and a
counterexample to general composability (`not_isComposable_kl`). -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory Set Filter Topology InformationTheory
open scoped ENNReal

namespace ProbabilityTheory

/-- KL has infinite slope at `∞`, so mass singular to `ν` costs `⊤`. -/
theorem derivAtTop_klFun : derivAtTop klFun = ⊤ := by
  refine Tendsto.limsup_eq (EReal.tendsto_coe_atTop.comp ?_)
  have h : Tendsto (fun t : ℝ ↦ Real.log t + (1 / t - 1)) atTop atTop :=
    Real.tendsto_log_atTop.atTop_add
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_id |>.sub_const 1)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [klFun]
  field_simp
  ring

variable {X : Type*} [MeasurableSpace X] {μ ν : Measure X}

/-- On finite measures the `klFun`-divergence is Mathlib's generalized KL divergence
`∫ log (dμ/dν) dμ - μ(X) + ν(X)`, which is ordinary KL between probability measures. -/
theorem fDiv_klFun_eq_klDiv [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv klFun μ ν = klDiv μ ν := by
  by_cases hac : μ ≪ ν
  · by_cases hint : Integrable (fun x ↦ klFun (μ.rnDeriv ν x).toReal) ν
    · rw [fDiv_of_integrable hint, (singularPart_eq_zero μ ν).2 hac, klDiv_eq_integral_klFun]
      simp only [hac, (integrable_klFun_rnDeriv_iff hac).1 hint, and_self, ↓reduceIte]
      rw [EReal.coe_ennreal_ofReal,
        max_eq_left (integral_nonneg fun _ ↦ klFun_nonneg ENNReal.toReal_nonneg)]
      simp
    · rw [fDiv_of_not_integrable hint,
        klDiv_of_not_integrable (mt (integrable_klFun_rnDeriv_iff hac).2 hint)]
      simp
  · rw [klDiv_of_not_ac hac]
    by_contra h
    exact hac (absolutelyContinuous_of_fDiv_ne_top derivAtTop_klFun (by simpa using h))

/-- The pointwise generalized KL term `p log (p / q) + q - p`, the real-valued perspective of
`klFun` used to prove the finite chain rule. -/
noncomputable def klTerm (p q : ℝ) : ℝ := p * Real.log (p / q) + q - p

/-- Away from `q = 0 < p`, the perspective of `klFun` is the pointwise KL term. -/
theorem persp_klFun {p q : ℝ} (hq : 0 ≤ q) (hpq : q = 0 → p = 0) :
    persp klFun p q = klTerm p q := by
  rcases hq.eq_or_lt with rfl | hq
  · simp [hpq rfl, klTerm]
  rw [persp_of_ne_zero hq.ne', klTerm, klFun, EReal.coe_eq_coe_iff]
  have : q * (p / q) = p := mul_div_cancel₀ p hq.ne'
  linear_combination (Real.log (p / q) - 1) * this

theorem klTerm_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : q = 0 → p = 0) :
    0 ≤ klTerm p q := by
  have := persp_nonneg (fun _ ht ↦ klFun_nonneg ht) hp hq
  rwa [persp_klFun hq hpq, EReal.coe_nonneg] at this

/-- The generalized KL term of a product splits into weighted terms plus a cross term that
vanishes when summed against kernels of equal mass. -/
theorem klTerm_mul {p q k l : ℝ} (hp : 0 ≤ p) (hk : 0 ≤ k) (hq : 0 ≤ q) (hl : 0 ≤ l)
    (hpq : q = 0 → p = 0) (hkl : l = 0 → k = 0) :
    klTerm (p * k) (q * l) = k * klTerm p q + p * klTerm k l + (q - p) * (l - k) := by
  rcases hp.eq_or_lt with rfl | hp
  · simp [klTerm]
    ring
  rcases hk.eq_or_lt with rfl | hk
  · simp [klTerm]
    ring
  have hq : 0 < q := hq.lt_of_ne fun h ↦ hp.ne' (hpq h.symm)
  have hl : 0 < l := hl.lt_of_ne fun h ↦ hk.ne' (hkl h.symm)
  unfold klTerm
  rw [mul_div_mul_comm, Real.log_mul (div_pos hp hq).ne' (div_pos hk hl).ne']
  ring

/-- Log-sum inequality for the generalized KL term. -/
theorem klTerm_sum_le {ι : Type*} (s : Finset ι) {a b : ι → ℝ} (ha : ∀ i ∈ s, 0 ≤ a i)
    (hb : ∀ i ∈ s, 0 ≤ b i) (hab : ∀ i ∈ s, b i = 0 → a i = 0) :
    klTerm (∑ i ∈ s, a i) (∑ i ∈ s, b i) ≤ ∑ i ∈ s, klTerm (a i) (b i) := by
  have h := persp_sum_le convexOn_klFun s ha hb
  rw [persp_klFun (Finset.sum_nonneg hb) fun h0 ↦ Finset.sum_eq_zero fun i hi ↦
      hab i hi ((Finset.sum_eq_zero_iff_of_nonneg hb).1 h0 i hi),
    Finset.sum_congr rfl fun i hi ↦ persp_klFun (hb i hi) (hab i hi),
    ← EReal.coe_finset_sum, EReal.coe_le_coe_iff] at h
  exact h

/-- On a finite space with absolute continuity, the `klFun`-divergence is a real sum of terms. -/
theorem fDiv_klFun_eq_sum {I : Type*} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (ρ₁ ρ₂ : Measure I) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂]
    (h : ∀ i, ρ₂ {i} = 0 → ρ₁ {i} = 0) :
    fDiv klFun ρ₁ ρ₂ = ((∑ i, klTerm (ρ₁ {i}).toReal (ρ₂ {i}).toReal : ℝ) : EReal) := by
  rw [fDiv_eq_sum convexOn_klFun continuous_klFun.continuousWithinAt, EReal.coe_finset_sum]
  refine Finset.sum_congr rfl fun i _ ↦ persp_klFun ENNReal.toReal_nonneg fun hq ↦ ?_
  rw [ENNReal.toReal_eq_zero_iff] at hq ⊢
  exact .inl (h i (hq.resolve_right (measure_ne_top _ _)))

/-- Chain rule for generalized KL between finite spaces when the two kernels lose the same mass
at every point (Rocq proves it only at mass `1`, `KL_top_composable_gen` under `FillKL`). -/
theorem fDiv_klFun_comp_le_of_mass_eq {M N : ℕ} [NeZero M] (μ₁ μ₂ : Measure (ULift.{u} (Fin M)))
    [IsSubProbabilityMeasure μ₁] [IsSubProbabilityMeasure μ₂]
    (κ η : Kernel (ULift.{u} (Fin M)) (ULift.{u} (Fin N))) [IsSubMarkovKernel κ]
    [IsSubMarkovKernel η] (hmass : ∀ j, κ j univ = η j univ) :
    fDiv klFun (κ ∘ₘ μ₁) (η ∘ₘ μ₂) ≤ fDiv klFun μ₁ μ₂ + ⨆ j, fDiv klFun (κ j) (η j) := by
  have hkl₀ : ∀ t, 0 ≤ t → 0 ≤ klFun t := fun _ ht ↦ klFun_nonneg ht
  have he₀ := fDiv_nonneg_of_nonneg hkl₀ (μ := μ₁) (ν := μ₂)
  set d := ⨆ j, fDiv klFun (κ j) (η j)
  have hd (j) : fDiv klFun (κ j) (η j) ≤ d := le_iSup (fun j ↦ fDiv klFun (κ j) (η j)) j
  have hd₀ : 0 ≤ d := (fDiv_nonneg_of_nonneg hkl₀).trans (hd ⟨0⟩)
  rcases eq_or_ne (fDiv klFun μ₁ μ₂) ⊤ with he | he
  · rw [he, EReal.top_add_of_ne_bot (ne_bot_of_le_ne_bot EReal.zero_ne_bot hd₀)]
    exact le_top
  rcases eq_or_ne d ⊤ with hdt | hdt
  · rw [hdt, EReal.add_top_of_ne_bot (ne_bot_of_le_ne_bot EReal.zero_ne_bot he₀)]
    exact le_top
  -- finiteness and absolute continuity
  have hμ : μ₁ ≪ μ₂ := absolutelyContinuous_of_fDiv_ne_top derivAtTop_klFun he
  have hκ (j) : κ j ≪ η j :=
    absolutelyContinuous_of_fDiv_ne_top derivAtTop_klFun (ne_top_of_le_ne_top hdt (hd j))
  have hbind (i) : (η ∘ₘ μ₂) {i} = 0 → (κ ∘ₘ μ₁) {i} = 0 := by
    intro h
    rw [Measure.bind_apply .of_discrete η.measurable.aemeasurable, lintegral_fintype,
      Finset.sum_eq_zero_iff] at h
    rw [Measure.bind_apply .of_discrete κ.measurable.aemeasurable, lintegral_fintype,
      Finset.sum_eq_zero_iff]
    intro j _
    rcases mul_eq_zero.1 (h j (Finset.mem_univ _)) with h | h
    · rw [hκ j h, zero_mul]
    · rw [hμ h, mul_zero]
  have hdR : d = (d.toReal : EReal) :=
    (EReal.coe_toReal hdt (ne_bot_of_le_ne_bot EReal.zero_ne_bot hd₀)).symm
  have hD (j) : ∑ i, klTerm (κ j {i}).toReal (η j {i}).toReal ≤ d.toReal := by
    have := hd j
    rwa [fDiv_klFun_eq_sum _ _ fun i h ↦ hκ j h, hdR, EReal.coe_le_coe_iff] at this
  -- zero patterns for `klTerm`
  have hp0 (j) : (μ₂ {j}).toReal = 0 → (μ₁ {j}).toReal = 0 := by
    simp only [ENNReal.toReal_eq_zero_iff, measure_ne_top, or_false]
    exact fun h ↦ hμ h
  have hk0 (j i) : (η j {i}).toReal = 0 → (κ j {i}).toReal = 0 := by
    simp only [ENNReal.toReal_eq_zero_iff, measure_ne_top, or_false]
    exact fun h ↦ hκ j h
  -- masses: equal per kernel row, at most `1`
  have hmassR (j) : ∑ i, (κ j {i}).toReal = ∑ i, (η j {i}).toReal := by
    rw [sum_toReal_singleton, sum_toReal_singleton, hmass]
  have hm1 (j) : ∑ i, (κ j {i}).toReal ≤ 1 := by
    rw [sum_toReal_singleton]
    exact (IsSubProbabilityMeasure.toReal_mem_Icc _).2
  have hp1 : ∑ j, (μ₁ {j}).toReal ≤ 1 := by
    rw [sum_toReal_singleton]
    exact (IsSubProbabilityMeasure.toReal_mem_Icc _).2
  have hg0 (j) : 0 ≤ klTerm (μ₁ {j}).toReal (μ₂ {j}).toReal :=
    klTerm_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg (hp0 j)
  rw [fDiv_klFun_eq_sum _ _ hbind, fDiv_klFun_eq_sum _ _ fun j h ↦ hμ h, hdR, ← EReal.coe_add,
    EReal.coe_le_coe_iff]
  simp_rw [toReal_comp_singleton_eq_sum]
  -- log-sum (klTerm_sum_le)
  calc ∑ i, klTerm (∑ j, (μ₁ {j}).toReal * (κ j {i}).toReal)
        (∑ j, (μ₂ {j}).toReal * (η j {i}).toReal)
      ≤ ∑ i, ∑ j, klTerm ((μ₁ {j}).toReal * (κ j {i}).toReal)
          ((μ₂ {j}).toReal * (η j {i}).toReal) :=
        Finset.sum_le_sum fun i _ ↦ klTerm_sum_le _ (fun _ _ ↦ by positivity)
          (fun _ _ ↦ by positivity) fun j _ h ↦ by
            rcases mul_eq_zero.1 h with h | h
            · rw [hp0 j h, zero_mul]
            · rw [hk0 j i h, mul_zero]
    -- klTerm_mul, then swap sums
    _ = ∑ j, ((∑ i, (κ j {i}).toReal) * klTerm (μ₁ {j}).toReal (μ₂ {j}).toReal +
          (μ₁ {j}).toReal * ∑ i, klTerm (κ j {i}).toReal (η j {i}).toReal +
          ((μ₂ {j}).toReal - (μ₁ {j}).toReal) *
            (∑ i, (η j {i}).toReal - ∑ i, (κ j {i}).toReal)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.sum_congr rfl fun i _ ↦ klTerm_mul ENNReal.toReal_nonneg
          ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg (hp0 j) (hk0 j i)]
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
          Finset.sum_sub_distrib]
    -- the cross term vanishes by equal mass; bound the κ-mass by 1
    _ ≤ ∑ j, (klTerm (μ₁ {j}).toReal (μ₂ {j}).toReal + (μ₁ {j}).toReal * d.toReal) := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        rw [hmassR j, sub_self, mul_zero, add_zero]
        gcongr
        · exact mul_le_of_le_one_left (hg0 j) ((hmassR j).symm ▸ hm1 j)
        · exact hD j
    -- bound the μ₁-mass by 1
    _ ≤ ∑ j, klTerm (μ₁ {j}).toReal (μ₂ {j}).toReal + d.toReal := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        gcongr
        exact mul_le_of_le_one_left (EReal.toReal_nonneg hd₀) hp1

/-- Between scaled point masses the `klFun`-divergence is the generalized KL term. -/
theorem fDiv_klFun_smul_dirac {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hab : b = 0 → a = 0) :
    fDiv klFun (a • dirac PUnit.unit.{u + 1}) (b • dirac PUnit.unit) =
      klTerm a.toReal b.toReal := by
  rw [fDiv_smul_dirac convexOn_klFun continuous_klFun.continuousWithinAt ha hb,
    persp_klFun ENNReal.toReal_nonneg fun h ↦ ?_]
  rw [ENNReal.toReal_eq_zero_iff] at h ⊢
  exact .inl (hab (h.resolve_right hb))

end ProbabilityTheory

namespace GradedDivergence

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {μ ν : Measure X} {r : ℝ≥0∞}

/-- Generalized KL on sub-probability measures: the Barthe–Olmedo divergence with `γ = 0`. -/
noncomputable def klDivergence : GradedDivergence.{u} ℝ≥0∞ :=
  bofDivergence klFun 0

theorem klDivergence_iff_fDiv : klDivergence r μ ν ↔ fDiv klFun μ ν ≤ r := by
  rw [klDivergence, bofDivergence_iff, bofThresh_zero_left]

/-- The budget bounds Mathlib's generalized KL divergence. -/
theorem klDivergence_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDivergence r μ ν ↔ klDiv μ ν ≤ r := by
  rw [klDivergence_iff_fDiv, fDiv_klFun_eq_klDiv, EReal.coe_ennreal_le_coe_ennreal_iff]

/-- Generalized KL is graded. -/
instance isGraded_kl : klDivergence.{u}.IsGraded :=
  isGraded_bofDivergence convexOn_klFun continuous_klFun.continuousWithinAt

/-- Generalized KL is reflexive. -/
instance isReflexive_kl : klDivergence.{u}.IsReflexive :=
  isReflexive_bofDivergence klFun_one

/-- Data processing along a sub-Markov kernel. -/
theorem klDivergence_comp_self [IsFiniteMeasure μ] [IsFiniteMeasure ν] (κ : Kernel X Y)
    [IsSubMarkovKernel κ] (h : klDivergence r μ ν) : klDivergence r (κ ∘ₘ μ) (κ ∘ₘ ν) :=
  bofDivergence_comp_self convexOn_klFun continuous_klFun.continuousWithinAt
    (fun _ ht ↦ klFun_nonneg ht) κ h

/-- Composition for kernels that lose the same mass at every point, with no filling (Rocq
`pdiv_chain_KL` needs mass `1`). -/
theorem klDivergence_comp_of_mass_eq {b c : ℝ≥0∞} {μ₁ μ₂ : Measure X} [IsSubProbabilityMeasure μ₁]
    [IsSubProbabilityMeasure μ₂] {κ η : Kernel X Y} [IsSubMarkovKernel κ] [IsSubMarkovKernel η]
    (hmass : ∀ x, κ x univ = η x univ) (hμ : klDivergence b μ₁ μ₂)
    (hκ : ∀ x, klDivergence c (κ x) (η x)) : klDivergence (b + c) (κ ∘ₘ μ₁) (η ∘ₘ μ₂) := by
  -- the finite-space reduction needs a nonempty source
  cases isEmpty_or_nonempty X
  · rw [μ₁.eq_zero_of_isEmpty, μ₂.eq_zero_of_isEmpty, bind_zero_left, bind_zero_left]
    exact IsGraded.mono zero_le (IsReflexive.refl _)
  simp only [klDivergence_iff_fDiv] at hμ hκ ⊢
  rw [EReal.coe_ennreal_add]
  exact (fDiv_comp_le_of_finite_of_mass convexOn_klFun continuous_klFun.continuousWithinAt
    convexOn_klFun continuous_klFun.continuousWithinAt convexOn_klFun
    continuous_klFun.continuousWithinAt (fun _ _ _ _ ↦ add_le_add) (· = ·)
    (fun h ↦ fDiv_klFun_comp_le_of_mass_eq _ _ _ _ h) κ η hmass).trans
    (add_le_add hμ (iSup_le hκ))

/-- Generalized KL does not compose additively once kernels may lose mass: with point masses
`μ = δ`, `ν = ½ δ` and kernels `δ`, `½ δ` the composite exceeds the sum by `1/4`. -/
theorem not_isComposable_kl : ¬ klDivergence.{u}.IsComposable := by
  intro h
  set P : Measure PUnit.{u + 1} := dirac PUnit.unit
  have hhalf : IsSubProbabilityMeasure ((1 / 2 : ℝ≥0∞) • P) := ⟨by simp [P]⟩
  have : IsSubMarkovKernel (Kernel.const PUnit.{u + 1} P) := ⟨fun _ ↦ by simp; infer_instance⟩
  have : IsSubMarkovKernel (Kernel.const PUnit.{u + 1} ((1 / 2 : ℝ≥0∞) • P)) :=
    ⟨fun _ ↦ by simp only [Kernel.const_apply]; infer_instance⟩
  have h12 : klTerm 1 (1 / 2) = Real.log 2 - 1 / 2 := by
    simp only [klTerm, one_div, div_inv_eq_mul, one_mul]
    ring
  have h14 : klTerm 1 (1 / 4) = 2 * Real.log 2 - 3 / 4 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    simp only [klTerm, one_div, div_inv_eq_mul, one_mul, this]
    ring
  have h0 : 0 ≤ Real.log 2 - 1 / 2 :=
    h12 ▸ klTerm_nonneg zero_le_one (by norm_num) fun h ↦ by norm_num at h
  set b := ENNReal.ofReal (Real.log 2 - 1 / 2)
  have hb : (b : EReal) = ((Real.log 2 - 1 / 2 : ℝ) : EReal) := by
    rw [EReal.coe_ennreal_ofReal, max_eq_left h0]
  have hP : P = (1 : ℝ≥0∞) • P := (one_smul _ _).symm
  have hμ : klDivergence b P ((1 / 2 : ℝ≥0∞) • P) := by
    rw [klDivergence_iff_fDiv, hP, smul_smul, mul_one,
      fDiv_klFun_smul_dirac (by simp) (by simp) (by simp), hb]
    norm_num [h12]
  have hκ : ∀ x, klDivergence b (Kernel.const PUnit.{u + 1} P x)
      (Kernel.const PUnit.{u + 1} ((1 / 2 : ℝ≥0∞) • P) x) := fun _ ↦ by
    simpa only [Kernel.const_apply] using hμ
  have hc := h.comp hμ hκ
  have e1 : P univ • P = (1 : ℝ≥0∞) • P := by simp [P]
  have e2 : ((1 / 2 : ℝ≥0∞) • P) univ • (1 / 2 : ℝ≥0∞) • P = (1 / 4 : ℝ≥0∞) • P := by
    rw [Measure.smul_apply, smul_smul]
    simp only [P, measure_univ, smul_eq_mul, mul_one]
    congr 1
    rw [one_div, one_div, ← ENNReal.mul_inv (by simp) (by simp)]
    norm_num
  rw [klDivergence_iff_fDiv, Measure.const_comp, Measure.const_comp, e1, e2,
    fDiv_klFun_smul_dirac (by simp) (by simp) (by simp)] at hc
  rw [← ENNReal.ofReal_add h0 h0, EReal.coe_ennreal_ofReal,
    max_eq_left (by linarith), EReal.coe_le_coe_iff] at hc
  norm_num at hc
  linarith [h14]

end GradedDivergence
