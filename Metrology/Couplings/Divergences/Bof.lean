module

public import Metrology.Couplings.Divergences.FDivBound
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! Barthe–Olmedo divergences on sub-probability measures without filling: generalized KL and
`α`-Hellinger (Barthe–Olmedo, ICALP 2013). -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory Set Filter Topology InformationTheory
open scoped ENNReal

namespace ProbabilityTheory

/-! ## The Barthe–Olmedo regrading -/

/-- The regrading `t ↦ (exp (γ t) - 1) / γ`, the identity at `γ = 0` (Rocq
`gamma_form_of_additive`). -/
noncomputable def bofReal (γ t : ℝ) : ℝ :=
  if γ = 0 then t else (Real.exp (γ * t) - 1) / γ

theorem bofReal_zero_left (t : ℝ) : bofReal 0 t = t := by simp [bofReal]

theorem bofReal_zero_right (γ : ℝ) : bofReal γ 0 = 0 := by simp [bofReal]

/-- The regrading turns sums into Barthe–Olmedo sums `a + b + γ a b`. -/
theorem bofReal_add (γ s t : ℝ) :
    bofReal γ (s + t) = bofReal γ s + bofReal γ t + γ * bofReal γ s * bofReal γ t := by
  unfold bofReal
  split_ifs with h
  · simp [h]
  · field_simp
    rw [mul_add, Real.exp_add]
    ring

theorem bofReal_mono (γ : ℝ) : Monotone (bofReal γ) := fun s t hst ↦ by
  unfold bofReal
  split_ifs with h
  · exact hst
  rcases lt_or_gt_of_ne h with h | h
  · rw [div_le_div_right_of_neg h]
    linarith [Real.exp_le_exp.2 (mul_le_mul_of_nonpos_left hst h.le)]
  · gcongr

theorem bofReal_nonneg (γ : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ bofReal γ t :=
  bofReal_zero_right γ ▸ bofReal_mono γ ht

/-- For negative `γ` the regrading stays below `-1 / γ`. -/
theorem bofReal_le_of_neg {γ : ℝ} (hγ : γ < 0) (t : ℝ) : bofReal γ t ≤ -1 / γ := by
  simp only [bofReal, hγ.ne, ↓reduceIte]
  rw [div_le_div_right_of_neg hγ]
  linarith [Real.exp_pos (γ * t)]

/-- The Barthe–Olmedo threshold `θ γ` on budgets, `⊤` at `⊤`. -/
noncomputable def bofThresh (γ : ℝ) (r : ℝ≥0∞) : EReal :=
  if r = ⊤ then ⊤ else ((bofReal γ r.toReal : ℝ) : EReal)

@[simp]
theorem bofThresh_top (γ : ℝ) : bofThresh γ ⊤ = ⊤ := by simp [bofThresh]

theorem bofThresh_of_ne_top (γ : ℝ) {r : ℝ≥0∞} (hr : r ≠ ⊤) :
    bofThresh γ r = ((bofReal γ r.toReal : ℝ) : EReal) := by
  simp [bofThresh, hr]

@[simp]
theorem bofThresh_zero (γ : ℝ) : bofThresh γ 0 = 0 := by
  simp [bofThresh, bofReal_zero_right]

/-- At `γ = 0` the threshold is the budget itself. -/
theorem bofThresh_zero_left (r : ℝ≥0∞) : bofThresh 0 r = r := by
  rcases eq_or_ne r ⊤ with rfl | hr
  · simp
  · rw [bofThresh_of_ne_top 0 hr, bofReal_zero_left, EReal.coe_ennreal_toReal hr]

theorem bofThresh_mono (γ : ℝ) : Monotone (bofThresh γ) := fun r r' h ↦ by
  rcases eq_or_ne r' ⊤ with rfl | hr'
  · simp
  have hr : r ≠ ⊤ := ne_top_of_le_ne_top hr' h
  rw [bofThresh_of_ne_top γ hr, bofThresh_of_ne_top γ hr', EReal.coe_le_coe_iff]
  exact bofReal_mono γ (ENNReal.toReal_mono hr' h)

theorem bofThresh_nonneg (γ : ℝ) (r : ℝ≥0∞) : 0 ≤ bofThresh γ r :=
  bofThresh_zero γ ▸ bofThresh_mono γ (zero_le (a := r))

end ProbabilityTheory

/-! ## The Barthe–Olmedo divergence -/

namespace GradedDivergence

/-- The Barthe–Olmedo divergence: the `f`-divergence is below `θ γ` of the budget, with no filling
of lost mass. -/
noncomputable def bofDivergence (f : ℝ → ℝ) (γ : ℝ) : GradedDivergence.{u} ℝ≥0∞ :=
  fDivBound Unit (fun _ _ ↦ f) (fun r _ ↦ bofThresh γ r)

variable {f : ℝ → ℝ} {γ : ℝ} {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]
  {μ ν : Measure X} {r : ℝ≥0∞}

theorem bofDivergence_iff : bofDivergence f γ r μ ν ↔ fDiv f μ ν ≤ bofThresh γ r :=
  ⟨fun h ↦ h (), fun h _ ↦ h⟩

theorem isGraded_bofDivergence (hf : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousWithinAt f (Ici 0) 0) : (bofDivergence.{u} f γ).IsGraded :=
  isGraded_fDivBound (fun _ _ ↦ hf) (fun _ _ ↦ hf_cont) (fun _ _ _ _ _ _ ↦ le_rfl)
    (fun _ _ h _ ↦ bofThresh_mono γ h) fun _ ↦ bofThresh_top γ

theorem isReflexive_bofDivergence (hf1 : f 1 = 0) : (bofDivergence.{u} f γ).IsReflexive :=
  isReflexive_fDivBound fun _ ↦ by simp [hf1]

/-- Data processing along a sub-Markov kernel, for a nonnegative generator. -/
theorem bofDivergence_comp_self (hf : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousWithinAt f (Ici 0) 0) (hf₀ : ∀ t, 0 ≤ t → 0 ≤ f t) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (κ : Kernel X Y) [IsSubMarkovKernel κ]
    (h : bofDivergence f γ r μ ν) : bofDivergence f γ r (κ ∘ₘ μ) (κ ∘ₘ ν) :=
  bofDivergence_iff.2 <| (fDiv_comp_le_of_nonneg hf hf_cont hf₀ κ).trans (bofDivergence_iff.1 h)

end GradedDivergence

/-! ## Generalized KL -/

namespace ProbabilityTheory

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
      rw [EReal.coe_ennreal_ofReal, max_eq_left (integral_nonneg fun _ ↦ klFun_nonneg ENNReal.toReal_nonneg)]
      simp
    · rw [fDiv_of_not_integrable hint,
        klDiv_of_not_integrable (mt (integrable_klFun_rnDeriv_iff hac).2 hint)]
      simp
  · rw [klDiv_of_not_ac hac]
    by_contra h
    exact hac (absolutelyContinuous_of_fDiv_ne_top derivAtTop_klFun (by simpa using h))

/-- The pointwise generalized KL term `p log (p / q) + q - p`. -/
noncomputable def klTerm (p q : ℝ) : ℝ := p * Real.log (p / q) + q - p

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

/-- Total mass of a measure on a finite space as a sum of real point masses. -/
theorem sum_toReal_singleton {I : Type*} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (ρ : Measure I) [IsFiniteMeasure ρ] :
    ∑ i, (ρ {i}).toReal = (ρ univ).toReal := by
  rw [← ENNReal.toReal_sum fun _ _ ↦ measure_ne_top _ _, sum_measure_singleton, Finset.coe_univ]

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
  -- real point masses
  have hp0 (j) : (μ₂ {j}).toReal = 0 → (μ₁ {j}).toReal = 0 := by
    simp only [ENNReal.toReal_eq_zero_iff, measure_ne_top, or_false]
    exact fun h ↦ hμ h
  have hk0 (j i) : (η j {i}).toReal = 0 → (κ j {i}).toReal = 0 := by
    simp only [ENNReal.toReal_eq_zero_iff, measure_ne_top, or_false]
    exact fun h ↦ hκ j h
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
  calc ∑ i, klTerm (∑ j, (μ₁ {j}).toReal * (κ j {i}).toReal)
        (∑ j, (μ₂ {j}).toReal * (η j {i}).toReal)
      ≤ ∑ i, ∑ j, klTerm ((μ₁ {j}).toReal * (κ j {i}).toReal)
          ((μ₂ {j}).toReal * (η j {i}).toReal) :=
        Finset.sum_le_sum fun i _ ↦ klTerm_sum_le _ (fun _ _ ↦ by positivity)
          (fun _ _ ↦ by positivity) fun j _ h ↦ by
            rcases mul_eq_zero.1 h with h | h
            · rw [hp0 j h, zero_mul]
            · rw [hk0 j i h, mul_zero]
    _ = ∑ j, ((∑ i, (κ j {i}).toReal) * klTerm (μ₁ {j}).toReal (μ₂ {j}).toReal +
          (μ₁ {j}).toReal * ∑ i, klTerm (κ j {i}).toReal (η j {i}).toReal +
          ((μ₂ {j}).toReal - (μ₁ {j}).toReal) *
            (∑ i, (η j {i}).toReal - ∑ i, (κ j {i}).toReal)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.sum_congr rfl fun i _ ↦ klTerm_mul ENNReal.toReal_nonneg
          ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg (hp0 j) (hk0 j i)]
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_sub_distrib]
    _ ≤ ∑ j, (klTerm (μ₁ {j}).toReal (μ₂ {j}).toReal + (μ₁ {j}).toReal * d.toReal) := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        rw [hmassR j, sub_self, mul_zero, add_zero]
        gcongr
        · exact mul_le_of_le_one_left (hg0 j) ((hmassR j).symm ▸ hm1 j)
        · exact hD j
    _ ≤ ∑ j, klTerm (μ₁ {j}).toReal (μ₂ {j}).toReal + d.toReal := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        gcongr
        exact mul_le_of_le_one_left (EReal.toReal_nonneg hd₀) hp1

end ProbabilityTheory

namespace ProbabilityTheory

/-- Between scaled point masses the `klFun`-divergence is the generalized KL term. -/
theorem fDiv_klFun_smul_dirac {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hab : b = 0 → a = 0) :
    fDiv klFun (a • dirac PUnit.unit.{u + 1}) (b • dirac PUnit.unit) = klTerm a.toReal b.toReal := by
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

instance isGraded_kl : klDivergence.{u}.IsGraded :=
  isGraded_bofDivergence convexOn_klFun continuous_klFun.continuousWithinAt

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

/-! ## `α`-Hellinger -/

namespace ProbabilityTheory

variable {α : ℝ}

/-- The normalized `α`-Hellinger generator `(α t + 1 - α - t ^ α) / (1 - α)`. -/
noncomputable def hellFun (α t : ℝ) : ℝ := (α * t + (1 - α) - t ^ α) / (1 - α)

/-- The pointwise `α`-Hellinger term `(α p + (1 - α) q - p ^ α q ^ (1 - α)) / (1 - α)`. -/
noncomputable def hellTerm (α p q : ℝ) : ℝ :=
  (α * p + (1 - α) * q - p ^ α * q ^ (1 - α)) / (1 - α)

theorem hellFun_one (α : ℝ) : hellFun α 1 = 0 := by simp [hellFun]

theorem rpow_mul_rpow_le (hα0 : 0 < α) (hα1 : α < 1) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    p ^ α * q ^ (1 - α) ≤ α * p + (1 - α) * q :=
  Real.geom_mean_le_arith_mean2_weighted hα0.le (by linarith) hp hq (by ring)

theorem hellFun_nonneg (hα0 : 0 < α) (hα1 : α < 1) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hellFun α t := by
  have := rpow_mul_rpow_le hα0 hα1 ht zero_le_one
  simp only [Real.one_rpow, mul_one] at this
  exact div_nonneg (by linarith) (by linarith)

theorem hellTerm_nonneg (hα0 : 0 < α) (hα1 : α < 1) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    0 ≤ hellTerm α p q :=
  div_nonneg (by linarith [rpow_mul_rpow_le hα0 hα1 hp hq]) (by linarith)

theorem convexOn_hellFun (hα0 : 0 < α) (hα1 : α < 1) : ConvexOn ℝ (Ici 0) (hellFun α) := by
  have h : ConvexOn ℝ (Ici 0) ((fun t ↦ α * t + (1 - α)) - fun t : ℝ ↦ t ^ α) :=
    ConvexOn.sub ((convexOn_id (convex_Ici 0)).smul hα0.le |>.add_const _)
      (Real.concaveOn_rpow hα0.le hα1.le)
  have := h.smul (inv_nonneg.2 (sub_pos.2 hα1).le)
  refine this.congr fun t _ ↦ ?_
  simp [hellFun, div_eq_inv_mul]

theorem continuous_hellFun (hα0 : 0 ≤ α) : Continuous (hellFun α) := by
  unfold hellFun
  exact (((continuous_const.mul continuous_id).add continuous_const).sub
    (Real.continuous_rpow_const hα0)).div_const _

theorem derivAtTop_hellFun (hα1 : α < 1) :
    derivAtTop (hellFun α) = ((α / (1 - α) : ℝ) : EReal) := by
  refine Tendsto.limsup_eq (EReal.tendsto_coe.2 ?_)
  have hs : 0 < 1 - α := sub_pos.2 hα1
  have h : Tendsto (fun t : ℝ ↦ (α + (1 - α) / t - t ^ (α - 1)) / (1 - α)) atTop
      (𝓝 ((α + 0 - 0) / (1 - α))) := by
    refine ((tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)).sub ?_).div_const _
    simpa [neg_sub] using tendsto_rpow_neg_atTop (y := 1 - α) hs
  rw [add_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [hellFun, Real.rpow_sub ht, Real.rpow_one]
  field_simp

theorem persp_hellFun (hα1 : α < 1) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    persp (hellFun α) p q = hellTerm α p q := by
  have hs : 0 < 1 - α := sub_pos.2 hα1
  rcases hq.eq_or_lt with rfl | hq
  · rw [persp_zero_right, derivAtTop_hellFun hα1, ← EReal.coe_mul, hellTerm,
      Real.zero_rpow hs.ne']
    congr 1
    ring
  rw [persp_of_ne_zero hq.ne', hellFun, hellTerm, EReal.coe_eq_coe_iff,
    Real.div_rpow hp hq.le, Real.rpow_sub hq, Real.rpow_one]
  have : 0 < q ^ α := Real.rpow_pos_of_pos hq α
  field_simp

/-- The Hellinger term of a product splits into weighted terms plus a cross term that vanishes
when summed against kernels of equal mass. -/
theorem hellTerm_mul (hα1 : α < 1) {p q k l : ℝ} (hp : 0 ≤ p) (hk : 0 ≤ k) (hq : 0 ≤ q)
    (hl : 0 ≤ l) :
    hellTerm α (p * k) (q * l) = k * hellTerm α p q + p ^ α * q ^ (1 - α) * hellTerm α k l +
      (q - p ^ α * q ^ (1 - α)) * (l - k) := by
  have hs : (1 - α) ≠ 0 := (sub_pos.2 hα1).ne'
  unfold hellTerm
  rw [Real.mul_rpow hp hk, Real.mul_rpow hq hl]
  field_simp
  ring

theorem hellTerm_sum_le (hα0 : 0 < α) (hα1 : α < 1) {ι : Type*} (s : Finset ι) {a b : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    hellTerm α (∑ i ∈ s, a i) (∑ i ∈ s, b i) ≤ ∑ i ∈ s, hellTerm α (a i) (b i) := by
  have h := persp_sum_le (convexOn_hellFun hα0 hα1) s ha hb
  rwa [persp_hellFun hα1 (Finset.sum_nonneg ha) (Finset.sum_nonneg hb),
    Finset.sum_congr rfl fun i hi ↦ persp_hellFun hα1 (ha i hi) (hb i hi),
    ← EReal.coe_finset_sum, EReal.coe_le_coe_iff] at h

/-- On a finite space the `α`-Hellinger divergence is a real sum of terms. -/
theorem fDiv_hellFun_eq_sum (hα0 : 0 < α) (hα1 : α < 1) {I : Type*} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I] (ρ₁ ρ₂ : Measure I) [IsFiniteMeasure ρ₁]
    [IsFiniteMeasure ρ₂] :
    fDiv (hellFun α) ρ₁ ρ₂ = ((∑ i, hellTerm α (ρ₁ {i}).toReal (ρ₂ {i}).toReal : ℝ) : EReal) := by
  rw [fDiv_eq_sum (convexOn_hellFun hα0 hα1) (continuous_hellFun hα0.le).continuousWithinAt,
    EReal.coe_finset_sum]
  exact Finset.sum_congr rfl fun i _ ↦
    persp_hellFun hα1 ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- The Bhattacharyya mass of two sub-probability measures on a finite space is at most one minus
`1 - α` times their Hellinger divergence. -/
theorem sum_rpow_mul_rpow_le (hα0 : 0 < α) (hα1 : α < 1) {I : Type*} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (ρ₁ ρ₂ : Measure I) [IsSubProbabilityMeasure ρ₁]
    [IsSubProbabilityMeasure ρ₂] :
    ∑ i, (ρ₁ {i}).toReal ^ α * (ρ₂ {i}).toReal ^ (1 - α) ≤
      1 - (1 - α) * ∑ i, hellTerm α (ρ₁ {i}).toReal (ρ₂ {i}).toReal := by
  have hs : (1 - α) ≠ 0 := (sub_pos.2 hα1).ne'
  have hp1 := (sum_toReal_singleton ρ₁).trans_le (IsSubProbabilityMeasure.toReal_mem_Icc _).2
  have hq1 := (sum_toReal_singleton ρ₂).trans_le (IsSubProbabilityMeasure.toReal_mem_Icc _).2
  have hwj (i : I) : (ρ₁ {i}).toReal ^ α * (ρ₂ {i}).toReal ^ (1 - α) = α * (ρ₁ {i}).toReal +
      (1 - α) * (ρ₂ {i}).toReal - (1 - α) * hellTerm α (ρ₁ {i}).toReal (ρ₂ {i}).toReal := by
    simp only [hellTerm]
    field_simp
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ hwj i, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  nlinarith

/-- On a finite space the `α`-Hellinger divergence of sub-probability measures is at most
`1 / (1 - α)`. -/
theorem sum_hellTerm_le_inv (hα0 : 0 < α) (hα1 : α < 1) {I : Type*} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (ρ₁ ρ₂ : Measure I) [IsSubProbabilityMeasure ρ₁]
    [IsSubProbabilityMeasure ρ₂] :
    ∑ i, hellTerm α (ρ₁ {i}).toReal (ρ₂ {i}).toReal ≤ (1 - α)⁻¹ := by
  have h := sum_rpow_mul_rpow_le hα0 hα1 ρ₁ ρ₂
  have h0 : 0 ≤ ∑ i, (ρ₁ {i}).toReal ^ α * (ρ₂ {i}).toReal ^ (1 - α) :=
    Finset.sum_nonneg fun _ _ ↦ by positivity
  rw [← one_div, le_div_iff₀ (sub_pos.2 hα1)]
  linarith

/-- An extended real clamped into `[0, 1 / (1 - α)]`, the range of the `α`-Hellinger divergence on
sub-probability measures. -/
noncomputable def hellClamp (α : ℝ) (a : EReal) : ℝ :=
  (min (max a 0) (((1 - α)⁻¹ : ℝ) : EReal)).toReal

/-- The Barthe–Olmedo chain `a + d - (1 - α) a d` for `α`-Hellinger, on clamped arguments so that
it is monotone. -/
noncomputable def hellChain (α : ℝ) (a d : EReal) : EReal :=
  ((hellClamp α a + hellClamp α d - (1 - α) * hellClamp α a * hellClamp α d : ℝ) : EReal)

theorem hellClamp_coe {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ (1 - α)⁻¹) : hellClamp α x = x := by
  simp [hellClamp, max_eq_left (EReal.coe_nonneg.2 h0), min_eq_left (EReal.coe_le_coe_iff.2 h1)]

section Clamp

variable (hα1 : α < 1)
include hα1

theorem hellClamp_bounds (a : EReal) :
    0 ≤ min (max a 0) (((1 - α)⁻¹ : ℝ) : EReal) ∧
      min (max a 0) (((1 - α)⁻¹ : ℝ) : EReal) ≤ (((1 - α)⁻¹ : ℝ) : EReal) :=
  ⟨le_min (le_max_right _ _) (EReal.coe_nonneg.2 (inv_nonneg.2 (sub_pos.2 hα1).le)),
    min_le_right _ _⟩

theorem hellClamp_mono : Monotone (hellClamp α) := fun a b h ↦
  EReal.toReal_le_toReal (min_le_min_right _ (max_le_max_right 0 h))
    (ne_bot_of_le_ne_bot EReal.zero_ne_bot (hellClamp_bounds hα1 a).1)
    (ne_top_of_le_ne_top (EReal.coe_ne_top _) (hellClamp_bounds hα1 b).2)

theorem hellClamp_nonneg (a : EReal) : 0 ≤ hellClamp α a :=
  EReal.toReal_nonneg (hellClamp_bounds hα1 a).1

theorem mul_hellClamp_le_one (a : EReal) : (1 - α) * hellClamp α a ≤ 1 := by
  have h : hellClamp α a ≤ (1 - α)⁻¹ := (EReal.toReal_le_toReal (hellClamp_bounds hα1 a).2
    (ne_bot_of_le_ne_bot EReal.zero_ne_bot (hellClamp_bounds hα1 a).1)
    (EReal.coe_ne_top _)).trans_eq (EReal.toReal_coe _)
  calc (1 - α) * hellClamp α a ≤ (1 - α) * (1 - α)⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ (sub_pos.2 hα1).ne'

theorem hellChain_mono ⦃a a' d d' : EReal⦄ (ha : a ≤ a') (hd : d ≤ d') :
    hellChain α a d ≤ hellChain α a' d' := by
  simp only [hellChain, EReal.coe_le_coe_iff]
  have h₁ := hellClamp_mono hα1 ha
  have h₂ := hellClamp_mono hα1 hd
  have h₃ := mul_hellClamp_le_one hα1 d'
  have h₄ := mul_hellClamp_le_one hα1 a
  nlinarith [mul_nonneg (sub_nonneg.2 h₁) (sub_nonneg.2 h₃),
    mul_nonneg (sub_nonneg.2 h₂) (sub_nonneg.2 h₄)]

end Clamp

/-- Barthe–Olmedo chain rule for `α`-Hellinger between finite spaces when the two kernels lose the
same mass at every point (Rocq `FdivChain` needs mass `1`). -/
theorem fDiv_hellFun_comp_le_of_mass_eq (hα0 : 0 < α) (hα1 : α < 1) {M N : ℕ} [NeZero M]
    (μ₁ μ₂ : Measure (ULift.{u} (Fin M))) [IsSubProbabilityMeasure μ₁]
    [IsSubProbabilityMeasure μ₂] (κ η : Kernel (ULift.{u} (Fin M)) (ULift.{u} (Fin N)))
    [IsSubMarkovKernel κ] [IsSubMarkovKernel η] (hmass : ∀ j, κ j univ = η j univ) :
    fDiv (hellFun α) (κ ∘ₘ μ₁) (η ∘ₘ μ₂) ≤
      hellChain α (fDiv (hellFun α) μ₁ μ₂) (⨆ j, fDiv (hellFun α) (κ j) (η j)) := by
  set C := hellClamp α (⨆ j, fDiv (hellFun α) (κ j) (η j))
  have hC0 : 0 ≤ C := hellClamp_nonneg hα1 _
  have hsum₀ {I : Type u} [Fintype I] [MeasurableSpace I] (ρ₁ ρ₂ : Measure I) :
      0 ≤ ∑ i, hellTerm α (ρ₁ {i}).toReal (ρ₂ {i}).toReal :=
    Finset.sum_nonneg fun _ _ ↦ hellTerm_nonneg hα0 hα1 ENNReal.toReal_nonneg
      ENNReal.toReal_nonneg
  have hκ (j) : ∑ i, hellTerm α (κ j {i}).toReal (η j {i}).toReal ≤ C := by
    rw [← hellClamp_coe (hsum₀ _ _) (sum_hellTerm_le_inv hα0 hα1 _ _)]
    refine hellClamp_mono hα1 ?_
    rw [← fDiv_hellFun_eq_sum hα0 hα1]
    exact le_iSup (fun j ↦ fDiv (hellFun α) (κ j) (η j)) j
  set p := fun j ↦ (μ₁ {j}).toReal
  set q := fun j ↦ (μ₂ {j}).toReal
  set w := fun j ↦ p j ^ α * q j ^ (1 - α)
  have hw : ∑ j, w j ≤ 1 - (1 - α) * ∑ j, hellTerm α (p j) (q j) :=
    sum_rpow_mul_rpow_le hα0 hα1 μ₁ μ₂
  have hmassR (j) : ∑ i, (κ j {i}).toReal = ∑ i, (η j {i}).toReal := by
    rw [sum_toReal_singleton, sum_toReal_singleton, hmass]
  have hm1 (j) : ∑ i, (κ j {i}).toReal ≤ 1 := by
    rw [sum_toReal_singleton]
    exact (IsSubProbabilityMeasure.toReal_mem_Icc _).2
  have hg0 (j) : 0 ≤ hellTerm α (p j) (q j) :=
    hellTerm_nonneg hα0 hα1 ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  rw [fDiv_hellFun_eq_sum hα0 hα1, fDiv_hellFun_eq_sum hα0 hα1 μ₁ μ₂, hellChain,
    hellClamp_coe (hsum₀ _ _) (sum_hellTerm_le_inv hα0 hα1 _ _), EReal.coe_le_coe_iff]
  simp_rw [toReal_comp_singleton_eq_sum]
  calc ∑ i, hellTerm α (∑ j, p j * (κ j {i}).toReal) (∑ j, q j * (η j {i}).toReal)
      ≤ ∑ i, ∑ j, hellTerm α (p j * (κ j {i}).toReal) (q j * (η j {i}).toReal) :=
        Finset.sum_le_sum fun i _ ↦ hellTerm_sum_le hα0 hα1 _ (fun _ _ ↦ by positivity)
          fun _ _ ↦ by positivity
    _ = ∑ j, ((∑ i, (κ j {i}).toReal) * hellTerm α (p j) (q j) +
          w j * ∑ i, hellTerm α (κ j {i}).toReal (η j {i}).toReal +
          (q j - w j) * (∑ i, (η j {i}).toReal - ∑ i, (κ j {i}).toReal)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.sum_congr rfl fun i _ ↦ hellTerm_mul hα1 ENNReal.toReal_nonneg
          ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
          Finset.sum_sub_distrib, w]
        rfl
    _ ≤ ∑ j, (hellTerm α (p j) (q j) + w j * C) := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        rw [hmassR j, sub_self, mul_zero, add_zero]
        have : 0 ≤ w j := by positivity
        gcongr
        · exact mul_le_of_le_one_left (hg0 j) ((hmassR j).symm ▸ hm1 j)
        · exact hκ j
    _ = ∑ j, hellTerm α (p j) (q j) + (∑ j, w j) * C := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hw hC0]

/-- Between scaled point masses the `α`-Hellinger divergence is the Hellinger term. -/
theorem fDiv_hellFun_smul_dirac (hα0 : 0 < α) (hα1 : α < 1) {a b : ℝ≥0∞} (ha : a ≠ ⊤)
    (hb : b ≠ ⊤) :
    fDiv (hellFun α) (a • dirac PUnit.unit.{u + 1}) (b • dirac PUnit.unit) =
      hellTerm α a.toReal b.toReal := by
  rw [fDiv_smul_dirac (convexOn_hellFun hα0 hα1) (continuous_hellFun hα0.le).continuousWithinAt
    ha hb, persp_hellFun hα1 ENNReal.toReal_nonneg ENNReal.toReal_nonneg]

end ProbabilityTheory

namespace GradedDivergence

variable {α : ℝ} {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {μ ν : Measure X}
  {r : ℝ≥0∞}

/-- The `α`-Hellinger divergence on sub-probability measures: the Barthe–Olmedo divergence with
`γ = α - 1` (Rényi of order `α < 1` after regrading). -/
noncomputable def hellingerDivergence (α : ℝ) : GradedDivergence.{u} ℝ≥0∞ :=
  bofDivergence (hellFun α) (α - 1)

theorem hellingerDivergence_iff :
    hellingerDivergence α r μ ν ↔ fDiv (hellFun α) μ ν ≤ bofThresh (α - 1) r :=
  bofDivergence_iff

section Instances

variable (α) [hα : Fact (α ∈ Ioo (0 : ℝ) 1)]

instance isGraded_hellinger : (hellingerDivergence.{u} α).IsGraded :=
  isGraded_bofDivergence (convexOn_hellFun hα.out.1 hα.out.2)
    (continuous_hellFun hα.out.1.le).continuousWithinAt

instance isReflexive_hellinger : (hellingerDivergence.{u} α).IsReflexive :=
  isReflexive_bofDivergence (hellFun_one α)

end Instances

/-- Data processing along a sub-Markov kernel. -/
theorem hellingerDivergence_comp_self (hα0 : 0 < α) (hα1 : α < 1) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (κ : Kernel X Y) [IsSubMarkovKernel κ] (h : hellingerDivergence α r μ ν) :
    hellingerDivergence α r (κ ∘ₘ μ) (κ ∘ₘ ν) :=
  bofDivergence_comp_self (convexOn_hellFun hα0 hα1) (continuous_hellFun hα0.le).continuousWithinAt
    (fun _ ↦ hellFun_nonneg hα0 hα1) κ h

/-- Barthe–Olmedo composition for kernels that lose the same mass at every point, with no filling
(Rocq `FdivChain` needs mass `1`). -/
theorem hellingerDivergence_comp_of_mass_eq (hα0 : 0 < α) (hα1 : α < 1) {b c : ℝ≥0∞}
    {μ₁ μ₂ : Measure X} [IsSubProbabilityMeasure μ₁] [IsSubProbabilityMeasure μ₂]
    {κ η : Kernel X Y} [IsSubMarkovKernel κ] [IsSubMarkovKernel η]
    (hmass : ∀ x, κ x univ = η x univ) (hμ : hellingerDivergence α b μ₁ μ₂)
    (hκ : ∀ x, hellingerDivergence α c (κ x) (η x)) :
    hellingerDivergence α (b + c) (κ ∘ₘ μ₁) (η ∘ₘ μ₂) := by
  have : Fact (α ∈ Ioo (0 : ℝ) 1) := ⟨⟨hα0, hα1⟩⟩
  cases isEmpty_or_nonempty X
  · rw [μ₁.eq_zero_of_isEmpty, μ₂.eq_zero_of_isEmpty, bind_zero_left, bind_zero_left]
    exact IsGraded.mono zero_le (IsReflexive.refl _)
  simp only [hellingerDivergence_iff] at hμ hκ ⊢
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp
  rcases eq_or_ne c ⊤ with rfl | hc
  · simp
  rw [bofThresh_of_ne_top _ hb] at hμ
  simp only [bofThresh_of_ne_top _ hc] at hκ
  rw [bofThresh_of_ne_top _ (ENNReal.add_ne_top.2 ⟨hb, hc⟩), ENNReal.toReal_add hb hc, bofReal_add]
  have hθ (t : ℝ≥0∞) : 0 ≤ bofReal (α - 1) t.toReal ∧ bofReal (α - 1) t.toReal ≤ (1 - α)⁻¹ :=
    ⟨bofReal_nonneg _ ENNReal.toReal_nonneg, (bofReal_le_of_neg (by linarith) _).trans_eq
      (by rw [div_eq_mul_inv, ← neg_sub, inv_neg]; ring)⟩
  calc fDiv (hellFun α) (κ ∘ₘ μ₁) (η ∘ₘ μ₂)
      ≤ hellChain α (fDiv (hellFun α) μ₁ μ₂) (⨆ x, fDiv (hellFun α) (κ x) (η x)) :=
        fDiv_comp_le_of_finite_of_mass (convexOn_hellFun hα0 hα1)
          (continuous_hellFun hα0.le).continuousWithinAt (convexOn_hellFun hα0 hα1)
          (continuous_hellFun hα0.le).continuousWithinAt (convexOn_hellFun hα0 hα1)
          (continuous_hellFun hα0.le).continuousWithinAt (hellChain_mono hα1) (· = ·)
          (fun h ↦ fDiv_hellFun_comp_le_of_mass_eq hα0 hα1 _ _ _ _ h) κ η hmass
    _ ≤ hellChain α (bofReal (α - 1) b.toReal) (bofReal (α - 1) c.toReal) :=
        hellChain_mono hα1 hμ (iSup_le hκ)
    _ = _ := by
        rw [hellChain, hellClamp_coe (hθ b).1 (hθ b).2, hellClamp_coe (hθ c).1 (hθ c).2,
          EReal.coe_eq_coe_iff]
        ring

/-- `α`-Hellinger does not compose once kernels may lose mass: point masses `δ`, `¼ δ` and
kernels `δ`, `¼ δ` give squared-Hellinger values `1/4` and `9/16 > 15/32` at `α = 1/2`. -/
theorem not_isComposable_hellinger_half : ¬ (hellingerDivergence.{u} (1 / 2)).IsComposable := by
  intro h
  have hα0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hα1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hsq {x : ℝ} (hx : 0 ≤ x) : (x ^ 2) ^ (1 - 1 / 2 : ℝ) = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  have h14 : hellTerm (1 / 2) 1 (1 / 4) = 1 / 4 := by
    have := hsq (x := 1 / 2) (by norm_num)
    rw [hellTerm, Real.one_rpow, one_mul, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, this]
    norm_num
  have h116 : hellTerm (1 / 2) 1 (1 / 16) = 9 / 16 := by
    have := hsq (x := 1 / 4) (by norm_num)
    rw [hellTerm, Real.one_rpow, one_mul, show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, this]
    norm_num
  -- the budget whose threshold is `1/4`
  set t : ℝ := 2 * Real.log (8 / 7)
  have ht : 0 ≤ t := mul_nonneg zero_le_two (Real.log_nonneg (by norm_num))
  have hθ : bofReal (1 / 2 - 1) t = 1 / 4 := by
    have : Real.exp ((1 / 2 - 1) * t) = 7 / 8 := by
      rw [show (1 / 2 - 1) * t = -Real.log (8 / 7) by simp only [t]; ring, Real.exp_neg,
        Real.exp_log (by norm_num)]
      norm_num
    simp only [bofReal, show (1 / 2 - 1 : ℝ) ≠ 0 by norm_num, ↓reduceIte, this]
    norm_num
  set b := ENNReal.ofReal t
  have hbt : b.toReal = t := ENNReal.toReal_ofReal ht
  set P : Measure PUnit.{u + 1} := dirac PUnit.unit
  have : IsSubProbabilityMeasure ((1 / 4 : ℝ≥0∞) • P) := ⟨by simp [P]⟩
  have : IsSubMarkovKernel (Kernel.const PUnit.{u + 1} P) := ⟨fun _ ↦ by simp; infer_instance⟩
  have : IsSubMarkovKernel (Kernel.const PUnit.{u + 1} ((1 / 4 : ℝ≥0∞) • P)) :=
    ⟨fun _ ↦ by simp only [Kernel.const_apply]; infer_instance⟩
  have hP : P = (1 : ℝ≥0∞) • P := (one_smul _ _).symm
  have hq : ((1 / 4 : ℝ≥0∞)).toReal = 1 / 4 := by norm_num
  have hμ : hellingerDivergence (1 / 2) b P ((1 / 4 : ℝ≥0∞) • P) := by
    rw [hellingerDivergence_iff, hP, smul_smul, mul_one,
      fDiv_hellFun_smul_dirac hα0 hα1 (by simp) (by simp), bofThresh_of_ne_top _ (by simp [b]),
      hbt, hθ, ENNReal.toReal_one, hq, h14]
  have hκ : ∀ x, hellingerDivergence (1 / 2) b (Kernel.const PUnit.{u + 1} P x)
      (Kernel.const PUnit.{u + 1} ((1 / 4 : ℝ≥0∞) • P) x) := fun _ ↦ by
    simpa only [Kernel.const_apply] using hμ
  have hc := h.comp hμ hκ
  have e1 : P univ • P = (1 : ℝ≥0∞) • P := by simp [P]
  have e2 : ((1 / 4 : ℝ≥0∞) • P) univ • (1 / 4 : ℝ≥0∞) • P = (1 / 16 : ℝ≥0∞) • P := by
    rw [Measure.smul_apply, smul_smul]
    simp only [P, measure_univ, smul_eq_mul, mul_one]
    congr 1
    rw [one_div, one_div, ← ENNReal.mul_inv (by simp) (by simp)]
    norm_num
  have h16 : ((1 / 16 : ℝ≥0∞)).toReal = 1 / 16 := by norm_num
  rw [hellingerDivergence_iff, Measure.const_comp, Measure.const_comp, e1, e2,
    fDiv_hellFun_smul_dirac hα0 hα1 (by simp) (by simp),
    bofThresh_of_ne_top _ (by simp [b]), ENNReal.toReal_add (by simp [b]) (by simp [b]), hbt,
    bofReal_add, hθ, ENNReal.toReal_one, h16, h116, EReal.coe_le_coe_iff] at hc
  norm_num at hc

end GradedDivergence
