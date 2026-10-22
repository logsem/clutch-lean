module

public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Metrology.Couplings.Divergences.Persp
public import Metrology.Couplings.SubProbability

/-! # Integral `f`-divergences

`fDiv f μ ν` is `∫ f (dμ/dν) dν + f'(∞) μ⊥(X)` (Approximate Span Liftings, Def. 2.7), with its
basic values and monotonicity. Main result: partition sums are below it (`sum_persp_le_fDiv`). -/

@[expose] public section

open MeasureTheory Measure Set Filter Topology
open scoped ENNReal

namespace ProbabilityTheory
open ENNReal (toReal_nonneg)
open EReal (coe_add_top coe_ennreal_nonneg coe_ennreal_pos coe_ennreal_toReal coe_le_coe_iff coe_mul
  coe_nonneg coe_toReal top_mul_of_pos)
open Finset (measurable_sum single_le_sum sum_add_distrib sum_eq_single sum_le_sum sum_mul
  sum_nonneg)
open Real (norm_of_nonneg)

variable {f g : ℝ → ℝ}

/-! ## The `f`-divergence -/

variable {X : Type*} [MeasurableSpace X] {μ ν : Measure X}

open Classical in
/-- The `f`-divergence `∫ f (dμ/dν) dν + f'(∞) μ⊥(X)`, and `⊤` when the integral diverges
(Def. 2.7). -/
noncomputable def fDiv (f : ℝ → ℝ) (μ ν : Measure X) : EReal :=
  if Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν then
    ((∫ x, f (μ.rnDeriv ν x).toReal ∂ν : ℝ) : EReal) + derivAtTop f * μ.singularPart ν univ
  else ⊤

/-- The `f`-divergence when `f ∘ dμ/dν` is integrable. -/
theorem fDiv_of_integrable (h : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    fDiv f μ ν =
      ((∫ x, f (μ.rnDeriv ν x).toReal ∂ν : ℝ) : EReal) + derivAtTop f * μ.singularPart ν univ := by
  simp [fDiv, h]

/-- If `f ∘ (dμ/dν)` is not integrable, the `f`-divergence is `⊤`. -/
theorem fDiv_of_not_integrable (h : ¬Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    fDiv f μ ν = ⊤ := by
  simp [fDiv, h]

/-! ## Values, sign and absolute continuity -/

section

variable (μ ν : Measure X)

/-- On the diagonal the `f`-divergence is the mass times `f 1`. -/
theorem fDiv_self_eq [IsFiniteMeasure μ] :
    fDiv f μ μ = (((μ univ).toReal * f 1 : ℝ) : EReal) := by
  have h : (fun x ↦ f (μ.rnDeriv μ x).toReal) =ᵐ[μ] fun _ ↦ f 1 :=
    μ.rnDeriv_self.mono fun x hx ↦ by simp [hx]
  rw [fDiv_of_integrable ((integrable_const (f 1)).congr h.symm), integral_congr_ae h,
    singularPart_self]
  simp [measureReal_def]

/-- From the zero measure the `f`-divergence is the mass times `f 0`. -/
theorem fDiv_zero_left_eq [IsFiniteMeasure ν] :
    fDiv f 0 ν = (((ν univ).toReal * f 0 : ℝ) : EReal) := by
  have h : (fun x ↦ f ((0 : Measure X).rnDeriv ν x).toReal) =ᵐ[ν] fun _ ↦ f 0 :=
    (rnDeriv_zero ν).mono fun x hx ↦ by simp [hx]
  rw [fDiv_of_integrable ((integrable_const (f 0)).congr h.symm), integral_congr_ae h,
    singularPart_zero]
  simp [measureReal_def]

/-- For a sub-probability measure `μ`, `μ(univ) * c ≤ max 0 c`. -/
theorem toReal_univ_mul_le_max [IsSubProbabilityMeasure μ] (c : ℝ) :
    (μ univ).toReal * c ≤ max 0 c := by
  obtain ⟨h0, h1⟩ := IsSubProbabilityMeasure.toReal_mem_Icc (μ := μ) univ
  exact (mul_le_mul_of_nonneg_left (le_max_right 0 _) h0).trans
    (mul_le_of_le_one_left (le_max_left _ _) h1)

/-- The `f`-divergence of a sub-probability measure with itself is at most `max 0 (f 1)`. -/
theorem fDiv_self_le [IsSubProbabilityMeasure μ] :
    fDiv f μ μ ≤ ((max 0 (f 1) : ℝ) : EReal) := by
  rw [fDiv_self_eq, coe_le_coe_iff]
  exact toReal_univ_mul_le_max μ _

/-- The `f`-divergence of the zero measure from a sub-probability measure `ν` is at most
`max 0 (f 0)`. -/
theorem fDiv_zero_left_le [IsSubProbabilityMeasure ν] :
    fDiv f 0 ν ≤ ((max 0 (f 0) : ℝ) : EReal) := by
  rw [fDiv_zero_left_eq, coe_le_coe_iff]
  exact toReal_univ_mul_le_max ν _

/-- Against the zero measure the `f`-divergence is the mass times the slope at infinity. -/
theorem fDiv_zero_right_eq : fDiv f μ 0 = derivAtTop f * μ univ := by
  simp [fDiv_of_integrable integrable_zero_measure]

end

/-- A divergence with infinite slope at infinity that is finite forces absolute continuity. -/
theorem absolutelyContinuous_of_fDiv_ne_top [μ.HaveLebesgueDecomposition ν]
    (hf : derivAtTop f = ⊤) (h : fDiv f μ ν ≠ ⊤) : μ ≪ ν := by
  by_cases hint : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν
  · rw [← singularPart_eq_zero, ← measure_univ_eq_zero]
    by_contra h0
    rw [fDiv_of_integrable hint, hf,
      top_mul_of_pos (coe_ennreal_pos.2 (pos_iff_ne_zero.2 h0)), coe_add_top] at h
    exact h rfl
  · exact absurd (fDiv_of_not_integrable hint) h

/-- A function nonnegative on `[0, ∞)` has nonnegative `f`-divergence. -/
theorem fDiv_nonneg_of_nonneg (hf : ∀ t, 0 ≤ t → 0 ≤ f t) : 0 ≤ fDiv f μ ν := by
  by_cases hint : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν
  · rw [fDiv_of_integrable hint]
    exact add_nonneg (coe_nonneg.2 (integral_nonneg fun _ ↦ hf _ toReal_nonneg))
      (mul_nonneg (derivAtTop_nonneg hf) (coe_ennreal_nonneg _))
  · simp [fDiv_of_not_integrable hint]

/-! ## Partition sums are below the `f`-divergence -/

/-- A function continuous on `[0, ∞)` is measurable on nonnegative arguments. -/
theorem _root_.ContinuousOn.measurable_comp_of_nonneg (hf : ContinuousOn f (Ici 0)) {G : X → ℝ}
    (hG : Measurable G) (hG0 : ∀ x, 0 ≤ G x) : Measurable fun x ↦ f (G x) := by
  have h : (fun x ↦ f (G x)) = (fun t ↦ f (max t 0)) ∘ G :=
    funext fun x ↦ by simp [max_eq_left (hG0 x)]
  exact h ▸ (hf.comp_continuous (continuous_id.max continuous_const)
    fun t ↦ le_max_right t 0).measurable.comp hG

/-- Multiplying by `D : EReal` on scalars `0 ≤ r ≤ m` is multiplying by a real `d`, nonnegative
when `D` is. -/
theorem exists_real_mul_eq_coe_mul (D : EReal) (m : ℝ) (hD : D = ⊤ → m = 0) (hbot : D ≠ ⊥) :
    ∃ d : ℝ, (∀ r : ℝ, 0 ≤ r → r ≤ m → (r : EReal) * D = (r * d : ℝ)) ∧ (0 ≤ D → 0 ≤ d) := by
  by_cases hDtop : D = ⊤
  · refine ⟨0, fun r hr hrm ↦ ?_, fun _ ↦ le_rfl⟩
    obtain rfl : r = 0 := le_antisymm (by simpa [hD hDtop] using hrm) hr
    simp
  · refine ⟨D.toReal, fun r _ _ ↦ ?_, EReal.toReal_nonneg⟩
    rw [coe_mul, coe_toReal hDtop hbot]

section

variable (hf : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0)
  [IsFiniteMeasure μ] [IsFiniteMeasure ν]
include hf hf_cont

/-- Weighted partition sums are below the `f`-divergence, when the weights sum to `1` or `f` is
nonnegative. -/
theorem sum_persp_integral_le_fDiv {ι : Type*} (s : Finset ι) {w : ι → X → ℝ}
    (hw : ∀ i, Measurable (w i)) (hw0 : ∀ i x, 0 ≤ w i x) (hw1 : ∀ x, ∑ i ∈ s, w i x ≤ 1)
    (h : (∀ x, ∑ i ∈ s, w i x = 1) ∨ ∀ t, 0 ≤ t → 0 ≤ f t) :
    ∑ i ∈ s, persp f (∫ x, w i x ∂μ) (∫ x, w i x ∂ν) ≤ fDiv f μ ν := by
  -- Jensen on the density part and the slope at infinity on the singular part; either the
  -- weights cover everything or `f ≥ 0`, so the uncovered part only drops a nonnegative amount
  by_cases hint : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν
  swap
  · simp [fDiv_of_not_integrable hint]
  set G : X → ℝ := fun x ↦ (μ.rnDeriv ν x).toReal
  set μs := μ.singularPart ν
  have hwi (i) (hi : i ∈ s) (x) : w i x ≤ 1 := (single_le_sum (fun j _ ↦ hw0 j x) hi).trans (hw1 x)
  have hwb (i) (hi : i ∈ s) (x) : ‖w i x‖ ≤ 1 := (norm_of_nonneg (hw0 i x)).le.trans (hwi i hi x)
  have hint_w (i) (hi : i ∈ s) (ρ : Measure X) [IsFiniteMeasure ρ] : Integrable (w i) ρ :=
    .of_bound (hw i).aestronglyMeasurable 1 (ae_of_all _ (hwb i hi))
  have hsplit (i) (hi : i ∈ s) : ∫ x, w i x ∂μ = ∫ x, w i x * G x ∂ν + ∫ x, w i x ∂μs := by
    conv_lhs => rw [← μ.rnDeriv_add_singularPart ν]
    rw [integral_add_measure (hint_w i hi _) (hint_w i hi _),
      integral_withDensity_eq_integral_toReal_smul (measurable_rnDeriv _ _) (rnDeriv_lt_top _ _)]
    simp_rw [smul_eq_mul, mul_comm (μ.rnDeriv ν _).toReal]
    rfl
  have hsing {φ : X → ℝ} (hφ : Integrable φ μs) (hφ1 : ∀ x, φ x ≤ 1) :
      ∫ x, φ x ∂μs ≤ μs.real univ :=
    calc ∫ x, φ x ∂μs ≤ ∫ _, (1 : ℝ) ∂μs := integral_mono hφ (integrable_const 1) hφ1
      _ = μs.real univ := by simp
  -- infinite slope with singular mass makes fDiv = ⊤; otherwise trade the slope for a real `d`
  by_cases htop : derivAtTop f = ⊤ ∧ μs univ ≠ 0
  · rw [fDiv_of_integrable hint, htop.1,
      top_mul_of_pos (coe_ennreal_pos.2 (pos_iff_ne_zero.2 htop.2)), coe_add_top]
    exact le_top
  obtain ⟨d, hd, hd0⟩ := exists_real_mul_eq_coe_mul (derivAtTop f) (μs.real univ)
    (fun hD ↦ by simp [measureReal_def, not_not.1 (not_and.1 htop hD)]) (derivAtTop_ne_bot hf)
  -- per cell: split ∫w dμ into density and singular parts; Jensen on the first, slope on the second
  have hterm (i) (hi : i ∈ s) : persp f (∫ x, w i x ∂μ) (∫ x, w i x ∂ν) ≤
      ((∫ x, w i x * f (G x) ∂ν + (∫ x, w i x ∂μs) * d : ℝ) : EReal) := by
    have hs0 : 0 ≤ ∫ x, w i x ∂μs := integral_nonneg (hw0 i)
    rw [hsplit i hi, ← add_zero (∫ x, w i x ∂ν), EReal.coe_add]
    calc _ ≤ persp f (∫ x, w i x * G x ∂ν) (∫ x, w i x ∂ν) + persp f (∫ x, w i x ∂μs) 0 :=
          persp_add_le hf (integral_nonneg fun x ↦ mul_nonneg (hw0 i x) toReal_nonneg)
            hs0 (integral_nonneg (hw0 i)) le_rfl
      _ ≤ _ := add_le_add (persp_integral_le hf hf_cont (fun _ ↦ toReal_nonneg)
            integrable_toReal_rnDeriv hint (hw i) (hw0 i) (hwi i hi))
            (by rw [persp_zero_right, hd _ hs0 (hsing (hint_w i hi _) (hwi i hi))])
  calc ∑ i ∈ s, persp f (∫ x, w i x ∂μ) (∫ x, w i x ∂ν)
      ≤ ∑ i ∈ s, ((∫ x, w i x * f (G x) ∂ν + (∫ x, w i x ∂μs) * d : ℝ) : EReal) := sum_le_sum hterm
    _ = ((∫ x, (∑ i ∈ s, w i x) * f (G x) ∂ν + (∫ x, ∑ i ∈ s, w i x ∂μs) * d : ℝ) : EReal) := by
        rw [← EReal.coe_finset_sum, sum_add_distrib, ← sum_mul,
          ← integral_finsetSum _ fun i hi ↦ hint.bdd_mul (hw i).aestronglyMeasurable
            (ae_of_all _ (hwb i hi)),
          ← integral_finsetSum _ fun i hi ↦ hint_w i hi _]
        simp_rw [sum_mul]
        rfl
    _ ≤ ((∫ x, f (G x) ∂ν + μs.real univ * d : ℝ) : EReal) := by
        rw [coe_le_coe_iff]
        rcases h with h | h
        · simp [h]
        refine add_le_add (integral_mono ?_ hint fun x ↦
          mul_le_of_le_one_left (h _ toReal_nonneg) (hw1 x))
          (mul_le_mul_of_nonneg_right (hsing (integrable_finsetSum _ fun i hi ↦ hint_w i hi _) hw1)
            (hd0 (derivAtTop_nonneg h)))
        exact hint.bdd_mul (measurable_sum _ fun i _ ↦ hw i).aestronglyMeasurable
          (ae_of_all _ fun x ↦
            (norm_of_nonneg (sum_nonneg fun i _ ↦ hw0 i x)).le.trans (hw1 x))
    _ = fDiv f μ ν := by
        rw [fDiv_of_integrable hint, EReal.coe_add, ← hd _ measureReal_nonneg le_rfl, mul_comm,
          measureReal_def, coe_ennreal_toReal (measure_ne_top _ _)]

/-- Partition sums are below the `f`-divergence (the ≤ half of Thm. 4.7). -/
theorem sum_persp_le_fDiv {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {k : X → ι} (hk : Measurable k) :
    ∑ i, persp f (μ (k ⁻¹' {i})).toReal (ν (k ⁻¹' {i})).toReal ≤ fDiv f μ ν := by
  have hA (i : ι) : MeasurableSet (k ⁻¹' {i}) := hk (measurableSet_singleton i)
  have hsum (x : X) : ∑ i, (k ⁻¹' {i}).indicator (1 : X → ℝ) x = 1 := by
    rw [sum_eq_single (k x) (fun i _ hi ↦ by simp [hi.symm]) (by simp)]
    simp
  simpa only [integral_indicator_const _ (hA _), smul_eq_mul, mul_one, measureReal_def] using
    sum_persp_integral_le_fDiv hf hf_cont Finset.univ (fun i ↦ measurable_const.indicator (hA i))
      (fun i x ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) x) (fun x ↦ (hsum x).le) (.inl hsum)

/-! ## Monotonicity -/

/-- The `f`-divergence is monotone in `f` on `[0, ∞)`, when the smaller `f` is convex and
continuous at `0`. -/
theorem fDiv_mono (h : ∀ t, 0 ≤ t → f t ≤ g t) :
    fDiv f μ ν ≤ fDiv g μ ν := by
  by_cases hg : Integrable (fun x ↦ g (μ.rnDeriv ν x).toReal) ν
  swap
  · simp [fDiv_of_not_integrable hg]
  set G : X → ℝ := fun x ↦ (μ.rnDeriv ν x).toReal
  have hG : Measurable G := (measurable_rnDeriv μ ν).ennreal_toReal
  obtain ⟨a, c, hac⟩ :=
    hf.exists_affine_le_real isClosed_Ici (hf.continuousOn_Ici hf_cont).lowerSemicontinuousOn
  have hfG : Integrable (fun x ↦ f (G x)) ν :=
    integrable_of_le_of_le ((hf.continuousOn_Ici hf_cont).measurable_comp_of_nonneg hG
        fun _ ↦ toReal_nonneg).aestronglyMeasurable
      (ae_of_all _ fun _ ↦ hac _ toReal_nonneg)
      (ae_of_all _ fun _ ↦ h _ toReal_nonneg)
      ((integrable_toReal_rnDeriv.const_mul a).add (integrable_const c)) hg
  rw [fDiv_of_integrable hfG, fDiv_of_integrable hg]
  exact add_le_add (coe_le_coe_iff.2 (integral_mono hfG hg fun _ ↦ h _ toReal_nonneg))
    (mul_le_mul_of_nonneg_right (derivAtTop_mono h) (coe_ennreal_nonneg _))

end

/-! ## Nonnegativity -/

/-- Between probability measures a normalised `f`-divergence is nonnegative. -/
theorem fDiv_nonneg (hf : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0)
    (hf1 : f 1 = 0) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : 0 ≤ fDiv f μ ν := by
  simpa [persp_of_ne_zero, hf1] using
    sum_persp_le_fDiv hf hf_cont (μ := μ) (ν := ν) (k := fun _ : X ↦ (0 : Fin 1)) measurable_const

end ProbabilityTheory
