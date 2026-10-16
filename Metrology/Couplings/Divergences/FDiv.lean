module

public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Metrology.Couplings.Divergences.Persp
public import Metrology.Couplings.SubProbability

/-! Integral `f`-divergences (Approximate Span Liftings, Def. 2.7, Thm. 4.7). -/

@[expose] public section

open MeasureTheory Measure Set Filter Topology
open scoped ENNReal

namespace ProbabilityTheory

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

theorem fDiv_of_integrable (h : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    fDiv f μ ν =
      ((∫ x, f (μ.rnDeriv ν x).toReal ∂ν : ℝ) : EReal) + derivAtTop f * μ.singularPart ν univ := by
  simp [fDiv, h]

theorem fDiv_of_not_integrable (h : ¬Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    fDiv f μ ν = ⊤ := by
  simp [fDiv, h]

/-- A function continuous on `[0, ∞)` is measurable on nonnegative arguments. -/
theorem _root_.ContinuousOn.measurable_comp_of_nonneg (hf : ContinuousOn f (Ici 0)) {G : X → ℝ}
    (hG : Measurable G) (hG0 : ∀ x, 0 ≤ G x) : Measurable fun x ↦ f (G x) := by
  have : Continuous fun t ↦ f (max t 0) :=
    hf.comp_continuous (continuous_id.max continuous_const) fun t ↦ le_max_right t 0
  have h : (fun x ↦ f (G x)) = (fun t ↦ f (max t 0)) ∘ G :=
    funext fun x ↦ by simp [max_eq_left (hG0 x)]
  exact h ▸ this.measurable.comp hG

/-- Weighted partition sums are below the `f`-divergence: Jensen on the density part, the slope
at infinity on the singular part. -/
theorem sum_persp_integral_le_fDiv (hf : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousWithinAt f (Ici 0) 0) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {ι : Type*} (s : Finset ι) {w : ι → X → ℝ} (hw : ∀ i, Measurable (w i))
    (hw0 : ∀ i x, 0 ≤ w i x) (hw1 : ∀ x, ∑ i ∈ s, w i x ≤ 1)
    (h : (∀ x, ∑ i ∈ s, w i x = 1) ∨ ∀ t, 0 ≤ t → 0 ≤ f t) :
    ∑ i ∈ s, persp f (∫ x, w i x ∂μ) (∫ x, w i x ∂ν) ≤ fDiv f μ ν := by
  by_cases hint : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν
  swap
  · simp [fDiv_of_not_integrable hint]
  set G : X → ℝ := fun x ↦ (μ.rnDeriv ν x).toReal
  set μs := μ.singularPart ν
  have hwi (i) (hi : i ∈ s) (x) : w i x ≤ 1 :=
    (Finset.single_le_sum (fun j _ ↦ hw0 j x) hi).trans (hw1 x)
  have hwb (i) (hi : i ∈ s) (x) : ‖w i x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hw0 i x)]
    exact hwi i hi x
  have hint_w (i) (hi : i ∈ s) (ρ : Measure X) [IsFiniteMeasure ρ] : Integrable (w i) ρ :=
    .of_bound (hw i).aestronglyMeasurable 1 (ae_of_all _ (hwb i hi))
  have hsplit (i) (hi : i ∈ s) : ∫ x, w i x ∂μ = ∫ x, w i x * G x ∂ν + ∫ x, w i x ∂μs := by
    conv_lhs => rw [← μ.rnDeriv_add_singularPart ν]
    rw [integral_add_measure (hint_w i hi _) (hint_w i hi _),
      integral_withDensity_eq_integral_toReal_smul (measurable_rnDeriv _ _) (rnDeriv_lt_top _ _)]
    simp_rw [smul_eq_mul, mul_comm (μ.rnDeriv ν _).toReal]
    rfl
  have hsing (i) (hi : i ∈ s) : ∫ x, w i x ∂μs ≤ μs.real univ :=
    calc ∫ x, w i x ∂μs ≤ ∫ _, (1 : ℝ) ∂μs :=
          integral_mono (hint_w i hi _) (integrable_const 1) (hwi i hi)
      _ = μs.real univ := by simp
  by_cases htop : derivAtTop f = ⊤ ∧ μs univ ≠ 0
  · rw [fDiv_of_integrable hint, htop.1,
      EReal.top_mul_of_pos (EReal.coe_ennreal_pos.2 (pos_iff_ne_zero.2 htop.2)), EReal.coe_add_top]
    exact le_top
  -- otherwise the singular part costs a real `d` per unit of mass
  obtain ⟨d, hd, hd0⟩ : ∃ d : ℝ, (∀ r : ℝ, 0 ≤ r → r ≤ μs.real univ →
      (r : EReal) * derivAtTop f = (r * d : ℝ)) ∧ (0 ≤ derivAtTop f → 0 ≤ d) := by
    by_cases hDtop : derivAtTop f = ⊤
    · refine ⟨0, fun r hr hrm ↦ ?_, fun _ ↦ le_rfl⟩
      have h0 : μs univ = 0 := by_contra fun h0 ↦ htop ⟨hDtop, h0⟩
      obtain rfl : r = 0 := le_antisymm (by simpa [measureReal_def, h0] using hrm) hr
      simp
    · refine ⟨(derivAtTop f).toReal, fun r _ _ ↦ ?_, EReal.toReal_nonneg⟩
      rw [EReal.coe_mul, EReal.coe_toReal hDtop (derivAtTop_ne_bot hf)]
  have hterm (i) (hi : i ∈ s) : persp f (∫ x, w i x ∂μ) (∫ x, w i x ∂ν) ≤
      ((∫ x, w i x * f (G x) ∂ν + (∫ x, w i x ∂μs) * d : ℝ) : EReal) := by
    have hs0 : 0 ≤ ∫ x, w i x ∂μs := integral_nonneg (hw0 i)
    rw [hsplit i hi, ← add_zero (∫ x, w i x ∂ν), EReal.coe_add]
    calc _ ≤ persp f (∫ x, w i x * G x ∂ν) (∫ x, w i x ∂ν) + persp f (∫ x, w i x ∂μs) 0 :=
          persp_add_le hf (integral_nonneg fun x ↦ mul_nonneg (hw0 i x) ENNReal.toReal_nonneg)
            hs0 (integral_nonneg (hw0 i)) le_rfl
      _ ≤ _ := add_le_add (persp_integral_le hf hf_cont (fun _ ↦ ENNReal.toReal_nonneg)
            integrable_toReal_rnDeriv hint (hw i) (hw0 i) (hwi i hi))
            (by rw [persp_zero_right, hd _ hs0 (hsing i hi)])
  have hsum_int : Integrable (fun x ↦ (∑ i ∈ s, w i x) * f (G x)) ν :=
    hint.bdd_mul (Finset.measurable_sum _ fun i _ ↦ hw i).aestronglyMeasurable
      (ae_of_all _ fun x ↦ by
        rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ ↦ hw0 i x)]
        exact hw1 x)
  calc ∑ i ∈ s, persp f (∫ x, w i x ∂μ) (∫ x, w i x ∂ν)
      ≤ ∑ i ∈ s, ((∫ x, w i x * f (G x) ∂ν + (∫ x, w i x ∂μs) * d : ℝ) : EReal) :=
        Finset.sum_le_sum hterm
    _ = ((∫ x, (∑ i ∈ s, w i x) * f (G x) ∂ν + (∫ x, ∑ i ∈ s, w i x ∂μs) * d : ℝ) : EReal) := by
        rw [← EReal.coe_finset_sum, Finset.sum_add_distrib, ← Finset.sum_mul,
          ← integral_finsetSum _ fun i hi ↦ hint.bdd_mul (hw i).aestronglyMeasurable
            (ae_of_all _ (hwb i hi)),
          ← integral_finsetSum _ fun i hi ↦ hint_w i hi _]
        simp_rw [Finset.sum_mul]
        rfl
    _ ≤ ((∫ x, f (G x) ∂ν + μs.real univ * d : ℝ) : EReal) := by
        rw [EReal.coe_le_coe_iff]
        rcases h with h | h
        · simp [h]
        refine add_le_add (integral_mono hsum_int hint fun x ↦
          mul_le_of_le_one_left (h _ ENNReal.toReal_nonneg) (hw1 x))
          (mul_le_mul_of_nonneg_right ?_ (hd0 (derivAtTop_nonneg h)))
        calc ∫ x, ∑ i ∈ s, w i x ∂μs ≤ ∫ _, (1 : ℝ) ∂μs :=
              integral_mono (integrable_finsetSum _ fun i hi ↦ hint_w i hi _)
                (integrable_const 1) hw1
          _ = μs.real univ := by simp
    _ = fDiv f μ ν := by
        rw [fDiv_of_integrable hint, EReal.coe_add, ← hd _ measureReal_nonneg le_rfl, mul_comm,
          measureReal_def, EReal.coe_ennreal_toReal (measure_ne_top _ _)]

/-- Partition sums are below the `f`-divergence. -/
theorem sum_persp_le_fDiv (hf : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {k : X → ι} (hk : Measurable k) :
    ∑ i, persp f (μ (k ⁻¹' {i})).toReal (ν (k ⁻¹' {i})).toReal ≤ fDiv f μ ν := by
  classical
  have hA (i : ι) : MeasurableSet (k ⁻¹' {i}) := hk (measurableSet_singleton i)
  have hsum (x : X) : ∑ i, (k ⁻¹' {i}).indicator (1 : X → ℝ) x = 1 := by
    rw [Finset.sum_eq_single (k x) (fun i _ hi ↦ by simp [Ne.symm hi]) (by simp)]
    simp
  have := sum_persp_integral_le_fDiv (μ := μ) (ν := ν) hf hf_cont Finset.univ
    (fun i ↦ measurable_const.indicator (hA i))
    (fun i x ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) x) (fun x ↦ (hsum x).le) (.inl hsum)
  simpa only [integral_indicator_const _ (hA _), smul_eq_mul, mul_one, measureReal_def] using this

/-! ## The partition characterisation -/

/-- Above an affine minorant `ℓ`, the `f`-divergence is the lower integral of `f - ℓ` at the
density, plus the integral of `ℓ`, plus the singular part. -/
theorem fDiv_eq_lintegral_sub (hf : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousWithinAt f (Ici 0) 0) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {a c : ℝ}
    (h : ∀ t, 0 ≤ t → a * t + c ≤ f t) :
    fDiv f μ ν = ((∫⁻ x, ENNReal.ofReal (f (μ.rnDeriv ν x).toReal -
        (a * (μ.rnDeriv ν x).toReal + c)) ∂ν : ℝ≥0∞) : EReal) +
      ((∫ x, (a * (μ.rnDeriv ν x).toReal + c) ∂ν : ℝ) : EReal) +
      derivAtTop f * μ.singularPart ν univ := by
  set G : X → ℝ := fun x ↦ (μ.rnDeriv ν x).toReal
  have hG : Measurable G := (measurable_rnDeriv μ ν).ennreal_toReal
  have hL : Integrable (fun x ↦ a * G x + c) ν :=
    (integrable_toReal_rnDeriv.const_mul a).add (integrable_const c)
  have hφ0 : 0 ≤ᵐ[ν] fun x ↦ f (G x) - (a * G x + c) :=
    ae_of_all _ fun x ↦ sub_nonneg.2 (h _ ENNReal.toReal_nonneg)
  by_cases hint : Integrable (fun x ↦ f (G x)) ν
  · have h := ofReal_integral_eq_lintegral_ofReal (hint.sub hL) hφ0
    simp only [Pi.sub_apply] at h
    rw [fDiv_of_integrable hint, ← h, EReal.coe_ennreal_ofReal,
      max_eq_left (integral_nonneg_of_ae hφ0), ← EReal.coe_add, integral_sub hint hL,
      sub_add_cancel]
  have htop : ∫⁻ x, ENNReal.ofReal (f (G x) - (a * G x + c)) ∂ν = ⊤ := by
    by_contra hne
    have hfG := (hf.continuousOn_Ici hf_cont).measurable_comp_of_nonneg hG
      fun _ ↦ ENNReal.toReal_nonneg
    refine hint (((?_ : Integrable (fun x ↦ f (G x) - (a * G x + c)) ν).add hL).congr
      (ae_of_all _ fun x ↦ by simp))
    exact ⟨(hfG.sub ((hG.const_mul a).add_const c)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hφ0).2 (lt_top_iff_ne_top.2 hne)⟩
  rw [fDiv_of_not_integrable hint, htop, EReal.coe_ennreal_top, EReal.top_add_coe,
    EReal.top_add_of_ne_bot (derivAtTop_mul_ne_bot hf (measure_ne_top _ _))]

theorem measurable_partialSups_affine {a c : ℕ → ℝ} {G : X → ℝ} (hG : Measurable G) (N : ℕ) :
    Measurable fun x ↦ partialSups (fun i ↦ a i * G x + c i) N := by
  simp_rw [partialSups_eq_sup'_range]
  exact Finset.measurable_range_sup'' fun i _ ↦ (hG.const_mul _).add_const _

/-- The maximum of finitely many affine functions of an integrable function is integrable. -/
theorem integrable_partialSups_affine [IsFiniteMeasure ν] {a c : ℕ → ℝ} {G : X → ℝ}
    (hG : Measurable G) (hGi : Integrable G ν) (N : ℕ) :
    Integrable (fun x ↦ partialSups (fun i ↦ a i * G x + c i) N) ν := by
  refine Integrable.mono' (g := fun x ↦ ∑ i ∈ Finset.range (N + 1), |a i * G x + c i|)
    (integrable_finsetSum _ fun i _ ↦ ((hGi.const_mul _).add (integrable_const _)).abs)
    (measurable_partialSups_affine hG N).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
    fun i ↦ a i * G x + c i
  rw [Real.norm_eq_abs, partialSups_eq_sup'_range, he]
  exact Finset.single_le_sum (f := fun i ↦ |a i * G x + c i|) (fun _ _ ↦ abs_nonneg _) hi

/-- Finitely many affine minorants: the integral of their maximum at the density, plus the
singular part, is at most a partition sum. -/
theorem exists_partition_ge_integral_partialSups_add {a c : ℕ → ℝ}
    (h : ∀ i t, 0 ≤ t → a i * t + c i ≤ f t) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (N : ℕ) :
    ∃ k : X → Fin (N + 2), Measurable k ∧
      ((∫ x, partialSups (fun i ↦ a i * (μ.rnDeriv ν x).toReal + c i) N ∂ν : ℝ) : EReal) +
        derivAtTop f * μ.singularPart ν univ ≤
      ∑ i, persp f (μ (k ⁻¹' {i})).toReal (ν (k ⁻¹' {i})).toReal := by
  classical
  set G : X → ℝ := fun x ↦ (μ.rnDeriv ν x).toReal
  have hG : Measurable G := (measurable_rnDeriv μ ν).ennreal_toReal
  have hGi : Integrable G ν := integrable_toReal_rnDeriv
  set H : X → ℝ := fun x ↦ partialSups (fun i ↦ a i * G x + c i) N
  have hH : Measurable H := measurable_partialSups_affine hG N
  -- a dominating minorant at each point, chosen measurably
  have hex (x : X) : ∃ i, i ≤ N ∧ a i * G x + c i = H x := by
    obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
      fun i ↦ a i * G x + c i
    exact ⟨i, Nat.lt_succ_iff.1 (Finset.mem_range.1 hi), by
      simp only [H, partialSups_eq_sup'_range, he]⟩
  set j : X → ℕ := fun x ↦ Nat.find (hex x)
  have hj : Measurable j := measurable_find hex fun i ↦
    (MeasurableSet.const (i ≤ N)).inter (measurableSet_eq_fun ((hG.const_mul _).add_const _) hH)
  have hjN (x : X) : j x ≤ N := (Nat.find_spec (hex x)).1
  have hjH (x : X) : a (j x) * G x + c (j x) = H x := (Nat.find_spec (hex x)).2
  -- `T` carries the density part, its complement the singular part
  set T := (mutuallySingular_singularPart μ ν).nullSet
  have hT : MeasurableSet T := (mutuallySingular_singularPart μ ν).measurableSet_nullSet
  have hνT : ν Tᶜ = 0 := (mutuallySingular_singularPart μ ν).measure_compl_nullSet
  have hμsT : μ.singularPart ν T = 0 := (mutuallySingular_singularPart μ ν).measure_nullSet
  let k : X → Fin (N + 2) := fun x ↦ if x ∈ T then Fin.ofNat (N + 2) (j x) else Fin.last (N + 1)
  have hk : Measurable k :=
    Measurable.ite hT ((measurable_of_countable (Fin.ofNat (N + 2))).comp hj) measurable_const
  have hjk (x : X) : j x % (N + 2) = j x := Nat.mod_eq_of_lt (by have := hjN x; omega)
  set C : Fin (N + 1) → Set X := fun i ↦ T ∩ {x | j x = i}
  have hC (i : Fin (N + 1)) : MeasurableSet (C i) := hT.inter (hj (measurableSet_singleton _))
  have hcell (i : Fin (N + 1)) : k ⁻¹' {i.castSucc} = C i := by
    ext x
    by_cases hx : x ∈ T
    · simp [k, C, hx, Fin.ext_iff, hjk]
    · simp [k, C, hx, (Fin.castSucc_lt_last i).ne']
  have hlast : k ⁻¹' {Fin.last (N + 1)} = Tᶜ := by
    ext x
    by_cases hx : x ∈ T
    · simp [k, hx, Fin.ext_iff, hjk, (hjN x).trans_lt (Nat.lt_succ_self N) |>.ne]
    · simp [k, hx]
  -- masses inside `T` are integrals of the density
  have hμ (A : Set X) (hA : MeasurableSet A) (hAT : A ⊆ T) : (μ A).toReal = ∫ x in A, G x ∂ν := by
    rw [setIntegral_toReal_rnDeriv_eq_withDensity' hA, measureReal_def]
    conv_lhs => rw [← μ.singularPart_add_rnDeriv ν]
    rw [Measure.add_apply, measure_mono_null hAT hμsT, zero_add]
  have hμTc : μ Tᶜ = μ.singularPart ν univ := by
    conv_lhs => rw [← μ.singularPart_add_rnDeriv ν]
    rw [Measure.add_apply, withDensity_absolutelyContinuous _ _ hνT, add_zero,
      ← measure_add_measure_compl hT, hμsT, zero_add]
  have hterm (i : Fin (N + 1)) : ((∫ x in C i, H x ∂ν : ℝ) : EReal) ≤
      persp f (μ (C i)).toReal (ν (C i)).toReal := by
    refine Eq.trans_le ?_ (affine_le_persp (h i) ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    rw [hμ _ (hC i) inter_subset_left, setIntegral_congr_fun (hC i) fun x hx ↦
      (show H x = a i * G x + c i by rw [← hjH x, hx.2])]
    rw [integral_add (hGi.integrableOn.const_mul _) (integrableOn_const (measure_ne_top _ _)),
      integral_const_mul, setIntegral_const, smul_eq_mul, measureReal_def, mul_comm (c i)]
  have hUnion : ⋃ i, C i = T := by
    ext x
    simp only [C, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun ⟨_, hx, _⟩ ↦ hx, fun hx ↦ ⟨⟨j x, by have := hjN x; omega⟩, hx, rfl⟩⟩
  have hdisj : Pairwise (Function.onFun Disjoint C) := fun i i' hii' ↦
    disjoint_left.2 fun x hx hx' ↦ hii' (Fin.ext (hx.2.symm.trans hx'.2))
  have hHi : Integrable H ν := integrable_partialSups_affine hG hGi N
  have hT_ae : ∀ᵐ x ∂ν, x ∈ T := by
    simpa using measure_eq_zero_iff_ae_notMem.1 hνT
  refine ⟨k, hk, ?_⟩
  rw [Fin.sum_univ_castSucc, hlast, hνT, hμTc, ENNReal.toReal_zero, persp_zero_right]
  simp_rw [hcell]
  calc ((∫ x, H x ∂ν : ℝ) : EReal) + derivAtTop f * μ.singularPart ν univ
      = ∑ i, ((∫ x in C i, H x ∂ν : ℝ) : EReal) +
          ((μ.singularPart ν univ).toReal : EReal) * derivAtTop f := by
        rw [← EReal.coe_finset_sum, ← integral_iUnion_fintype hC hdisj fun _ ↦ hHi.integrableOn,
          hUnion, restrict_eq_self_of_ae_mem hT_ae, mul_comm,
          EReal.coe_ennreal_toReal (measure_ne_top _ _)]
    _ ≤ _ := add_le_add (Finset.sum_le_sum fun i _ ↦ hterm i) le_rfl

/-- The `f`-divergence is at most the supremum of its partition sums: partition by the dominating
piece of a growing family of affine minorants, plus the singular set. -/
theorem fDiv_le_iSup_partition (hf : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousWithinAt f (Ici 0) 0) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv f μ ν ≤ ⨆ (n : ℕ) (k : X → Fin n) (_ : Measurable k),
      ∑ i, persp f (μ (k ⁻¹' {i})).toReal (ν (k ⁻¹' {i})).toReal := by
  obtain ⟨l, c, hle, hsup⟩ :=
    hf.real_sSup_of_nat_affine_eq isClosed_Ici (hf.continuousOn_Ici hf_cont).lowerSemicontinuousOn
  set a : ℕ → ℝ := fun i ↦ l i 1
  have hl (i : ℕ) (t : ℝ) : l i t = a i * t := by
    simpa [a, mul_comm] using (l i).map_smul t 1
  have hmin (i : ℕ) (t : ℝ) (ht : 0 ≤ t) : a i * t + c i ≤ f t := by
    simpa [hl] using hle i ⟨t, ht⟩
  have hsup' (t : ℝ) (ht : 0 ≤ t) : ⨆ i, (a i * t + c i) = f t := by
    simpa [iSup_apply, hl] using congrFun hsup ⟨t, ht⟩
  set G : X → ℝ := fun x ↦ (μ.rnDeriv ν x).toReal
  have hG : Measurable G := (measurable_rnDeriv μ ν).ennreal_toReal
  set H : ℕ → X → ℝ := fun N x ↦ partialSups (fun i ↦ a i * G x + c i) N
  set L : X → ℝ := fun x ↦ a 0 * G x + c 0
  have hLi : Integrable L ν := (integrable_toReal_rnDeriv.const_mul _).add (integrable_const _)
  have hLm : Measurable L := (hG.const_mul _).add_const _
  have hHL (N : ℕ) (x : X) : L x ≤ H N x :=
    le_partialSups_of_le (fun i ↦ a i * G x + c i) (Nat.zero_le N)
  have hbdd (x : X) : BddAbove (range fun i ↦ a i * G x + c i) :=
    ⟨f (G x), forall_mem_range.2 fun i ↦ hmin i _ ENNReal.toReal_nonneg⟩
  have hHmono (x : X) : Monotone fun N ↦ H N x := (partialSups _).monotone
  have hHlim (x : X) : Tendsto (fun N ↦ H N x) atTop (𝓝 (f (G x))) := by
    have := tendsto_atTop_ciSup (hHmono x) (bddAbove_range_partialSups.2 (hbdd x))
    rwa [ciSup_partialSups_eq (hbdd x), hsup' _ ENNReal.toReal_nonneg] at this
  -- above `L`, the lower integrals of the partial maxima increase to that of `f`
  set E : ℕ → ℝ≥0∞ := fun N ↦ ∫⁻ x, ENNReal.ofReal (H N x - L x) ∂ν
  have hE (N : ℕ) :
      ((∫ x, H N x ∂ν : ℝ) : EReal) = (E N : EReal) + ((∫ x, L x ∂ν : ℝ) : EReal) := by
    have hHi : Integrable (H N) ν := integrable_partialSups_affine hG integrable_toReal_rnDeriv N
    have hφ0 : 0 ≤ᵐ[ν] fun x ↦ H N x - L x := ae_of_all _ fun x ↦ sub_nonneg.2 (hHL N x)
    have h := ofReal_integral_eq_lintegral_ofReal (hHi.sub hLi) hφ0
    simp only [Pi.sub_apply] at h
    rw [show E N = _ from h.symm, EReal.coe_ennreal_ofReal,
      max_eq_left (integral_nonneg_of_ae hφ0), ← EReal.coe_add, integral_sub hHi hLi,
      sub_add_cancel]
  have hElim : Tendsto E atTop (𝓝 (∫⁻ x, ENNReal.ofReal (f (G x) - L x) ∂ν)) :=
    lintegral_tendsto_of_tendsto_of_monotone
      (fun N ↦ ((measurable_partialSups_affine hG N).sub hLm).ennreal_ofReal.aemeasurable)
      (ae_of_all _ fun x _ _ hNM ↦ ENNReal.ofReal_le_ofReal (sub_le_sub_right (hHmono x hNM) _))
      (ae_of_all _ fun x ↦ (ENNReal.continuous_ofReal.tendsto _).comp ((hHlim x).sub_const _))
  have hK : ((∫ x, L x ∂ν : ℝ) : EReal) + derivAtTop f * μ.singularPart ν univ ≠ ⊥ :=
    EReal.add_ne_bot_iff.2 ⟨EReal.coe_ne_bot _, derivAtTop_mul_ne_bot hf (measure_ne_top _ _)⟩
  rw [fDiv_eq_lintegral_sub hf hf_cont (hmin 0), add_assoc]
  refine le_of_tendsto' ((EReal.continuousAt_add (Or.inr hK)
    (Or.inl (EReal.coe_ennreal_ne_bot _))).tendsto.comp
    (((continuous_coe_ennreal_ereal.tendsto _).comp hElim).prodMk_nhds tendsto_const_nhds))
    fun N ↦ ?_
  obtain ⟨k, hk, hle⟩ :=
    exists_partition_ge_integral_partialSups_add (μ := μ) (ν := ν) (fun i ↦ hmin i) N
  refine Eq.trans_le ?_ (le_iSup_of_le (N + 2) <| le_iSup_of_le k <| le_iSup_of_le hk hle)
  simp only [Function.comp_apply]
  rw [← add_assoc, ← hE N]

/-- The `f`-divergence is the supremum of its sums over finite measurable partitions
(Def. 2.7, Thm. 4.7). -/
theorem fDiv_eq_iSup_partition (hf : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousWithinAt f (Ici 0) 0) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv f μ ν = ⨆ (n : ℕ) (k : X → Fin n) (_ : Measurable k),
      ∑ i, persp f (μ (k ⁻¹' {i})).toReal (ν (k ⁻¹' {i})).toReal :=
  le_antisymm (fDiv_le_iSup_partition hf hf_cont)
    (iSup_le fun _ ↦ iSup_le fun _ ↦ iSup_le fun hk ↦ sum_persp_le_fDiv hf hf_cont hk)

/-- A larger weight gives a larger `f`-divergence; only the smaller weight needs to be convex, so
that its integral is bounded below. -/
theorem fDiv_mono (hf : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0)
    (h : ∀ t, 0 ≤ t → f t ≤ g t) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv f μ ν ≤ fDiv g μ ν := by
  by_cases hg : Integrable (fun x ↦ g (μ.rnDeriv ν x).toReal) ν
  swap
  · simp [fDiv_of_not_integrable hg]
  set G : X → ℝ := fun x ↦ (μ.rnDeriv ν x).toReal
  have hG : Measurable G := (measurable_rnDeriv μ ν).ennreal_toReal
  obtain ⟨a, c, hac⟩ :=
    hf.exists_affine_le_real isClosed_Ici (hf.continuousOn_Ici hf_cont).lowerSemicontinuousOn
  have hfG : Integrable (fun x ↦ f (G x)) ν :=
    integrable_of_le_of_le
      ((hf.continuousOn_Ici hf_cont).measurable_comp_of_nonneg hG
        fun _ ↦ ENNReal.toReal_nonneg).aestronglyMeasurable
      (ae_of_all _ fun _ ↦ hac _ ENNReal.toReal_nonneg)
      (ae_of_all _ fun _ ↦ h _ ENNReal.toReal_nonneg)
      ((integrable_toReal_rnDeriv.const_mul a).add (integrable_const c)) hg
  rw [fDiv_of_integrable hfG, fDiv_of_integrable hg]
  exact add_le_add (EReal.coe_le_coe_iff.2 (integral_mono hfG hg fun _ ↦ h _ ENNReal.toReal_nonneg))
    (mul_le_mul_of_nonneg_right (derivAtTop_mono h) (EReal.coe_ennreal_nonneg _))

/-! ## Values and data processing -/

/-- On the diagonal the `f`-divergence is the mass times `f 1`. -/
theorem fDiv_self_eq (μ : Measure X) [IsFiniteMeasure μ] :
    fDiv f μ μ = (((μ univ).toReal * f 1 : ℝ) : EReal) := by
  have h : (fun x ↦ f (μ.rnDeriv μ x).toReal) =ᵐ[μ] fun _ ↦ f 1 :=
    μ.rnDeriv_self.mono fun x hx ↦ by simp [hx]
  rw [fDiv_of_integrable ((integrable_const (f 1)).congr h.symm), integral_congr_ae h,
    singularPart_self]
  simp [measureReal_def]

theorem fDiv_self (hf1 : f 1 = 0) (μ : Measure X) [SigmaFinite μ] : fDiv f μ μ = 0 := by
  have h : (fun x ↦ f (μ.rnDeriv μ x).toReal) =ᵐ[μ] fun _ ↦ 0 :=
    μ.rnDeriv_self.mono fun x hx ↦ by simp [hx, hf1]
  rw [fDiv_of_integrable ((integrable_zero _ _ _).congr h.symm), integral_congr_ae h,
    singularPart_self]
  simp

/-- From the zero measure the `f`-divergence is the mass times `f 0`. -/
theorem fDiv_zero_left_eq (ν : Measure X) [IsFiniteMeasure ν] :
    fDiv f 0 ν = (((ν univ).toReal * f 0 : ℝ) : EReal) := by
  have h : (fun x ↦ f ((0 : Measure X).rnDeriv ν x).toReal) =ᵐ[ν] fun _ ↦ f 0 :=
    (rnDeriv_zero ν).mono fun x hx ↦ by simp [hx]
  rw [fDiv_of_integrable ((integrable_const (f 0)).congr h.symm), integral_congr_ae h,
    singularPart_zero]
  simp [measureReal_def]

theorem fDiv_zero_left (hf0 : f 0 = 0) (ν : Measure X) : fDiv f 0 ν = 0 := by
  have h : (fun x ↦ f ((0 : Measure X).rnDeriv ν x).toReal) =ᵐ[ν] fun _ ↦ 0 :=
    (rnDeriv_zero ν).mono fun x hx ↦ by simp [hx, hf0]
  rw [fDiv_of_integrable ((integrable_zero _ _ _).congr h.symm), integral_congr_ae h,
    singularPart_zero]
  simp

theorem fDiv_self_le (μ : Measure X) [IsSubProbabilityMeasure μ] :
    fDiv f μ μ ≤ ((max 0 (f 1) : ℝ) : EReal) := by
  rw [fDiv_self_eq, EReal.coe_le_coe_iff]
  obtain ⟨h0, h1⟩ := IsSubProbabilityMeasure.toReal_mem_Icc (μ := μ) univ
  exact (mul_le_mul_of_nonneg_left (le_max_right 0 _) h0).trans
    (mul_le_of_le_one_left (le_max_left _ _) h1)

theorem fDiv_zero_left_le (ν : Measure X) [IsSubProbabilityMeasure ν] :
    fDiv f 0 ν ≤ ((max 0 (f 0) : ℝ) : EReal) := by
  rw [fDiv_zero_left_eq, EReal.coe_le_coe_iff]
  obtain ⟨h0, h1⟩ := IsSubProbabilityMeasure.toReal_mem_Icc (μ := ν) univ
  exact (mul_le_mul_of_nonneg_left (le_max_right 0 _) h0).trans
    (mul_le_of_le_one_left (le_max_left _ _) h1)

/-- A divergence with infinite slope at infinity that is finite forces absolute continuity. -/
theorem absolutelyContinuous_of_fDiv_ne_top [μ.HaveLebesgueDecomposition ν]
    (hf : derivAtTop f = ⊤) (h : fDiv f μ ν ≠ ⊤) : μ ≪ ν := by
  by_cases hint : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν
  · rw [← singularPart_eq_zero, ← measure_univ_eq_zero]
    by_contra h0
    rw [fDiv_of_integrable hint, hf,
      EReal.top_mul_of_pos (EReal.coe_ennreal_pos.2 (pos_iff_ne_zero.2 h0)), EReal.coe_add_top] at h
    exact h rfl
  · exact absurd (fDiv_of_not_integrable hint) h

theorem fDiv_nonneg_of_nonneg (hf : ∀ t, 0 ≤ t → 0 ≤ f t) : 0 ≤ fDiv f μ ν := by
  by_cases hint : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν
  · rw [fDiv_of_integrable hint]
    exact add_nonneg (EReal.coe_nonneg.2 (integral_nonneg fun _ ↦ hf _ ENNReal.toReal_nonneg))
      (mul_nonneg (derivAtTop_nonneg hf) (EReal.coe_ennreal_nonneg _))
  · simp [fDiv_of_not_integrable hint]

/-- Between probability measures a normalised `f`-divergence is nonnegative. -/
theorem fDiv_nonneg (hf : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0)
    (hf1 : f 1 = 0) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : 0 ≤ fDiv f μ ν := by
  simpa [persp_of_ne_zero, hf1] using
    sum_persp_le_fDiv hf hf_cont (μ := μ) (ν := ν) (k := fun _ : X ↦ (0 : Fin 1)) measurable_const

variable {Y : Type*} [MeasurableSpace Y]

/-- Data processing along a sub-Markov kernel; when the kernel may lose mass, the weight must be
nonnegative. -/
theorem fDiv_comp_le_of_isSubMarkovKernel (hf : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousWithinAt f (Ici 0) 0) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel X Y) [IsSubMarkovKernel κ] (h : (∀ x, κ x univ = 1) ∨ ∀ t, 0 ≤ t → 0 ≤ f t) :
    fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ fDiv f μ ν := by
  rw [fDiv_eq_iSup_partition hf hf_cont]
  refine iSup_le fun n ↦ iSup_le fun k ↦ iSup_le fun hk ↦ ?_
  have hA (i : Fin n) : MeasurableSet (k ⁻¹' {i}) := hk (measurableSet_singleton i)
  have hw (x : X) : ∑ i, (κ x (k ⁻¹' {i})).toReal = (κ x univ).toReal := by
    rw [← ENNReal.toReal_sum fun _ _ ↦ measure_ne_top _ _,
      sum_measure_preimage_singleton _ fun i _ ↦ hA i, Finset.coe_univ, preimage_univ]
  have hint (ρ : Measure X) [IsFiniteMeasure ρ] (i : Fin n) :
      ((κ ∘ₘ ρ) (k ⁻¹' {i})).toReal = ∫ x, (κ x (k ⁻¹' {i})).toReal ∂ρ := by
    rw [Measure.bind_apply (hA i) κ.aemeasurable,
      integral_toReal (κ.measurable_coe (hA i)).aemeasurable (ae_of_all _ fun _ ↦
        measure_lt_top _ _)]
  simp_rw [hint]
  refine sum_persp_integral_le_fDiv hf hf_cont Finset.univ
    (fun i ↦ (κ.measurable_coe (hA i)).ennreal_toReal) (fun _ _ ↦ ENNReal.toReal_nonneg)
    (fun x ↦ ?_) (h.imp_left fun h x ↦ by rw [hw, h, ENNReal.toReal_one])
  rw [hw]
  exact (IsSubProbabilityMeasure.toReal_mem_Icc (μ := κ x) _).2

/-- Data processing along a Markov kernel. -/
theorem fDiv_comp_le (hf : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (κ : Kernel X Y) [IsMarkovKernel κ] :
    fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ fDiv f μ ν :=
  fDiv_comp_le_of_isSubMarkovKernel hf hf_cont κ (.inl fun _ ↦ measure_univ)

/-- Data processing along a sub-Markov kernel, for a nonnegative weight. -/
theorem fDiv_comp_le_of_nonneg (hf : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousWithinAt f (Ici 0) 0) (hf₀ : ∀ t, 0 ≤ t → 0 ≤ f t)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (κ : Kernel X Y) [IsSubMarkovKernel κ] :
    fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ fDiv f μ ν :=
  fDiv_comp_le_of_isSubMarkovKernel hf hf_cont κ (.inr hf₀)

/-- Data processing along a measurable map. -/
theorem fDiv_map_le (hf : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {k : X → Y} (hk : Measurable k := by fun_prop) :
    fDiv f (μ.map k) (ν.map k) ≤ fDiv f μ ν := by
  rw [← deterministic_comp_eq_map hk, ← deterministic_comp_eq_map hk]
  exact fDiv_comp_le hf hf_cont _

/-- Lower semicontinuity: along an increasing sequence on the left, the `f`-divergence of the
supremum is at most the `liminf` of the `f`-divergences. -/
theorem fDiv_le_liminf_of_monotone (hf : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousWithinAt f (Ici 0) 0) {μ : ℕ → Measure X} (hμ : Monotone μ)
    [IsFiniteMeasure (⨆ n, μ n)] [IsFiniteMeasure ν] :
    fDiv f (⨆ n, μ n) ν ≤ liminf (fun n ↦ fDiv f (μ n) ν) atTop := by
  have (n : ℕ) : IsFiniteMeasure (μ n) := isFiniteMeasure_of_le _ (le_iSup μ n)
  rw [fDiv_eq_iSup_partition hf hf_cont]
  refine iSup_le fun m ↦ iSup_le fun k ↦ iSup_le fun hk ↦ ?_
  have hlim : Tendsto (fun n ↦ ∑ i, persp f (μ n (k ⁻¹' {i})).toReal (ν (k ⁻¹' {i})).toReal)
      atTop (𝓝 (∑ i, persp f ((⨆ n, μ n) (k ⁻¹' {i})).toReal (ν (k ⁻¹' {i})).toReal)) := by
    refine EReal.tendsto_finset_sum _ (fun i _ ↦ ?_) fun i _ ↦ persp_ne_bot hf ENNReal.toReal_nonneg
    have hA : MeasurableSet (k ⁻¹' {i}) := hk (measurableSet_singleton i)
    set A := k ⁻¹' {i}
    have hsup : (⨆ n, μ n) A = ⨆ n, μ n A := iSup_apply_of_monotone hμ hA
    have hlim : Tendsto (fun n ↦ (μ n A).toReal) atTop (𝓝 ((⨆ n, μ n) A).toReal) :=
      (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
        (hsup ▸ tendsto_atTop_iSup fun _ _ h ↦ hμ h A)
    rcases eq_or_ne ((⨆ n, μ n) A) 0 with h0 | h0
    · have hn (n : ℕ) : μ n A = 0 := le_antisymm (h0 ▸ hsup ▸ le_iSup (μ · A) n) zero_le
      simp [hn, h0]
    obtain ⟨N, hN⟩ : ∃ N, μ N A ≠ 0 := by
      by_contra! h
      exact h0 (hsup.trans (by simp [h]))
    have hpos (n : ℕ) : (μ (n + N) A).toReal ≠ 0 := ENNReal.toReal_ne_zero.2
      ⟨fun h ↦ hN (le_antisymm (h ▸ hμ (Nat.le_add_left N n) A) zero_le), measure_ne_top _ _⟩
    refine (tendsto_add_atTop_iff_nat N).1 (tendsto_persp hf ((tendsto_add_atTop_iff_nat N).2 hlim)
      tendsto_const_nhds (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ ENNReal.toReal_nonneg)
      (fun n ↦ ?_) fun _ ↦ Iff.rfl)
    simp [hpos n, ENNReal.toReal_eq_zero_iff, h0, measure_ne_top]
  rw [← hlim.liminf_eq]
  exact liminf_le_liminf (.of_forall fun n ↦ sum_persp_le_fDiv hf hf_cont hk)

/-- Left continuity: along an increasing sequence on the left, the `f`-divergence of the
supremum is at most the supremum of the `f`-divergences. -/
theorem fDiv_iSup_left_le (hf : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0)
    {μ : ℕ → Measure X} (hμ : Monotone μ) [IsFiniteMeasure (⨆ n, μ n)] [IsFiniteMeasure ν] :
    fDiv f (⨆ n, μ n) ν ≤ ⨆ n, fDiv f (μ n) ν :=
  (fDiv_le_liminf_of_monotone hf hf_cont hμ).trans <| (Filter.liminf_le_limsup).trans limsup_le_iSup

end ProbabilityTheory
