module

public import Metrology.Couplings.Divergences.FDiv

/-!
# Partition formula and data processing for `f`-divergences

`fDiv_eq_iSup_partition`: the `f`-divergence is the supremum of its finite-partition sums
(Approximate Span Liftings, Thm. 4.7); data processing and semicontinuity follow.
-/

@[expose] public section

open MeasureTheory Measure Set Filter Topology ENNReal

namespace ProbabilityTheory

variable {f : ℝ → ℝ} {X : Type*} [MeasurableSpace X] {μ ν : Measure X}

/-! ## The partition characterisation -/

/-! ### Splitting off a minorant -/

/-- Above an integrable minorant `L`, the integral of `F` is the lower integral of `F - L` plus
the integral of `L`. -/
theorem coe_integral_eq_lintegral_add {F L : X → ℝ} (hF : Integrable F ν) (hL : Integrable L ν)
    (hLF : ∀ x, L x ≤ F x) :
    ((∫ x, F x ∂ν : ℝ) : EReal) =
      ((∫⁻ x, ENNReal.ofReal (F x - L x) ∂ν : ℝ≥0∞) : EReal) + ((∫ x, L x ∂ν : ℝ) : EReal) := by
  have h0 : 0 ≤ᵐ[ν] fun x ↦ F x - L x := ae_of_all _ fun x ↦ sub_nonneg.2 (hLF x)
  have h := ofReal_integral_eq_lintegral_ofReal (hF.sub hL) h0
  simp only [Pi.sub_apply] at h
  rw [← h, EReal.coe_ennreal_ofReal, max_eq_left (integral_nonneg_of_ae h0), ← EReal.coe_add,
    integral_sub hF hL, sub_add_cancel]

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Above an affine minorant `ℓ`, the `f`-divergence is the lower integral of `f - ℓ` at the
density, plus the integral of `ℓ`, plus the singular part. -/
theorem fDiv_eq_lintegral_sub (hf : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousWithinAt f (Ici 0) 0) {a c : ℝ}
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
    ae_of_all _ fun x ↦ sub_nonneg.2 (h _ toReal_nonneg)
  by_cases hint : Integrable (fun x ↦ f (G x)) ν
  · rw [fDiv_of_integrable hint,
      coe_integral_eq_lintegral_add hint hL fun _ ↦ h _ toReal_nonneg, add_assoc]
  have htop : ∫⁻ x, ENNReal.ofReal (f (G x) - (a * G x + c)) ∂ν = ⊤ := by
    by_contra hne
    have hfG := (hf.continuousOn_Ici hf_cont).measurable_comp_of_nonneg hG fun _ ↦ toReal_nonneg
    refine hint (((?_ : Integrable (fun x ↦ f (G x) - (a * G x + c)) ν).add hL).congr
      (ae_of_all _ fun x ↦ by simp))
    exact ⟨(hfG.sub ((hG.const_mul a).add_const c)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hφ0).2 (lt_top_iff_ne_top.2 hne)⟩
  rw [fDiv_of_not_integrable hint, htop, EReal.coe_ennreal_top, EReal.top_add_coe,
    EReal.top_add_of_ne_bot (derivAtTop_mul_ne_bot hf (measure_ne_top _ _))]

/-! ### Finite maxima of affine minorants give partition sums -/

/-- A finite maximum of affine functions of a measurable function is measurable. -/
theorem measurable_partialSups_affine {a c : ℕ → ℝ} {G : X → ℝ} (hG : Measurable G) (N : ℕ) :
    Measurable fun x ↦ partialSups (fun i ↦ a i * G x + c i) N := by
  simp_rw [partialSups_eq_sup'_range]
  exact Finset.measurable_range_sup'' fun i _ ↦ (hG.const_mul _).add_const _

/-- The maximum of finitely many affine functions of an integrable function is integrable. -/
theorem integrable_partialSups_affine {a c : ℕ → ℝ} {G : X → ℝ}
    (hG : Measurable G) (hGi : Integrable G ν) (N : ℕ) :
    Integrable (fun x ↦ partialSups (fun i ↦ a i * G x + c i) N) ν := by
  refine Integrable.mono' (g := fun x ↦ ∑ i ∈ Finset.range (N + 1), |a i * G x + c i|)
    (integrable_finsetSum _ fun i _ ↦ ((hGi.const_mul _).add (integrable_const _)).abs)
    (measurable_partialSups_affine hG N).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
    fun i ↦ a i * G x + c i
  rw [Real.norm_eq_abs, partialSups_eq_sup'_range, he]
  exact Finset.single_le_sum (f := fun i ↦ |a i * G x + c i|) (fun _ _ ↦ abs_nonneg _) hi

/-- The integral of a finite maximum of affine minorants at the density, plus the singular part,
is at most a partition sum. -/
theorem exists_partition_ge_integral_partialSups_add {a c : ℕ → ℝ}
    (h : ∀ i t, 0 ≤ t → a i * t + c i ≤ f t) (N : ℕ) :
    ∃ k : X → Fin (N + 2), Measurable k ∧
      ((∫ x, partialSups (fun i ↦ a i * (μ.rnDeriv ν x).toReal + c i) N ∂ν : ℝ) : EReal) +
        derivAtTop f * μ.singularPart ν univ ≤
      ∑ i, persp f (μ (k ⁻¹' {i})).toReal (ν (k ⁻¹' {i})).toReal := by
  classical
  -- cell `i ≤ N` collects the points of the `ν`-carrying set where minorant `i` is the first to
  -- attain the maximum; the last cell `N + 1` is the singular set
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
    refine Eq.trans_le ?_ (affine_le_persp (h i) toReal_nonneg toReal_nonneg)
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
  rw [Fin.sum_univ_castSucc, hlast, hνT, hμTc, toReal_zero, persp_zero_right]
  simp_rw [hcell]
  calc ((∫ x, H x ∂ν : ℝ) : EReal) + derivAtTop f * μ.singularPart ν univ
      = ∑ i, ((∫ x in C i, H x ∂ν : ℝ) : EReal) +
          ((μ.singularPart ν univ).toReal : EReal) * derivAtTop f := by
        rw [← EReal.coe_finset_sum, ← integral_iUnion_fintype hC hdisj fun _ ↦ hHi.integrableOn,
          hUnion, restrict_eq_self_of_ae_mem hT_ae, mul_comm,
          EReal.coe_ennreal_toReal (measure_ne_top _ _)]
    _ ≤ _ := add_le_add (Finset.sum_le_sum fun i _ ↦ hterm i) le_rfl

/-! ### The partition formula -/

/-- The `f`-divergence is at most the supremum of its partition sums: the maxima of the first `N`
affine minorants increase to `f`, and each gives a partition sum below the supremum. -/
theorem fDiv_le_iSup_partition (hf : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousWithinAt f (Ici 0) 0) :
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
    ⟨f (G x), forall_mem_range.2 fun i ↦ hmin i _ toReal_nonneg⟩
  have hHmono (x : X) : Monotone fun N ↦ H N x := (partialSups _).monotone
  have hHlim (x : X) : Tendsto (fun N ↦ H N x) atTop (𝓝 (f (G x))) := by
    have := tendsto_atTop_ciSup (hHmono x) (bddAbove_range_partialSups.2 (hbdd x))
    rwa [ciSup_partialSups_eq (hbdd x), hsup' _ toReal_nonneg] at this
  -- above `L`, the lower integrals of the partial maxima increase to that of `f`
  set E : ℕ → ℝ≥0∞ := fun N ↦ ∫⁻ x, ENNReal.ofReal (H N x - L x) ∂ν
  have hE (N : ℕ) : ((∫ x, H N x ∂ν : ℝ) : EReal) = (E N : EReal) + ((∫ x, L x ∂ν : ℝ) : EReal) :=
    coe_integral_eq_lintegral_add (integrable_partialSups_affine hG integrable_toReal_rnDeriv N)
      hLi (hHL N)
  have hElim : Tendsto E atTop (𝓝 (∫⁻ x, ENNReal.ofReal (f (G x) - L x) ∂ν)) :=
    lintegral_tendsto_of_tendsto_of_monotone
      (fun N ↦ ((measurable_partialSups_affine hG N).sub hLm).ennreal_ofReal.aemeasurable)
      (ae_of_all _ fun x _ _ hNM ↦ ofReal_le_ofReal (sub_le_sub_right (hHmono x hNM) _))
      (ae_of_all _ fun x ↦ (continuous_ofReal.tendsto _).comp ((hHlim x).sub_const _))
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
    (hf_cont : ContinuousWithinAt f (Ici 0) 0) :
    fDiv f μ ν = ⨆ (n : ℕ) (k : X → Fin n) (_ : Measurable k),
      ∑ i, persp f (μ (k ⁻¹' {i})).toReal (ν (k ⁻¹' {i})).toReal :=
  le_antisymm (fDiv_le_iSup_partition hf hf_cont)
    (iSup_le fun _ ↦ iSup_le fun _ ↦ iSup_le fun hk ↦ sum_persp_le_fDiv hf hf_cont hk)

/-! ## Data processing and semicontinuity -/

variable {Y : Type*} [MeasurableSpace Y]

/-- Data processing along a sub-Markov kernel; when the kernel may lose mass, the weight must be
nonnegative. -/
theorem fDiv_comp_le_of_isSubMarkovKernel (hf : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousWithinAt f (Ici 0) 0)
    (κ : Kernel X Y) [IsSubMarkovKernel κ] (h : (∀ x, κ x univ = 1) ∨ ∀ t, 0 ≤ t → 0 ≤ f t) :
    fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ fDiv f μ ν := by
  rw [fDiv_eq_iSup_partition hf hf_cont]
  refine iSup_le fun n ↦ iSup_le fun k ↦ iSup_le fun hk ↦ ?_
  have hA (i : Fin n) : MeasurableSet (k ⁻¹' {i}) := hk (measurableSet_singleton i)
  have hw (x : X) : ∑ i, (κ x (k ⁻¹' {i})).toReal = (κ x univ).toReal := by
    rw [← toReal_sum fun _ _ ↦ measure_ne_top _ _,
      sum_measure_preimage_singleton _ fun i _ ↦ hA i, Finset.coe_univ, preimage_univ]
  have hint (ρ : Measure X) [IsFiniteMeasure ρ] (i : Fin n) :
      ((κ ∘ₘ ρ) (k ⁻¹' {i})).toReal = ∫ x, (κ x (k ⁻¹' {i})).toReal ∂ρ := by
    rw [Measure.bind_apply (hA i) κ.aemeasurable,
      integral_toReal (κ.measurable_coe (hA i)).aemeasurable (ae_of_all _ fun _ ↦
        measure_lt_top _ _)]
  simp_rw [hint]
  refine sum_persp_integral_le_fDiv hf hf_cont Finset.univ
    (fun i ↦ (κ.measurable_coe (hA i)).ennreal_toReal) (fun _ _ ↦ toReal_nonneg)
    (fun x ↦ ?_) (h.imp_left fun h x ↦ by rw [hw, h, toReal_one])
  rw [hw]
  exact (IsSubProbabilityMeasure.toReal_mem_Icc _).2

/-- Data processing along a Markov kernel. -/
theorem fDiv_comp_le (hf : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0)
    (κ : Kernel X Y) [IsMarkovKernel κ] :
    fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ fDiv f μ ν :=
  fDiv_comp_le_of_isSubMarkovKernel hf hf_cont κ (.inl fun _ ↦ measure_univ)

/-- Data processing along a sub-Markov kernel, for a nonnegative weight. -/
theorem fDiv_comp_le_of_nonneg (hf : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousWithinAt f (Ici 0) 0) (hf₀ : ∀ t, 0 ≤ t → 0 ≤ f t)
    (κ : Kernel X Y) [IsSubMarkovKernel κ] :
    fDiv f (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ fDiv f μ ν :=
  fDiv_comp_le_of_isSubMarkovKernel hf hf_cont κ (.inr hf₀)

/-- Data processing along a measurable map. -/
theorem fDiv_map_le (hf : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0)
    {k : X → Y} (hk : Measurable k := by fun_prop) :
    fDiv f (μ.map k) (ν.map k) ≤ fDiv f μ ν := by
  rw [← deterministic_comp_eq_map hk, ← deterministic_comp_eq_map hk]
  exact fDiv_comp_le hf hf_cont _

/-- Lower semicontinuity: along an increasing sequence on the left, the `f`-divergence of the
supremum is at most the `liminf` of the `f`-divergences. -/
theorem fDiv_le_liminf_of_monotone (hf : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousWithinAt f (Ici 0) 0) {μs : ℕ → Measure X} (hμ : Monotone μs)
    [IsFiniteMeasure (⨆ n, μs n)] :
    fDiv f (⨆ n, μs n) ν ≤ liminf (fun n ↦ fDiv f (μs n) ν) atTop := by
  have (n : ℕ) : IsFiniteMeasure (μs n) := isFiniteMeasure_of_le _ (le_iSup μs n)
  rw [fDiv_eq_iSup_partition hf hf_cont]
  refine iSup_le fun m ↦ iSup_le fun k ↦ iSup_le fun hk ↦ ?_
  have hlim : Tendsto (fun n ↦ ∑ i, persp f (μs n (k ⁻¹' {i})).toReal (ν (k ⁻¹' {i})).toReal)
      atTop (𝓝 (∑ i, persp f ((⨆ n, μs n) (k ⁻¹' {i})).toReal (ν (k ⁻¹' {i})).toReal)) := by
    refine EReal.tendsto_finset_sum _ (fun i _ ↦ ?_) fun i _ ↦ persp_ne_bot hf toReal_nonneg
    have hA : MeasurableSet (k ⁻¹' {i}) := hk (measurableSet_singleton i)
    set A := k ⁻¹' {i}
    have hsup : (⨆ n, μs n) A = ⨆ n, μs n A := iSup_apply_of_monotone hμ hA
    have hlimA : Tendsto (fun n ↦ (μs n A).toReal) atTop (𝓝 ((⨆ n, μs n) A).toReal) :=
      (tendsto_toReal (measure_ne_top _ _)).comp (hsup ▸ tendsto_atTop_iSup fun _ _ h ↦ hμ h A)
    rcases eq_or_ne ((⨆ n, μs n) A) 0 with h0 | h0
    · have hn (n : ℕ) : μs n A = 0 := le_antisymm (h0 ▸ hsup ▸ le_iSup (μs · A) n) zero_le
      simp [hn, h0]
    obtain ⟨N, hN⟩ : ∃ N, μs N A ≠ 0 := by
      by_contra! h
      exact h0 (hsup.trans (by simp [h]))
    have hpos (n : ℕ) : (μs (n + N) A).toReal ≠ 0 := toReal_ne_zero.2
      ⟨fun h ↦ hN (le_antisymm (h ▸ hμ (Nat.le_add_left N n) A) zero_le), measure_ne_top _ _⟩
    refine (tendsto_add_atTop_iff_nat N).1 (tendsto_persp hf ((tendsto_add_atTop_iff_nat N).2 hlimA)
      tendsto_const_nhds (fun _ ↦ toReal_nonneg) (fun _ ↦ toReal_nonneg)
      (fun n ↦ ?_) fun _ ↦ Iff.rfl)
    simp [hpos n, toReal_eq_zero_iff, h0, measure_ne_top]
  rw [← hlim.liminf_eq]
  exact liminf_le_liminf (.of_forall fun n ↦ sum_persp_le_fDiv hf hf_cont hk)

/-- Along an increasing sequence on the left, the `f`-divergence of the supremum is at most the
supremum of the `f`-divergences. -/
theorem fDiv_iSup_left_le (hf : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0)
    {μs : ℕ → Measure X} (hμ : Monotone μs) [IsFiniteMeasure (⨆ n, μs n)] :
    fDiv f (⨆ n, μs n) ν ≤ ⨆ n, fDiv f (μs n) ν :=
  calc fDiv f (⨆ n, μs n) ν
      ≤ liminf (fun n ↦ fDiv f (μs n) ν) atTop := fDiv_le_liminf_of_monotone hf hf_cont hμ
    _ ≤ limsup (fun n ↦ fDiv f (μs n) ν) atTop := liminf_le_limsup
    _ ≤ ⨆ n, fDiv f (μs n) ν := limsup_le_iSup

end ProbabilityTheory
