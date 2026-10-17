module

public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Topology.Sion
public import Metrology.Couplings.Divergences.RenyiCodensity

/-! The Rényi–Strassen theorem: a Rényi codensity lifting is witnessed by a kernel that moves mass
along the cost and lands within the Rényi budget (Rocq `renyi_kernel_algebra_final.v`,
`renyi_strassen.v`). -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory GradedLifting
open scoped ENNReal

namespace MeasureTheory

/-- On a finite space the integral of `ofReal ∘ f` is the `ofReal` of the weighted sum. -/
theorem lintegral_ofReal_eq_sum {Z : Type*} [Fintype Z] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] (P : Measure Z) [IsFiniteMeasure P] {f : Z → ℝ} (hf : 0 ≤ f) :
    ∫⁻ z, ENNReal.ofReal (f z) ∂P = ENNReal.ofReal (∑ z, (P {z}).toReal * f z) := by
  rw [lintegral_fintype, ENNReal.ofReal_sum_of_nonneg fun z _ ↦
    mul_nonneg ENNReal.toReal_nonneg (hf z)]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _),
    mul_comm]

end MeasureTheory

namespace ProbabilityTheory

variable {α : ℝ}

/-- Finite Hölder duality, by Sion's minimax theorem: if every weighting `w ≥ 0` has
`∑ m w ^ γ ≤ A (∑ n M) ^ γ` whenever `q x y w x ≤ M y`, with `γ = (α - 1) / α`, then some plan
`s ≥ 0` with rows of mass at most `1` has a reduct `ν' x = ∑ n y q x y s y x` with
`∑ persp (m x) (ν' x) ≤ A ^ α` (Rocq `minimizer_exists`, `renyi_moment_le_of_minimizer`). -/
theorem exists_plan_sum_persp_rpow_le {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X]
    (hα : 1 < α) {m : X → ℝ} {n : Y → ℝ} {q : X → Y → ℝ} {A : ℝ} (hm : ∀ x, 0 ≤ m x)
    (hn : ∀ y, 0 ≤ n y) (hq : ∀ x y, 0 ≤ q x y) (hA : 0 ≤ A)
    (h : ∀ w : X → ℝ, 0 ≤ w → ∀ M : Y → ℝ, (∀ x y, q x y * w x ≤ M y) →
      ∑ x, m x * w x ^ ((α - 1) / α) ≤ A * (∑ y, n y * M y) ^ ((α - 1) / α)) :
    ∃ s : Y → X → ℝ, 0 ≤ s ∧ (∀ y, ∑ x, s y x ≤ 1) ∧
      ∑ x, persp (· ^ α) (m x) (∑ y, n y * q x y * s y x) ≤ ((A ^ α : ℝ) : EReal) := by
  set γ := (α - 1) / α with hγ_def
  have hα0 : 0 < α := by linarith
  have hγ0 : 0 < γ := div_pos (by linarith) hα0
  have hγ1 : γ ≤ 1 := (div_le_one hα0).2 (by linarith)
  have hαγ : α * γ = α - 1 := by rw [hγ_def]; field_simp
  set P : Set (Y → X → ℝ) := {s | 0 ≤ s ∧ ∀ y, ∑ x, s y x ≤ 1}
  set W : Set (X → ℝ) := Set.Ici 0
  set ν' : (Y → X → ℝ) → X → ℝ := fun s x ↦ ∑ y, n y * q x y * s y x
  -- the Lagrangian: affine in the plan, concave in the weighting
  set F : (Y → X → ℝ) → (X → ℝ) → ℝ :=
    fun s w ↦ ∑ x, (α * m x * w x ^ γ - (α - 1) * ν' s x * w x)
  have hν' (a b : ℝ) (s t : Y → X → ℝ) (x : X) :
      ν' (a • s + b • t) x = a * ν' s x + b * ν' t x := by
    simp only [ν', Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  have hν'0 (s : Y → X → ℝ) (hs : s ∈ P) (x : X) : 0 ≤ ν' s x :=
    Finset.sum_nonneg fun y _ ↦ mul_nonneg (mul_nonneg (hn y) (hq x y)) (hs.1 y x)
  have hPc : Convex ℝ P := fun s hs t ht a b ha hb hab ↦ by
    refine ⟨add_nonneg (smul_nonneg ha hs.1) (smul_nonneg hb ht.1), fun y ↦ ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left (hs.2 y) ha, mul_le_mul_of_nonneg_left (ht.2 y) hb]
  have hconv (w : X → ℝ) : ConvexOn ℝ P (F · w) := by
    refine ⟨hPc, fun s _ t _ a b _ _ hab ↦ le_of_eq ?_⟩
    simp only [F, hν', smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ ↦ by linear_combination (-(α * m x * w x ^ γ)) * hab
  have hconc (s : Y → X → ℝ) : ConcaveOn ℝ W (F s) := by
    refine ⟨convex_Ici 0, fun u hu v hv a b ha hb hab ↦ ?_⟩
    simp only [F, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ ↦ ?_
    have hx := (Real.concaveOn_rpow hγ0.le hγ1).2 (hu x) (hv x) ha hb hab
    simp only [smul_eq_mul] at hx
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx (mul_nonneg hα0.le (hm x))]
  have hcont_s (w : X → ℝ) : Continuous (F · w) := by fun_prop
  have hcont_w (s : Y → X → ℝ) : Continuous (F s) := by
    have := Real.continuous_rpow_const hγ0.le
    fun_prop
  have hP : IsCompact P := by
    refine (isCompact_Icc (a := (0 : Y → X → ℝ)) (b := 1)).of_isClosed_subset ?_
      fun s (hs : s ∈ P) ↦ ⟨hs.1, fun y x ↦ ?_⟩
    · have hcl : IsClosed (⋂ y, {s : Y → X → ℝ | ∑ x, s y x ≤ 1}) :=
        isClosed_iInter fun y ↦ isClosed_le (by fun_prop) continuous_const
      rw [Set.iInter_ofPred] at hcl
      exact isClosed_Ici.inter hcl
    · exact (Finset.single_le_sum (fun x _ ↦ hs.1 y x) (Finset.mem_univ x)).trans (hs.2 y)
  have hPne : P.Nonempty := ⟨0, le_rfl, fun _ ↦ by simp⟩
  have hlsc_s (w : X → ℝ) : LowerSemicontinuous fun s ↦ (F s w : EReal) :=
    (continuous_coe_real_ereal.comp (hcont_s w)).lowerSemicontinuous
  have husc_w (s : Y → X → ℝ) : UpperSemicontinuous fun w ↦ (F s w : EReal) :=
    (continuous_coe_real_ereal.comp (hcont_w s)).upperSemicontinuous
  have hqconv (w : X → ℝ) : QuasiconvexOn ℝ P (Real.toEReal ∘ (F · w)) :=
    (hconv w).quasiconvexOn.monotone_comp EReal.coe_strictMono.monotone
  have hqconc (s : Y → X → ℝ) : QuasiconcaveOn ℝ W (Real.toEReal ∘ F s) :=
    (hconc s).quasiconcaveOn.monotone_comp EReal.coe_strictMono.monotone
  have hminimax := Sion.minimax' (f := fun s w ↦ (F s w : EReal)) hPne hPc hP
    (fun w _ ↦ (hlsc_s w).lowerSemicontinuousOn _) (fun w _ ↦ hqconv w) (convex_Ici 0)
    (fun s _ ↦ (husc_w s).upperSemicontinuousOn _) fun s _ ↦ hqconc s
  -- each weighting is beaten by the plan sending each fiber to its heaviest point
  have hsup : ⨆ w ∈ W, ⨅ s ∈ P, (F s w : EReal) ≤ ((A ^ α : ℝ) : EReal) := by
    refine iSup₂_le fun w hw ↦ ?_
    choose xs hxs using fun y ↦ Finite.exists_max fun x ↦ q x y * w x
    classical
    have hsw : (fun y ↦ Pi.single (xs y) 1) ∈ P :=
      ⟨fun y x ↦ by by_cases hx : x = xs y <;> simp [hx], fun y ↦ by simp⟩
    refine (iInf₂_le _ hsw).trans (EReal.coe_le_coe_iff.2 ?_)
    set M : Y → ℝ := fun y ↦ q (xs y) y * w (xs y)
    set Λ := ∑ y, n y * M y
    have hL : ∑ x, ν' (fun y ↦ Pi.single (xs y) 1) x * w x = Λ := by
      simp only [ν', Λ, M, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [Finset.sum_eq_single (xs y) (fun x _ hx ↦ by simp [hx]) (by simp)]
      simp [mul_assoc]
    have hΛ : 0 ≤ Λ := Finset.sum_nonneg fun y _ ↦ mul_nonneg (hn y) (mul_nonneg (hq _ _) (hw _))
    have hamgm := Real.geom_mean_le_arith_mean2_weighted hγ0.le (inv_nonneg.2 hα0.le) hΛ
      (Real.rpow_nonneg hA α) (by rw [hγ_def]; field_simp; ring)
    rw [← Real.rpow_mul hA, mul_inv_cancel₀ hα0.ne', Real.rpow_one] at hamgm
    have hH := h w hw M fun x y ↦ hxs y x
    calc F (fun y ↦ Pi.single (xs y) 1) w
        = α * ∑ x, m x * w x ^ γ - (α - 1) * ∑ x, ν' (fun y ↦ Pi.single (xs y) 1) x * w x := by
          simp only [F, Finset.sum_sub_distrib, Finset.mul_sum]
          congr 1 <;> exact Finset.sum_congr rfl fun _ _ ↦ by ring
      _ ≤ α * (A * Λ ^ γ) - (α - 1) * Λ := by rw [hL]; gcongr
      _ ≤ A ^ α := by
          have := mul_le_mul_of_nonneg_left hamgm hα0.le
          rw [mul_add, ← mul_assoc α γ, hαγ, ← mul_assoc α α⁻¹, mul_inv_cancel₀ hα0.ne',
            one_mul] at this
          linarith
  -- a plan minimizing the supremum over weightings
  have hlsc : LowerSemicontinuousOn (fun s ↦ ⨆ w ∈ W, (F s w : EReal)) P := fun s _ ↦
    lowerSemicontinuousWithinAt_iSup fun w ↦ lowerSemicontinuousWithinAt_iSup fun _ ↦
      (hlsc_s w).lowerSemicontinuousWithinAt _ _
  obtain ⟨s, hs, hmin⟩ := hlsc.exists_isMinOn hPne hP
  have hbound (w : X → ℝ) (hw : w ∈ W) : F s w ≤ A ^ α := by
    refine EReal.coe_le_coe_iff.1 ?_
    calc (F s w : EReal) ≤ ⨆ w ∈ W, (F s w : EReal) :=
          le_iSup₂ (f := fun w _ ↦ (F s w : EReal)) w hw
      _ ≤ ⨅ t ∈ P, ⨆ w ∈ W, (F t w : EReal) := le_iInf₂ fun t ht ↦ isMinOn_iff.1 hmin t ht
      _ ≤ _ := hminimax ▸ hsup
  refine ⟨s, hs.1, hs.2, ?_⟩
  -- the reduct charges every point that `m` charges: else a spike at that point beats `A ^ α`
  have hac (x : X) (hx : ν' s x = 0) : m x = 0 := by
    classical
    by_contra hmx
    have hmx' : 0 < α * m x := mul_pos hα0 ((hm x).lt_of_ne' hmx)
    set t := (A ^ α / (α * m x) + 1) ^ γ⁻¹
    have ht : t ^ γ = A ^ α / (α * m x) + 1 :=
      Real.rpow_inv_rpow (by positivity) hγ0.ne'
    have hF : F s (Pi.single x t) = α * m x * t ^ γ := by
      simp only [F]
      rw [Finset.sum_eq_single x (fun x' _ hx' ↦ by simp [hx', Real.zero_rpow hγ0.ne']) (by simp)]
      simp [hx]
    have := hbound (Pi.single x t) fun x' ↦ by
      by_cases hx' : x' = x
      · subst hx'
        simp only [Pi.single_eq_same, Pi.zero_apply]
        positivity
      · simp [hx']
    rw [hF, ht, mul_add, mul_div_cancel₀ _ hmx'.ne', mul_one] at this
    linarith
  -- at the optimal weighting `(m / ν') ^ α` the Lagrangian is the sum of perspectives
  set w : X → ℝ := fun x ↦ if ν' s x = 0 then 0 else (m x / ν' s x) ^ α
  have hw : w ∈ W := fun x ↦ by
    simp only [w, Pi.zero_apply]
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (div_nonneg (hm x) (hν'0 s hs x)) _
  refine le_trans (le_of_eq ?_) (EReal.coe_le_coe_iff.2 (hbound w hw))
  rw [EReal.coe_finset_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  change persp _ (m x) (ν' s x) = _
  rcases (hν'0 s hs x).eq_or_lt with h0 | hpos
  · rw [← h0, hac x h0.symm, persp_rpow_zero_left hα0 le_rfl]
    simp [w, ← h0]
  rw [persp_rpow_of_pos α hpos, EReal.coe_eq_coe_iff]
  simp only [w, hpos.ne', ite_false]
  set r := m x / ν' s x
  have hr : 0 ≤ r := div_nonneg (hm x) hpos.le
  have hmr : m x = r * ν' s x := (div_mul_cancel₀ _ hpos.ne').symm
  rw [← Real.rpow_mul hr, hαγ, hmr]
  have : r ^ α = r ^ (α - 1) * r := by
    rw [← Real.rpow_add_one' hr (by linarith), sub_add_cancel]
  rw [this]
  ring

end ProbabilityTheory

namespace GradedDivergence

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {α : ℝ} {ρ : ℝ≥0∞}
  {E : X → Y → ℝ≥0∞} {μ : Measure X} {ν : Measure Y}

/-! ## Soundness -/

/-- Raising `e^{(α - 1) ε / α}` to the conjugate exponent `α / (α - 1)` gives `e^ε`. -/
theorem expBudget_conj_rpow (hα : 1 < α) {ε : ℝ≥0∞} (hε : ε ≠ ⊤) :
    expBudget (ENNReal.ofReal ((α - 1) / α) * ε) ^ (α / (α - 1)) = expBudget ε := by
  have hα1 : α - 1 ≠ 0 := by linarith
  have hγ : 0 ≤ (α - 1) / α := div_nonneg (by linarith) (by linarith)
  have hβ : 0 ≤ α / (α - 1) := div_nonneg (by linarith) (by linarith)
  rw [expBudget_of_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hε), expBudget_of_ne_top hε,
    ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hβ,
    ← Real.exp_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hγ]
  congr 2
  field_simp

/-- A kernel whose `e^E`-weighted mass is at most `1` everywhere is sub-Markov. -/
theorem isSubMarkovKernel_of_lintegral_expBudget_le {r : Kernel Y X}
    (hr : ∀ y, ∫⁻ x, expBudget (E x y) ∂(r y) ≤ 1) : IsSubMarkovKernel r where
  isSubProbabilityMeasure y := ⟨by
    calc r y Set.univ = ∫⁻ _, 1 ∂(r y) := by simp
      _ ≤ ∫⁻ x, expBudget (E x y) ∂(r y) := lintegral_mono fun x ↦ one_le_expBudget _
      _ ≤ 1 := hr y⟩

/-- A kernel `r` with `∫ e^{E x y} d(r y) ≤ 1` and `D_α(μ ‖ r ∘ ν) ≤ ρ` witnesses the Rényi
codensity lifting of `μ` and `ν` at the cost `E` (Rocq `witness_soundness`,
`Kant_exact_uncond`). -/
theorem codensity_renyi_of_kernel [hα : Fact (1 < α)] [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] (hE : ∀ y, Measurable fun x ↦ E x y) {r : Kernel Y X}
    (hr : ∀ y, ∫⁻ x, expBudget (E x y) ∂(r y) ≤ 1) (hD : renyiDivergence α ρ μ (r ∘ₘ ν)) :
    (renyiDivergence α).codensity ρ E μ ν := by
  rcases eq_or_ne ρ ⊤ with rfl | hρ
  · exact codensity_top E μ ν
  have := isSubMarkovKernel_of_lintegral_expBudget_le hr
  have hcoupl : RdpCoupl α ρ (· = ·) μ (r ∘ₘ ν) :=
    (rdpCoupl_iff_codensity hρ).2 (codensity_rel_eq_iff.2 hD)
  refine codensity_renyi_of_slackHolder fun f g hf hg hfg ↦ ?_
  have hγ : 0 ≤ (α - 1) / α := div_nonneg (by linarith [hα.out]) (by linarith [hα.out])
  have hβ : 0 ≤ α / (α - 1) := div_nonneg (by linarith [hα.out]) (by linarith [hα.out])
  -- along each fiber `r y`, `f ^ β` is at most `e^E g(y) ^ β`, which integrates to `g(y) ^ β`
  have hfiber (y : Y) : ∫⁻ x, f x ^ (α / (α - 1)) ∂(r y) ≤ g y ^ (α / (α - 1)) := by
    have hEy : Measurable fun x ↦ expBudget (E x y) := expBudget_mono.measurable.comp (hE y)
    have hfin : ∀ᵐ x ∂(r y), E x y < ⊤ := by
      filter_upwards [ae_lt_top hEy (ne_top_of_le_ne_top ENNReal.one_ne_top (hr y))] with x hx
      exact expBudget_lt_top_iff.1 hx
    calc ∫⁻ x, f x ^ (α / (α - 1)) ∂(r y)
        ≤ ∫⁻ x, expBudget (E x y) * g y ^ (α / (α - 1)) ∂(r y) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hfin] with x hx
          grw [hfg x y hx, ENNReal.mul_rpow_of_nonneg _ _ hβ, expBudget_conj_rpow hα.out hx.ne]
      _ = (∫⁻ x, expBudget (E x y) ∂(r y)) * g y ^ (α / (α - 1)) :=
          lintegral_mul_const _ hEy
      _ ≤ g y ^ (α / (α - 1)) := mul_le_of_le_one_left' (hr y)
  calc ∫⁻ x, f x ∂μ
      ≤ expBudget (ENNReal.ofReal ((α - 1) / α) * ρ) *
          (∫⁻ x, f x ^ (α / (α - 1)) ∂(r ∘ₘ ν)) ^ ((α - 1) / α) :=
        hcoupl hf hf fun _ _ h ↦ h ▸ le_rfl
    _ ≤ expBudget (ENNReal.ofReal ((α - 1) / α) * ρ) *
          (∫⁻ y, g y ^ (α / (α - 1)) ∂ν) ^ ((α - 1) / α) := by
        rw [Measure.lintegral_bind r.measurable.aemeasurable (hf.pow_const _).aemeasurable]
        exact mul_le_mul_right (ENNReal.rpow_le_rpow (lintegral_mono hfiber) hγ) _

/-! ## Completeness on finite spaces -/

/-- On finite spaces a Rényi codensity lifting at the cost `E` is witnessed by a kernel `r` with
`∫ e^{E x y} d(r y) ≤ 1` and `D_α(μ ‖ r ∘ ν) ≤ ρ` (Rocq `renyi_strassen_finite`,
`Kant_exact_uncond`). -/
theorem exists_kernel_of_codensity_renyi [Finite X] [Finite Y] [MeasurableSingletonClass X]
    [MeasurableSingletonClass Y] [hα : Fact (1 < α)] [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] (h : (renyiDivergence α).codensity ρ E μ ν) :
    ∃ r : Kernel Y X, (∀ y, ∫⁻ x, expBudget (E x y) ∂(r y) ≤ 1) ∧
      renyiDivergence α ρ μ (r ∘ₘ ν) := by
  rcases eq_or_ne ρ ⊤ with rfl | hρ
  · exact ⟨0, fun y ↦ by simp, renyiDivergence_top hα.out _ _⟩
  cases isEmpty_or_nonempty X
  · exact ⟨0, fun y ↦ by simp, by rw [μ.eq_zero_of_isEmpty]; exact IsZeroLeft.zero_left _ _⟩
  cases nonempty_fintype X
  cases nonempty_fintype Y
  classical
  have hα1 := hα.out
  have hα0 : 0 < α := by linarith
  set γ := (α - 1) / α with hγ_def
  have hγ0 : 0 < γ := div_pos (by linarith) hα0
  have hγβ : γ * (α / (α - 1)) = 1 := by
    have : α - 1 ≠ 0 := by linarith
    rw [hγ_def]
    field_simp
  set q : X → Y → ℝ := fun x y ↦ (expBudget (E x y))⁻¹.toReal
  have hqE (x : X) (y : Y) (hE : E x y ≠ ⊤) : q x y = Real.exp (-(E x y).toReal) := by
    rw [Real.exp_neg, ← ENNReal.toReal_ofReal (inv_nonneg.2 (Real.exp_pos _).le),
      ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← expBudget_of_ne_top hE]
  have hq0 (x : X) (y : Y) : 0 ≤ q x y := ENNReal.toReal_nonneg
  set A := Real.exp (γ * ρ.toReal)
  -- the slack-Hölder head, read on finite sums
  have hSH := slackHolder_of_codensity hρ h
  have hHolder (w : X → ℝ) (hw : 0 ≤ w) (M : Y → ℝ) (hM : ∀ x y, q x y * w x ≤ M y) :
      ∑ x, (μ {x}).toReal * w x ^ γ ≤ A * (∑ y, (ν {y}).toReal * M y) ^ γ := by
    have hM0 (y : Y) : 0 ≤ M y :=
      (mul_nonneg (hq0 _ y) (hw (Classical.arbitrary X))).trans (hM _ y)
    have hfg (x : X) (y : Y) (hE : E x y < ⊤) : ENNReal.ofReal (w x ^ γ) ≤
        expBudget (ENNReal.ofReal γ * E x y) * ENNReal.ofReal (M y ^ γ) := by
      rw [expBudget_of_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE.ne),
        ENNReal.toReal_mul, ENNReal.toReal_ofReal hγ0.le,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm γ, Real.exp_mul,
        ← Real.mul_rpow (Real.exp_pos _).le (hM0 y)]
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (hw x) ?_ hγ0.le)
      have := hM x y
      rw [hqE x y hE.ne] at this
      calc w x = Real.exp (E x y).toReal * (Real.exp (-(E x y).toReal) * w x) := by
            rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
        _ ≤ Real.exp (E x y).toReal * M y := by gcongr
    have hMβ (y : Y) : ENNReal.ofReal (M y ^ γ) ^ (α / (α - 1)) = ENNReal.ofReal (M y) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hM0 y) _)
        (div_nonneg hα0.le (by linarith)), ← Real.rpow_mul (hM0 y), hγβ, Real.rpow_one]
    have key := hSH (f := fun x ↦ ENNReal.ofReal (w x ^ γ))
      (g := fun y ↦ ENNReal.ofReal (M y ^ γ)) .of_discrete .of_discrete hfg
    simp_rw [hMβ] at key
    rw [lintegral_ofReal_eq_sum μ fun x ↦ Real.rpow_nonneg (hw x) _,
      lintegral_ofReal_eq_sum ν hM0,
      expBudget_of_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hρ),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hγ0.le,
      ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun y _ ↦
        mul_nonneg ENNReal.toReal_nonneg (hM0 y)) hγ0.le,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le] at key
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.exp_pos _).le
      (Real.rpow_nonneg (Finset.sum_nonneg fun y _ ↦
        mul_nonneg ENNReal.toReal_nonneg (hM0 y)) _))).1 key
  obtain ⟨s, hs0, hs1, hs⟩ := exists_plan_sum_persp_rpow_le hα1
    (fun _ ↦ ENNReal.toReal_nonneg) (fun _ ↦ ENNReal.toReal_nonneg) hq0 (Real.exp_pos _).le
    hHolder
  -- the witness kernel moves `q x y s y x` of the mass at `y` to `x`
  let r : Kernel Y X := ⟨fun y ↦ ∑ x, ENNReal.ofReal (q x y * s y x) • dirac x, .of_discrete⟩
  have hr (y : Y) : r y = ∑ x, ENNReal.ofReal (q x y * s y x) • dirac x := rfl
  have hwit (y : Y) : ∫⁻ x, expBudget (E x y) ∂(r y) ≤ 1 := by
    rw [hr, lintegral_finsetSum_measure]
    calc ∑ x, ∫⁻ x', expBudget (E x' y) ∂(ENNReal.ofReal (q x y * s y x) • dirac x)
        ≤ ∑ x, ENNReal.ofReal (s y x) := Finset.sum_le_sum fun x _ ↦ by
          rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
          rcases eq_or_ne (E x y) ⊤ with hE | hE
          · simp [q, hE]
          rw [hqE x y hE, expBudget_of_ne_top hE,
            ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (hs0 y x)),
            mul_comm, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ = ENNReal.ofReal (∑ x, s y x) := (ENNReal.ofReal_sum_of_nonneg fun x _ ↦ hs0 y x).symm
      _ ≤ 1 := ENNReal.ofReal_le_one.2 (hs1 y)
  refine ⟨r, hwit, ?_⟩
  have := isSubMarkovKernel_of_lintegral_expBudget_le hwit
  have hred (x : X) : ((r ∘ₘ ν) {x}).toReal = ∑ y, (ν {y}).toReal * q x y * s y x := by
    have hry (y : Y) : r y {x} = ENNReal.ofReal (q x y * s y x) := by
      rw [hr, Measure.finsetSum_apply, Finset.sum_eq_single x
        (fun x' _ hx' ↦ by simp [hx']) (by simp)]
      simp
    rw [Measure.bind_apply (measurableSet_singleton x) r.measurable.aemeasurable]
    simp_rw [hry]
    rw [lintegral_ofReal_eq_sum ν fun y ↦ mul_nonneg (hq0 x y) (hs0 y x),
      ENNReal.toReal_ofReal (Finset.sum_nonneg fun y _ ↦
        mul_nonneg ENNReal.toReal_nonneg (mul_nonneg (hq0 x y) (hs0 y x)))]
    simp_rw [mul_assoc]
  rw [renyiDivergence_iff_of_ne_top hα1.le hρ, fDiv_eq_sum (convexOn_rpow hα1.le)
    (continuousWithinAt_rpow_zero hα0)]
  simp_rw [hred]
  refine hs.trans_eq ?_
  rw [← Real.exp_mul, hγ_def]
  congr 2
  field_simp

/-- The Rényi–Strassen theorem on finite spaces: the Rényi codensity lifting at the cost `E` holds
exactly when some kernel `r` with `∫ e^{E x y} d(r y) ≤ 1` has `D_α(μ ‖ r ∘ ν) ≤ ρ` (Rocq
`Kant_exact_uncond`, `kernel_strassen_uncond`). -/
theorem codensity_renyi_iff_exists_kernel [Finite X] [Finite Y] [MeasurableSingletonClass X]
    [MeasurableSingletonClass Y] [Fact (1 < α)] [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] :
    (renyiDivergence α).codensity ρ E μ ν ↔ ∃ r : Kernel Y X,
      (∀ y, ∫⁻ x, expBudget (E x y) ∂(r y) ≤ 1) ∧ renyiDivergence α ρ μ (r ∘ₘ ν) :=
  ⟨exists_kernel_of_codensity_renyi, fun ⟨_, hr, hD⟩ ↦
    codensity_renyi_of_kernel (fun _ ↦ .of_discrete) hr hD⟩

end GradedDivergence
