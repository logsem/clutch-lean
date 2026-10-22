module

public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Metrology.Couplings.Divergences.Bof

/-! # `α`-Hellinger divergence on sub-probability measures

Barthe–Olmedo's `hellingerDivergence α` (ICALP 2013) composes along kernels of equal mass
(`hellingerDivergence_comp_of_mass_eq`), but not in general (`not_isComposable_hellinger_half`). -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace ProbabilityTheory

variable {α : ℝ}

/-! ## The generator and its pointwise term -/

/-- The normalized `α`-Hellinger generator `(α t + 1 - α - t ^ α) / (1 - α)`. -/
noncomputable def hellFun (α t : ℝ) : ℝ := (α * t + (1 - α) - t ^ α) / (1 - α)

/-- The pointwise `α`-Hellinger term `(α p + (1 - α) q - p ^ α q ^ (1 - α)) / (1 - α)`; it is
`persp (hellFun α) p q` (`persp_hellFun`), as a real number so that finite sums stay in `ℝ`. -/
noncomputable def hellTerm (α p q : ℝ) : ℝ :=
  (α * p + (1 - α) * q - p ^ α * q ^ (1 - α)) / (1 - α)

/-- The generator vanishes at `1`, which gives reflexivity. -/
theorem hellFun_one (α : ℝ) : hellFun α 1 = 0 := by simp [hellFun]

section Both1

variable (hα0 : 0 < α) (hα1 : α < 1)
include hα0 hα1

/-- Weighted AM–GM for two terms. -/
theorem rpow_mul_rpow_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    p ^ α * q ^ (1 - α) ≤ α * p + (1 - α) * q :=
  Real.geom_mean_le_arith_mean2_weighted hα0.le (by linarith) hp hq (by ring)

/-- The generator is nonnegative on `[0, ∞)`. -/
theorem hellFun_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hellFun α t := by
  have := rpow_mul_rpow_le hα0 hα1 ht zero_le_one
  simp only [Real.one_rpow, mul_one] at this
  exact div_nonneg (by linarith) (by linarith)

/-- The pointwise Hellinger term is nonnegative. -/
theorem hellTerm_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    0 ≤ hellTerm α p q :=
  div_nonneg (by linarith [rpow_mul_rpow_le hα0 hα1 hp hq]) (by linarith)

/-- The generator is convex on `[0, ∞)`, so `fDiv (hellFun α)` is an `f`-divergence. -/
theorem convexOn_hellFun : ConvexOn ℝ (Ici 0) (hellFun α) := by
  have h : ConvexOn ℝ (Ici 0) ((fun t ↦ α * t + (1 - α)) - fun t : ℝ ↦ t ^ α) :=
    ConvexOn.sub ((convexOn_id (convex_Ici 0)).smul hα0.le |>.add_const _)
      (Real.concaveOn_rpow hα0.le hα1.le)
  have := h.smul (inv_nonneg.2 (sub_pos.2 hα1).le)
  refine this.congr fun t _ ↦ ?_
  simp [hellFun, div_eq_inv_mul]

end Both1

/-- The generator is continuous for `0 ≤ α`. -/
theorem continuous_hellFun (hα0 : 0 ≤ α) : Continuous (hellFun α) := by
  unfold hellFun
  exact (((continuous_const.mul continuous_id).add continuous_const).sub
    (Real.continuous_rpow_const hα0)).div_const _

/-- The generator has slope `α / (1 - α)` at `∞`. -/
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

/-- The perspective of the generator is the pointwise Hellinger term. -/
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

section Both2

variable (hα0 : 0 < α) (hα1 : α < 1)
include hα0 hα1

/-- The Hellinger term of sums is at most the sum of the terms (joint convexity). -/
theorem hellTerm_sum_le {ι : Type*} (s : Finset ι) {a b : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) :
    hellTerm α (∑ i ∈ s, a i) (∑ i ∈ s, b i) ≤ ∑ i ∈ s, hellTerm α (a i) (b i) := by
  have h := persp_sum_le (convexOn_hellFun hα0 hα1) s ha hb
  rwa [persp_hellFun hα1 (Finset.sum_nonneg ha) (Finset.sum_nonneg hb),
    Finset.sum_congr rfl fun i hi ↦ persp_hellFun hα1 (ha i hi) (hb i hi),
    ← EReal.coe_finset_sum, EReal.coe_le_coe_iff] at h

/-! ## Finite spaces: Hellinger divergence as a sum of terms -/

/-- On a finite space the `α`-Hellinger divergence is a real sum of terms. -/
theorem fDiv_hellFun_eq_sum {I : Type*} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I] (ρ₁ ρ₂ : Measure I) [IsFiniteMeasure ρ₁]
    [IsFiniteMeasure ρ₂] :
    fDiv (hellFun α) ρ₁ ρ₂ = ((∑ i, hellTerm α (ρ₁ {i}).toReal (ρ₂ {i}).toReal : ℝ) : EReal) := by
  rw [fDiv_eq_sum (convexOn_hellFun hα0 hα1) (continuous_hellFun hα0.le).continuousWithinAt,
    EReal.coe_finset_sum]
  exact Finset.sum_congr rfl fun i _ ↦
    persp_hellFun hα1 ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- The Bhattacharyya mass of two sub-probability measures on a finite space is at most one minus
`1 - α` times their Hellinger divergence. -/
theorem sum_rpow_mul_rpow_le {I : Type*} [Fintype I] [MeasurableSpace I]
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
theorem sum_hellTerm_le_inv {I : Type*} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (ρ₁ ρ₂ : Measure I) [IsSubProbabilityMeasure ρ₁]
    [IsSubProbabilityMeasure ρ₂] :
    ∑ i, hellTerm α (ρ₁ {i}).toReal (ρ₂ {i}).toReal ≤ (1 - α)⁻¹ := by
  have h := sum_rpow_mul_rpow_le hα0 hα1 ρ₁ ρ₂
  have h0 : 0 ≤ ∑ i, (ρ₁ {i}).toReal ^ α * (ρ₂ {i}).toReal ^ (1 - α) :=
    Finset.sum_nonneg fun _ _ ↦ by positivity
  rw [← one_div, le_div_iff₀ (sub_pos.2 hα1)]
  linarith

end Both2

/-! ## The Barthe–Olmedo chain -/

/-- An extended real clamped into `[0, 1 / (1 - α)]`, the range of the `α`-Hellinger divergence on
sub-probability measures. -/
noncomputable def hellClamp (α : ℝ) (a : EReal) : ℝ :=
  (min (max a 0) (((1 - α)⁻¹ : ℝ) : EReal)).toReal

/-- The chain `a + d - (1 - α) a d` on clamped arguments, so that it is monotone and
`hellChain (θ s) (θ t) = θ (s + t)` (`bofReal_add` at `γ = α - 1`). -/
noncomputable def hellChain (α : ℝ) (a d : EReal) : EReal :=
  ((hellClamp α a + hellClamp α d - (1 - α) * hellClamp α a * hellClamp α d : ℝ) : EReal)

/-- Clamping leaves values in `[0, 1 / (1 - α)]` unchanged. -/
theorem hellClamp_coe {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ (1 - α)⁻¹) : hellClamp α x = x := by
  simp [hellClamp, max_eq_left (EReal.coe_nonneg.2 h0), min_eq_left (EReal.coe_le_coe_iff.2 h1)]

section Clamp

variable (hα1 : α < 1)
include hα1

/-- The clamp lands in `[0, 1 / (1 - α)]`. -/
theorem hellClamp_bounds (a : EReal) :
    0 ≤ min (max a 0) (((1 - α)⁻¹ : ℝ) : EReal) ∧
      min (max a 0) (((1 - α)⁻¹ : ℝ) : EReal) ≤ (((1 - α)⁻¹ : ℝ) : EReal) :=
  ⟨le_min (le_max_right _ _) (EReal.coe_nonneg.2 (inv_nonneg.2 (sub_pos.2 hα1).le)),
    min_le_right _ _⟩

/-- The clamp is monotone. -/
theorem hellClamp_mono : Monotone (hellClamp α) := fun a b h ↦
  EReal.toReal_le_toReal (min_le_min_right _ (max_le_max_right 0 h))
    (ne_bot_of_le_ne_bot EReal.zero_ne_bot (hellClamp_bounds hα1 a).1)
    (ne_top_of_le_ne_top (EReal.coe_ne_top _) (hellClamp_bounds hα1 b).2)

/-- The clamp is nonnegative. -/
theorem hellClamp_nonneg (a : EReal) : 0 ≤ hellClamp α a :=
  EReal.toReal_nonneg (hellClamp_bounds hα1 a).1

/-- The clamp times `1 - α` is at most `1`. -/
theorem mul_hellClamp_le_one (a : EReal) : (1 - α) * hellClamp α a ≤ 1 := by
  have h : hellClamp α a ≤ (1 - α)⁻¹ := (EReal.toReal_le_toReal (hellClamp_bounds hα1 a).2
    (ne_bot_of_le_ne_bot EReal.zero_ne_bot (hellClamp_bounds hα1 a).1)
    (EReal.coe_ne_top _)).trans_eq (EReal.toReal_coe _)
  calc (1 - α) * hellClamp α a ≤ (1 - α) * (1 - α)⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ (sub_pos.2 hα1).ne'

/-- The clamped chain is monotone, as `fDiv_comp_le_of_finite_of_mass` requires. -/
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

/-! ## Chain rule on finite spaces -/

section Both3

variable (hα0 : 0 < α) (hα1 : α < 1)
include hα0 hα1

/-- Barthe–Olmedo chain rule for `α`-Hellinger between finite spaces when the two kernels lose the
same mass at every point (Rocq `FdivChain`). -/
theorem fDiv_hellFun_comp_le_of_mass_eq {M N : ℕ} [NeZero M]
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
  -- split each cell with `hellTerm_mul`; the cross term `(q - w) (Σ η - Σ κ)` vanishes exactly
  -- because the kernels lose equal mass (`hmass`)
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
theorem fDiv_hellFun_smul_dirac {a b : ℝ≥0∞} (ha : a ≠ ⊤)
    (hb : b ≠ ⊤) :
    fDiv (hellFun α) (a • dirac PUnit.unit.{u + 1}) (b • dirac PUnit.unit) =
      hellTerm α a.toReal b.toReal := by
  rw [fDiv_smul_dirac (convexOn_hellFun hα0 hα1) (continuous_hellFun hα0.le).continuousWithinAt
    ha hb, persp_hellFun hα1 ENNReal.toReal_nonneg ENNReal.toReal_nonneg]

end Both3

end ProbabilityTheory

namespace GradedDivergence

/-! ## The graded divergence -/

variable {α : ℝ} {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {μ ν : Measure X}
  {r : ℝ≥0∞}

/-- The `α`-Hellinger divergence on sub-probability measures: the Barthe–Olmedo divergence with
`γ = α - 1`. -/
noncomputable def hellingerDivergence (α : ℝ) : GradedDivergence.{u} ℝ≥0∞ :=
  bofDivergence (hellFun α) (α - 1)

/-- The budget bounds the Hellinger generator's `f`-divergence through `bofThresh`. -/
theorem hellingerDivergence_iff :
    hellingerDivergence α r μ ν ↔ fDiv (hellFun α) μ ν ≤ bofThresh (α - 1) r :=
  bofDivergence_iff

section Instances

variable (α) [hα : Fact (α ∈ Ioo (0 : ℝ) 1)]

/-- The `α`-Hellinger divergence is graded. -/
instance isGraded_hellinger : (hellingerDivergence.{u} α).IsGraded :=
  isGraded_bofDivergence (convexOn_hellFun hα.out.1 hα.out.2)
    (continuous_hellFun hα.out.1.le).continuousWithinAt

/-- The `α`-Hellinger divergence is reflexive. -/
instance isReflexive_hellinger : (hellingerDivergence.{u} α).IsReflexive :=
  isReflexive_bofDivergence (hellFun_one α)

end Instances

/-! ## Composition -/

/-- Data processing along a sub-Markov kernel. -/
theorem hellingerDivergence_comp_self (hα0 : 0 < α) (hα1 : α < 1) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (κ : Kernel X Y) [IsSubMarkovKernel κ] (h : hellingerDivergence α r μ ν) :
    hellingerDivergence α r (κ ∘ₘ μ) (κ ∘ₘ ν) :=
  bofDivergence_comp_self (convexOn_hellFun hα0 hα1) (continuous_hellFun hα0.le).continuousWithinAt
    (fun _ ↦ hellFun_nonneg hα0 hα1) κ h

/-- Barthe–Olmedo composition for kernels that lose the same mass at every point (Rocq
`FdivChain`). -/
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
  -- thresholds lie in `[0, 1/(1-α)]`, where the clamp is the identity, so the chain is
  -- `bofReal_add`
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

/-! ## Failure of composition with mass loss -/

/-- `α`-Hellinger at `α = 1/2` does not compose once kernels may lose mass. -/
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
