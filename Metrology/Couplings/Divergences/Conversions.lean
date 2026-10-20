module

public import Metrology.Couplings.Divergences.Concentrated
public import Metrology.Couplings.LiftingHom
public import Metrology.Couplings.Divergences.RenyiStrassen

/-! Conversions between DP and its Rényi relaxations (Approximate Span Liftings, Fig. 4).
Tags `[X/Y]` name the arrow `X → Y` of Fig. 4 (`D` = pure DP, `R` = Rényi, `z` = zCDP,
`t` = tCDP). -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory GradedLifting Set Filter Topology Real
open scoped ENNReal

namespace GradedDivergence

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {α ω : ℝ}

section

variable {μ ν : Measure X}

/-! ## Pure DP bounds every Rényi divergence -/

/-- A DP bound without slack bounds the Rényi divergences by its budget ([D/z]). -/
theorem renyi_of_dp (hα : 1 < α) {ε : ℝ≥0∞} [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] (h : dp (ε, 0) μ ν) : renyiDivergence α ε μ ν := by
  rcases eq_or_ne ε ⊤ with rfl | hε
  · exact renyiDivergence_top hα μ ν
  have hB : Bound (ENNReal.ofReal (exp ε.toReal)) 0 μ ν := by
    simpa [expBudget_of_ne_top hε] using h hε.lt_top
  rw [renyiDivergence_iff_of_ne_top hα.le hε, fDiv_eq_iSup_partition (convexOn_rpow hα.le)
    (continuousWithinAt_rpow_zero (zero_lt_one.trans hα))]
  refine iSup_le fun n ↦ iSup_le fun k ↦ iSup_le fun hk ↦ ?_
  set e := ε.toReal
  -- partition form: on each cell `p ≤ e^ε q`, so `q (p/q)^α ≤ e^{(α-1)ε} p`; summing gives
  -- `≤ e^{(α-1)ε}`
  have hcell (i : Fin n) : persp (· ^ α) (μ (k ⁻¹' {i})).toReal (ν (k ⁻¹' {i})).toReal ≤
      ((exp ((α - 1) * e) * (μ (k ⁻¹' {i})).toReal : ℝ) : EReal) := by
    set p := (μ (k ⁻¹' {i})).toReal
    set q := (ν (k ⁻¹' {i})).toReal
    have hpq : p ≤ exp e * q := by
      simpa [p, q, ENNReal.toReal_mul, (exp_pos e).le] using
        ENNReal.toReal_mono (by finiteness) (hB _ (hk (measurableSet_singleton i)))
    have hp : 0 ≤ p := ENNReal.toReal_nonneg
    obtain hq | hq : 0 = q ∨ 0 < q := ENNReal.toReal_nonneg.eq_or_lt
    · rw [← hq, mul_zero] at hpq
      simp [← hq, le_antisymm hpq hp]
    rw [persp_rpow_of_pos α hq, EReal.coe_le_coe_iff]
    have hr : p / q ≤ exp e := (div_le_iff₀ hq).2 (by linarith)
    calc q * (p / q) ^ α = p * (p / q) ^ (α - 1) := by
          rcases hp.eq_or_lt with h0 | h0
          · simp [← h0, Real.zero_rpow (by linarith : α ≠ 0),
              Real.zero_rpow (by linarith : α - 1 ≠ 0)]
          rw [Real.rpow_sub_one (div_pos h0 hq).ne']
          field_simp
      _ ≤ p * exp e ^ (α - 1) := by gcongr
      _ = exp ((α - 1) * e) * p := by rw [← exp_mul, mul_comm e, mul_comm]
  calc ∑ i, persp (· ^ α) (μ (k ⁻¹' {i})).toReal (ν (k ⁻¹' {i})).toReal
      ≤ ∑ i, ((exp ((α - 1) * e) * (μ (k ⁻¹' {i})).toReal : ℝ) : EReal) :=
        Finset.sum_le_sum fun i _ ↦ hcell i
    _ = ((exp ((α - 1) * e) * (μ (k ⁻¹' univ)).toReal : ℝ) : EReal) := by
        rw [← EReal.coe_finset_sum, ← Finset.mul_sum, ← ENNReal.toReal_sum (by finiteness),
          sum_measure_preimage_singleton _ fun _ _ ↦ hk (measurableSet_singleton _),
          Finset.coe_univ]
    _ ≤ ((exp ((α - 1) * e) : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.2 (mul_le_of_le_one_right (exp_pos _).le
          (IsSubProbabilityMeasure.toReal_mem_Icc _).2)

/-- Pure DP gives zCDP ([D/z]). -/
theorem zcdp_of_dp {ε : ℝ≥0∞} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    (h : dp (ε, 0) μ ν) : zcdpDivergence (ε, 0) μ ν :=
  concentratedDivergence_of_forall fun α _ ↦ by simpa using renyi_of_dp α.2 h

/-! ## Concentrated bounds give Rényi bounds -/

/-- zCDP gives a Rényi bound at every order (Def. 2.4). -/
theorem renyi_of_zcdp (hα : 1 < α) {ξ ρ : ℝ≥0∞} (h : zcdpDivergence (ξ, ρ) μ ν) :
    renyiDivergence α (ξ + ENNReal.ofReal α * ρ) μ ν :=
  zcdpDivergence_iff.1 h α hα

/-- tCDP gives a Rényi bound at every order below `ω` (Def. 2.5). -/
theorem renyi_of_tcdp (hα : 1 < α) (hω : α < ω) {ρ : ℝ≥0∞} (h : tcdpDivergence ω ρ μ ν) :
    renyiDivergence α (ENNReal.ofReal α * ρ) μ ν :=
  tcdpDivergence_iff.1 h α hα hω

/-! ## Rényi bounds give DP bounds -/

/-- A moment bound of order `α` gives the DP inequality with slack `δ` and budget
`r + log (1 / δ) / (α - 1)`: test the two-cell partition `{S, Sᶜ}` (cf. [R/D]). -/
theorem bound_of_fDiv_rpow_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] {r δ : ℝ} (hα : 1 < α)
    (hδ : 0 < δ) (h : fDiv (· ^ α) μ ν ≤ ((exp ((α - 1) * r) : ℝ) : EReal)) :
    Bound (ENNReal.ofReal (exp (r + log (1 / δ) / (α - 1)))) (ENNReal.ofReal δ) μ ν := by
  set E := exp ((α - 1) * r)
  intro S hS
  classical
  let k : X → Fin 2 := fun x ↦ if x ∈ S then 0 else 1
  have hk : Measurable k := measurable_const.ite hS measurable_const
  have h0 : k ⁻¹' {0} = S := by
    ext
    simp [k]
  set p := (μ S).toReal
  set q := (ν S).toReal
  have hcell : persp (· ^ α) p q ≤ (E : EReal) := by
    have hsum := (sum_persp_le_fDiv (convexOn_rpow hα.le)
      (continuousWithinAt_rpow_zero (zero_lt_one.trans hα)) hk).trans h
    rw [Fin.sum_univ_two, h0] at hsum
    exact (le_add_of_nonneg_right
      (persp_rpow_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)).trans hsum
  have hp : 0 ≤ p := ENNReal.toReal_nonneg
  have hq : 0 ≤ q := ENNReal.toReal_nonneg
  suffices hpq : p ≤ exp (r + log (1 / δ) / (α - 1)) * q + δ by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ S), ← ENNReal.ofReal_toReal (measure_ne_top ν S),
      ← ENNReal.ofReal_mul (exp_pos _).le, ← ENNReal.ofReal_add (by positivity) hδ.le]
    exact ENNReal.ofReal_le_ofReal hpq
  rcases hq.eq_or_lt with hq0 | hq0
  · rcases hp.eq_or_lt with hp0 | hp0
    · rw [← hp0]
      positivity
    · rw [← hq0, persp_rpow_zero_right hα hp0] at hcell
      exact absurd hcell (by simp)
  rw [persp_rpow_of_pos α hq0, EReal.coe_le_coe_iff] at hcell
  -- if `p > e^ε q + δ` then `q (p/q)^α > δ e^{ε(α-1)} = e^{(α-1) r}`, contradicting `hcell`
  by_contra! hcon
  have hpδ : δ < p := lt_of_le_of_lt (le_add_of_nonneg_left (by positivity)) hcon
  set ε := r + log (1 / δ) / (α - 1)
  have hr : exp ε < p / q := by
    rw [lt_div_iff₀ hq0]
    linarith [mul_nonneg (exp_pos ε).le hq]
  have hα' : 0 < α - 1 := sub_pos.2 hα
  have hp0 : p ≠ 0 := (hδ.trans hpδ).ne'
  have key : p * exp ε ^ (α - 1) < E := by
    calc p * exp ε ^ (α - 1) < p * (p / q) ^ (α - 1) := by gcongr
      _ = q * (p / q) ^ α := by
          rw [Real.rpow_sub_one (div_pos (hδ.trans hpδ) hq0).ne']
          field_simp
      _ ≤ E := hcell
  have hE : E = δ * exp ε ^ (α - 1) := by
    rw [← exp_mul, show ε * (α - 1) = (α - 1) * r + log (1 / δ) by
      simp only [ε]; field_simp, exp_add, exp_log (by positivity),
      mul_left_comm, mul_one_div_cancel hδ.ne', mul_one]
  rw [hE] at key
  exact (lt_of_mul_lt_mul_right key (by positivity)).not_gt hpδ

/-- A Rényi bound of order `α` gives DP at every slack `δ > 0` ([R/D]). -/
theorem dp_of_renyi [IsFiniteMeasure μ] [IsFiniteMeasure ν] {ρ : ℝ≥0∞} {δ : ℝ} (hα : 1 < α)
    (hδ : 0 < δ) (h : renyiDivergence α ρ μ ν) :
    dp (ρ + ENNReal.ofReal (log (1 / δ) / (α - 1)), ENNReal.ofReal δ) μ ν := by
  rcases eq_or_ne ρ ⊤ with rfl | hρ
  · simpa using dp_top_left
  intro _
  rw [expBudget_of_ne_top (by finiteness), ENNReal.toReal_add hρ ENNReal.ofReal_ne_top]
  refine (bound_of_fDiv_rpow_le hα hδ ((renyiDivergence_iff_of_ne_top hα.le hρ).1 h)).mono ?_
    le_rfl
  gcongr
  rw [ENNReal.toReal_ofReal']
  exact le_max_left _ _

/-- Rényi bounds `g α` at the orders `α ∈ A` give DP at every slack `δ > 0`, at the best order
([R/D]). -/
theorem dp_of_forall_renyi [IsFiniteMeasure μ] [IsFiniteMeasure ν] {A : Set ℝ} (hA : A ⊆ Ioi 1)
    {g : ℝ → ℝ≥0∞} {δ : ℝ} (hδ : 0 < δ) (h : ∀ α ∈ A, renyiDivergence α (g α) μ ν) :
    dp (⨅ α ∈ A, g α + ENNReal.ofReal (log (1 / δ) / (α - 1)), ENNReal.ofReal δ) μ ν :=
  dp_iInf_left fun α ↦ by
    by_cases hα : α ∈ A
    · simpa [hα] using dp_of_renyi (hA hα) hδ (h α hα)
    · simpa [hα] using dp_top_left

/-- Moment bounds on the line `ξ + α ρ` at all orders `α > 1` give the DP inequality with slack `δ`
and budget `ξ + ρ + 2 √(ρ log (1 / δ))`, at the order `1 + √(log (1 / δ) / ρ)` (cf. [z/D]). -/
theorem bound_of_forall_fDiv_rpow_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] {ξ ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ) (hδ₁ : δ < 1)
    (h : ∀ α, 1 < α → fDiv (· ^ α) μ ν ≤ ((exp ((α - 1) * (ξ + α * ρ)) : ℝ) : EReal)) :
    Bound (ENNReal.ofReal (exp (ξ + ρ + 2 * √(ρ * log (1 / δ))))) (ENNReal.ofReal δ) μ ν := by
  have hL := log_pos (one_lt_one_div hδ hδ₁)
  rcases hρ.eq_or_lt with rfl | hρ
  · -- with `ρ = 0`, let the order tend to infinity
    have he : Tendsto (fun n : ℕ ↦ ξ + log (1 / δ) / ((n + 2 : ℝ) - 1)) atTop (𝓝 ξ) := by
      have : Tendsto (fun n : ℕ ↦ log (1 / δ) / ((n + 2 : ℝ) - 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
      simpa using tendsto_const_nhds.add this
    simp only [zero_mul, Real.sqrt_zero, mul_zero, add_zero]
    refine Bound.of_tendsto he fun n ↦ ?_
    have := h (n + 2) (by linarith [n.cast_nonneg (α := ℝ)])
    rw [mul_zero, add_zero] at this
    exact bound_of_fDiv_rpow_le (by linarith [n.cast_nonneg (α := ℝ)]) hδ this
  · -- otherwise use the optimal order `1 + √(log (1 / δ) / ρ)`
    set t := √(log (1 / δ) / ρ)
    have ht : 0 < t := sqrt_pos.2 (div_pos hL hρ)
    have ht2 : t ^ 2 = log (1 / δ) / ρ := sq_sqrt (div_pos hL hρ).le
    have := bound_of_fDiv_rpow_le (by linarith) hδ (h (1 + t) (by linarith))
    have hs : √(ρ * log (1 / δ)) = ρ * t := by
      rw [show ρ * log (1 / δ) = (ρ * t) ^ 2 by rw [mul_pow, ht2]; field_simp,
        sqrt_sq (by positivity)]
    have heq : ξ + (1 + t) * ρ + log (1 / δ) / (1 + t - 1) =
        ξ + ρ + 2 * √(ρ * log (1 / δ)) := by
      rw [hs, add_sub_cancel_left, show log (1 / δ) = ρ * t ^ 2 by rw [ht2]; field_simp]
      field_simp
      ring
    rwa [heq] at this

/-- Moment bounds on the line `α ρ` at the orders `1 < α < ω` give the DP inequality with slack
`δ`, at the order `β = min ω (1 + √(log (1 / δ) / ρ))` (cf. [t/D]). -/
theorem bound_of_forall_lt_fDiv_rpow_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] {ρ δ : ℝ}
    (hρ : 0 < ρ) (hω : 1 < ω) (hδ : 0 < δ) (hδ₁ : δ < 1)
    (h : ∀ α, 1 < α → α < ω → fDiv (· ^ α) μ ν ≤ ((exp ((α - 1) * (α * ρ)) : ℝ) : EReal)) :
    Bound (ENNReal.ofReal (exp (ρ * min ω (1 + √(log (1 / δ) / ρ)) +
      log (1 / δ) / (min ω (1 + √(log (1 / δ) / ρ)) - 1)))) (ENNReal.ofReal δ) μ ν := by
  have hL := log_pos (one_lt_one_div hδ hδ₁)
  set β := min ω (1 + √(log (1 / δ) / ρ))
  have hβ : 1 < β := lt_min hω (by linarith [sqrt_pos.2 (div_pos hL hρ)])
  have key {α : ℝ} (hα : 1 < α) (hαω : α < ω) :
      Bound (ENNReal.ofReal (exp (ρ * α + log (1 / δ) / (α - 1)))) (ENNReal.ofReal δ) μ ν := by
    simpa only [mul_comm α ρ] using bound_of_fDiv_rpow_le hα hδ (h α hα hαω)
  rcases (min_le_left ω _ : β ≤ ω).lt_or_eq with hlt | hβω
  · exact key hβ hlt
  -- at the boundary `β = ω`, approach `ω` from below
  set a : ℕ → ℝ := fun n ↦ ω - (ω - 1) / (n + 2)
  have ha : Tendsto a atTop (𝓝 ω) := by
    simpa [a] using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop (R := ℝ))))
  have ha₁ (n : ℕ) : 1 < a n := by
    have : (ω - 1) / (n + 2) < ω - 1 :=
      div_lt_self (by linarith) (by linarith [n.cast_nonneg (α := ℝ)])
    simp only [a]
    linarith
  have haω (n : ℕ) : a n < ω := by
    simp only [a]
    linarith [div_pos (by linarith : 0 < ω - 1) (by positivity : (0 : ℝ) < n + 2)]
  rw [show β = ω from hβω]
  exact Bound.of_tendsto ((tendsto_const_nhds.mul ha).add (tendsto_const_nhds.div
    (ha.sub_const 1) (by linarith))) fun n ↦ key (ha₁ n) (haω n)

/-- zCDP gives DP at every slack `0 < δ < 1` ([z/D]). -/
theorem dp_of_zcdp [IsFiniteMeasure μ] [IsFiniteMeasure ν] {ξ ρ : ℝ≥0∞} {δ : ℝ} (hδ : 0 < δ)
    (hδ₁ : δ < 1) (h : zcdpDivergence (ξ, ρ) μ ν) :
    dp (ξ + ρ + ENNReal.ofReal (2 * √(ρ.toReal * log (1 / δ))), ENNReal.ofReal δ) μ ν := by
  rcases eq_or_ne ξ ⊤ with rfl | hξ
  · simpa using dp_top_left
  rcases eq_or_ne ρ ⊤ with rfl | hρ
  · simpa using dp_top_left
  intro _
  rw [expBudget_of_ne_top (by finiteness), ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top,
    ENNReal.toReal_add hξ hρ, ENNReal.toReal_ofReal (by positivity)]
  refine bound_of_forall_fDiv_rpow_le ENNReal.toReal_nonneg hδ hδ₁ fun α hα ↦ ?_
  have := (renyiDivergence_iff_of_ne_top hα.le (by finiteness)).1 (renyi_of_zcdp hα h)
  rwa [ENNReal.toReal_add hξ (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith)] at this

/-- tCDP gives DP at every slack `0 < δ < 1`, at the order
`β = min ω (1 + √(log (1 / δ) / ρ))` ([t/D]). -/
theorem dp_of_tcdp [IsFiniteMeasure μ] [IsFiniteMeasure ν] {ρ : ℝ≥0∞} {δ : ℝ} (hρ : 0 < ρ)
    (hω : 1 < ω) (hδ : 0 < δ) (hδ₁ : δ < 1) (h : tcdpDivergence ω ρ μ ν) :
    dp (ρ * ENNReal.ofReal (min ω (1 + √(log (1 / δ) / ρ.toReal))) +
      ENNReal.ofReal (log (1 / δ) / (min ω (1 + √(log (1 / δ) / ρ.toReal)) - 1)),
      ENNReal.ofReal δ) μ ν := by
  set β := min ω (1 + √(log (1 / δ) / ρ.toReal))
  rcases eq_or_ne ρ ⊤ with rfl | hρ'
  · have hβ : 0 < β := lt_min (zero_lt_one.trans hω) (by positivity)
    simpa [ENNReal.top_mul (ENNReal.ofReal_pos.2 hβ).ne'] using dp_top_left
  have hL := log_pos (one_lt_one_div hδ hδ₁)
  have hρr : 0 < ρ.toReal := ENNReal.toReal_pos hρ.ne' hρ'
  have hβ : 1 < β := lt_min hω (by linarith [sqrt_pos.2 (div_pos hL hρr)])
  intro _
  rw [expBudget_of_ne_top (by finiteness), ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal (div_nonneg hL.le (by linarith))]
  refine bound_of_forall_lt_fDiv_rpow_le hρr hω hδ hδ₁ fun α hα hαω ↦ ?_
  have := (renyiDivergence_iff_of_ne_top hα.le (by finiteness)).1 (renyi_of_tcdp hα hαω h)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this

end

/-! ## Conversions of codensity liftings -/

/-- Point masses with ordered masses are within budget zero for a reflexive, right-monotone
divergence. -/
theorem zero_smul_dirac_of_le {B : Type v} [Zero B] {D : GradedDivergence.{u} B} [D.IsReflexive]
    [D.IsRightMonotone] {a a' : ℝ≥0∞} (h : a ≤ a') (ha' : a' ≤ 1) :
    D 0 (a • dirac PUnit.unit.{u + 1}) (a' • dirac PUnit.unit) := by
  have : IsSubProbabilityMeasure (a • dirac PUnit.unit.{u + 1}) := ⟨by simpa using h.trans ha'⟩
  have : IsSubProbabilityMeasure (a' • dirac PUnit.unit.{u + 1}) := ⟨by simpa using ha'⟩
  exact IsRightMonotone.right_mono (by gcongr) (IsReflexive.refl _)

/-- A conversion of a divergence into DP carries codensity liftings of relations along: test the
DP lifting with mass kernels. -/
theorem codensity_dp_rel_of_imp {B : Type v} [AddZeroClass B] [PartialOrder B]
    [CanonicallyOrderedAdd B] [OrderTop B] {D : GradedDivergence.{u} B} [D.IsGraded]
    [D.IsReflexive] [D.IsRightMonotone] {φ : B → ℝ≥0∞ × ℝ≥0∞}
    (himp : ∀ b {Z : Type u} [MeasurableSpace Z] {μ ν : Measure Z} [IsSubProbabilityMeasure μ]
      [IsSubProbabilityMeasure ν], D b μ ν → dp (φ b) μ ν)
    (htop : (φ ⊤).1 = ⊤) {b : B} {S : X → Y → Prop} {μ : Measure X} {ν : Measure Y}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] (h : (codensity D).Rel b S μ ν) :
    (codensity dp).Rel (φ b) S μ ν := by
  rcases eq_or_lt_of_le (le_top : b ≤ ⊤) with rfl | hb
  · exact (Prod.ext htop rfl : φ ⊤ = (⊤, (φ ⊤).2)) ▸ codensity_dp_top_left
  rcases eq_or_ne (φ b).1 ⊤ with hε | hε
  · exact (Prod.ext hε rfl : φ b = (⊤, (φ b).2)) ▸ codensity_dp_top_left
  refine (codensity_dp_rel_iff hε).2 fun f g hf hg hf1 hg1 hfg ↦ ?_
  have := Kernel.isSubMarkovKernel_mass.{u} hf hf1
  have := Kernel.isSubMarkovKernel_mass.{u} hg hg1
  have hD := codensity_rel_iff.1 h (by rwa [add_zero])
    (k := Kernel.mass.{u} hf) (l := Kernel.mass.{u} hg) fun x y hS ↦ by
      simpa [Kernel.mass_apply] using zero_smul_dirac_of_le (hfg x y hS) (hg1 y)
  rw [add_zero] at hD
  exact dp_smul_dirac_iff.1 (by simpa only [Kernel.mass_comp] using himp b hD) hε.lt_top

end GradedDivergence

/-! ## Homomorphisms into DP -/

open GradedDivergence

namespace LiftingRelHom

variable {α ω δ : ℝ}

/-- Rényi liftings of relations are DP liftings at every slack `δ > 0` ([R/D]). -/
noncomputable def renyiToDp [hα : Fact (1 < α)] (hδ : 0 < δ) :
    LiftingRelHom (codensity (renyiDivergence.{u} α)) (codensity dp.{u}) where
  map ρ := (ρ + ENNReal.ofReal (log (1 / δ) / (α - 1)), ENNReal.ofReal δ)
  mono _ _ h := Prod.mk_le_mk.2 ⟨by gcongr, le_rfl⟩
  map_rel := codensity_dp_rel_of_imp (D := renyiDivergence α) (fun _ ↦ dp_of_renyi hα.out hδ)
    (by simp)

@[simp]
theorem renyiToDp_map [Fact (1 < α)] (hδ : 0 < δ) (ρ : ℝ≥0∞) :
    (renyiToDp.{u} (α := α) hδ).map ρ =
      (ρ + ENNReal.ofReal (log (1 / δ) / (α - 1)), ENNReal.ofReal δ) :=
  rfl

/-- zCDP codensity liftings of relations are DP liftings at every slack `δ > 0`, at the best
order ([z/D]). -/
noncomputable def codensityZcdpToDp (hδ : 0 < δ) :
    LiftingRelHom (codensity zcdpDivergence.{u}) (codensity dp.{u}) where
  map b := (⨅ α ∈ Ioi 1, b.1 + ENNReal.ofReal α * b.2 + ENNReal.ofReal (log (1 / δ) / (α - 1)),
    ENNReal.ofReal δ)
  mono _ _ h := Prod.mk_le_mk.2 ⟨iInf₂_mono fun _ _ ↦ by grw [h.1, h.2], le_rfl⟩
  map_rel := codensity_dp_rel_of_imp (D := zcdpDivergence)
    (fun _ ↦ (dp_of_forall_renyi subset_rfl hδ fun _ hα ↦ renyi_of_zcdp hα ·))
    (by simp)

@[simp]
theorem codensityZcdpToDp_map (hδ : 0 < δ) (b : ℝ≥0∞ × ℝ≥0∞) :
    (codensityZcdpToDp.{u} hδ).map b =
      (⨅ α ∈ Ioi 1, b.1 + ENNReal.ofReal α * b.2 + ENNReal.ofReal (log (1 / δ) / (α - 1)),
        ENNReal.ofReal δ) :=
  rfl

/-- tCDP codensity liftings of relations are DP liftings at every slack `δ > 0`, at the best
order below `ω` ([t/D]). -/
noncomputable def codensityTcdpToDp (hδ : 0 < δ) :
    LiftingRelHom (codensity (tcdpDivergence.{u} ω)) (codensity dp.{u}) where
  map ρ := (⨅ α ∈ Ioo 1 ω, ENNReal.ofReal α * ρ + ENNReal.ofReal (log (1 / δ) / (α - 1)),
    ENNReal.ofReal δ)
  mono _ _ h := Prod.mk_le_mk.2 ⟨iInf₂_mono fun _ _ ↦ by gcongr, le_rfl⟩
  map_rel := codensity_dp_rel_of_imp (D := tcdpDivergence ω)
    (fun _ ↦ (dp_of_forall_renyi Ioo_subset_Ioi_self hδ fun _ hα ↦ renyi_of_tcdp hα.1 hα.2 ·))
    (by simp +contextual [ENNReal.mul_top, (zero_lt_one.trans _).ne'])

@[simp]
theorem codensityTcdpToDp_map (hδ : 0 < δ) (ρ : ℝ≥0∞) :
    (codensityTcdpToDp.{u} (ω := ω) hδ).map ρ =
      (⨅ α ∈ Ioo 1 ω, ENNReal.ofReal α * ρ + ENNReal.ofReal (log (1 / δ) / (α - 1)),
        ENNReal.ofReal δ) :=
  rfl

/-- zCDP liftings of relations are DP liftings at every slack `δ > 0`, at the best order
([z/D]). -/
noncomputable def zcdpToDp (hδ : 0 < δ) : LiftingRelHom zcdpLifting.{u} (codensity dp.{u}) :=
  (codensityZcdpToDp hδ).comp ((LiftingHom.concentratedToCodensity _).toLiftingRelHom rfl)

@[simp]
theorem zcdpToDp_map (hδ : 0 < δ) (b : ℝ≥0∞ × ℝ≥0∞) :
    (zcdpToDp.{u} hδ).map b =
      (⨅ α ∈ Ioi 1, b.1 + ENNReal.ofReal α * b.2 + ENNReal.ofReal (log (1 / δ) / (α - 1)),
        ENNReal.ofReal δ) :=
  rfl

/-- tCDP liftings of relations are DP liftings at every slack `δ > 0`, at the best order below
`ω` ([t/D]). -/
noncomputable def tcdpToDp (hδ : 0 < δ) : LiftingRelHom (tcdpLifting.{u} ω) (codensity dp.{u}) :=
  (codensityTcdpToDp hδ).comp ((LiftingHom.tcdpToCodensity ω).toLiftingRelHom rfl)

@[simp]
theorem tcdpToDp_map (hδ : 0 < δ) (ρ : ℝ≥0∞) :
    (tcdpToDp.{u} (ω := ω) hδ).map ρ =
      (⨅ α ∈ Ioo 1 ω, ENNReal.ofReal α * ρ + ENNReal.ofReal (log (1 / δ) / (α - 1)),
        ENNReal.ofReal δ) :=
  rfl

end LiftingRelHom

/-- Without the quadratic term, the best Rényi conversion of `(ξ, 0)` costs nothing over `ξ`:
send the order to infinity. -/
theorem iInf_conversion_le (ξ : ℝ≥0∞) {δ : ℝ} :
    ⨅ α ∈ Set.Ioi (1 : ℝ), ξ + ENNReal.ofReal α * 0 +
      ENNReal.ofReal (Real.log (1 / δ) / (α - 1)) ≤ ξ := by
  refine ENNReal.le_of_forall_pos_le_add fun t ht _ ↦ ?_
  set l := Real.log (1 / δ)
  have hl : 0 < |l| + 1 := by positivity
  have ht' : (0 : ℝ) < t := ht
  refine (iInf₂_le (1 + (|l| + 1) / t) (lt_add_of_pos_right _ (div_pos hl ht'))).trans ?_
  rw [mul_zero, add_zero, add_sub_cancel_left]
  gcongr
  refine ENNReal.ofReal_le_of_le_toReal ?_
  rw [ENNReal.coe_toReal, div_div_eq_mul_div, div_le_iff₀ hl]
  nlinarith [le_abs_self l]

namespace GradedDivergence

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] {S : X → Y → Prop} {α ω δ : ℝ}

/-- zCDP liftings of relations are DP liftings at every slack `0 < δ < 1`, in closed form
([z/D]). -/
theorem codensity_dp_rel_of_zcdp {ξ ρ : ℝ≥0∞} (hδ : 0 < δ) (hδ₁ : δ < 1)
    (h : (codensity zcdpDivergence).Rel (ξ, ρ) S μ ν) :
    (codensity dp).Rel
      (ξ + ρ + ENNReal.ofReal (2 * √(ρ.toReal * log (1 / δ))), ENNReal.ofReal δ) S μ ν :=
  codensity_dp_rel_of_imp (φ := fun b ↦
      (b.1 + b.2 + ENNReal.ofReal (2 * √(b.2.toReal * log (1 / δ))), ENNReal.ofReal δ))
    (fun _ ↦ dp_of_zcdp hδ hδ₁) (by simp) h

/-- tCDP liftings of relations are DP liftings at every slack `δ > 0`, at a fixed order
`1 < α < ω` ([t/D]). -/
theorem codensity_dp_rel_of_tcdp {ρ : ℝ≥0∞} (hα : 1 < α) (hαω : α < ω) (hδ : 0 < δ)
    (h : (codensity (tcdpDivergence ω)).Rel ρ S μ ν) :
    (codensity dp).Rel
      (ENNReal.ofReal α * ρ + ENNReal.ofReal (log (1 / δ) / (α - 1)), ENNReal.ofReal δ) S μ ν :=
  ((LiftingRelHom.codensityTcdpToDp hδ).map_rel h).mono
    (Prod.mk_le_mk.2 ⟨iInf₂_le α ⟨hα, hαω⟩, le_rfl⟩) fun _ _ ↦ id

end GradedDivergence
