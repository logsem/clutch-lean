module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Metrology.Couplings.DP.Basic

/-! Conversions between differential privacy and its Rényi relaxations (Approximate Span
Liftings, Fig. 4: [D/z], [R/D], [z/D], [t/D]). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Real
open scoped ENNReal

namespace DPDiv

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-! ### The Rényi weight -/

theorem slopeAtTop_rpow {α : ℝ} (hα : 1 < α) : (WeightFunction.rpow α).slopeAtTop = ⊤ := by
  refine Tendsto.limsup_eq (EReal.tendsto_coe_atTop.comp ?_)
  refine (tendsto_rpow_atTop (sub_pos.2 hα)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [WeightFunction.rpow, Real.rpow_sub_one ht.ne']

theorem persp_rpow_of_pos (α : ℝ) {p q : ℝ} (hq : 0 < q) :
    (WeightFunction.rpow α).persp p q = ((q * (p / q) ^ α : ℝ) : EReal) := by
  simp [WeightFunction.persp, hq.ne', WeightFunction.rpow]

theorem persp_rpow_of_zero {α : ℝ} (hα : 1 < α) {p : ℝ} (hp : 0 < p) :
    (WeightFunction.rpow α).persp p 0 = ⊤ := by
  simp [WeightFunction.persp, hp.ne', slopeAtTop_rpow hα, EReal.coe_mul_top_of_pos hp]

theorem persp_rpow_nonneg {α : ℝ} (hα : 1 < α) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    0 ≤ (WeightFunction.rpow α).persp p q := by
  rcases hq.eq_or_lt with rfl | hq
  · rcases hp.eq_or_lt with rfl | hp
    · simp [WeightFunction.persp]
    · simp [persp_rpow_of_zero hα hp]
  · rw [persp_rpow_of_pos α hq]
    exact EReal.coe_nonneg.2 (by positivity)

/-! ### Rényi bounds as `f`-divergence bounds -/

theorem coe_mul_le_iff {c : ℝ} (hc : 0 < c) {L : EReal} {d : ℝ} :
    (c : EReal) * L ≤ d ↔ L ≤ ((d / c : ℝ) : EReal) := by
  induction L with
  | bot => simp [EReal.coe_mul_bot_of_pos hc]
  | top => simp [EReal.coe_mul_top_of_pos hc]
  | coe l => rw [← EReal.coe_mul, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff, le_div_iff₀ hc,
      mul_comm]

/-- A Rényi divergence bound is a bound on the `t ↦ t ^ α` divergence. -/
theorem renyiDiv_le_iff {α : ℝ} (hα : 1 < α) (μ ν : Measure X) (d : ℝ) :
    renyiDiv α μ ν ≤ d ↔
      (fDiv (.rpow α) μ ν).toENNReal ≤ ENNReal.ofReal (exp ((α - 1) * d)) := by
  rw [renyiDiv, coe_mul_le_iff (inv_pos.2 (sub_pos.2 hα)), ← ENNReal.log_le_log_iff,
    ENNReal.log_ofReal_of_pos (exp_pos _), log_exp, div_inv_eq_mul, mul_comm]

theorem le_coe_toENNReal (x : EReal) : x ≤ (x.toENNReal : EReal) := by
  rcases le_total 0 x with h | h
  · rw [EReal.coe_toENNReal h]
  · exact h.trans (EReal.coe_ennreal_nonneg _)

/-! ### [D/z]: pure DP bounds every Rényi divergence -/

/-- A DP inequality without slack bounds the Rényi divergences by the budget (cf. [D/z]). -/
theorem renyiDiv_le_of_bound {μ ν : Measure X} [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] {ε : ℝ} (h : Bound (ENNReal.ofReal (exp ε)) 0 μ ν) {α : ℝ}
    (hα : 1 < α) : renyiDiv α μ ν ≤ ε := by
  rw [renyiDiv_le_iff hα, ← EReal.toENNReal_coe (x := ENNReal.ofReal _)]
  refine EReal.toENNReal_le_toENNReal (iSup_le fun n ↦ iSup_le fun k ↦ iSup_le fun hk ↦ ?_)
  have hcell (i : Fin n) : (WeightFunction.rpow α).persp (μ (k ⁻¹' {i})).toReal
      (ν (k ⁻¹' {i})).toReal ≤ ((exp ((α - 1) * ε) * (μ (k ⁻¹' {i})).toReal : ℝ) : EReal) := by
    set p := (μ (k ⁻¹' {i})).toReal
    set q := (ν (k ⁻¹' {i})).toReal
    have hpq : p ≤ exp ε * q := by
      have := h _ (hk (measurableSet_singleton i))
      rw [add_zero] at this
      simpa [p, q, ENNReal.toReal_mul, (exp_pos ε).le] using
        ENNReal.toReal_mono (by finiteness) this
    rcases (ENNReal.toReal_nonneg : 0 ≤ q).eq_or_lt with hq | hq
    · have hq' : q = 0 := hq.symm
      rw [hq', mul_zero] at hpq
      have hp : p = 0 := le_antisymm hpq ENNReal.toReal_nonneg
      rw [hq', hp]
      simp [WeightFunction.persp]
    rw [persp_rpow_of_pos α hq, EReal.coe_le_coe_iff]
    have hr : p / q ≤ exp ε := (div_le_iff₀ hq).2 (by linarith)
    have hp : 0 ≤ p := ENNReal.toReal_nonneg
    calc q * (p / q) ^ α = p * (p / q) ^ (α - 1) := by
          rcases hp.eq_or_lt with h0 | h0
          · simp [← h0, Real.zero_rpow (by linarith : α ≠ 0),
              Real.zero_rpow (by linarith : α - 1 ≠ 0)]
          have : p ≠ 0 := h0.ne'
          rw [Real.rpow_sub_one (div_pos h0 hq).ne']
          field_simp
          rfl
      _ ≤ p * exp ε ^ (α - 1) := by gcongr
      _ = exp ((α - 1) * ε) * p := by rw [← exp_mul, mul_comm ε, mul_comm]
  calc ∑ i, (WeightFunction.rpow α).persp (μ (k ⁻¹' {i})).toReal (ν (k ⁻¹' {i})).toReal
      ≤ ∑ i, ((exp ((α - 1) * ε) * (μ (k ⁻¹' {i})).toReal : ℝ) : EReal) :=
        Finset.sum_le_sum fun i _ ↦ hcell i
    _ = ((exp ((α - 1) * ε) * (μ (k ⁻¹' univ)).toReal : ℝ) : EReal) := by
        rw [← EReal.coe_finset_sum, ← Finset.mul_sum, ← ENNReal.toReal_sum (by finiteness),
          sum_measure_preimage_singleton _ fun _ _ ↦ hk (measurableSet_singleton _),
          Finset.coe_univ]
    _ ≤ (ENNReal.ofReal (exp ((α - 1) * ε)) : EReal) := by
        rw [EReal.coe_ennreal_ofReal, max_eq_left (exp_pos _).le, EReal.coe_le_coe_iff]
        refine mul_le_of_le_one_right (exp_pos _).le ?_
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one ((measure_mono (subset_univ _)).trans
          (IsSubProbabilityMeasure.measure_univ_le_one.trans ENNReal.ofReal_one.ge))

/-! ### [R/D]: Rényi bounds give DP inequalities -/

/-- A Rényi bound of order `α` gives the DP inequality with slack `δ` and budget
`ρ + log (1 / δ) / (α - 1)` (cf. [R/D]). -/
theorem bound_of_renyiDiv_le {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {α ρ δ : ℝ} (hα : 1 < α) (hδ : 0 < δ) (h : renyiDiv α μ ν ≤ ρ) :
    Bound (ENNReal.ofReal (exp (ρ + log (1 / δ) / (α - 1)))) (ENNReal.ofReal δ) μ ν := by
  rw [renyiDiv_le_iff hα] at h
  set E := exp ((α - 1) * ρ)
  intro S hS
  classical
  -- the two-cell partition `{S, Sᶜ}` bounds the perspective on `S`
  let k : X → Fin 2 := fun x ↦ if x ∈ S then 0 else 1
  have hk : Measurable k := measurable_const.ite hS measurable_const
  have h0 : k ⁻¹' {0} = S := by ext x; by_cases hx : x ∈ S <;> simp [k, hx]
  set p := (μ S).toReal
  set q := (ν S).toReal
  have hcell : (WeightFunction.rpow α).persp p q ≤ (ENNReal.ofReal E : EReal) := by
    have hsum : ∑ i, (WeightFunction.rpow α).persp (μ (k ⁻¹' {i})).toReal
        (ν (k ⁻¹' {i})).toReal ≤ fDiv (.rpow α) μ ν :=
      le_iSup_of_le 2 <| le_iSup_of_le k <| le_iSup_of_le hk le_rfl
    rw [Fin.sum_univ_two, h0] at hsum
    refine le_trans ?_ ((hsum.trans (le_coe_toENNReal _)).trans
      (EReal.coe_ennreal_le_coe_ennreal_iff.2 h))
    exact le_add_of_nonneg_right
      (persp_rpow_nonneg hα ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  have hp : 0 ≤ p := ENNReal.toReal_nonneg
  have hq : 0 ≤ q := ENNReal.toReal_nonneg
  -- reduce to the real inequality `p ≤ e^ε q + δ`
  suffices hpq : p ≤ exp (ρ + log (1 / δ) / (α - 1)) * q + δ by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ S), ← ENNReal.ofReal_toReal (measure_ne_top ν S),
      ← ENNReal.ofReal_mul (exp_pos _).le, ← ENNReal.ofReal_add (by positivity) hδ.le]
    exact ENNReal.ofReal_le_ofReal hpq
  rcases hq.eq_or_lt with hq0 | hq0
  · -- an event of `ν`-mass zero has `μ`-mass zero
    rcases hp.eq_or_lt with hp0 | hp0
    · rw [← hp0]; positivity
    · rw [← hq0, persp_rpow_of_zero hα hp0] at hcell
      exact absurd hcell (by simp)
  rw [persp_rpow_of_pos α hq0, EReal.coe_ennreal_ofReal, max_eq_left (exp_pos _).le,
    EReal.coe_le_coe_iff] at hcell
  by_contra! hcon
  have hpδ : δ < p := lt_of_le_of_lt (le_add_of_nonneg_left (by positivity)) hcon
  set ε := ρ + log (1 / δ) / (α - 1)
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
    rw [← exp_mul, show ε * (α - 1) = (α - 1) * ρ + log (1 / δ) by
      simp only [ε]; field_simp, exp_add, exp_log (by positivity)]
    field_simp
    rfl
  rw [hE] at key
  exact absurd (lt_of_mul_lt_mul_right key (by positivity)) (not_lt.2 hpδ.le)

/-- DP inequalities for budgets converging to `e₀` give the DP inequality at `e₀`. -/
theorem bound_of_tendsto {μ ν : Measure X} [IsFiniteMeasure ν] {e : ℕ → ℝ} {e₀ : ℝ}
    (he : Tendsto e atTop (𝓝 e₀)) {δ : ℝ≥0∞}
    (h : ∀ n, Bound (ENNReal.ofReal (exp (e n))) δ μ ν) :
    Bound (ENNReal.ofReal (exp e₀)) δ μ ν := fun S hS ↦
  ge_of_tendsto' ((ENNReal.Tendsto.mul_const
    (ENNReal.tendsto_ofReal ((continuous_exp.tendsto e₀).comp he))
    (Or.inr (measure_ne_top ν S))).add_const δ) fun n ↦ h n S hS

/-! ### Mechanism-level conversions -/

variable {m : Mechanism X Y} {Φ : Adjacency X}

/-- Pure differential privacy implies zero-concentrated differential privacy ([D/z]). -/
theorem zCDP_of_DP [∀ x, IsSubProbabilityMeasure (m x)] {ε : ℝ} (h : DP m Φ ε 0) :
    zCDP m Φ ε 0 := fun _ _ hx α hα ↦ by
  rw [mul_zero, add_zero]
  exact renyiDiv_le_of_bound (h hx) hα

/-- Rényi differential privacy implies differential privacy ([R/D]). -/
theorem DP_of_RDP [IsFiniteKernel m] {α ρ δ : ℝ} (hα : 1 < α) (hδ : 0 < δ) (h : RDP m Φ α ρ) :
    DP m Φ (ρ + log (1 / δ) / (α - 1)) (ENNReal.ofReal δ) := fun _ _ hx ↦
  bound_of_renyiDiv_le hα hδ (h hx)

/-- Zero-concentrated differential privacy implies differential privacy ([z/D]). -/
theorem DP_of_zCDP [IsFiniteKernel m] {ξ ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ : 0 < δ) (hδ₁ : δ < 1)
    (h : zCDP m Φ ξ ρ) :
    DP m Φ (ξ + ρ + 2 * √(ρ * log (1 / δ))) (ENNReal.ofReal δ) := fun x x' hx ↦ by
  have hL : 0 < log (1 / δ) := log_pos (by rw [one_div]; exact one_lt_inv_iff₀.2 ⟨hδ, hδ₁⟩)
  rcases hρ.eq_or_lt with rfl | hρ
  · -- with `ρ = 0`, let the order tend to infinity
    have he : Tendsto (fun n : ℕ ↦ ξ + log (1 / δ) / ((n + 2 : ℝ) - 1)) atTop (𝓝 ξ) := by
      have : Tendsto (fun n : ℕ ↦ log (1 / δ) / ((n + 2 : ℝ) - 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
      simpa using tendsto_const_nhds.add this
    simp only [zero_mul, Real.sqrt_zero, mul_zero, add_zero]
    refine bound_of_tendsto he fun n ↦ ?_
    have := h hx (n + 2) (by linarith [n.cast_nonneg (α := ℝ)])
    rw [mul_zero, add_zero] at this
    exact bound_of_renyiDiv_le (by linarith [n.cast_nonneg (α := ℝ)]) hδ this
  · -- otherwise use the optimal order `1 + √(log (1 / δ) / ρ)`
    set t := √(log (1 / δ) / ρ)
    have ht : 0 < t := sqrt_pos.2 (div_pos hL hρ)
    have ht2 : t ^ 2 = log (1 / δ) / ρ := sq_sqrt (div_pos hL hρ).le
    have := bound_of_renyiDiv_le (α := 1 + t) (by linarith) hδ (h hx (1 + t) (by linarith))
    have hs : √(ρ * log (1 / δ)) = ρ * t := by
      rw [show ρ * log (1 / δ) = (ρ * t) ^ 2 by rw [mul_pow, ht2]; field_simp,
        sqrt_sq (by positivity)]
    have heq : ξ + (1 + t) * ρ + log (1 / δ) / (1 + t - 1) = ξ + ρ + 2 * √(ρ * log (1 / δ)) := by
      rw [hs, add_sub_cancel_left, show log (1 / δ) = ρ * t ^ 2 by rw [ht2]; field_simp]
      field_simp
      ring
    rwa [heq] at this

/-- Truncated concentrated differential privacy implies differential privacy, at the order
`β = min ω (1 + √(log (1 / δ) / ρ))` ([t/D]). -/
theorem DP_of_tCDP [IsFiniteKernel m] {ρ ω δ : ℝ} (hρ : 0 < ρ) (hω : 1 < ω) (hδ : 0 < δ)
    (hδ₁ : δ < 1) (h : tCDP m Φ ρ ω) :
    DP m Φ (ρ * min ω (1 + √(log (1 / δ) / ρ)) + log (1 / δ) / (min ω (1 + √(log (1 / δ) / ρ)) - 1))
      (ENNReal.ofReal δ) := fun x x' hx ↦ by
  have hL : 0 < log (1 / δ) := log_pos (by rw [one_div]; exact one_lt_inv_iff₀.2 ⟨hδ, hδ₁⟩)
  set β := min ω (1 + √(log (1 / δ) / ρ))
  have hβ : 1 < β := lt_min hω (by linarith [sqrt_pos.2 (div_pos hL hρ)])
  have key {α : ℝ} (hα : 1 < α) (hαω : α < ω) :
      Bound (ENNReal.ofReal (exp (ρ * α + log (1 / δ) / (α - 1)))) (ENNReal.ofReal δ)
        (m x) (m x') := by
    have := bound_of_renyiDiv_le hα hδ (h hx α hα hαω)
    rwa [mul_comm α ρ] at this
  rcases (min_le_left ω _ : β ≤ ω).lt_or_eq with hlt | heq
  · exact key hβ hlt
  · -- at the boundary `β = ω`, approach `ω` from below
    set a : ℕ → ℝ := fun n ↦ ω - (ω - 1) / (n + 2)
    have ha : Tendsto a atTop (𝓝 ω) := by
      simpa [a] using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop (R := ℝ))))
    have ha₁ (n : ℕ) : 1 < a n := by
      have : (ω - 1) / (n + 2) < ω - 1 :=
        div_lt_self (by linarith) (by linarith [n.cast_nonneg (α := ℝ)])
      simp only [a]; linarith
    have haω (n : ℕ) : a n < ω := by
      simp only [a]; linarith [div_pos (by linarith : 0 < ω - 1) (by positivity : (0 : ℝ) < n + 2)]
    have hβω : β = ω := heq
    rw [hβω]
    refine bound_of_tendsto ?_ fun n ↦ key (ha₁ n) (haω n)
    exact (tendsto_const_nhds.mul ha).add (tendsto_const_nhds.div (ha.sub_const 1)
      (by linarith))

end DPDiv
