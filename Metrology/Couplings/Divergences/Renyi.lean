module

public import Metrology.Couplings.Divergences.FDivBound
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-! # Rényi divergence

`renyiDivergence α` bounds the moment `fDiv (·^α)` by `e^{(α-1)ρ}`, i.e. `renyiDiv α ≤ ρ`
(Def. 2.2); main result: Rényi budgets add (`isComposable_renyi`, Thm. 4.11). -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory GradedLifting Set Filter Topology
open scoped ENNReal

namespace ProbabilityTheory
open Real ENNReal

variable {X : Type*} [MeasurableSpace X] {α : ℝ}

/-! ## The Rényi value -/

/-- The Rényi divergence `D_α(μ ‖ ν) = (α - 1)⁻¹ log ∫ (dμ/dν)^α dν` (Def. 2.2). -/
noncomputable def renyiDiv (α : ℝ) (μ ν : Measure X) : EReal :=
  ((α - 1)⁻¹ : ℝ) * ENNReal.log (fDiv (· ^ α) μ ν).toENNReal

theorem fDiv_rpow_nonneg {μ ν : Measure X} : 0 ≤ fDiv (· ^ α) μ ν :=
  fDiv_nonneg_of_nonneg fun _ ht ↦ rpow_nonneg ht α

end ProbabilityTheory

namespace GradedDivergence
open Real ENNReal

/-! ## The moment threshold `e^{(α-1)ρ}` -/

section renyiThresh

variable {α : ℝ} {ρ : ℝ≥0∞}

/-- The moment threshold `exp ((α - 1) ρ)`, `⊤` at `ρ = ⊤`. -/
noncomputable def renyiThresh (α : ℝ) (ρ : ℝ≥0∞) : EReal :=
  expBudget (ENNReal.ofReal (α - 1) * ρ)

/-- For finite `ρ` and `1 ≤ α`, the Rényi threshold is `exp ((α - 1) * ρ)`. -/
theorem renyiThresh_of_ne_top (hα : 1 ≤ α) (hρ : ρ ≠ ⊤) :
    renyiThresh α ρ = ((Real.exp ((α - 1) * ρ.toReal) : ℝ) : EReal) := by
  rw [renyiThresh, expBudget_of_ne_top (by finiteness), toReal_mul,
    toReal_ofReal (sub_nonneg.2 hα), EReal.coe_ennreal_ofReal, max_eq_left (exp_pos _).le]

theorem renyiThresh_top (hα : 1 < α) : renyiThresh α ⊤ = ⊤ := by
  simp [renyiThresh, mul_top (ofReal_pos.2 (sub_pos.2 hα)).ne']

@[simp]
theorem renyiThresh_zero : renyiThresh α 0 = 1 := by
  simp [renyiThresh]

theorem renyiThresh_mono : Monotone (renyiThresh α) := fun _ _ h ↦
  EReal.coe_ennreal_le_coe_ennreal_iff.2 (expBudget_mono (by gcongr))

theorem renyiThresh_nonneg : 0 ≤ renyiThresh α ρ :=
  EReal.coe_ennreal_nonneg _

/-- The Rényi threshold turns sums of budgets into products. -/
theorem renyiThresh_add (ρ ρ' : ℝ≥0∞) :
    renyiThresh α (ρ + ρ') = renyiThresh α ρ * renyiThresh α ρ' := by
  rw [renyiThresh, mul_add, expBudget_add, EReal.coe_ennreal_mul, renyiThresh, renyiThresh]

/-- The threshold is right continuous in the budget. -/
theorem le_renyiThresh_of_forall_lt (hα : 1 < α) {x : EReal}
    (h : ∀ ρ', ρ < ρ' → x ≤ renyiThresh α ρ') : x ≤ renyiThresh α ρ := by
  rcases eq_or_ne ρ ⊤ with rfl | hρ
  · simp [renyiThresh_top hα]
  have hlim : Tendsto (fun s : ℝ ↦ ((exp ((α - 1) * (ρ.toReal + s)) : ℝ) : EReal))
      (𝓝[>] 0) (𝓝 ((exp ((α - 1) * (ρ.toReal + 0)) : ℝ) : EReal)) :=
    ((continuous_coe_real_ereal.comp (by fun_prop)).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [renyiThresh_of_ne_top hα.le hρ, ← add_zero ρ.toReal]
  refine ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun s (hs : 0 < s) ↦ ?_)
  refine (h (ρ + .ofReal s) (lt_add_right hρ (by simpa using hs))).trans_eq ?_
  rw [renyiThresh_of_ne_top hα.le (by finiteness), toReal_add hρ ofReal_ne_top,
    toReal_ofReal hs.le]

end renyiThresh

/-! ## The Rényi divergence -/

/-- The Rényi divergence bound `D_α(μ ‖ ν) ≤ ρ`, as the moment bound
`∫ (dμ/dν)^α dν ≤ e^{(α - 1) ρ}` (Def. 2.2). -/
noncomputable def renyiDivergence (α : ℝ) : GradedDivergence.{u} ℝ≥0∞ :=
  fDivBound Unit (fun _ _ t ↦ t ^ α) fun ρ _ ↦ renyiThresh α ρ

variable {X : Type u} [MeasurableSpace X] {α : ℝ} {ρ : ℝ≥0∞} {μ ν : Measure X}

/-- Unfolds the Rényi divergence to its moment bound. -/
theorem renyiDivergence_iff : renyiDivergence α ρ μ ν ↔ fDiv (· ^ α) μ ν ≤ renyiThresh α ρ :=
  ⟨fun h ↦ h (), fun h _ ↦ h⟩

/-- At a finite budget, the Rényi divergence bound is the `α`-th moment bound. -/
theorem renyiDivergence_iff_of_ne_top (hα : 1 ≤ α) (hρ : ρ ≠ ⊤) :
    renyiDivergence α ρ μ ν ↔ fDiv (· ^ α) μ ν ≤ ((Real.exp ((α - 1) * ρ.toReal) : ℝ) : EReal) := by
  rw [renyiDivergence_iff, renyiThresh_of_ne_top hα hρ]

theorem renyiDivergence_top (hα : 1 < α) (μ ν : Measure X) : renyiDivergence α ⊤ μ ν :=
  renyiDivergence_iff.2 (renyiThresh_top hα ▸ le_top)

/-- The moment bound is the Rényi divergence bound `D_α(μ ‖ ν) ≤ ρ` (Def. 2.2). -/
theorem renyiDivergence_iff_renyiDiv_le (hα : 1 < α) :
    renyiDivergence α ρ μ ν ↔ renyiDiv α μ ν ≤ ρ := by
  have hα1 : 0 < α - 1 := sub_pos.2 hα
  rw [renyiDivergence_iff, renyiThresh, expBudget, renyiDiv,
    ← EReal.coe_toENNReal fDiv_rpow_nonneg, EReal.coe_ennreal_le_coe_ennreal_iff,
    ← ENNReal.log_le_log_iff, EReal.log_exp, EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal,
    max_eq_left hα1.le, EReal.le_coe_mul_iff hα1, EReal.toENNReal_coe]

end GradedDivergence

namespace ProbabilityTheory
open Real ENNReal

/-! ## Support: the weight `t ↦ t ^ α` -/

variable {X : Type*} [MeasurableSpace X] {α : ℝ}

theorem continuousWithinAt_rpow_zero (hα : 0 < α) :
    ContinuousWithinAt (· ^ α : ℝ → ℝ) (Ici 0) 0 :=
  (continuousAt_rpow_const 0 α (.inr hα.le)).continuousWithinAt

/-- For `α > 1`, `t ^ α` grows faster than linearly, so singular mass costs `⊤`. -/
theorem derivAtTop_rpow (hα : 1 < α) : derivAtTop (· ^ α) = ⊤ := by
  refine Tendsto.limsup_eq (EReal.tendsto_coe_atTop.comp ?_)
  refine (tendsto_rpow_atTop (sub_pos.2 hα)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht using rpow_sub_one ht.ne' α

/-- For `q > 0`, the perspective of `t ↦ t ^ α` at `(p, q)` is `q (p / q) ^ α`. -/
theorem persp_rpow_of_pos (α : ℝ) {p q : ℝ} (hq : 0 < q) :
    persp (· ^ α) p q = ((q * (p / q) ^ α : ℝ) : EReal) :=
  persp_of_ne_zero hq.ne'

/-- For `1 < α` and `p > 0`, the perspective of `t ↦ t ^ α` at `(p, 0)` is `⊤`. -/
theorem persp_rpow_zero_right (hα : 1 < α) {p : ℝ} (hp : 0 < p) : persp (· ^ α) p 0 = ⊤ := by
  rw [persp_zero_right, derivAtTop_rpow hα, EReal.coe_mul_top_of_pos hp]

theorem persp_rpow_zero_left (hα : 0 < α) {q : ℝ} (hq : 0 ≤ q) : persp (· ^ α) 0 q = 0 := by
  rcases hq.eq_or_lt with rfl | hq
  · simp
  · simp [persp_rpow_of_pos α hq, zero_rpow hα.ne']

theorem persp_rpow_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) : 0 ≤ persp (· ^ α) p q :=
  persp_nonneg (fun _ ht ↦ rpow_nonneg ht α) hp hq

theorem persp_rpow_pos (hα : 1 < α) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    0 < persp (· ^ α) x y := by
  rcases hy.eq_or_lt with rfl | hy
  · simp [persp_rpow_zero_right hα hx]
  · rw [persp_rpow_of_pos α hy]
    exact EReal.coe_pos.2 (mul_pos hy (rpow_pos_of_pos (div_pos hx hy) _))

/-- The perspective of `t ↦ t ^ α` is multiplicative; this gives the product chain rule
`fDiv_rpow_comp_le`. -/
theorem persp_rpow_mul (hα : 1 < α) {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) : persp (· ^ α) (a * c) (b * d) = persp (· ^ α) a b * persp (· ^ α) c d := by
  have hα0 : 0 < α := by linarith
  rcases ha.eq_or_lt with rfl | ha
  · simp [persp_rpow_zero_left hα0 (mul_nonneg hb hd), persp_rpow_zero_left hα0 hb]
  rcases hc.eq_or_lt with rfl | hc
  · simp [persp_rpow_zero_left hα0 (mul_nonneg hb hd), persp_rpow_zero_left hα0 hd]
  rcases hb.eq_or_lt with rfl | hb
  · rw [zero_mul, persp_rpow_zero_right hα (mul_pos ha hc), persp_rpow_zero_right hα ha,
      EReal.top_mul_of_pos (persp_rpow_pos hα hc hd)]
  rcases hd.eq_or_lt with rfl | hd
  · rw [mul_zero, persp_rpow_zero_right hα (mul_pos ha hc), persp_rpow_zero_right hα hc,
      EReal.mul_top_of_pos (persp_rpow_pos hα ha hb.le)]
  rw [persp_rpow_of_pos α (mul_pos hb hd), persp_rpow_of_pos α hb, persp_rpow_of_pos α hd,
    ← EReal.coe_mul, EReal.coe_eq_coe_iff, mul_div_mul_comm,
    mul_rpow (div_pos ha hb).le (div_pos hc hd).le]
  ring

/-- For `r > 0`, `r (p / r) ^ α = p ^ α * r ^ (1 - α)`. -/
theorem mul_div_rpow_eq_rpow_mul_rpow_sub {p r : ℝ} (hp : 0 ≤ p) (hr : 0 < r) :
    r * (p / r) ^ α = p ^ α * r ^ (1 - α) := by
  rw [Real.div_rpow hp hr.le, Real.rpow_sub hr, Real.rpow_one]
  field_simp

theorem persp_rpow_anti_right (hα : 1 < α) {p q q' : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (h : q ≤ q') :
    persp (· ^ α) p q' ≤ persp (· ^ α) p q := by
  rcases hq.eq_or_lt with rfl | hq
  · rcases hp.eq_or_lt with rfl | hp
    · rw [persp_rpow_zero_left (zero_lt_one.trans hα) h]
      exact persp_rpow_nonneg le_rfl le_rfl
    · rw [persp_rpow_zero_right hα hp]
      exact le_top
  rw [persp_rpow_of_pos α (hq.trans_le h), persp_rpow_of_pos α hq, EReal.coe_le_coe_iff,
    mul_div_rpow_eq_rpow_mul_rpow_sub hp (hq.trans_le h), mul_div_rpow_eq_rpow_mul_rpow_sub hp hq]
  exact mul_le_mul_of_nonneg_left
    (rpow_le_rpow_of_nonpos hq h (by linarith)) (rpow_nonneg hp α)

theorem persp_rpow_mono_left (hα : 1 < α) {p p' q : ℝ} (hp : 0 ≤ p) (h : p ≤ p') (hq : 0 ≤ q) :
    persp (· ^ α) p q ≤ persp (· ^ α) p' q := by
  rcases hq.eq_or_lt with rfl | hq
  · rcases hp.eq_or_lt with rfl | hp
    · rw [persp_rpow_zero_left (zero_lt_one.trans hα) le_rfl]
      exact persp_rpow_nonneg h le_rfl
    · rw [persp_rpow_zero_right hα (hp.trans_le h)]
      exact le_top
  rw [persp_rpow_of_pos α hq, persp_rpow_of_pos α hq, EReal.coe_le_coe_iff]
  gcongr

/-- For `b > 0`, `(e^{(α - 1) r} / b)^{1/α} * b = e^{(α - 1) r / α} b^{(α - 1) / α}`. -/
theorem rpow_inv_exp_div_mul_eq (hα : 1 < α) {b : ℝ} (hb : 0 < b) (r : ℝ) :
    (Real.exp ((α - 1) * r) / b) ^ α⁻¹ * b =
      Real.exp ((α - 1) / α * r) * b ^ ((α - 1) / α) := by
  have hα0 : 0 < α := zero_lt_one.trans hα
  rw [div_rpow (exp_pos _).le hb.le, ← exp_mul, div_mul_eq_mul_div, mul_div_assoc,
    show (α - 1) / α = 1 - α⁻¹ by field_simp, Real.rpow_sub hb, Real.rpow_one]
  congr 2
  field_simp

/-- A perspective bound by `e^{(α - 1) r}` is the Hölder bound
`a ≤ e^{(α - 1) r / α} b^{(α - 1) / α}`. -/
theorem persp_rpow_le_exp_iff (hα : 1 < α) {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    persp (· ^ α) a b ≤ ((Real.exp ((α - 1) * r) : ℝ) : EReal) ↔
      a ≤ Real.exp ((α - 1) / α * r) * b ^ ((α - 1) / α) := by
  have hα0 : 0 < α := zero_lt_one.trans hα
  rcases hb.eq_or_lt with rfl | hb
  · rw [zero_rpow (div_ne_zero (sub_ne_zero.2 hα.ne') hα0.ne'), mul_zero]
    rcases ha.eq_or_lt with rfl | ha
    · simp [persp_rpow_zero_left hα0 le_rfl, (exp_pos _).le]
    · simp [persp_rpow_zero_right hα ha, ha.not_ge]
  rw [persp_rpow_of_pos α hb, EReal.coe_le_coe_iff, ← le_div_iff₀' hb,
    ← le_rpow_inv_iff_of_pos (div_nonneg ha hb.le) (div_nonneg (exp_pos _).le hb.le) hα0,
    div_le_iff₀ hb, rpow_inv_exp_div_mul_eq hα hb r]

/-- The `α`-moment decreases as the right measure grows. -/
theorem fDiv_rpow_anti_right (hα : 1 < α) {μ ν ν' : Measure X} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν'] (h : ν ≤ ν') : fDiv (· ^ α) μ ν' ≤ fDiv (· ^ α) μ ν := by
  have := isFiniteMeasure_of_le ν' h
  simp only [fDiv_eq_iSup_partition (convexOn_rpow hα.le)
    (continuousWithinAt_rpow_zero (zero_lt_one.trans hα))]
  exact iSup_mono fun n ↦ iSup_mono fun k ↦ iSup_mono fun _ ↦ Finset.sum_le_sum fun i _ ↦
    persp_rpow_anti_right hα toReal_nonneg toReal_nonneg
      (toReal_mono (measure_ne_top ν' _) (le_iff'.1 h _))

/-- The `α`-moment increases as the left measure grows. -/
theorem fDiv_rpow_mono_left (hα : 1 < α) {μ μ' ν : Measure X} [IsFiniteMeasure μ']
    [IsFiniteMeasure ν] (h : μ ≤ μ') : fDiv (· ^ α) μ ν ≤ fDiv (· ^ α) μ' ν := by
  have := isFiniteMeasure_of_le μ' h
  simp only [fDiv_eq_iSup_partition (convexOn_rpow hα.le)
    (continuousWithinAt_rpow_zero (zero_lt_one.trans hα))]
  exact iSup_mono fun n ↦ iSup_mono fun k ↦ iSup_mono fun _ ↦ Finset.sum_le_sum fun i _ ↦
    persp_rpow_mono_left hα toReal_nonneg
      (toReal_mono (measure_ne_top μ' _) (le_iff'.1 h _)) toReal_nonneg

/-- The perspective of `t ↦ t ^ α` of a product with a family of nonnegative reals splits as the
product of perspectives. -/
theorem persp_rpow_mul_sum {ι : Type*} {s : Finset ι} {c d : ι → ℝ} {a b : ℝ} (hα : 1 < α)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 0 ≤ d i) :
    ∑ i ∈ s, persp (· ^ α) (a * c i) (b * d i) =
      persp (· ^ α) a b * ∑ i ∈ s, persp (· ^ α) (c i) (d i) := by
  rw [EReal.mul_finset_sum_of_nonneg _ _ fun i _ ↦ persp_rpow_nonneg (hc i) (hd i)]
  exact Finset.sum_congr rfl fun i _ ↦ persp_rpow_mul hα ha hb (hc i) (hd i)

/-- Between finite spaces the `t ↦ t ^ α` divergence of two compositions is at most that of the
inputs times the largest one of the kernels (App. C.4, by Jensen's inequality). -/
theorem fDiv_rpow_comp_le (hα : 1 < α) {M N : ℕ} (μ₁ μ₂ : Measure (ULift.{u} (Fin M)))
    [IsSubProbabilityMeasure μ₁] [IsSubProbabilityMeasure μ₂]
    (κ η : Kernel (ULift.{u} (Fin M)) (ULift.{u} (Fin N))) [IsSubMarkovKernel κ]
    [IsSubMarkovKernel η] :
    fDiv (· ^ α) (κ ∘ₘ μ₁) (η ∘ₘ μ₂) ≤ fDiv (· ^ α) μ₁ μ₂ * ⨆ j, fDiv (· ^ α) (κ j) (η j) := by
  have hf := convexOn_rpow hα.le
  have hf_cont := continuousWithinAt_rpow_zero (zero_lt_one.trans hα)
  have hP {a b : ℝ≥0∞} : 0 ≤ persp (· ^ α) a.toReal b.toReal :=
    persp_rpow_nonneg toReal_nonneg toReal_nonneg
  rw [fDiv_eq_sum hf hf_cont, fDiv_eq_sum hf hf_cont]
  simp_rw [toReal_comp_singleton_eq_sum]
  calc ∑ i, persp (· ^ α) (∑ j, (μ₁ {j}).toReal * (κ j {i}).toReal)
        (∑ j, (μ₂ {j}).toReal * (η j {i}).toReal)
      ≤ ∑ i, ∑ j, persp (· ^ α) ((μ₁ {j}).toReal * (κ j {i}).toReal)
          ((μ₂ {j}).toReal * (η j {i}).toReal) :=
        Finset.sum_le_sum fun i _ ↦ persp_sum_le hf _ (fun _ _ ↦ by positivity)
          fun _ _ ↦ by positivity
    _ = ∑ j, persp (· ^ α) (μ₁ {j}).toReal (μ₂ {j}).toReal *
          ∑ i, persp (· ^ α) (κ j {i}).toReal (η j {i}).toReal := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ ↦ persp_rpow_mul_sum hα toReal_nonneg toReal_nonneg
          (fun _ ↦ toReal_nonneg) fun _ ↦ toReal_nonneg
    _ ≤ ∑ j, persp (· ^ α) (μ₁ {j}).toReal (μ₂ {j}).toReal *
          ⨆ j, fDiv (· ^ α) (κ j) (η j) := by
        refine Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left ?_ hP
        rw [← fDiv_eq_sum hf hf_cont]
        exact le_iSup (fun j ↦ fDiv (· ^ α) (κ j) (η j)) j
    _ = (∑ j, persp (· ^ α) (μ₁ {j}).toReal (μ₂ {j}).toReal) *
          ⨆ j, fDiv (· ^ α) (κ j) (η j) := by
        rw [mul_comm, EReal.mul_finset_sum_of_nonneg _ _ fun _ _ ↦ hP]
        simp_rw [mul_comm]

end ProbabilityTheory

namespace GradedDivergence
open Real ENNReal

variable {X : Type u} [MeasurableSpace X] {α : ℝ} {ρ : ℝ≥0∞} {μ ν : Measure X}

/-! ## Between point masses -/

/-- Comparing in `ℝ≥0∞` with `e^c b^γ` is comparing real parts, for finite `a`, `b` and `γ ≥ 0`. -/
theorem le_ofReal_exp_mul_rpow_iff {a b : ℝ≥0∞} {γ c : ℝ} (hγ : 0 ≤ γ) (ha : a ≠ ⊤)
    (hb : b ≠ ⊤) :
    a ≤ ENNReal.ofReal (exp c) * b ^ γ ↔ a.toReal ≤ exp c * b.toReal ^ γ := by
  have hb' : b ^ γ = ENNReal.ofReal (b.toReal ^ γ) := by
    rw [← ofReal_rpow_of_nonneg toReal_nonneg hγ, ofReal_toReal hb]
  rw [hb', ← ofReal_mul (exp_pos _).le, le_ofReal_iff_toReal_le ha (by positivity)]

/-- Between scaled point masses, a finite Rényi budget is the Hölder bound
`a ≤ e^{(α - 1) ρ / α} b^{(α - 1) / α}`. -/
theorem renyiDivergence_smul_dirac_iff (hα : 1 < α) (hρ : ρ ≠ ⊤) {a b : ℝ≥0∞} (ha : a ≠ ⊤)
    (hb : b ≠ ⊤) :
    renyiDivergence α ρ (a • dirac PUnit.unit.{u + 1}) (b • dirac PUnit.unit) ↔
      a ≤ expBudget (ENNReal.ofReal ((α - 1) / α) * ρ) * b ^ ((α - 1) / α) := by
  have hγ : 0 ≤ (α - 1) / α := div_nonneg (by linarith) (by linarith)
  rw [renyiDivergence_iff_of_ne_top hα.le hρ, fDiv_smul_dirac (convexOn_rpow hα.le)
    (continuousWithinAt_rpow_zero (zero_lt_one.trans hα)) ha hb,
    persp_rpow_le_exp_iff hα toReal_nonneg toReal_nonneg,
    expBudget_of_ne_top (mul_ne_top ofReal_ne_top hρ), toReal_mul, toReal_ofReal hγ,
    le_ofReal_exp_mul_rpow_iff hγ ha hb]

/-! ## Classes of the Rényi divergence -/

section Instances

variable (α) [hα : Fact (1 < α)]

/-- The Rényi divergence is graded. -/
instance isGraded_renyi : (renyiDivergence.{u} α).IsGraded :=
  isGraded_fDivBound (fun _ _ ↦ convexOn_rpow hα.out.le)
    (fun _ _ ↦ continuousWithinAt_rpow_zero (zero_lt_one.trans hα.out))
    (fun _ _ _ _ _ _ ↦ le_rfl) (fun _ _ h _ ↦ renyiThresh_mono h) fun _ ↦ renyiThresh_top hα.out

/-- The Rényi divergence is reflexive. -/
instance isReflexive_renyi : (renyiDivergence.{u} α).IsReflexive :=
  isReflexive_fDivBound fun _ ↦ by simp

/-- The zero measure is within every Rényi budget of every measure. -/
instance isZeroLeft_renyi : (renyiDivergence.{u} α).IsZeroLeft :=
  isZeroLeft_fDivBound fun _ _ ↦ by
    simp [Real.zero_rpow (zero_lt_one.trans hα.out).ne', renyiThresh, EReal.coe_ennreal_nonneg]

/-- The Rényi divergence is left continuous (Rocq `GCFamLim_RDP`). -/
instance isLeftContinuous_renyi : (renyiDivergence.{u} α).IsLeftContinuous :=
  isLeftContinuous_fDivBound (fun _ _ ↦ convexOn_rpow hα.out.le)
    fun _ _ ↦ continuousWithinAt_rpow_zero (zero_lt_one.trans hα.out)

/-- The Rényi divergence is monotone in the right measure. -/
instance isRightMonotone_renyi : (renyiDivergence.{u} α).IsRightMonotone where
  right_mono _ := fun hν h ↦
    renyiDivergence_iff.2 ((fDiv_rpow_anti_right hα.out hν).trans (renyiDivergence_iff.1 h))

/-- The Rényi divergence is antitone in the left measure. -/
instance isLeftAntitone_renyi : (renyiDivergence.{u} α).IsLeftAntitone where
  left_anti _ := fun hμ h ↦
    renyiDivergence_iff.2 ((fDiv_rpow_mono_left hα.out hμ).trans (renyiDivergence_iff.1 h))

/-- Rényi budgets are closed from above. -/
instance isBudgetClosed_renyi : (renyiDivergence.{u} α).IsBudgetClosed :=
  isBudgetClosed_fDivBound (fun _ _ _ ↦ rfl) fun _ _ _ h ↦ le_renyiThresh_of_forall_lt hα.out h

/-- Moments multiply under composition, so Rényi budgets add (Thm. 4.11, by Thm. 4.6). -/
instance isComposable_renyi : (renyiDivergence.{u} α).IsComposable :=
  -- the `_of_mul` chain is stated with `max 0 _`, which is the identity on Rényi moments (they
  -- are nonnegative)
  isComposable_fDivBound_of_mul (fun _ _ ↦ convexOn_rpow hα.out.le)
    (fun _ _ ↦ continuousWithinAt_rpow_zero (zero_lt_one.trans hα.out))
    (fun _ _ _ ↦ by
      intros
      rw [max_eq_right fDiv_rpow_nonneg,
        max_eq_right (le_iSup_of_le (⟨0⟩ : ULift (Fin _)) fDiv_rpow_nonneg)]
      exact fDiv_rpow_comp_le hα.out _ _ _ _)
    (fun _ _ _ ↦ by
      rw [renyiThresh_add, max_eq_right renyiThresh_nonneg, max_eq_right renyiThresh_nonneg])
    fun _ _ ↦ renyiThresh_nonneg

end Instances

/-! ## The Rényi codensity lifting -/

/-- Below `⊤` no Rényi budget relates a point mass to the zero measure, so none is absorbing. -/
theorem not_absorbing_codensity_renyi (hα : 1 < α) (hρ : ρ < ⊤) :
    ¬(codensity (renyiDivergence.{u} α)).Absorbing ρ := by
  have : Fact (1 < α) := ⟨hα⟩
  refine not_absorbing_of_refutes fun h ↦ ?_
  have := renyiDivergence_iff.1 <| h (by rwa [add_zero])
    (k := Kernel.id) (l := 0) fun _ _ ↦ by simpa using IsGraded.top _ _
  simp [fDiv_zero_right_eq, derivAtTop_rpow hα, renyiThresh_of_ne_top hα.le hρ.ne] at this

/-- A finite Rényi budget relates two measures along equality only if the first is absolutely
continuous in the second (Rocq `RDPcoupl_eq_absolute_continuity`). -/
theorem absolutelyContinuous_of_codensity_renyi_rel_eq (hα : 1 < α) (hρ : ρ ≠ ⊤)
    [IsFiniteMeasure μ] (h : (codensity (renyiDivergence.{u} α)).Rel ρ (· = ·) μ ν) : μ ≪ ν := by
  have : Fact (1 < α) := ⟨hα⟩
  classical
  -- test the lifting with the indicator of a `ν`-null set `t`: the point-mass Hölder bound then
  -- forces `μ t ≤ e^… · 0 ^ ((α - 1) / α) = 0`
  intro s hs
  set t := toMeasurable ν s
  have ht : MeasurableSet t := measurableSet_toMeasurable ν s
  have hνt : ν t = 0 := by rwa [measure_toMeasurable]
  refine measure_mono_null (subset_toMeasurable ν s) ?_
  have hF : Measurable (t.indicator (1 : X → ℝ≥0∞)) := measurable_one.indicator ht
  have := Kernel.isSubMarkovKernel_mass.{u} hF fun x ↦ indicator_le_self' (by simp) x
  have key := h (c := 0) (by simpa using hρ.lt_top)
    (k := Kernel.mass hF) (l := Kernel.mass hF) fun x y ↦ by
      by_cases hxy : x = y
      · subst hxy
        simpa [relCost_of] using IsReflexive.refl (Kernel.mass hF x)
      · simpa [relCost_of_not hxy] using renyiDivergence_top hα _ _
  rw [Kernel.mass_comp, Kernel.mass_comp, add_zero, lintegral_indicator_one ht,
    lintegral_indicator_one ht, hνt,
    renyiDivergence_smul_dirac_iff hα hρ (measure_ne_top μ t) zero_ne_top,
    zero_rpow_of_pos (div_pos (sub_pos.2 hα) (zero_lt_one.trans hα)), mul_zero] at key
  exact nonpos_iff_eq_zero.1 key

end GradedDivergence
