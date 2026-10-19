module

public import Metrology.Couplings.Divergences.FDivBound

/-! Barthe–Olmedo divergences on sub-probability measures, without filling (Barthe–Olmedo,
ICALP 2013). -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory Set Filter Topology
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
