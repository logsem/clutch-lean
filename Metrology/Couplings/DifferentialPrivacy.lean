module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Kernel.Defs
public import Metrology.Couplings.ApproximateSpanLifting

/-! Differential privacy, its relaxations, and `f`-divergences (Approximate Span Liftings, §2). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

theorem EReal.coe_finset_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    ((∑ i ∈ s, x i : ℝ) : EReal) = ∑ i ∈ s, (x i : EReal) :=
  map_sum (⟨⟨(↑), EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) x s

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A randomized algorithm: a kernel from inputs to distributions on outputs. -/
abbrev Mechanism (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] := Kernel X Y

/-- An adjacency relation on inputs. -/
abbrev Adjacency (X : Type*) := X → X → Prop

/-! ### `f`-divergences -/

/-- The weight function of an `f`-divergence (Def. 2.6). -/
abbrev WeightFunction := ℝ → ℝ

namespace WeightFunction

/-- The slope `lim f t / t` of a weight function at infinity. -/
noncomputable def slopeAtTop (f : WeightFunction) : EReal :=
  limsup (fun t : ℝ ↦ ((f t / t : ℝ) : EReal)) atTop

/-- The perspective `b f (a / b)`, extended by `0 f (0 / 0) = 0` and `0 f (a / 0) = a f'(∞)`. -/
noncomputable def persp (f : WeightFunction) (a b : ℝ) : EReal :=
  if b = 0 then (if a = 0 then 0 else a * f.slopeAtTop) else ((b * f (a / b) : ℝ) : EReal)

/-- The weight `t ↦ max 0 (t - e^ε)` of `(ε, δ)`-differential privacy. -/
noncomputable def dp (ε : ℝ) : WeightFunction := fun t ↦ max 0 (t - Real.exp ε)

/-- The weight `t ↦ t ^ α` of the Rényi divergence of order `α`. -/
noncomputable def rpow (α : ℝ) : WeightFunction := fun t ↦ t ^ α

theorem slopeAtTop_dp (ε : ℝ) : (dp ε).slopeAtTop = 1 := by
  refine Tendsto.limsup_eq (EReal.tendsto_coe.2 ?_)
  have h : Tendsto (fun t : ℝ ↦ 1 - Real.exp ε / t) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := Real.exp ε)).div_atTop tendsto_id)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (Real.exp ε)] with t ht
  have ht0 : 0 < t := (Real.exp_pos ε).trans ht
  rw [dp, max_eq_right (by linarith)]
  field_simp

theorem persp_dp (ε : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (dp ε).persp a b = ((max 0 (a - Real.exp ε * b) : ℝ) : EReal) := by
  rcases hb.eq_or_lt with rfl | hb
  · by_cases ha0 : a = 0
    · simp [persp, ha0]
    · simp [persp, ha0, slopeAtTop_dp, max_eq_right ha]
  · simp only [persp, hb.ne', ↓reduceIte, dp]
    rw [mul_max_of_nonneg _ _ hb.le, mul_zero, mul_sub, mul_div_cancel₀ _ hb.ne', mul_comm]

end WeightFunction

/-- The `f`-divergence, as a supremum over finite measurable partitions (Def. 2.7, Thm. 4.7). -/
noncomputable def fDiv (f : WeightFunction) (μ ν : Measure X) : EReal :=
  ⨆ (n : ℕ) (k : X → Fin n) (_ : Measurable k),
    ∑ i, f.persp (μ (k ⁻¹' {i})).toReal (ν (k ⁻¹' {i})).toReal

/-- A family of `f`-divergences, graded by the index of the weight (§4.2). -/
noncomputable def fDivFamily {ι : Type*} (F : ι → WeightFunction) : GradedDivergence.{u} ι :=
  fun α {_} _ μ ν ↦ fDiv (F α) μ ν

/-- An `f`-divergence as a singly graded divergence. -/
noncomputable abbrev fDivergence (f : WeightFunction) : GradedDivergence.{u} Unit :=
  fDivFamily fun _ ↦ f

/-- Pushing forward along a measurable map does not increase an `f`-divergence. -/
instance fDivFamily.isFunctorial {ι : Type*} (F : ι → WeightFunction) :
    (fDivFamily F : GradedDivergence.{u} ι).IsFunctorial where
  map_le _ X Y _ _ k μ ν _ _ hk := by
    refine iSup_le fun n ↦ iSup_le fun k' ↦ iSup_le fun hk' ↦ ?_
    refine le_iSup_of_le n <| le_iSup_of_le (k' ∘ k) <| le_iSup_of_le (hk'.comp hk) ?_
    simp only [Measure.map_apply hk (hk' (measurableSet_singleton _)), preimage_comp, le_refl]

/-- The DP `f`-divergence is the largest gap `μ S - e^ε ν S` over measurable events. -/
theorem fDiv_dp_eq_iSup (ε : ℝ) (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv (.dp ε) μ ν = ⨆ (S : Set X) (_ : MeasurableSet S),
      (((μ S).toReal - Real.exp ε * (ν S).toReal : ℝ) : EReal) := by
  apply le_antisymm
  · refine iSup_le fun n ↦ iSup_le fun k ↦ iSup_le fun hk ↦ ?_
    set x : Fin n → ℝ := fun i ↦ (μ (k ⁻¹' {i})).toReal - Real.exp ε * (ν (k ⁻¹' {i})).toReal
    set P := Finset.univ.filter fun i ↦ 0 ≤ x i
    have hP : MeasurableSet (k ⁻¹' (P : Set (Fin n))) := hk (.of_discrete)
    refine le_iSup₂_of_le _ hP (le_of_eq ?_)
    have hsum (ρ : Measure X) [IsFiniteMeasure ρ] :
        ∑ i ∈ P, (ρ (k ⁻¹' {i})).toReal = (ρ (k ⁻¹' P)).toReal := by
      rw [← ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _),
        sum_measure_preimage_singleton _ fun _ _ ↦ hk (measurableSet_singleton _)]
    simp_rw [WeightFunction.persp_dp ε ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ← EReal.coe_finset_sum, ← hsum μ, ← hsum ν, Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun i _ ↦ by split_ifs with h <;> simp [x, h, le_of_not_ge]
  · refine iSup₂_le fun S hS ↦ ?_
    classical
    let k : X → Fin 2 := fun x ↦ if x ∈ S then 0 else 1
    have hk : Measurable k := measurable_const.ite hS measurable_const
    have h0 : k ⁻¹' {0} = S := by ext x; by_cases hx : x ∈ S <;> simp [k, hx]
    refine le_iSup_of_le 2 <| le_iSup_of_le k <| le_iSup_of_le hk ?_
    simp only [Fin.sum_univ_two, h0,
      WeightFunction.persp_dp ε ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    exact (le_max_right _ _).trans (le_add_of_nonneg_right (le_max_left _ _))

/-- A DP `f`-divergence bound is the DP inequality on events. -/
theorem fDiv_dp_le_iff (ε : ℝ) (δ : ℝ≥0∞) (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    fDiv (.dp ε) μ ν ≤ δ ↔
      ∀ S, MeasurableSet S → μ S ≤ ENNReal.ofReal (Real.exp ε) * ν S + δ := by
  rw [fDiv_dp_eq_iSup, iSup₂_le_iff]
  refine forall₂_congr fun S _ ↦ ?_
  rcases eq_or_ne δ ⊤ with rfl | hδ
  · simp
  rw [← EReal.coe_ennreal_toReal hδ, EReal.coe_le_coe_iff,
    ← ENNReal.toReal_le_toReal (measure_ne_top _ _) (by finiteness),
    ENNReal.toReal_add (by finiteness) hδ, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos ε).le]
  constructor <;> intro h <;> linarith

/-- The Rényi divergence of order `α` (Def. 2.2). -/
noncomputable def renyiDiv (α : ℝ) (μ ν : Measure X) : EReal :=
  ((α - 1)⁻¹ : ℝ) * ENNReal.log (fDiv (.rpow α) μ ν).toENNReal

/-! ### Differential privacy and its relaxations -/

section Privacy

variable (m : Mechanism X Y) (Φ : Adjacency X)

/-- `(ε, δ)`-differential privacy (Def. 2.1). -/
def DP (ε : ℝ) (δ : ℝ≥0∞) : Prop :=
  ∀ ⦃x x'⦄, Φ x x' → ∀ S, MeasurableSet S → m x S ≤ ENNReal.ofReal (Real.exp ε) * m x' S + δ

/-- `(α, ρ)`-Rényi differential privacy (Def. 2.3). -/
def RDP (α ρ : ℝ) : Prop :=
  ∀ ⦃x x'⦄, Φ x x' → renyiDiv α (m x) (m x') ≤ ρ

/-- `(ξ, ρ)`-zero-concentrated differential privacy (Def. 2.4). -/
def zCDP (ξ ρ : ℝ) : Prop :=
  ∀ ⦃x x'⦄, Φ x x' → ∀ α, 1 < α → renyiDiv α (m x) (m x') ≤ ((ξ + α * ρ : ℝ) : EReal)

/-- `(ρ, ω)`-truncated concentrated differential privacy (Def. 2.5). -/
def tCDP (ρ ω : ℝ) : Prop :=
  ∀ ⦃x x'⦄, Φ x x' → ∀ α, 1 < α → α < ω → renyiDiv α (m x) (m x') ≤ ((α * ρ : ℝ) : EReal)

/-- Differential privacy bounds the DP `f`-divergence between adjacent outputs (§2.2). -/
theorem DP_iff_fDiv_dp [IsFiniteKernel m] {ε : ℝ} {δ : ℝ≥0∞} :
    DP m Φ ε δ ↔ ∀ ⦃x x'⦄, Φ x x' → fDiv (.dp ε) (m x) (m x') ≤ δ :=
  forall₃_congr fun _ _ _ ↦ (fDiv_dp_le_iff ε δ _ _).symm

end Privacy

/-! ### Two-witness relational liftings -/

open Span in
/-- The two-witness relational lifting of `R` for an `f`-divergence (Eq. 5), as an approximate
span lifting. -/
def TWRL (R : X → Y → Prop) (f : WeightFunction) (δ : EReal) (μ : Measure X) (ν : Measure Y) :
    Prop :=
  ((Span.ofRel {p | R p.1 p.2})♯[fDivergence f, (), δ]).Rel μ ν

open Span in
/-- Lifting equality relates exactly the pairs at `f`-divergence at most `δ` (§2.2). -/
theorem TWRL_eq_iff (f : WeightFunction) (δ : EReal) {μ ν : Measure X}
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    TWRL (· = ·) f δ μ ν ↔ fDiv f μ ν ≤ δ := by
  unfold TWRL
  constructor
  · intro h
    have := (Hom.lift Hom.eqToDiag () δ).rel h
    simp only [Hom.lift, Hom.eqToDiag, Measure.map_id] at this
    exact (rel_lift_diag.1 this).le
  · intro h
    have := (Hom.lift Hom.diagToEq () δ).rel
      ((rel_lift_diag (Δ := fDivergence f) (μ := μ) (ν := ν)).2 ⟨inferInstance, inferInstance, h⟩)
    simpa only [Hom.lift, Hom.diagToEq, Measure.map_id] using this
