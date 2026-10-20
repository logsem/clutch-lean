module

public import Metrology.Couplings.Divergences.Dp
public import Metrology.Couplings.Divergences.FDivFinite

/-! # The `fDivBound` constructor
Graded divergences cut out by thresholds on `f`-divergences (Approximate Span Liftings, §4.2):
graded, reflexive and composable (Thm. 4.9) criteria; `dp_iff_fDivBound` shows DP is one. -/

@[expose] public section

universe u v w

open MeasureTheory Measure ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace GradedDivergence

variable {B : Type v} {K : Type w} {weight : B → K → ℝ → ℝ} {thresh : B → K → EReal}

/-! ## The constructor -/

/-- One constructor for the concrete divergences: a threshold on each indexed `f`-divergence. -/
def fDivBound (K : Type w) (weight : B → K → ℝ → ℝ) (thresh : B → K → EReal) :
    GradedDivergence.{u} B :=
  fun b _ _ μ ν ↦ ∀ k, fDiv (weight b k) μ ν ≤ thresh b k

theorem fDivBound_def {b : B} {X : Type u} [MeasurableSpace X] {μ ν : Measure X} :
    fDivBound K weight thresh b μ ν ↔ ∀ k, fDiv (weight b k) μ ν ≤ thresh b k :=
  Iff.rfl

/-! ## Structural properties -/

/-- Weights that shrink and thresholds that grow with the budget give a graded divergence. -/
theorem isGraded_fDivBound [LE B] [Top B] (hw : ∀ b k, ConvexOn ℝ (Ici 0) (weight b k))
    (hw_cont : ∀ b k, ContinuousWithinAt (weight b k) (Ici 0) 0)
    (hanti : ∀ ⦃b b'⦄, b ≤ b' → ∀ k t, 0 ≤ t → weight b' k t ≤ weight b k t)
    (hmono : ∀ ⦃b b'⦄, b ≤ b' → ∀ k, thresh b k ≤ thresh b' k) (htop : ∀ k, thresh ⊤ k = ⊤) :
    (fDivBound.{u} K weight thresh).IsGraded where
  mono b b' hb _ _ μ ν _ _ h k := calc
    fDiv (weight b' k) μ ν ≤ fDiv (weight b k) μ ν :=
      fDiv_mono (hw b' k) (hw_cont b' k) (hanti hb k)
    _ ≤ thresh b k := h k
    _ ≤ thresh b' k := hmono hb k
  top _ _ _ _ k := htop k ▸ le_top

/-- Self-divergences are the mass times `weight 0 k 1`: a threshold above its positive part gives
reflexivity. -/
theorem isReflexive_fDivBound [Zero B]
    (h : ∀ k, ((max 0 (weight 0 k 1) : ℝ) : EReal) ≤ thresh 0 k) :
    (fDivBound.{u} K weight thresh).IsReflexive where
  refl μ _ k := (fDiv_self_le μ).trans (h k)

/-- Divergences from zero are the mass times `weight b k 0`: a threshold above its positive part
makes the zero measure meet every budget. -/
theorem isZeroLeft_fDivBound (h : ∀ b k, ((max 0 (weight b k 0) : ℝ) : EReal) ≤ thresh b k) :
    (fDivBound.{u} K weight thresh).IsZeroLeft where
  zero_left b _ _ ν _ k := (fDiv_zero_left_le ν).trans (h b k)

/-- Convex weights continuous at zero make the bound left continuous. -/
theorem isLeftContinuous_fDivBound (hw : ∀ b k, ConvexOn ℝ (Ici 0) (weight b k))
    (hw_cont : ∀ b k, ContinuousWithinAt (weight b k) (Ici 0) 0) :
    (fDivBound.{u} K weight thresh).IsLeftContinuous where
  iSup_left b X _ μ _ hμ ν _ h k := by
    have : IsFiniteMeasure (⨆ n, μ n) := by
      refine ⟨?_⟩
      rw [iSup_apply_of_monotone hμ MeasurableSet.univ]
      exact (iSup_le fun n ↦ IsSubProbabilityMeasure.measure_univ_le_one).trans_lt
        ENNReal.one_lt_top
    exact (fDiv_iSup_left_le (hw b k) (hw_cont b k) hμ).trans (iSup_le fun n ↦ h n k)

/-- With weights fixed across budgets, thresholds closed from above give closed budgets. -/
theorem isBudgetClosed_fDivBound [LT B] (hw : ∀ b b' k, weight b k = weight b' k)
    (hthresh : ∀ b k (x : EReal), (∀ b', b < b' → x ≤ thresh b' k) → x ≤ thresh b k) :
    (fDivBound.{u} K weight thresh).IsBudgetClosed where
  of_forall_gt h k := hthresh _ k _ fun b' hb ↦ hw _ b' k ▸ h b' hb k

/-! ## Composability -/

/-- Composability from a per-index chain rule on nonempty inputs (Thm. 4.9); `hpos` handles an
empty input space, where both composites are zero. -/
theorem isComposable_fDivBound [Add B] {chain : EReal → EReal → EReal}
    (hchain : ∀ ⦃a a' c c'⦄, a ≤ a' → c ≤ c' → chain a c ≤ chain a' c')
    (hweight : ∀ b c k {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] [Nonempty X]
      {μ₁ μ₂ : Measure X} [IsSubProbabilityMeasure μ₁] [IsSubProbabilityMeasure μ₂]
      {κ η : Kernel X Y} [IsSubMarkovKernel κ] [IsSubMarkovKernel η],
      fDiv (weight (b + c) k) (κ ∘ₘ μ₁) (η ∘ₘ μ₂) ≤
        chain (fDiv (weight b k) μ₁ μ₂) (⨆ x, fDiv (weight c k) (κ x) (η x)))
    (hthresh : ∀ b c k, chain (thresh b k) (thresh c k) ≤ thresh (b + c) k)
    (hpos : ∀ b k, 0 ≤ thresh b k) :
    (fDivBound.{u} K weight thresh).IsComposable where
  comp b c X Y _ _ μ₁ μ₂ _ _ κ η _ _ hμ hκ k := by
    cases isEmpty_or_nonempty X
    · rw [μ₁.eq_zero_of_isEmpty, μ₂.eq_zero_of_isEmpty, bind_zero_left, fDiv_zero_left_eq]
      simpa using hpos (b + c) k
    calc fDiv (weight (b + c) k) (κ ∘ₘ μ₁) (η ∘ₘ μ₂)
        ≤ chain (fDiv (weight b k) μ₁ μ₂) (⨆ x, fDiv (weight c k) (κ x) (η x)) := hweight b c k
      _ ≤ chain (thresh b k) (thresh c k) := hchain (hμ k) (iSup_le fun x ↦ hκ x k)
      _ ≤ thresh (b + c) k := hthresh b c k

/-- Composability from a globally monotone per-index chain rule between finite spaces
(Thms. 4.6, 4.9); multiplicative chains use `isComposable_fDivBound_of_mul`. -/
theorem isComposable_fDivBound_of_finite [Add B] (hw : ∀ b k, ConvexOn ℝ (Ici 0) (weight b k))
    (hw_cont : ∀ b k, ContinuousWithinAt (weight b k) (Ici 0) 0) {chain : EReal → EReal → EReal}
    (hchain : ∀ ⦃a a' c c'⦄, a ≤ a' → c ≤ c' → chain a c ≤ chain a' c')
    (hfin : ∀ b c k {M N : ℕ} [NeZero M] {μ₁ μ₂ : Measure (ULift.{u} (Fin M))}
      [IsSubProbabilityMeasure μ₁] [IsSubProbabilityMeasure μ₂]
      {κ η : Kernel (ULift.{u} (Fin M)) (ULift.{u} (Fin N))} [IsSubMarkovKernel κ]
      [IsSubMarkovKernel η],
      fDiv (weight (b + c) k) (κ ∘ₘ μ₁) (η ∘ₘ μ₂) ≤
        chain (fDiv (weight b k) μ₁ μ₂) (⨆ i, fDiv (weight c k) (κ i) (η i)))
    (hthresh : ∀ b c k, chain (thresh b k) (thresh c k) ≤ thresh (b + c) k)
    (hpos : ∀ b k, 0 ≤ thresh b k) :
    (fDivBound.{u} K weight thresh).IsComposable :=
  isComposable_fDivBound hchain (fun b c k ↦
    fDiv_comp_le_of_finite (hw _ k) (hw_cont _ k) (hw b k) (hw_cont b k) (hw c k) (hw_cont c k)
      hchain (hfin b c k) _ _) hthresh hpos

/-- Nonnegative weights whose perspectives split (condition (A')) compose additively
(Sato–Katsumata, Prop. 1). -/
theorem isComposable_fDivBound_of_perspSplit [Add B]
    (hw : ∀ b k, ConvexOn ℝ (Ici 0) (weight b k))
    (hw_cont : ∀ b k, ContinuousWithinAt (weight b k) (Ici 0) 0)
    (hw₀ : ∀ b k t, 0 ≤ t → 0 ≤ weight b k t) {β β' : ℝ} (hβ : β ∈ Icc (0 : ℝ) 1)
    (hβ' : β' ∈ Icc (0 : ℝ) 1)
    (hA : ∀ b c k, PerspSplit (weight (b + c) k) (weight b k) (weight c k) β β')
    (hthresh : ∀ b c k, thresh b k + thresh c k ≤ thresh (b + c) k)
    (hpos : ∀ b k, 0 ≤ thresh b k) :
    (fDivBound.{u} K weight thresh).IsComposable :=
  isComposable_fDivBound_of_finite hw hw_cont (fun _ _ _ _ ↦ add_le_add)
    (fun b c k ↦ fDiv_comp_le_of_perspSplit (hw _ k) (hw_cont _ k) (hw b k) (hw_cont b k)
      (hw c k) (hw_cont c k) (hw₀ _ k) (hw₀ b k) (hw₀ c k) hβ hβ' (hA b c k) ..) hthresh hpos

/-- Multiplicative chain rules (Rényi shape) go through the clamped chain `max 0 a * max 0 c`,
which is globally monotone. -/
theorem isComposable_fDivBound_of_mul [Add B] (hw : ∀ b k, ConvexOn ℝ (Ici 0) (weight b k))
    (hw_cont : ∀ b k, ContinuousWithinAt (weight b k) (Ici 0) 0)
    (hfin : ∀ b c k {M N : ℕ} [NeZero M] {μ₁ μ₂ : Measure (ULift.{u} (Fin M))}
      [IsSubProbabilityMeasure μ₁] [IsSubProbabilityMeasure μ₂]
      {κ η : Kernel (ULift.{u} (Fin M)) (ULift.{u} (Fin N))} [IsSubMarkovKernel κ]
      [IsSubMarkovKernel η],
      fDiv (weight (b + c) k) (κ ∘ₘ μ₁) (η ∘ₘ μ₂) ≤
        max 0 (fDiv (weight b k) μ₁ μ₂) * max 0 (⨆ i, fDiv (weight c k) (κ i) (η i)))
    (hthresh : ∀ b c k, max 0 (thresh b k) * max 0 (thresh c k) ≤ thresh (b + c) k)
    (hpos : ∀ b k, 0 ≤ thresh b k) :
    (fDivBound.{u} K weight thresh).IsComposable :=
  isComposable_fDivBound_of_finite hw hw_cont
    (fun _ _ _ _ ha hc ↦ mul_le_mul (max_le_max le_rfl ha) (max_le_max le_rfl hc)
      (le_max_left _ _) ((le_max_left _ _).trans (max_le_max le_rfl ha)))
    hfin hthresh hpos

end GradedDivergence

namespace ProbabilityTheory
open Real ENNReal

/-! ## DP as an f-divergence bound -/

/-- The hockey-stick weight `t ↦ max 0 (t - e^ε)` of `(ε, δ)`-differential privacy (Def. 2.6). -/
noncomputable def dpWeight (ε t : ℝ) : ℝ := max 0 (t - Real.exp ε)

/-- The hockey-stick weight is convex on `[0, ∞)`. -/
theorem convexOn_dpWeight (ε : ℝ) : ConvexOn ℝ (Ici 0) (dpWeight ε) :=
  (convexOn_const 0 (convex_Ici 0)).sup
    ((convexOn_id (convex_Ici 0)).sub (concaveOn_const (exp ε) (convex_Ici 0)))

/-- The hockey-stick weight is continuous. -/
theorem continuous_dpWeight (ε : ℝ) : Continuous (dpWeight ε) :=
  continuous_const.max (continuous_id.sub continuous_const)

/-- The slope at infinity of the hockey-stick weight is `1`. -/
theorem derivAtTop_dpWeight (ε : ℝ) : derivAtTop (dpWeight ε) = 1 := by
  refine Tendsto.limsup_eq (EReal.tendsto_coe.2 ?_)
  have h : Tendsto (fun t : ℝ ↦ 1 - exp ε / t) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub ((tendsto_const_nhds (x := exp ε)).div_atTop tendsto_id)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (exp ε)] with t ht
  have ht0 : 0 < t := (exp_pos ε).trans ht
  rw [dpWeight, max_eq_right (by linarith)]
  field_simp

/-- The perspective of the hockey-stick weight is `max 0 (a - exp ε * b)`. -/
theorem persp_dpWeight (ε : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    persp (dpWeight ε) a b = ((max 0 (a - Real.exp ε * b) : ℝ) : EReal) := by
  rcases hb.eq_or_lt with rfl | hb
  · simp [derivAtTop_dpWeight, max_eq_right ha]
  rw [persp_of_ne_zero hb.ne', dpWeight, mul_max_of_nonneg _ _ hb.le, mul_zero, mul_sub,
    mul_div_cancel₀ _ hb.ne', mul_comm]

variable {X : Type u} [MeasurableSpace X] {μ ν : Measure X}

/-- Summing masses of cells in a finite set `P` gives the mass of their union. -/
theorem sum_toReal_preimage_singleton {n : ℕ} (ρ : Measure X)
    [IsFiniteMeasure ρ] {k : X → Fin n} (hk : Measurable k) (P : Finset (Fin n)) :
    ∑ i ∈ P, (ρ (k ⁻¹' {i})).toReal = (ρ (k ⁻¹' P)).toReal := by
  rw [← toReal_sum (fun _ _ ↦ measure_ne_top _ _),
    sum_measure_preimage_singleton _ fun _ _ ↦ hk (measurableSet_singleton _)]

/-- Every finite measurable partition gives a value at most the largest gap over events. -/
theorem sum_persp_dpWeight_le_iSup
    (ε : ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {n : ℕ} {k : X → Fin n} (hk : Measurable k) :
    ∑ i, persp (dpWeight ε) (μ (k ⁻¹' {i})).toReal (ν (k ⁻¹' {i})).toReal ≤
      ⨆ (S : Set X) (_ : MeasurableSet S),
        (((μ S).toReal - exp ε * (ν S).toReal : ℝ) : EReal) := by
  set x : Fin n → ℝ := fun i ↦ (μ (k ⁻¹' {i})).toReal - exp ε * (ν (k ⁻¹' {i})).toReal
  set P := Finset.univ.filter fun i ↦ 0 ≤ x i
  refine le_iSup₂_of_le _ (hk .of_discrete : MeasurableSet (k ⁻¹' (P : Set (Fin n))))
    (le_of_eq ?_)
  simp_rw [persp_dpWeight ε toReal_nonneg toReal_nonneg, ← EReal.coe_finset_sum,
    ← sum_toReal_preimage_singleton μ hk, ← sum_toReal_preimage_singleton ν hk, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun i _ ↦ by split_ifs with h <;> simp [x, h, le_of_not_ge]

/-- The gap on an event is at most the supremum over finite measurable partitions. -/
theorem coe_gap_le_iSup_partition
    (ε : ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {S : Set X} (hS : MeasurableSet S) :
    (((μ S).toReal - exp ε * (ν S).toReal : ℝ) : EReal) ≤
      ⨆ (n : ℕ) (k : X → Fin n) (_ : Measurable k),
        ∑ i, persp (dpWeight ε) (μ (k ⁻¹' {i})).toReal (ν (k ⁻¹' {i})).toReal := by
  classical
  let k : X → Fin 2 := fun x ↦ if x ∈ S then 0 else 1
  refine le_iSup_of_le 2 <| le_iSup_of_le k <|
    le_iSup_of_le (measurable_const.ite hS measurable_const) ?_
  simp only [Fin.sum_univ_two, (by ext; simp [k] : k ⁻¹' {0} = S),
    persp_dpWeight ε toReal_nonneg toReal_nonneg]
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  exact (le_max_right _ _).trans (le_add_of_nonneg_right (le_max_left _ _))

/-- The DP `f`-divergence is the largest gap `μ S - e^ε ν S` over measurable events. -/
theorem fDiv_dpWeight_eq_iSup (ε : ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv (dpWeight ε) μ ν = ⨆ (S : Set X) (_ : MeasurableSet S),
      (((μ S).toReal - Real.exp ε * (ν S).toReal : ℝ) : EReal) := by
  -- Partition formula; a partition sum is bounded by one event, and an event is a 2-cell partition.
  rw [fDiv_eq_iSup_partition (convexOn_dpWeight ε) (continuous_dpWeight ε).continuousWithinAt]
  exact le_antisymm
    (iSup_le fun _ ↦ iSup_le fun _ ↦ iSup_le fun hk ↦ sum_persp_dpWeight_le_iSup ε hk)
    (iSup₂_le fun _ hS ↦ coe_gap_le_iSup_partition ε hS)

/-- A DP `f`-divergence bound is the DP inequality on events. -/
theorem fDiv_dpWeight_le_iff (ε : ℝ) (δ : ℝ≥0∞) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv (dpWeight ε) μ ν ≤ δ ↔
      ∀ S, MeasurableSet S → μ S ≤ ENNReal.ofReal (Real.exp ε) * ν S + δ := by
  rw [fDiv_dpWeight_eq_iSup, iSup₂_le_iff]
  refine forall₂_congr fun S _ ↦ ?_
  rcases eq_or_ne δ ⊤ with rfl | hδ
  · simp
  rw [← EReal.coe_ennreal_toReal hδ, EReal.coe_le_coe_iff,
    ← toReal_le_toReal (measure_ne_top _ _) (by finiteness), toReal_add (by finiteness) hδ,
    toReal_mul, toReal_ofReal (exp_pos ε).le, sub_le_iff_le_add']

end ProbabilityTheory

namespace GradedDivergence

variable {X : Type u} [MeasurableSpace X] {μ ν : Measure X}

/-- `(ε, δ)`-DP is the `f`-divergence bound with weight `dpWeight ε` and threshold `δ`. -/
theorem dp_iff_fDivBound {ε δ : ℝ≥0∞} (hε : ε ≠ ⊤) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    dp (ε, δ) μ ν ↔
      fDivBound Unit (fun b _ ↦ dpWeight b.1.toReal) (fun b _ ↦ (b.2 : EReal)) (ε, δ) μ ν := by
  simp [dp_iff hε, fDivBound_def, fDiv_dpWeight_le_iff, expBudget_of_ne_top hε]

end GradedDivergence
