module

public import Metrology.Couplings.Divergences.FDivPartition

/-! # Finite chain rules lift to general spaces
`fDiv_comp_le_of_finite` (Thm. 4.6): a chain rule on finite spaces holds on all spaces, by
discretising inputs and outputs (also `fDiv_comp_le_of_perspSplit`). -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory Set Filter Topology
open ENNReal
open IsSubProbabilityMeasure (lintegral_add_const_le measure_le_one toReal_mem_Icc)
open Finset (card_le_univ mul_sum sum_add_distrib sum_congr sum_fiberwise sum_le_sum sum_mul
  sum_nonneg sum_singleton)
open Fintype (card_ne_zero equivFin)
open Nat (ceil_le ceil_lt_add_one le_ceil lt_succ_of_le one_le_iff_ne_zero one_le_two_pow)
open Fin (val_zero)
open PUnit (default_eq_unit unit)
open EReal (coe_ennreal_add coe_ennreal_le_coe_ennreal_iff coe_nonneg coe_toENNReal
  real_coe_toENNReal tendsto_finset_sum toENNReal_add toENNReal_le_toENNReal toENNReal_mul
  toENNReal_sum)

namespace Discretize

/-! ## Dyadic cells -/

/-- The dyadic cell of `v ∈ [0, 1]` at level `n`: `0` exactly at `0`, else `⌈v 2ⁿ⌉`. -/
noncomputable def cell (n : ℕ) (v : ℝ≥0∞) : Fin (2 ^ n + 1) :=
  if v = 0 then 0 else ⟨min ⌈v.toReal * 2 ^ n⌉₊ (2 ^ n), lt_succ_of_le (min_le_right _ _)⟩

/-- The dyadic cell is a measurable function of the value. -/
theorem measurable_cell (n : ℕ) : Measurable (cell n) := by
  have hceil : Measurable (Nat.ceil : ℝ → ℕ) := Nat.ceil_mono.measurable
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  exact measurable_of_countable (fun m : ℕ ↦
    (⟨min m (2 ^ n), lt_succ_of_le (min_le_right _ _)⟩ : Fin (2 ^ n + 1))) |>.comp
      (hceil.comp (measurable_toReal.mul_const _))

/-- The dyadic cell of a value at most `1` is `0` exactly when the value is `0`. -/
theorem cell_eq_zero_iff {n : ℕ} {v : ℝ≥0∞} (hv : v ≤ 1) : cell n v = 0 ↔ v = 0 := by
  refine ⟨fun h ↦ by_contra fun h0 ↦ ?_, fun h ↦ by simp [cell, h]⟩
  have hpos : 0 < v.toReal := toReal_pos h0 (hv.trans_lt one_lt_top).ne
  simp only [cell, h0, ↓reduceIte, Fin.ext_iff, val_zero] at h
  have : 1 ≤ ⌈v.toReal * 2 ^ n⌉₊ := one_le_iff_ne_zero.2 (by positivity)
  have : 1 ≤ 2 ^ n := one_le_two_pow
  omega

/-- Values in the same nonzero dyadic cell differ by less than `2⁻ⁿ`. -/
theorem abs_sub_lt_of_cell_eq {n : ℕ} {v w : ℝ≥0∞} (hv : v ≤ 1) (hw : w ≤ 1)
    (h : cell n v = cell n w) : |v.toReal - w.toReal| < (2 ^ n)⁻¹ := by
  rcases eq_or_ne v 0 with rfl | hv0
  · rw [(cell_eq_zero_iff hw).1 (h.symm.trans ((cell_eq_zero_iff zero_le_one).2 rfl))]
    simp
  have hw0 : w ≠ 0 := fun h0 ↦ hv0 ((cell_eq_zero_iff hv).1 (h.trans ((cell_eq_zero_iff hw).2 h0)))
  have hle (x : ℝ≥0∞) (hx : x ≤ 1) : ⌈x.toReal * 2 ^ n⌉₊ ≤ 2 ^ n := by
    refine ceil_le.2 ?_
    push_cast
    exact mul_le_of_le_one_left (by positivity) (toReal_le_of_le_ofReal zero_le_one
      (hx.trans ENNReal.ofReal_one.ge))
  simp only [cell, hv0, hw0, ↓reduceIte, Fin.ext_iff, min_eq_left (hle v hv),
    min_eq_left (hle w hw)] at h
  have hv_lt := ceil_lt_add_one (by positivity : 0 ≤ v.toReal * 2 ^ n)
  have hw_lt := ceil_lt_add_one (by positivity : 0 ≤ w.toReal * 2 ^ n)
  have hv_le := le_ceil (v.toReal * 2 ^ n)
  have hw_le := le_ceil (w.toReal * 2 ^ n)
  rw [h] at hv_lt hv_le
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have key (a b : ℝ) (hab : a * 2 ^ n - b * 2 ^ n < 1) : a - b < (2 ^ n)⁻¹ :=
    calc a - b = (a * 2 ^ n - b * 2 ^ n) * (2 ^ n)⁻¹ := by field_simp
      _ < 1 * (2 ^ n)⁻¹ := by gcongr
      _ = (2 ^ n)⁻¹ := one_mul _
  rw [abs_sub_lt_iff]
  exact ⟨key _ _ (by linarith), key _ _ (by linarith)⟩

/-- Masses in the same dyadic cell are within `2⁻ⁿ` of each other. -/
theorem le_add_of_cell_eq {n : ℕ} {v w : ℝ≥0∞} (hv : v ≤ 1) (hw : w ≤ 1)
    (h : cell n v = cell n w) : v ≤ w + ENNReal.ofReal (2 ^ n)⁻¹ := by
  have := (abs_sub_lt_iff.1 (abs_sub_lt_of_cell_eq hv hw h)).1
  rw [← ofReal_toReal (hv.trans_lt one_lt_top).ne,
    ← ofReal_toReal (hw.trans_lt one_lt_top).ne,
    ← ofReal_add toReal_nonneg (by positivity)]
  exact ofReal_le_ofReal (by linarith)

/-! ## Convergence on finite spaces -/

/-- Singleton-wise closeness of measures on a finite space gives closeness on every event. -/
private theorem measure_le_add_of_singleton {N : ℕ} {ρ ρ' : Measure (ULift.{u} (Fin N))} {c : ℝ≥0∞}
    (h : ∀ i, ρ {i} ≤ ρ' {i} + c) (T : Set (ULift.{u} (Fin N))) : ρ T ≤ ρ' T + N * c := by
  classical
  rw [← T.coe_toFinset, ← sum_measure_singleton, ← sum_measure_singleton]
  calc ∑ i ∈ T.toFinset, ρ {i} ≤ ∑ i ∈ T.toFinset, (ρ' {i} + c) := sum_le_sum fun i _ ↦ h i
    _ = ∑ i ∈ T.toFinset, ρ' {i} + T.toFinset.card * c := by simp [sum_add_distrib]
    _ ≤ ∑ i ∈ T.toFinset, ρ' {i} + N * c := by
        gcongr
        exact_mod_cast (card_le_univ _).trans_eq (by simp)

/-- Two-sided bounds that shrink to zero force convergence. -/
private theorem tendsto_of_le_add {a : ℕ → ℝ≥0∞} {b : ℝ≥0∞} (hb : b ≠ ⊤) {c : ℕ → ℝ≥0∞}
    (hc : Tendsto c atTop (𝓝 0)) (h₁ : ∀ n, a n ≤ b + c n) (h₂ : ∀ n, b ≤ a n + c n) :
    Tendsto a atTop (𝓝 b) := by
  refine (ENNReal.tendsto_nhds hb).2 fun ε hε ↦ ?_
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hc ε hε] with n hn
  exact ⟨tsub_le_iff_right.2 ((h₂ n).trans (by gcongr)), (h₁ n).trans (by gcongr)⟩

section Cells

/- `disc` sends `x` to the dyadic cells of all point masses of `κ x` and `η x`, and `rep` picks a
point with the same cells. So `K ∘ rep ∘ disc` (for `K = κ, η`) factors through a finite space, and
each point mass moves by less than `2⁻ⁿ` (`cell_fst`, `cell_snd`). Both kernels share one `disc`, so
the finite chain rule sees a single input space. -/

variable {X : Type u} {N : ℕ} (κ η : X → Measure (ULift.{u} (Fin N)))

/-- Cell vectors of level `n` over `N` points. -/
abbrev CellVec (N n : ℕ) := Fin N → Fin (2 ^ n + 1) × Fin (2 ^ n + 1)

/-- The dyadic cells of the singleton masses of `κ x` and `η x`. -/
noncomputable def cellVec (n : ℕ) (x : X) : CellVec N n :=
  fun i ↦ (cell n (κ x {⟨i⟩}), cell n (η x {⟨i⟩}))

/-- The discretization of the input space by cell vectors. -/
noncomputable def disc (n : ℕ) (x : X) : ULift.{u} (Fin (Fintype.card (CellVec N n))) :=
  ⟨equivFin _ (cellVec κ η n x)⟩

/-- The discretization of the input space is measurable. -/
theorem measurable_disc [MeasurableSpace X] (hκ : Measurable κ) (hη : Measurable η) (n : ℕ) :
    Measurable (disc κ η n) := by
  refine measurable_up.comp ((measurable_of_countable _).comp (measurable_pi_iff.2 fun i ↦ ?_))
  have hS := measurable_coe (.of_discrete : MeasurableSet {(⟨i⟩ : ULift.{u} (Fin N))})
  exact ((measurable_cell n).comp (hS.comp hκ)).prodMk ((measurable_cell n).comp (hS.comp hη))

section

variable [Nonempty X] (n : ℕ) (x : X)

open Classical in
/-- A representative point of each realized cell vector. -/
noncomputable def rep (j : ULift.{u} (Fin (Fintype.card (CellVec N n)))) : X :=
  if h : ∃ x, cellVec κ η n x = (equivFin _).symm j.down then h.choose
  else Classical.arbitrary X

/-- The representative of a cell has the same cell vector as the point. -/
theorem cellVec_rep_disc :
    cellVec κ η n (rep κ η n (disc κ η n x)) = cellVec κ η n x := by
  have h : ∃ y, cellVec κ η n y = (equivFin _).symm (disc κ η n x).down := ⟨x, by simp [disc]⟩
  simp only [rep, h, ↓reduceDIte, h.choose_spec]
  simp [disc]

/-- `rep` is measurable on the finite domain. -/
theorem measurable_rep [MeasurableSpace X] : Measurable (rep κ η n) :=
  (measurable_of_countable fun j ↦ rep κ η n ⟨j⟩).comp measurable_down

variable {κ η}

/-- The representative has the same `κ`-cells as the point. -/
theorem cell_fst (i : ULift.{u} (Fin N)) :
    cell n (κ (rep κ η n (disc κ η n x)) {i}) = cell n (κ x {i}) :=
  congrArg Prod.fst (congrFun (cellVec_rep_disc κ η n x) i.down)

/-- The representative has the same `η`-cells as the point. -/
theorem cell_snd (i : ULift.{u} (Fin N)) :
    cell n (η (rep κ η n (disc κ η n x)) {i}) = cell n (η x {i}) :=
  congrArg Prod.snd (congrFun (cellVec_rep_disc κ η n x) i.down)

end

/-- Binding with kernels that are pointwise close on events gives close measures. -/
theorem bind_le_add [MeasurableSpace X] {μ : Measure X} [IsSubProbabilityMeasure μ]
    {F F' : X → Measure (ULift.{u} (Fin N))}
    (hF : Measurable F) (hF' : Measurable F') {C : ℝ≥0∞} (h : ∀ x T, F x T ≤ F' x T + C)
    (T : Set (ULift.{u} (Fin N))) : (μ.bind F) T ≤ (μ.bind F') T + C := by
  have hT : MeasurableSet T := .of_discrete
  rw [bind_apply hT hF.aemeasurable, bind_apply hT hF'.aemeasurable]
  calc ∫⁻ x, F x T ∂μ ≤ ∫⁻ x, F' x T + C ∂μ := lintegral_mono fun x ↦ h x T
    _ ≤ ∫⁻ x, F' x T ∂μ + C := lintegral_add_const_le _ _

end Cells

variable {X : Type u} [MeasurableSpace X] {N : ℕ} {κ η : X → Measure (ULift.{u} (Fin N))}
  [Nonempty X]

/-- Discretizing a kernel changes the masses of events by at most `N 2⁻ⁿ`, which vanishes. -/
theorem tendsto_bind_disc {K : X → Measure (ULift.{u} (Fin N))} [∀ x, IsSubProbabilityMeasure (K x)]
    (hκ : Measurable κ) (hη : Measurable η) (hK : Measurable K) {μ : Measure X}
    [IsSubProbabilityMeasure μ]
    (hcell : ∀ n x i, cell n (K (rep κ η n (disc κ η n x)) {i}) = cell n (K x {i}))
    (T : Set (ULift.{u} (Fin N))) :
    Tendsto (fun n ↦ (μ.bind (K ∘ rep κ η n ∘ disc κ η n)) T) atTop (𝓝 ((μ.bind K) T)) := by
  set c : ℕ → ℝ≥0∞ := fun n ↦ N * ENNReal.ofReal (2 ^ n)⁻¹
  have hc : Tendsto c atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_ofReal (tendsto_inv_atTop_zero.comp
        (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))
    simpa [c] using Tendsto.const_mul this (Or.inr (natCast_ne_top N))
  have hKn (n : ℕ) : Measurable (K ∘ rep κ η n ∘ disc κ η n) :=
    hK.comp ((measurable_rep κ η n).comp (measurable_disc κ η hκ hη n))
  have := isSubProbabilityMeasure_bind μ K
  have hpt₁ (n : ℕ) (x : X) (i : ULift.{u} (Fin N)) :=
    le_add_of_cell_eq (measure_le_one {i}) (measure_le_one {i}) (hcell n x i)
  have hpt₂ (n : ℕ) (x : X) (i : ULift.{u} (Fin N)) :=
    le_add_of_cell_eq (measure_le_one {i}) (measure_le_one {i}) (hcell n x i).symm
  exact tendsto_of_le_add (measure_ne_top _ _) hc
    (fun n ↦ bind_le_add (hKn n) hK (fun x T ↦ measure_le_add_of_singleton (hpt₁ n x) T) T)
    (fun n ↦ bind_le_add hK (hKn n) (fun x T ↦ measure_le_add_of_singleton (hpt₂ n x) T) T)

/-- Discretizing a kernel keeps exactly the same null singletons after binding. -/
theorem bind_disc_singleton_eq_zero_iff {K : X → Measure (ULift.{u} (Fin N))}
    [∀ x, IsSubProbabilityMeasure (K x)] (hκ : Measurable κ) (hη : Measurable η)
    (hK : Measurable K) (μ : Measure X)
    (hcell : ∀ n x i, cell n (K (rep κ η n (disc κ η n x)) {i}) = cell n (K x {i}))
    (n : ℕ) (i : ULift.{u} (Fin N)) :
    (μ.bind (K ∘ rep κ η n ∘ disc κ η n)) {i} = 0 ↔ (μ.bind K) {i} = 0 := by
  have hKn : Measurable (K ∘ rep κ η n ∘ disc κ η n) :=
    hK.comp ((measurable_rep κ η n).comp (measurable_disc κ η hκ hη n))
  have hi := (.of_discrete : MeasurableSet {i})
  rw [bind_apply hi hKn.aemeasurable, bind_apply hi hK.aemeasurable,
    lintegral_eq_zero_iff (f := fun x ↦ (K ∘ rep κ η n ∘ disc κ η n) x {i})
      ((measurable_coe hi).comp hKn),
    lintegral_eq_zero_iff (f := fun x ↦ K x {i}) ((measurable_coe hi).comp hK)]
  refine eventually_congr (.of_forall fun x ↦ ?_)
  simp only [Pi.zero_apply, Function.comp_apply]
  rw [← cell_eq_zero_iff (measure_le_one {i}), hcell, cell_eq_zero_iff (measure_le_one {i})]

end Discretize

namespace ProbabilityTheory

open Discretize

variable {f f₁ f₂ g h : ℝ → ℝ}

/-! ## Finite spaces -/

/-- The mass of a point under a kernel pushforward is the sum over source points. -/
theorem toReal_comp_singleton_eq_sum {M N : ℕ} (μ : Measure (ULift.{u} (Fin M)))
    [IsSubProbabilityMeasure μ] (κ : Kernel (ULift.{u} (Fin M)) (ULift.{u} (Fin N)))
    [IsSubMarkovKernel κ] (i : ULift.{u} (Fin N)) :
    ((κ ∘ₘ μ) {i}).toReal = ∑ j, (μ {j}).toReal * (κ j {i}).toReal := by
  rw [bind_apply .of_discrete κ.measurable.aemeasurable,
    lintegral_fintype, toReal_sum fun _ _ ↦ by finiteness]
  exact sum_congr rfl fun j _ ↦ by rw [toReal_mul, mul_comm]

section

variable (hf : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0)
include hf hf_cont

/-- On a finite space the `f`-divergence is the sum over points. -/
theorem fDiv_eq_sum {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ρ₁ ρ₂ : Measure I) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] :
    fDiv f ρ₁ ρ₂ = ∑ i, persp f (ρ₁ {i}).toReal (ρ₂ {i}).toReal := by
  refine le_antisymm ?_ (by simpa using sum_persp_le_fDiv hf hf_cont measurable_id)
  rw [fDiv_eq_iSup_partition hf hf_cont]
  refine iSup_le fun n ↦ iSup_le fun k ↦ iSup_le fun _ ↦ ?_
  have hfib (ρ : Measure I) [IsFiniteMeasure ρ] (j : Fin n) :
      (ρ (k ⁻¹' {j})).toReal = ∑ i ∈ Finset.univ.filter (k · = j), (ρ {i}).toReal := by
    rw [← toReal_sum (fun _ _ ↦ measure_ne_top _ _), sum_measure_singleton]
    congr 2
    ext
    simp
  simp_rw [hfib]
  calc ∑ j, persp f (∑ i ∈ Finset.univ.filter (k · = j), (ρ₁ {i}).toReal)
        (∑ i ∈ Finset.univ.filter (k · = j), (ρ₂ {i}).toReal)
      ≤ ∑ j, ∑ i ∈ Finset.univ.filter (k · = j), persp f (ρ₁ {i}).toReal (ρ₂ {i}).toReal :=
        sum_le_sum fun j _ ↦ persp_sum_le hf _ (fun _ _ ↦ toReal_nonneg) fun _ _ ↦ toReal_nonneg
    _ = ∑ i, persp f (ρ₁ {i}).toReal (ρ₂ {i}).toReal := sum_fiberwise _ _ _

/-- Between point masses the `f`-divergence is the perspective of the masses. -/
theorem fDiv_smul_dirac {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    fDiv f (a • dirac unit.{u + 1}) (b • dirac unit) = persp f a.toReal b.toReal := by
  have : IsFiniteMeasure (a • dirac unit.{u + 1}) := ⟨by simpa using ha.lt_top⟩
  have : IsFiniteMeasure (b • dirac unit.{u + 1}) := ⟨by simpa using hb.lt_top⟩
  rw [fDiv_eq_sum hf hf_cont]
  simp only [Finset.univ_unique, default_eq_unit, sum_singleton, Measure.smul_apply,
    dirac_apply_of_mem (mem_singleton _), smul_eq_mul, mul_one]

variable {X : Type u} [MeasurableSpace X]

/-- An `f`-divergence is the supremum of its pushforwards to finite spaces (corollary of Thm. 4.7,
`fDiv_eq_iSup_partition`). -/
theorem fDiv_eq_iSup_map (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv f μ ν = ⨆ (n : ℕ) (k : X → ULift.{u} (Fin n)) (_ : Measurable k),
      fDiv f (μ.map k) (ν.map k) := by
  refine le_antisymm ?_ (iSup_le fun _ ↦ iSup_le fun _ ↦ iSup_le fun hk ↦ fDiv_map_le hf hf_cont hk)
  rw [fDiv_eq_iSup_partition hf hf_cont]
  refine iSup_le fun n ↦ iSup_le fun k ↦ iSup_le fun hk ↦ ?_
  have hk' : Measurable (ULift.up.{u} ∘ k) := measurable_up.comp hk
  refine le_iSup_of_le n <| le_iSup_of_le _ <| le_iSup_of_le hk' ?_
  rw [fDiv_eq_iSup_partition hf hf_cont]
  refine le_iSup_of_le n <| le_iSup_of_le ULift.down <| le_iSup_of_le measurable_down ?_
  simp only [map_apply hk' (measurable_down (measurableSet_singleton _))]
  exact le_rfl

/-! ## From finite chain rules to general ones -/

/-- Binding through the discretised input approximates the `f`-divergence of the binds
(Thm. 4.8, App. C.3). -/
theorem tendsto_fDiv_bind_disc [Nonempty X]
    {N : ℕ} {κ η : X → Measure (ULift.{u} (Fin N))} [∀ x, IsSubProbabilityMeasure (κ x)]
    [∀ x, IsSubProbabilityMeasure (η x)] (hκ : Measurable κ) (hη : Measurable η)
    (μ₁ μ₂ : Measure X) [IsSubProbabilityMeasure μ₁] [IsSubProbabilityMeasure μ₂] :
    Tendsto (fun n ↦ fDiv f (μ₁.bind (κ ∘ rep κ η n ∘ disc κ η n))
      (μ₂.bind (η ∘ rep κ η n ∘ disc κ η n))) atTop (𝓝 (fDiv f (μ₁.bind κ) (μ₂.bind η))) := by
  have hrd (n : ℕ) := (measurable_rep κ η n).comp (measurable_disc κ η hκ hη n)
  have {K : X → Measure (ULift.{u} (Fin N))} [∀ x, IsSubProbabilityMeasure (K x)] (n : ℕ)
      (x : X) : IsSubProbabilityMeasure ((K ∘ rep κ η n ∘ disc κ η n) x) :=
    inferInstanceAs (IsSubProbabilityMeasure (K _))
  have := isSubProbabilityMeasure_bind μ₁ κ
  have := isSubProbabilityMeasure_bind μ₂ η
  have (n : ℕ) := isSubProbabilityMeasure_bind μ₁ _ (hκ.comp (hrd n)).aemeasurable
  have (n : ℕ) := isSubProbabilityMeasure_bind μ₂ _ (hη.comp (hrd n)).aemeasurable
  have hsum (n : ℕ) := fDiv_eq_sum hf hf_cont (μ₁.bind (κ ∘ rep κ η n ∘ disc κ η n))
    (μ₂.bind (η ∘ rep κ η n ∘ disc κ η n))
  -- on a finite output `fDiv` is a sum of `persp` of point masses; each mass converges and keeps
  -- its zero/nonzero status, which is what continuity of `persp` needs
  rw [funext hsum, fDiv_eq_sum hf hf_cont]
  refine tendsto_finset_sum _ (fun i _ ↦ ?_) fun i _ ↦ persp_ne_bot hf toReal_nonneg
  have hlim {K : X → Measure (ULift.{u} (Fin N))} [∀ x, IsSubProbabilityMeasure (K x)]
      (hK : Measurable K) (μ : Measure X) [IsSubProbabilityMeasure μ]
      (hcell : ∀ n x i, cell n (K (rep κ η n (disc κ η n x)) {i}) = cell n (K x {i})) :
      Tendsto (fun n ↦ ((μ.bind (K ∘ rep κ η n ∘ disc κ η n)) {i}).toReal) atTop
        (𝓝 ((μ.bind K) {i}).toReal) :=
    have := isSubProbabilityMeasure_bind μ K
    (tendsto_toReal (measure_ne_top _ _)).comp (tendsto_bind_disc hκ hη hK hcell {i})
  have hzero {K : X → Measure (ULift.{u} (Fin N))} [∀ x, IsSubProbabilityMeasure (K x)]
      (hK : Measurable K) (μ : Measure X) [IsSubProbabilityMeasure μ]
      (hcell : ∀ n x i, cell n (K (rep κ η n (disc κ η n x)) {i}) = cell n (K x {i})) (n : ℕ) :
      ((μ.bind (K ∘ rep κ η n ∘ disc κ η n)) {i}).toReal = 0 ↔ ((μ.bind K) {i}).toReal = 0 := by
    have := isSubProbabilityMeasure_bind μ K
    have := isSubProbabilityMeasure_bind μ _ (hK.comp (hrd n)).aemeasurable
    simpa [toReal_eq_zero_iff] using bind_disc_singleton_eq_zero_iff hκ hη hK μ hcell n i
  exact tendsto_persp hf (hlim hκ μ₁ cell_fst) (hlim hη μ₂ cell_snd)
    (fun _ ↦ toReal_nonneg) (fun _ ↦ toReal_nonneg) (hzero hκ μ₁ cell_fst)
    (hzero hη μ₂ cell_snd)

/-- A chain rule between finite spaces for kernel pairs whose pointwise masses satisfy `Q` holds
between all spaces for such pairs (Thm. 4.6). -/
theorem fDiv_comp_le_of_finite_of_mass (hg : ConvexOn ℝ (Ici 0) g)
    (hg_cont : ContinuousWithinAt g (Ici 0) 0) (hh : ConvexOn ℝ (Ici 0) h)
    (hh_cont : ContinuousWithinAt h (Ici 0) 0) {chain : EReal → EReal → EReal}
    (hchain : ∀ ⦃a a' b b'⦄, a ≤ a' → b ≤ b' → chain a b ≤ chain a' b') (Q : ℝ≥0∞ → ℝ≥0∞ → Prop)
    (hfin : ∀ {M N : ℕ} [NeZero M] {μ₁ μ₂ : Measure (ULift.{u} (Fin M))}
      [IsSubProbabilityMeasure μ₁] [IsSubProbabilityMeasure μ₂]
      {κ η : Kernel (ULift.{u} (Fin M)) (ULift.{u} (Fin N))} [IsSubMarkovKernel κ]
      [IsSubMarkovKernel η], (∀ i, Q (κ i univ) (η i univ)) →
      fDiv f (κ ∘ₘ μ₁) (η ∘ₘ μ₂) ≤ chain (fDiv g μ₁ μ₂) (⨆ i, fDiv h (κ i) (η i)))
    {Y : Type u} [MeasurableSpace Y] [Nonempty X] {μ₁ μ₂ : Measure X}
    [IsSubProbabilityMeasure μ₁] [IsSubProbabilityMeasure μ₂] (κ η : Kernel X Y)
    [IsSubMarkovKernel κ] [IsSubMarkovKernel η] (hQ : ∀ x, Q (κ x univ) (η x univ)) :
    fDiv f (κ ∘ₘ μ₁) (η ∘ₘ μ₂) ≤ chain (fDiv g μ₁ μ₂) (⨆ x, fDiv h (κ x) (η x)) := by
  rw [fDiv_eq_iSup_map hf hf_cont]
  refine iSup_le fun N ↦ iSup_le fun k ↦ iSup_le fun hk ↦ ?_
  rw [map_comp μ₁ κ hk, map_comp μ₂ η hk]
  refine le_of_tendsto' (tendsto_fDiv_bind_disc hf hf_cont (κ.map k).measurable
    (η.map k).measurable μ₁ μ₂) fun n ↦ ?_
  set d := disc (κ.map k) (η.map k) n
  have hd : Measurable d := measurable_disc _ _ (κ.map k).measurable (η.map k).measurable n
  have he := measurable_rep (κ.map k) (η.map k) n
  have : NeZero (Fintype.card (CellVec N n)) := ⟨card_ne_zero⟩
  calc fDiv f (μ₁.bind (κ.map k ∘ rep (κ.map k) (η.map k) n ∘ d))
        (μ₂.bind (η.map k ∘ rep (κ.map k) (η.map k) n ∘ d))
      = fDiv f ((κ.map k).comap _ he ∘ₘ μ₁.map d) ((η.map k).comap _ he ∘ₘ μ₂.map d) := by
        rw [bind_map_eq μ₁ hd ((κ.map k).comap _ he).measurable,
          bind_map_eq μ₂ hd ((η.map k).comap _ he).measurable]
        rfl
    _ ≤ chain (fDiv g (μ₁.map d) (μ₂.map d))
          (⨆ j, fDiv h ((κ.map k).comap _ he j) ((η.map k).comap _ he j)) := hfin fun j ↦ by
        simpa [Kernel.comap_apply, Kernel.map_apply _ hk, map_apply hk MeasurableSet.univ]
          using hQ _
    _ ≤ chain (fDiv g μ₁ μ₂) (⨆ x, fDiv h (κ x) (η x)) := by
        refine hchain (fDiv_map_le hg hg_cont hd) (iSup_le fun j ↦ ?_)
        simp only [Kernel.comap_apply, Kernel.map_apply _ hk]
        exact (fDiv_map_le hh hh_cont hk).trans (le_iSup (fun x ↦ fDiv h (κ x) (η x)) _)

/-- A chain rule between finite spaces holds between all spaces (Thm. 4.6). -/
theorem fDiv_comp_le_of_finite (hg : ConvexOn ℝ (Ici 0) g)
    (hg_cont : ContinuousWithinAt g (Ici 0) 0) (hh : ConvexOn ℝ (Ici 0) h)
    (hh_cont : ContinuousWithinAt h (Ici 0) 0) {chain : EReal → EReal → EReal}
    (hchain : ∀ ⦃a a' b b'⦄, a ≤ a' → b ≤ b' → chain a b ≤ chain a' b')
    (hfin : ∀ {M N : ℕ} [NeZero M] {μ₁ μ₂ : Measure (ULift.{u} (Fin M))}
      [IsSubProbabilityMeasure μ₁] [IsSubProbabilityMeasure μ₂]
      {κ η : Kernel (ULift.{u} (Fin M)) (ULift.{u} (Fin N))} [IsSubMarkovKernel κ]
      [IsSubMarkovKernel η],
      fDiv f (κ ∘ₘ μ₁) (η ∘ₘ μ₂) ≤ chain (fDiv g μ₁ μ₂) (⨆ i, fDiv h (κ i) (η i)))
    {Y : Type u} [MeasurableSpace Y] [Nonempty X] {μ₁ μ₂ : Measure X}
    [IsSubProbabilityMeasure μ₁] [IsSubProbabilityMeasure μ₂] (κ η : Kernel X Y)
    [IsSubMarkovKernel κ] [IsSubMarkovKernel η] :
    fDiv f (κ ∘ₘ μ₁) (η ∘ₘ μ₂) ≤ chain (fDiv g μ₁ μ₂) (⨆ x, fDiv h (κ x) (η x)) :=
  fDiv_comp_le_of_finite_of_mass hf hf_cont hg hg_cont hh hh_cont hchain (fun _ _ ↦ True)
    (fun _ ↦ hfin) κ η fun _ ↦ trivial

end

/-! ## Additive chain rule from split perspectives -/

/-- The perspective of `f` at a product splits into those of `f₁` and `f₂`, weighted by convex
combinations with coefficients `β, β'` (condition (A') of Sato–Katsumata, Prop. 1). -/
def PerspSplit (f f₁ f₂ : ℝ → ℝ) (β β' : ℝ) : Prop :=
  ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (0 : ℝ) 1,
    persp f (z * w) (x * y) ≤ ((β * w + (1 - β) * y : ℝ) : EReal) * persp f₁ z x +
      ((β' * z + (1 - β') * x : ℝ) : EReal) * persp f₂ w y

/-- Under condition (A'), the `f`-divergence of two compositions between finite spaces is at most
the `f₁`-divergence of the inputs plus the largest `f₂`-divergence of the kernels
(Sato–Katsumata, Prop. 1). -/
theorem fDiv_comp_le_of_perspSplit (hf : ConvexOn ℝ (Ici 0) f)
    (hf_cont : ContinuousWithinAt f (Ici 0) 0) (hf₁ : ConvexOn ℝ (Ici 0) f₁)
    (hf₁_cont : ContinuousWithinAt f₁ (Ici 0) 0) (hf₂ : ConvexOn ℝ (Ici 0) f₂)
    (hf₂_cont : ContinuousWithinAt f₂ (Ici 0) 0) (hf₀ : ∀ t, 0 ≤ t → 0 ≤ f t)
    (hf₁₀ : ∀ t, 0 ≤ t → 0 ≤ f₁ t) (hf₂₀ : ∀ t, 0 ≤ t → 0 ≤ f₂ t) {β β' : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) (hβ' : β' ∈ Icc (0 : ℝ) 1) (hA : PerspSplit f f₁ f₂ β β')
    {M N : ℕ} [NeZero M] (μ₁ μ₂ : Measure (ULift.{u} (Fin M))) [IsSubProbabilityMeasure μ₁]
    [IsSubProbabilityMeasure μ₂] (κ η : Kernel (ULift.{u} (Fin M)) (ULift.{u} (Fin N)))
    [IsSubMarkovKernel κ] [IsSubMarkovKernel η] :
    fDiv f (κ ∘ₘ μ₁) (η ∘ₘ μ₂) ≤ fDiv f₁ μ₁ μ₂ + ⨆ j, fDiv f₂ (κ j) (η j) := by
  have hw {γ : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1) {a b : ℝ≥0∞} : 0 ≤ γ * a.toReal + (1 - γ) * b.toReal :=
    add_nonneg (mul_nonneg hγ.1 toReal_nonneg) (mul_nonneg (sub_nonneg.2 hγ.2) toReal_nonneg)
  have hc (γ : ℝ) (hγ : γ ∈ Icc (0 : ℝ) 1) {K : ℕ} (ρ ρ' : Measure (ULift.{u} (Fin K)))
      [IsSubProbabilityMeasure ρ] [IsSubProbabilityMeasure ρ'] :
      ∑ i, ENNReal.ofReal (γ * (ρ {i}).toReal + (1 - γ) * (ρ' {i}).toReal) ≤ 1 := by
    have hsum (ρ : Measure (ULift.{u} (Fin K))) [IsSubProbabilityMeasure ρ] :
        ∑ i, (ρ {i}).toReal ≤ 1 := by
      rw [← toReal_sum fun _ _ ↦ by finiteness, sum_measure_singleton]
      exact (toReal_mem_Icc _).2
    rw [← ofReal_sum_of_nonneg fun _ _ ↦ hw hγ, sum_add_distrib, ← mul_sum,
      ← mul_sum, ofReal_le_one]
    nlinarith [hsum ρ, hsum ρ', hγ.1, hγ.2]
  have hp {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ t → 0 ≤ g t) {a b : ℝ≥0∞} : 0 ≤ persp g a.toReal b.toReal :=
    persp_nonneg hg toReal_nonneg toReal_nonneg
  set S := ⨆ j, (fDiv f₂ (κ j) (η j)).toENNReal
  -- per output cell, split over inputs by joint convexity, apply (A') to each pair, swap sums; the
  -- convex weights `β κ + (1-β) η` and `β′ μ₁ + (1-β′) μ₂` have total mass ≤ 1 (`hc`)
  have key : (fDiv f (κ ∘ₘ μ₁) (η ∘ₘ μ₂)).toENNReal ≤ (fDiv f₁ μ₁ μ₂).toENNReal + S := by
    rw [fDiv_eq_sum hf hf_cont, fDiv_eq_sum hf₁ hf₁_cont]
    simp_rw [toReal_comp_singleton_eq_sum]
    calc (∑ i, persp f (∑ j, (μ₁ {j}).toReal * (κ j {i}).toReal)
          (∑ j, (μ₂ {j}).toReal * (η j {i}).toReal)).toENNReal
        ≤ (∑ i, ∑ j, persp f ((μ₁ {j}).toReal * (κ j {i}).toReal)
            ((μ₂ {j}).toReal * (η j {i}).toReal)).toENNReal :=
          toENNReal_le_toENNReal <| sum_le_sum fun i _ ↦ persp_sum_le hf _
            (fun _ _ ↦ by positivity) fun _ _ ↦ by positivity
      _ = ∑ i, ∑ j, (persp f ((μ₁ {j}).toReal * (κ j {i}).toReal)
            ((μ₂ {j}).toReal * (η j {i}).toReal)).toENNReal := by
          rw [toENNReal_sum _ fun _ _ ↦ sum_nonneg fun _ _ ↦
            persp_nonneg hf₀ (by positivity) (by positivity)]
          exact sum_congr rfl fun i _ ↦
            toENNReal_sum _ fun _ _ ↦ persp_nonneg hf₀ (by positivity) (by positivity)
      _ ≤ ∑ i, ∑ j, (ENNReal.ofReal (β * (κ j {i}).toReal + (1 - β) * (η j {i}).toReal) *
              (persp f₁ (μ₁ {j}).toReal (μ₂ {j}).toReal).toENNReal +
            ENNReal.ofReal (β' * (μ₁ {j}).toReal + (1 - β') * (μ₂ {j}).toReal) *
              (persp f₂ (κ j {i}).toReal (η j {i}).toReal).toENNReal) := by
          refine sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ ?_
          refine (toENNReal_le_toENNReal (hA _ (toReal_mem_Icc _) _ (toReal_mem_Icc _) _
            (toReal_mem_Icc _) _
            (toReal_mem_Icc _))).trans_eq ?_
          rw [toENNReal_add (EReal.mul_nonneg (coe_nonneg.2 (hw hβ)) (hp hf₁₀))
            (EReal.mul_nonneg (coe_nonneg.2 (hw hβ')) (hp hf₂₀)),
            toENNReal_mul (coe_nonneg.2 (hw hβ)),
            toENNReal_mul (coe_nonneg.2 (hw hβ')),
            real_coe_toENNReal, real_coe_toENNReal]
      _ = ∑ j, ((∑ i, ENNReal.ofReal (β * (κ j {i}).toReal + (1 - β) * (η j {i}).toReal)) *
              (persp f₁ (μ₁ {j}).toReal (μ₂ {j}).toReal).toENNReal +
            ENNReal.ofReal (β' * (μ₁ {j}).toReal + (1 - β') * (μ₂ {j}).toReal) *
              ∑ i, (persp f₂ (κ j {i}).toReal (η j {i}).toReal).toENNReal) := by
          rw [Finset.sum_comm]
          simp_rw [sum_add_distrib, sum_mul, mul_sum]
      _ ≤ ∑ j, ((persp f₁ (μ₁ {j}).toReal (μ₂ {j}).toReal).toENNReal +
            ENNReal.ofReal (β' * (μ₁ {j}).toReal + (1 - β') * (μ₂ {j}).toReal) * S) := by
          gcongr with j
          · exact mul_le_of_le_one_left zero_le (hc β hβ (κ j) (η j))
          rw [← toENNReal_sum _ fun _ _ ↦ hp hf₂₀, ← fDiv_eq_sum hf₂ hf₂_cont]
          exact le_iSup (fun j ↦ (fDiv f₂ (κ j) (η j)).toENNReal) j
      _ ≤ (∑ j, persp f₁ (μ₁ {j}).toReal (μ₂ {j}).toReal).toENNReal + S := by
          rw [sum_add_distrib, ← sum_mul, toENNReal_sum _ fun _ _ ↦ hp hf₁₀]
          exact add_le_add le_rfl (mul_le_of_le_one_left zero_le (hc β' hβ' μ₁ μ₂))
  -- all values are nonnegative, so the bound holds in the extended reals
  have h₀ := fDiv_nonneg_of_nonneg hf₀ (μ := κ ∘ₘ μ₁) (ν := η ∘ₘ μ₂)
  have h₁ := fDiv_nonneg_of_nonneg hf₁₀ (μ := μ₁) (ν := μ₂)
  have h₂ (j) := fDiv_nonneg_of_nonneg hf₂₀ (μ := κ j) (ν := η j)
  have hS : 0 ≤ ⨆ j, fDiv f₂ (κ j) (η j) := le_iSup_of_le ⟨0⟩ (h₂ _)
  calc fDiv f (κ ∘ₘ μ₁) (η ∘ₘ μ₂) = ((fDiv f (κ ∘ₘ μ₁) (η ∘ₘ μ₂)).toENNReal : EReal) :=
        (coe_toENNReal h₀).symm
    _ ≤ (((fDiv f₁ μ₁ μ₂).toENNReal + S : ℝ≥0∞) : EReal) := coe_ennreal_le_coe_ennreal_iff.2 key
    _ ≤ fDiv f₁ μ₁ μ₂ + ⨆ j, fDiv f₂ (κ j) (η j) := by
        rw [coe_ennreal_add, coe_toENNReal h₁, ← coe_toENNReal hS]
        exact add_le_add le_rfl (coe_ennreal_le_coe_ennreal_iff.2 (iSup_le fun j ↦
          toENNReal_le_toENNReal (le_iSup (fun j ↦ fDiv f₂ (κ j) (η j)) j)))

end ProbabilityTheory
