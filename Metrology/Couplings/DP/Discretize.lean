module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Metrology.Couplings.SubProbability

/-! Dyadic discretization of kernels into finite spaces (Approximate Span Liftings, App. C.3). -/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

universe u

namespace ULift

variable {N : ℕ}

theorem measurableSet_fin (T : Set (ULift.{u} (Fin N))) : MeasurableSet T :=
  measurable_down (t := up ⁻¹' T) .of_discrete

instance measurableSingletonClass_fin : MeasurableSingletonClass (ULift.{u} (Fin N)) :=
  ⟨fun _ ↦ measurableSet_fin _⟩

end ULift

namespace Discretize

/-! ### Dyadic cells -/

/-- The dyadic cell of `v ∈ [0, 1]` at level `n`: `0` exactly at `0`, else `⌈v 2ⁿ⌉`. -/
noncomputable def cell (n : ℕ) (v : ℝ≥0∞) : Fin (2 ^ n + 1) := by
  classical
  exact if v = 0 then 0 else ⟨min ⌈v.toReal * 2 ^ n⌉₊ (2 ^ n), Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem measurable_cell (n : ℕ) : Measurable (cell n) := by
  classical
  have hceil : Measurable (Nat.ceil : ℝ → ℕ) := Nat.ceil_mono.measurable
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  exact measurable_of_countable (fun m : ℕ ↦
    (⟨min m (2 ^ n), Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (2 ^ n + 1))) |>.comp
      (hceil.comp (ENNReal.measurable_toReal.mul_const _))

theorem cell_eq_zero_iff {n : ℕ} {v : ℝ≥0∞} (hv : v ≤ 1) : cell n v = 0 ↔ v = 0 := by
  classical
  refine ⟨fun h ↦ by_contra fun h0 ↦ ?_, fun h ↦ by simp [cell, h]⟩
  have hpos : 0 < v.toReal := ENNReal.toReal_pos h0 (hv.trans_lt ENNReal.one_lt_top).ne
  simp only [cell, h0, ↓reduceIte, Fin.ext_iff, Fin.val_zero] at h
  have : 1 ≤ ⌈v.toReal * 2 ^ n⌉₊ := Nat.one_le_iff_ne_zero.2 (by positivity)
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

/-- Values in the same nonzero dyadic cell differ by less than `2⁻ⁿ`. -/
theorem abs_sub_lt_of_cell_eq {n : ℕ} {v w : ℝ≥0∞} (hv : v ≤ 1) (hw : w ≤ 1)
    (h : cell n v = cell n w) : |v.toReal - w.toReal| < (2 ^ n)⁻¹ := by
  classical
  rcases eq_or_ne v 0 with rfl | hv0
  · rw [(cell_eq_zero_iff hw).1 (h.symm.trans ((cell_eq_zero_iff (n := n) zero_le_one).2 rfl))]
    simp
  have hw0 : w ≠ 0 := fun h0 ↦ hv0 ((cell_eq_zero_iff hv).1 (h.trans ((cell_eq_zero_iff hw).2 h0)))
  have hle (x : ℝ≥0∞) (hx : x ≤ 1) : ⌈x.toReal * 2 ^ n⌉₊ ≤ 2 ^ n := by
    refine Nat.ceil_le.2 ?_
    push_cast
    exact mul_le_of_le_one_left (by positivity) (ENNReal.toReal_le_of_le_ofReal zero_le_one
      (hx.trans ENNReal.ofReal_one.ge))
  simp only [cell, hv0, hw0, ↓reduceIte, Fin.ext_iff, min_eq_left (hle v hv),
    min_eq_left (hle w hw)] at h
  have hv' := Nat.ceil_lt_add_one (by positivity : 0 ≤ v.toReal * 2 ^ n)
  have hw' := Nat.ceil_lt_add_one (by positivity : 0 ≤ w.toReal * 2 ^ n)
  have hv'' := Nat.le_ceil (v.toReal * 2 ^ n)
  have hw'' := Nat.le_ceil (w.toReal * 2 ^ n)
  rw [h] at hv' hv''
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have key (a b : ℝ) (hab : a * 2 ^ n - b * 2 ^ n < 1) : a - b < (2 ^ n)⁻¹ :=
    calc a - b = (a * 2 ^ n - b * 2 ^ n) * (2 ^ n)⁻¹ := by field_simp
      _ < 1 * (2 ^ n)⁻¹ := by gcongr
      _ = (2 ^ n)⁻¹ := one_mul _
  rw [abs_sub_lt_iff]
  exact ⟨key _ _ (by linarith), key _ _ (by linarith)⟩

/-! ### Convergence on finite spaces -/

section Finite

variable {N : ℕ}

/-- Singleton-wise closeness of measures on a finite space gives closeness on every event. -/
theorem measure_le_add_of_singleton {ρ ρ' : Measure (ULift.{u} (Fin N))} {c : ℝ≥0∞}
    (h : ∀ i, ρ {i} ≤ ρ' {i} + c) (T : Set (ULift.{u} (Fin N))) : ρ T ≤ ρ' T + N * c := by
  classical
  rw [← T.coe_toFinset, ← sum_measure_singleton, ← sum_measure_singleton]
  calc ∑ i ∈ T.toFinset, ρ {i} ≤ ∑ i ∈ T.toFinset, (ρ' {i} + c) := Finset.sum_le_sum fun i _ ↦ h i
    _ = ∑ i ∈ T.toFinset, ρ' {i} + T.toFinset.card * c := by rw [Finset.sum_add_distrib]; simp
    _ ≤ ∑ i ∈ T.toFinset, ρ' {i} + N * c := by
        gcongr
        exact_mod_cast (Finset.card_le_univ _).trans_eq (by simp)

/-- Two-sided bounds that shrink to zero force convergence. -/
theorem tendsto_of_le_add {a : ℕ → ℝ≥0∞} {b : ℝ≥0∞} (hb : b ≠ ⊤) {c : ℕ → ℝ≥0∞}
    (hc : Tendsto c atTop (𝓝 0)) (h₁ : ∀ n, a n ≤ b + c n) (h₂ : ∀ n, b ≤ a n + c n) :
    Tendsto a atTop (𝓝 b) := by
  refine (ENNReal.tendsto_nhds hb).2 fun ε hε ↦ ?_
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hc ε hε] with n hn
  exact ⟨tsub_le_iff_right.2 ((h₂ n).trans (by gcongr)), (h₁ n).trans (by gcongr)⟩

end Finite

/-! ### Discretization -/

section Discretize

variable {X : Type u} [MeasurableSpace X] {N : ℕ} (f g : X → Measure (ULift.{u} (Fin N)))

/-- Cell vectors of level `n` over `N` points. -/
abbrev CellVec (N n : ℕ) := Fin N → Fin (2 ^ n + 1) × Fin (2 ^ n + 1)

/-- The dyadic cells of the singleton masses of `f x` and `g x`. -/
noncomputable def cellVec (n : ℕ) (x : X) : CellVec N n :=
  fun i ↦ (cell n (f x {⟨i⟩}), cell n (g x {⟨i⟩}))

/-- The discretization of the input space by cell vectors. -/
noncomputable def disc (n : ℕ) (x : X) : ULift.{u} (Fin (Fintype.card (CellVec N n))) :=
  ⟨Fintype.equivFin _ (cellVec f g n x)⟩

open Classical in
/-- A representative point of each realized cell vector. -/
noncomputable def rep [Nonempty X] (n : ℕ) (j : ULift.{u} (Fin (Fintype.card (CellVec N n)))) :
    X :=
  if h : ∃ x, cellVec f g n x = (Fintype.equivFin _).symm j.down then h.choose
  else Classical.arbitrary X

omit [MeasurableSpace X] in
theorem cellVec_rep_disc [Nonempty X] (n : ℕ) (x : X) :
    cellVec f g n (rep f g n (disc f g n x)) = cellVec f g n x := by
  have h : ∃ y, cellVec f g n y = (Fintype.equivFin _).symm (disc f g n x).down :=
    ⟨x, by simp [disc]⟩
  simp only [rep, h, ↓reduceDIte, h.choose_spec]
  simp [disc]

theorem measurable_disc (hf : Measurable f) (hg : Measurable g) (n : ℕ) :
    Measurable (disc f g n) := by
  refine measurable_up.comp ((measurable_of_countable _).comp (measurable_pi_iff.2 fun i ↦ ?_))
  have hS := Measure.measurable_coe (ULift.measurableSet_fin {(⟨i⟩ : ULift.{u} (Fin N))})
  exact ((measurable_cell n).comp (hS.comp hf)).prodMk ((measurable_cell n).comp (hS.comp hg))

theorem measurable_rep [Nonempty X] (n : ℕ) : Measurable (rep f g n) :=
  (measurable_of_countable fun j ↦ rep f g n ⟨j⟩).comp measurable_down

/-- Masses in the same dyadic cell are within `2⁻ⁿ` of each other. -/
theorem le_add_of_cell_eq {n : ℕ} {v w : ℝ≥0∞} (hv : v ≤ 1) (hw : w ≤ 1)
    (h : cell n v = cell n w) : v ≤ w + ENNReal.ofReal (2 ^ n)⁻¹ := by
  have := (abs_sub_lt_iff.1 (abs_sub_lt_of_cell_eq hv hw h)).1
  rw [← ENNReal.ofReal_toReal (hv.trans_lt ENNReal.one_lt_top).ne,
    ← ENNReal.ofReal_toReal (hw.trans_lt ENNReal.one_lt_top).ne,
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

variable {f g}

theorem singleton_le_one {ρ : Measure (ULift.{u} (Fin N))} [IsSubProbabilityMeasure ρ]
    (i : ULift.{u} (Fin N)) : ρ {i} ≤ 1 :=
  (measure_mono (subset_univ _)).trans IsSubProbabilityMeasure.measure_univ_le_one

omit [MeasurableSpace X] in
theorem cell_fst [Nonempty X] (n : ℕ) (x : X) (i : ULift.{u} (Fin N)) :
    cell n (f (rep f g n (disc f g n x)) {i}) = cell n (f x {i}) :=
  congrArg Prod.fst (congrFun (cellVec_rep_disc f g n x) i.down)

omit [MeasurableSpace X] in
theorem cell_snd [Nonempty X] (n : ℕ) (x : X) (i : ULift.{u} (Fin N)) :
    cell n (g (rep f g n (disc f g n x)) {i}) = cell n (g x {i}) :=
  congrArg Prod.snd (congrFun (cellVec_rep_disc f g n x) i.down)

/-- Binding with kernels that are pointwise close on events gives close measures. -/
theorem bind_le_add {μ : Measure X} [IsSubProbabilityMeasure μ]
    {F F' : X → Measure (ULift.{u} (Fin N))}
    (hF : Measurable F) (hF' : Measurable F') {C : ℝ≥0∞} (h : ∀ x T, F x T ≤ F' x T + C)
    (T : Set (ULift.{u} (Fin N))) : (μ.bind F) T ≤ (μ.bind F') T + C := by
  have hT := ULift.measurableSet_fin T
  rw [Measure.bind_apply hT hF.aemeasurable, Measure.bind_apply hT hF'.aemeasurable]
  calc ∫⁻ x, F x T ∂μ ≤ ∫⁻ x, F' x T + C ∂μ := lintegral_mono fun x ↦ h x T
    _ = ∫⁻ x, F' x T ∂μ + C * μ univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ ≤ ∫⁻ x, F' x T ∂μ + C := by
        gcongr
        exact mul_le_of_le_one_right' IsSubProbabilityMeasure.measure_univ_le_one

end Discretize

section Limits

variable {X : Type u} [MeasurableSpace X] {N : ℕ} {f g : X → Measure (ULift.{u} (Fin N))}
  [Nonempty X]

/-- Discretizing a kernel changes the masses of events by at most `N 2⁻ⁿ`, which vanishes. -/
theorem tendsto_bind_disc {K : X → Measure (ULift.{u} (Fin N))} [∀ x, IsSubProbabilityMeasure (K x)]
    (hf : Measurable f) (hg : Measurable g) (hK : Measurable K) {μ : Measure X}
    [IsSubProbabilityMeasure μ]
    (hcell : ∀ n x i, cell n (K (rep f g n (disc f g n x)) {i}) = cell n (K x {i}))
    (T : Set (ULift.{u} (Fin N))) :
    Tendsto (fun n ↦ (μ.bind (K ∘ rep f g n ∘ disc f g n)) T) atTop (𝓝 ((μ.bind K) T)) := by
  set c : ℕ → ℝ≥0∞ := fun n ↦ N * ENNReal.ofReal (2 ^ n)⁻¹
  have hc : Tendsto c atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal (tendsto_inv_atTop_zero.comp
        (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))
    simpa [c] using ENNReal.Tendsto.const_mul this (Or.inr (ENNReal.natCast_ne_top N))
  have hKn (n : ℕ) : Measurable (K ∘ rep f g n ∘ disc f g n) :=
    hK.comp ((measurable_rep f g n).comp (measurable_disc f g hf hg n))
  have := isSubProbabilityMeasure_bind (μ := μ) (f := K) inferInstance
  have hpt (n : ℕ) (x : X) (i : ULift.{u} (Fin N)) :=
    le_add_of_cell_eq (singleton_le_one (ρ := K x) i) (singleton_le_one i) (hcell n x i).symm
  have hpt' (n : ℕ) (x : X) (i : ULift.{u} (Fin N)) :=
    le_add_of_cell_eq (singleton_le_one (ρ := K (rep f g n (disc f g n x))) i)
      (singleton_le_one i) (hcell n x i)
  exact tendsto_of_le_add (measure_ne_top _ _) hc
    (fun n ↦ bind_le_add (hKn n) hK (fun x T ↦ measure_le_add_of_singleton (hpt' n x) T) T)
    (fun n ↦ bind_le_add hK (hKn n) (fun x T ↦ measure_le_add_of_singleton (hpt n x) T) T)

/-- Discretizing a kernel keeps exactly the same null singletons after binding. -/
theorem bind_disc_singleton_eq_zero_iff {K : X → Measure (ULift.{u} (Fin N))}
    [∀ x, IsSubProbabilityMeasure (K x)] (hf : Measurable f) (hg : Measurable g)
    (hK : Measurable K) (μ : Measure X)
    (hcell : ∀ n x i, cell n (K (rep f g n (disc f g n x)) {i}) = cell n (K x {i}))
    (n : ℕ) (i : ULift.{u} (Fin N)) :
    (μ.bind (K ∘ rep f g n ∘ disc f g n)) {i} = 0 ↔ (μ.bind K) {i} = 0 := by
  have hKn : Measurable (K ∘ rep f g n ∘ disc f g n) :=
    hK.comp ((measurable_rep f g n).comp (measurable_disc f g hf hg n))
  have hi := ULift.measurableSet_fin {i}
  rw [Measure.bind_apply hi hKn.aemeasurable, Measure.bind_apply hi hK.aemeasurable,
    lintegral_eq_zero_iff (f := fun x ↦ (K ∘ rep f g n ∘ disc f g n) x {i})
      ((Measure.measurable_coe hi).comp hKn),
    lintegral_eq_zero_iff (f := fun x ↦ K x {i}) ((Measure.measurable_coe hi).comp hK)]
  refine Filter.eventually_congr (.of_forall fun x ↦ ?_)
  simp only [Pi.zero_apply, Function.comp_apply]
  rw [← cell_eq_zero_iff (n := n) (singleton_le_one (ρ := K (rep f g n (disc f g n x))) i),
    hcell, cell_eq_zero_iff (singleton_le_one i)]

end Limits

/-- A measure on a finite space is zero exactly when all its singletons are null. -/
theorem measure_eq_zero_iff_singleton {N : ℕ} {ρ : Measure (ULift.{u} (Fin N))} :
    ρ = 0 ↔ ∀ i, ρ {i} = 0 := by
  classical
  refine ⟨fun h i ↦ by simp [h], fun h ↦ ?_⟩
  rw [← Measure.measure_univ_eq_zero, ← Finset.coe_univ, ← sum_measure_singleton]
  simp [h]

end Discretize
