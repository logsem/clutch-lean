module

public import Mathlib.Basic.Countable.Basic
public import Mathlib.Tactic.DeriveCountable
public import Mathlib.Logic.Equiv.List
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

/-# Dumping ground for lemmas that belong in Std or Mathlib -/

noncomputable section
open Classical MeasureTheory ProbabilityTheory Measure

theorem Discrete.measure_pos_of_singleton_pos {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] (μ : Measure α) (S : Set α) (hS : 0 < μ S) :
    ∃ x ∈ S, 0 < μ {x} := by
  by_contra! h
  have hzero : μ (⋃ x ∈ S, ({x} : Set α)) = 0 :=
    (measure_biUnion_null_iff (Set.to_countable S)).mpr fun x hxS =>
      nonpos_iff_eq_zero.mp (h x hxS)
  rw [Set.biUnion_of_singleton] at hzero
  exact (ne_of_gt hS) hzero

theorem Discrete.map_singleton_pos {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [Countable α]
    {f : α → β} {μ : Measure α} {b : β}
    (h : 0 < (μ.map f) {b}) :
    ∃ a, f a = b ∧ 0 < μ {a} := by
  rw [Measure.map_apply .of_discrete .of_discrete] at h
  obtain ⟨a, ha, hpos⟩ := Discrete.measure_pos_of_singleton_pos μ _ h
  -- `a ∈ f ⁻¹' {b}` means `f a ∈ {b}` means `f a = b`.
  exact ⟨a, Set.mem_singleton_iff.mp (Set.mem_preimage.mp ha), hpos⟩

theorem Measure.bind_map {α β γ : Type _}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [DiscreteMeasurableSpace β] {μ : Measure α} {f : α → β} {g : β → Measure γ}
    (hf : Measurable f) (hg : Measurable g) : g ∘ₘ (μ.map f) = (g ∘ f) ∘ₘ μ := by
  refine Measure.ext fun S hS => ?_
  simp only [Measure.bind, Measure.join_apply hS, Measure.map_map hg hf]

abbrev count (f : α → ENNReal) [MeasurableSpace α] := Measure.count.withDensity f

theorem Discrete.count_singleton [MeasurableSpace T] [MeasurableSingletonClass T]
    (f : T → ENNReal) (t : T) : count f {t} = f t := by simp

/-! ## Ports from `theories/prob/distribution.v` §1 (basic pmf bounds)

Rocq's `distr` bakes in `SeriesC μ ≤ 1`; here we take sub-probability as an
explicit hypothesis (`h : μ Set.univ ≤ 1`) or assume a probability-measure
instance where appropriate. -/

/-- On a countable discrete space, the total mass is the tsum of singleton
masses. -/
theorem Measure.univ_eq_tsum_singletons {α : Type _}
    [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    (μ : Measure α) : μ Set.univ = ∑' a, μ {a} := by
  have hunion : (Set.univ : Set α) = ⋃ a, ({a} : Set α) := by
    ext x; simp
  have hdisj : Pairwise (Function.onFun Disjoint fun a : α => ({a} : Set α)) := by
    intro i j hij
    exact Set.disjoint_singleton.mpr hij
  rw [hunion, measure_iUnion hdisj (fun _ => MeasurableSet.singleton _)]

/-- Rocq `pmf_1_eq_SeriesC`: if a singleton has full mass `1` and `μ` is a
sub-probability measure, then `μ univ = 1`. -/
theorem pmf_1_eq_SeriesC {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ : Measure α} {a : α} (hμ : μ {a} = 1) (hsub : μ Set.univ ≤ 1) :
    μ Set.univ = 1 := by
  refine le_antisymm hsub ?_
  calc (1 : ENNReal) = μ {a} := hμ.symm
    _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)

/-- Rocq `pmf_plus_neq_SeriesC`: singleton masses at distinct points sum to
at most the total mass. -/
theorem pmf_plus_neq_SeriesC {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) {a a' : α} (h : a ≠ a') :
    μ {a} + μ {a'} ≤ μ Set.univ := by
  have hdisj : Disjoint ({a} : Set α) ({a'} : Set α) := Set.disjoint_singleton.mpr h
  rw [← measure_union hdisj (MeasurableSet.singleton a')]
  exact measure_mono (Set.subset_univ _)

/-- Rocq `pmf_1_not_eq`: if a singleton `{a}` has full mass, then singletons
at other points have zero mass. -/
theorem pmf_1_not_eq {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ : Measure α} {a b : α} (ha : μ {a} = 1) (hsub : μ Set.univ ≤ 1)
    (hne : b ≠ a) : μ {b} = 0 := by
  -- From `μ {a} + μ {b} ≤ μ univ = 1` and `μ {a} = 1`, deduce `μ {b} ≤ 0`.
  have h1 : (1 : ENNReal) + μ {b} ≤ 1 + 0 := by
    rw [add_zero]
    calc (1 : ENNReal) + μ {b}
        = μ {a} + μ {b} := by rw [ha]
      _ ≤ μ Set.univ := pmf_plus_neq_SeriesC μ hne.symm
      _ = 1 := pmf_1_eq_SeriesC ha hsub
  exact le_antisymm
    ((ENNReal.add_le_add_iff_left ENNReal.one_ne_top).mp h1) bot_le

/-- Rocq `pmf_1_eq_dret`: a sub-probability measure with a full-mass singleton
equals the Dirac at that point. -/
theorem pmf_1_eq_dret {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] {μ : Measure α} {a : α} (ha : μ {a} = 1) (hsub : μ Set.univ ≤ 1) :
    μ = Measure.dirac a := by
  refine Measure.ext_of_singleton fun c => ?_
  rw [Measure.dirac_apply' _ (MeasurableSet.singleton c)]
  by_cases hca : c = a
  · subst hca
    rw [ha]
    simp only [Set.indicator_of_mem, Set.mem_singleton_iff, Pi.one_apply]
  · rw [pmf_1_not_eq ha hsub hca]
    simp only [Set.indicator_of_notMem, Set.mem_singleton_iff, Ne.symm hca, not_false_eq_true]

/-- Rocq `pmf_1_supp_eq`: if a singleton `{a}` has full mass and `{a'}` has
positive mass, then `a = a'`. -/
theorem pmf_1_supp_eq {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ : Measure α} {a a' : α} (ha : μ {a} = 1) (hsub : μ Set.univ ≤ 1)
    (ha' : 0 < μ {a'}) : a = a' := by
  by_contra hne
  -- μ {a'} would then be 0, contradicting ha'.
  have : μ {a'} = 0 := pmf_1_not_eq ha hsub (fun h => hne h.symm)
  exact ha'.ne' this

/-! ## Ports from `theories/prob/distribution.v` §3 (dbind workhorses) -/

/-- Rocq `dbind_const`: binding with a constant kernel on a probability measure
gives that constant. -/
theorem dbind_const {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ₁ : Measure α} (hμ₁ : μ₁ Set.univ = 1) (μ₂ : Measure β) :
    (μ₁.bind (fun _ => μ₂)) = μ₂ := by
  ext s hs
  rw [Measure.bind_apply hs (aemeasurable_const), lintegral_const, hμ₁, mul_one]

/-- Rocq `dret_const`: binding with a constant `dirac` on a probability measure
is that `dirac`. Special case of `dbind_const`. -/
theorem dret_const {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} (hμ : μ Set.univ = 1) (b : β) :
    (μ.bind (fun _ => Measure.dirac b)) = Measure.dirac b :=
  dbind_const hμ (Measure.dirac b)

/-- Rocq `dbind_comm`: bind commutes across independent sampling (Fubini on
discrete spaces). -/
theorem dbind_comm {α β γ : Type _}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [MeasurableSingletonClass γ] [Countable γ]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β]
    [Countable α] [Countable β]
    (μ₁ : Measure α) (μ₂ : Measure β) (f : α → β → Measure γ) :
    μ₁.bind (fun a => μ₂.bind (fun b => f a b))
      = μ₂.bind (fun b => μ₁.bind (fun a => f a b)) := by
  refine Measure.ext_of_singleton fun c => ?_
  simp_rw [Measure.bind_apply (MeasurableSet.singleton _)
    Measurable.of_discrete.aemeasurable, lintegral_countable' _,
    ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun b => tsum_congr fun a => ?_
  ring

/-- Monotone convergence / swap between `tsum` and `⨆` over `ℕ` on a countable
index set. Mirrors `Cfg.tsum_iSup_of_monotone` (ProbLang/BigStepEquiv.lean) without
specializing to `Cfg`. -/
theorem ENNReal.tsum_iSup_of_monotone' {α : Type _}
    [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    {f : ℕ → α → ENNReal} (hf : ∀ a, Monotone (f · a)) :
    ∑' a, ⨆ n, f n a = ⨆ n, ∑' a, f n a := by
  simp_rw [← MeasureTheory.lintegral_count]
  exact MeasureTheory.lintegral_iSup (fun _ => Measurable.of_discrete)
    (fun _ _ hmn a => hf a hmn)

/-- Rocq `dbind_Sup_seq`: monotone convergence for `bind` on a fixed singleton.
If the kernel at each point is the pointwise monotone supremum of an
`ℕ`-indexed family, so is the bind. -/
theorem dbind_Sup_seq {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace α] [Countable α]
    (μ : Measure α) (f : Nat → α → Measure β) (f' : α → Measure β)
    (b : β)
    (hsup : ∀ a, (f' a) {b} = ⨆ n, (f n a) {b})
    (hmono : ∀ n a, (f n a) {b} ≤ (f (n + 1) a) {b}) :
    (μ.bind f') {b} = ⨆ n, (μ.bind (f n)) {b} := by
  simp_rw [Measure.bind_apply (MeasurableSet.singleton _)
    Measurable.of_discrete.aemeasurable, lintegral_countable' _, hsup, ENNReal.iSup_mul]
  refine ENNReal.tsum_iSup_of_monotone' fun a i j hij => ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  clear hsup
  induction hij with
  | refl => exact le_refl _
  | step _ ih => exact ih.trans (hmono _ a)

/-- Rocq `dbind_dret_pmf_map`: `bind μ (dirac ∘ f) {f a} = μ {a}` when `f` is
injective. Equivalently, this is `(Measure.map f μ) {f a} = μ {a}`. -/
theorem dbind_dret_pmf_map {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace α] [Countable α]
    (μ : Measure α) (a : α) {f : α → β} (hf : Function.Injective f) :
    (μ.bind (fun a' => Measure.dirac (f a'))) {f a} = μ {a} := by
  rw [Measure.bind_apply (MeasurableSet.singleton _) Measurable.of_discrete.aemeasurable,
      lintegral_countable' (fun a' => (Measure.dirac (f a')) {f a}),
      tsum_eq_single a]
  · rw [Measure.dirac_apply' _ (MeasurableSet.singleton _),
        Set.indicator_of_mem (Set.mem_singleton _), Pi.one_apply, one_mul]
  · intro a' hne
    have hfne : f a' ≠ f a := fun h => hne (hf h)
    rw [Measure.dirac_apply' _ (MeasurableSet.singleton _),
        Set.indicator_of_notMem (fun h => hfne (Set.mem_singleton_iff.mp h))]
    exact zero_mul _

/-- Rocq `dbind_dret_pmf_map_ne`: if `b` is not in the image of `f` on the
support of `μ`, then the pushforward singleton mass is zero. -/
theorem dbind_dret_pmf_map_ne {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace α] [Countable α]
    (μ : Measure α) {f : α → β} {b : β}
    (hne : ¬ ∃ a, 0 < μ {a} ∧ f a = b) :
    (μ.bind (fun a => Measure.dirac (f a))) {b} = 0 := by
  rw [Measure.bind_apply (MeasurableSet.singleton _) Measurable.of_discrete.aemeasurable,
      lintegral_countable' (fun a => (Measure.dirac (f a)) {b})]
  refine ENNReal.tsum_eq_zero.mpr fun a => ?_
  rw [Measure.dirac_apply' _ (MeasurableSet.singleton _)]
  by_cases hμa : 0 < μ {a}
  · have hne' : f a ≠ b := fun heq => hne ⟨a, hμa, heq⟩
    rw [Set.indicator_of_notMem (fun h => hne' (Set.mem_singleton_iff.mp h))]
    exact zero_mul _
  · rw [le_antisymm (not_lt.mp hμa) bot_le]
    exact mul_zero _

/-- Rocq `dbind_mass`: total mass of a bind is the integral of the kernel
masses. -/
theorem dbind_mass {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [DiscreteMeasurableSpace α]
    (μ : Measure α) (f : α → Measure β) :
    (μ.bind f) Set.univ = ∫⁻ a, (f a) Set.univ ∂μ :=
  Measure.bind_apply MeasurableSet.univ Measurable.of_discrete.aemeasurable

/-- Rocq `dbind_pos`: a bind has positive singleton mass iff some intermediate
point contributes positive mass. -/
theorem dbind_pos {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DiscreteMeasurableSpace α] [Countable α]
    (μ : Measure α) (f : α → Measure β) (b : β) :
    0 < (μ.bind f) {b} ↔ ∃ a, 0 < μ {a} ∧ 0 < (f a) {b} := by
  rw [Measure.bind_apply (MeasurableSet.singleton b) Measurable.of_discrete.aemeasurable,
      lintegral_countable' (fun a => (f a) {b})]
  simp only [pos_iff_ne_zero, ne_eq, ENNReal.tsum_eq_zero, not_forall, mul_eq_zero, not_or]
  exact ⟨fun ⟨a, hf, hμ⟩ => ⟨a, hμ, hf⟩, fun ⟨a, hμ, hf⟩ => ⟨a, hf, hμ⟩⟩

/-- Rocq `dbind_inhabited_ex`: positivity of bind from an existential witness. -/
theorem dbind_inhabited_ex {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [DiscreteMeasurableSpace α] [Countable α]
    (μ : Measure α) (f : α → Measure β)
    (h : ∃ a, 0 < μ {a} ∧ 0 < (f a) Set.univ) :
    0 < (μ.bind f) Set.univ := by
  obtain ⟨a, hμa, hfa⟩ := h
  rw [dbind_mass, lintegral_countable' (fun a => (f a) Set.univ),
      pos_iff_ne_zero, ne_eq, ENNReal.tsum_eq_zero, not_forall]
  refine ⟨a, ?_⟩
  rw [mul_eq_zero, not_or]
  exact ⟨hfa.ne', hμa.ne'⟩

/-- Rocq `dbind_inhabited`: positivity of bind from two separate positivities. -/
theorem dbind_inhabited {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [DiscreteMeasurableSpace α] [Countable α]
    (μ : Measure α) (f : α → Measure β)
    (hμ : 0 < μ Set.univ) (hf : ∀ a, 0 < (f a) Set.univ) :
    0 < (μ.bind f) Set.univ := by
  obtain ⟨a, _, hμa⟩ := Discrete.measure_pos_of_singleton_pos μ _ hμ
  exact dbind_inhabited_ex μ f ⟨a, hμa, hf a⟩

/-- Rocq `dbind_dret_pair_left`: bind into a pair on the left. -/
theorem dbind_dret_pair_left {α α' : Type _}
    [MeasurableSpace α] [MeasurableSpace α']
    [MeasurableSingletonClass α] [MeasurableSingletonClass α']
    [DiscreteMeasurableSpace α] [Countable α]
    (μ : Measure α) (a' : α') (b : α) :
    (μ.bind (fun a => Measure.dirac (a, a'))) {(b, a')} = μ {b} := by
  rw [Measure.bind_apply (MeasurableSet.singleton _) Measurable.of_discrete.aemeasurable,
      lintegral_countable' (fun a => (Measure.dirac (a, a')) {(b, a')}), tsum_eq_single b]
  · -- The surviving term at `a = b`: `dirac (b, a') {(b, a')} * μ {b} = μ {b}`.
    rw [Measure.dirac_apply' _ (MeasurableSet.singleton _),
        Set.indicator_of_mem (Set.mem_singleton _), Pi.one_apply, one_mul]
  · intro a hab
    -- Off-diagonal: `dirac (a, a') {(b, a')}` is zero since `(a, a') ≠ (b, a')`.
    have hnotmem : (a, a') ∉ ({(b, a')} : Set (α × α')) := by
      rw [Set.mem_singleton_iff, Prod.mk.injEq, not_and]; intro h; exact absurd h hab
    rw [Measure.dirac_apply' _ (MeasurableSet.singleton _),
        Set.indicator_of_notMem hnotmem, zero_mul]

/-- Rocq `dbind_dret_pair_right`: bind into a pair on the right. -/
theorem dbind_dret_pair_right {α α' : Type _}
    [MeasurableSpace α] [MeasurableSpace α']
    [MeasurableSingletonClass α] [MeasurableSingletonClass α']
    [DiscreteMeasurableSpace α'] [Countable α']
    (μ : Measure α') (a : α) (b : α') :
    (μ.bind (fun a' => Measure.dirac (a, a'))) {(a, b)} = μ {b} := by
  rw [Measure.bind_apply (MeasurableSet.singleton _) Measurable.of_discrete.aemeasurable,
      lintegral_countable' (fun a' => (Measure.dirac (a, a')) {(a, b)}), tsum_eq_single b]
  · rw [Measure.dirac_apply' _ (MeasurableSet.singleton _),
        Set.indicator_of_mem (Set.mem_singleton _), Pi.one_apply, one_mul]
  · intro x hxb
    have hnotmem : (a, x) ∉ ({(a, b)} : Set (α × α')) := by
      rw [Set.mem_singleton_iff, Prod.mk.injEq, not_and]; intro _; exact hxb
    rw [Measure.dirac_apply' _ (MeasurableSet.singleton _),
        Set.indicator_of_notMem hnotmem, zero_mul]

/-- Rocq `dbind_det`: if the base measure has total mass `1` and every kernel
on the support has total mass `1`, so does the bind. -/
theorem dbind_det {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [DiscreteMeasurableSpace α] [Countable α]
    (μ : Measure α) (f : α → Measure β)
    (hμ : μ Set.univ = 1)
    (hf : ∀ a, 0 < μ {a} → (f a) Set.univ = 1) :
    (μ.bind f) Set.univ = 1 := by
  rw [dbind_mass, lintegral_countable' (fun a => (f a) Set.univ)]
  have hrw : ∀ a, (f a) Set.univ * μ {a} = μ {a} := fun a => by
    by_cases hμa : 0 < μ {a}
    · rw [hf a hμa, one_mul]
    · rw [le_antisymm (not_lt.mp hμa) bot_le, mul_zero]
  simp_rw [hrw, ← Measure.univ_eq_tsum_singletons]; exact hμ

/-- Rocq `dbind_det_inv_l`: if the bind has a full-mass singleton, the base
measure has total mass `1`. Requires the kernels to be sub-probability. -/
theorem dbind_det_inv_l {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace α] [Countable α]
    (μ : Measure α) (f : α → Measure β) (b : β)
    (hsub : μ Set.univ ≤ 1) (hfsub : ∀ a, (f a) Set.univ ≤ 1)
    (hbind : (μ.bind f) {b} = 1) :
    μ Set.univ = 1 := by
  refine le_antisymm hsub ?_
  calc (1 : ENNReal) = (μ.bind f) {b} := hbind.symm
    _ ≤ (μ.bind f) Set.univ := measure_mono (Set.subset_univ _)
    _ = ∫⁻ a, (f a) Set.univ ∂μ := dbind_mass _ _
    _ ≤ ∫⁻ _, 1 ∂μ := lintegral_mono hfsub
    _ = μ Set.univ := by simp

/-- Rocq `dbind_det_inv_r`: if the bind has a full-mass singleton, every kernel
on the support has singleton mass `1`. -/
theorem dbind_det_inv_r {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace α] [Countable α]
    (μ : Measure α) (f : α → Measure β) (b : β)
    (hsub : μ Set.univ ≤ 1) (hfsub : ∀ a, (f a) Set.univ ≤ 1)
    (hbind : (μ.bind f) {b} = 1) :
    ∀ a, 0 < μ {a} → (f a) {b} = 1 := by
  have hbind' : ∑' a, (f a) {b} * μ {a} = 1 := by
    rw [← hbind, Measure.bind_apply (MeasurableSet.singleton _)
         Measurable.of_discrete.aemeasurable,
        lintegral_countable' (fun a => (f a) {b})]
  have htotal : ∑' a, μ {a} = 1 :=
    (Measure.univ_eq_tsum_singletons μ).symm.trans (dbind_det_inv_l μ f b hsub hfsub hbind)
  have hterm : ∀ a, (f a) {b} * μ {a} ≤ μ {a} := fun a => by
    calc (f a) {b} * μ {a}
        ≤ 1 * μ {a} := by gcongr; exact (measure_mono (Set.subset_univ _)).trans (hfsub a)
      _ = μ {a} := one_mul _
  have hpointwise : ∀ a, (f a) {b} * μ {a} = μ {a} := fun a => by
    by_contra hne
    have := ENNReal.tsum_lt_tsum (i := a) (hbind'.trans_ne ENNReal.one_ne_top)
      hterm (lt_of_le_of_ne (hterm a) hne)
    rw [hbind', htotal] at this
    exact lt_irrefl _ this
  intro a ha
  have hμa_ne_top : μ {a} ≠ ⊤ :=
    ((measure_mono (Set.subset_univ _)).trans hsub).trans_lt ENNReal.one_lt_top |>.ne
  exact (ENNReal.mul_left_inj ha.ne' hμa_ne_top).mp ((hpointwise a).trans (one_mul _).symm)

/-! ## Ports from `theories/prob/distribution.v` §7 tail (dmap) -/

/-- Rocq `dmap_elem_eq`: singleton mass of a pushforward at a point in the
range, when `f` is injective. -/
theorem dmap_elem_eq {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace α] [Countable α]
    (μ : Measure α) (a : α) {f : α → β} (hf : Function.Injective f) :
    (μ.map f) {f a} = μ {a} := by
  rw [Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton _)]
  congr 1
  ext x
  -- `x ∈ f ⁻¹' {f a} ↔ f x = f a ↔ x = a ↔ x ∈ {a}`
  rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_singleton_iff, hf.eq_iff]

/-- Rocq `dmap_elem_ne`: singleton mass of a pushforward at a point not in the
image of the support is zero. -/
theorem dmap_elem_ne {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace α] [Countable α]
    (μ : Measure α) {f : α → β} {b : β}
    (hne : ¬ ∃ a, 0 < μ {a} ∧ f a = b) :
    (μ.map f) {b} = 0 := by
  rw [Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton _),
      show (f ⁻¹' {b}) = ⋃ a ∈ {a | f a = b}, ({a} : Set α) from by ext x; simp]
  refine (measure_biUnion_null_iff (Set.to_countable _)).mpr fun a ha => ?_
  by_contra h
  exact hne ⟨a, lt_of_le_of_ne bot_le (Ne.symm h), ha⟩

/-- Rocq `dmap_rearrange`: if `f` is injective and `f` covers the support of
`μ₁`, and `μ₁ (f a) = μ₂ a`, then `μ₁ = map f μ₂`. -/
theorem dmap_rearrange {α : Type _}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [DiscreteMeasurableSpace α] [Countable α]
    (μ₁ μ₂ : Measure α) {f : α → α} (hf : Function.Injective f)
    (hcov : ∀ a, 0 < μ₁ {a} → ∃ a', f a' = a)
    (hpt : ∀ a, μ₁ {f a} = μ₂ {a}) :
    μ₁ = μ₂.map f := by
  refine Measure.ext_of_singleton fun a => ?_
  by_cases h : ∃ a', f a' = a
  · obtain ⟨a', rfl⟩ := h
    rw [dmap_elem_eq μ₂ a' hf, hpt]
  · have h1 : μ₁ {a} = 0 := by
      by_contra hne
      exact h (hcov a (lt_of_le_of_ne bot_le (Ne.symm hne)))
    rw [h1, dmap_elem_ne μ₂ (fun ⟨a', _, heq⟩ => h ⟨a', heq⟩)]

/-! ## Ports from `theories/prob/distribution.v` §15 (dunif/dunifP) -/

/-- Rocq `dunif N` at the Mathlib level: the uniform measure on `Fin N`. Only
nonempty, so `N ≥ 1`. -/
noncomputable def dunif (N : Nat) [NeZero N] : Measure (Fin N) :=
  (PMF.uniformOfFintype (Fin N)).toMeasure

/-- Rocq `dunifP N` = uniform on `Fin (N+1)`. -/
noncomputable def dunifP (N : Nat) : Measure (Fin (N + 1)) := dunif (N + 1)

/-- Rocq `dmap_unif_zero`: if `a` is outside the range of an injection from
`Fin N`, then the pushforward has zero mass at `a`. -/
theorem dmap_unif_zero {α : Type _}
    [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    [DiscreteMeasurableSpace α]
    (N : Nat) [NeZero N] {f : Fin N → α} {a : α}
    (hne : ¬ ∃ n, f n = a) :
    ((dunif N).map f) {a} = 0 := by
  refine dmap_elem_ne _ ?_
  rintro ⟨n, _, hfn⟩
  exact hne ⟨n, hfn⟩

/-- Rocq `dmap_unif_nonzero`: pushforward mass at a point in the range is `1/N`. -/
theorem dmap_unif_nonzero {α : Type _}
    [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    [DiscreteMeasurableSpace α]
    (N : Nat) [NeZero N] {f : Fin N → α} (hf : Function.Injective f) (n : Fin N) :
    ((dunif N).map f) {f n} = (N : ENNReal)⁻¹ := by
  rw [dmap_elem_eq _ n hf, dunif,
      PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
      PMF.uniformOfFintype_apply, Fintype.card_fin]

/-- Rocq `dunifP_pos`: all singletons of `dunifP N` have positive mass. -/
theorem dunifP_pos (N : Nat) (n : Fin (N + 1)) :
    0 < (dunifP N) {n} := by
  rw [dunifP, dunif,
      PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
      PMF.uniformOfFintype_apply, Fintype.card_fin]
  exact ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)

/-- Rocq `dunifP_mass`: total mass is `1`. -/
theorem dunifP_mass (N : Nat) : (dunifP N) Set.univ = 1 := by
  rw [dunifP, dunif]
  exact (PMF.toMeasure_apply_eq_one_iff _ MeasurableSet.univ).mpr
    (Set.subset_univ _)

/-- Rocq `dunifP_not_dzero`: `dunifP N` is not the zero measure. -/
theorem dunifP_not_dzero (N : Nat) : dunifP N ≠ 0 := fun h => by
  have h1 : (dunifP N) Set.univ = 1 := dunifP_mass N
  rw [h, Measure.coe_zero, Pi.zero_apply] at h1
  exact zero_ne_one h1

/-! ## Ports from `theories/prob/distribution.v` §14 (lim_distr) -/

/-- Rocq `lim_distr_pmf`: singleton application of an `⨆` of measures on a
countable discrete space. Generic replacement for `Exec.lean`'s
`Discrete.iSup_measure_apply` specialized to `Cfg`. -/
theorem lim_distr_pmf {α : Type _}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [DiscreteMeasurableSpace α] [Countable α]
    {f : ℕ → Measure α} {a : α} :
    (⨆ i, f i) {a} = ⨆ i, (f i) {a} := by
  apply le_antisymm
  · let w : α → ENNReal := fun x => ⨆ i, (f i) {x}
    let μ : Measure α := Measure.sum (fun (x : α) => w x • Measure.dirac x)
    have hval : μ {a} = w a := by
      simp only [μ, Measure.sum_apply _ MeasurableSet.of_discrete,
        Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.of_discrete,
        Set.mem_singleton_iff, Set.indicator_apply, Pi.one_apply]
      simp only [mul_ite, mul_one, mul_zero]
      rw [tsum_eq_single a (fun b hb => ite_eq_right hb)]
      rw [ite_eq_left rfl]
    have hub : ∀ i, f i ≤ μ := by
      intro i
      rw [Measure.le_iff]
      intro s hs
      rw [Measure.sum_apply _ hs]
      simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs,
        Set.indicator_apply, Pi.one_apply, mul_ite, mul_one, mul_zero]
      rw [← Measure.sum_smul_dirac (f i)]
      rw [Measure.sum_apply _ hs]
      simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs,
        Set.indicator_apply, Pi.one_apply, mul_ite, mul_one, mul_zero]
      apply ENNReal.tsum_le_tsum
      intro x
      split
      · exact le_iSup (fun i => (f i) {x}) i
      · exact le_refl _
    have := Measure.le_iff'.mp (iSup_le hub) ({a} : Set α)
    simp only [hval] at this
    exact this
  · exact iSup_le (fun i => by gcongr; exact le_iSup f i)

/-- Rocq `distr_scal`: scaling a sub-prob measure by `r ∈ [0, 1/mass]`. We use
Mathlib's `SMul` on measures directly; there is no separate "sub-prob scalar"
wrapper. -/
theorem distr_scal_mass {α : Type _} [MeasurableSpace α]
    (r : ENNReal) (μ : Measure α) :
    (r • μ) Set.univ = r * μ Set.univ := by
  rw [Measure.smul_apply, smul_eq_mul]

/-! ## Ports from `theories/prob/distribution.v` §13 (distr_le / order) -/

/-- Rocq `distr_le_dbind`: `bind` is monotone in both arguments (singleton form). -/
theorem distr_le_dbind {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace α] [Countable α]
    {μ₁ μ₂ : Measure α} {f₁ f₂ : α → Measure β}
    (hμ : ∀ a, μ₁ {a} ≤ μ₂ {a})
    (hf : ∀ a b, (f₁ a) {b} ≤ (f₂ a) {b}) :
    ∀ b, (μ₁.bind f₁) {b} ≤ (μ₂.bind f₂) {b} := fun b => by
  simp_rw [Measure.bind_apply (MeasurableSet.singleton _)
    Measurable.of_discrete.aemeasurable, lintegral_countable' _]
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul' (hf a b) (hμ a)

/-- Rocq `distr_le_dmap_1`: `map f` is monotone (singleton form). -/
theorem distr_le_dmap_1 {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [Countable α]
    {μ₁ μ₂ : Measure α} (f : α → β) (hμ : ∀ a, μ₁ {a} ≤ μ₂ {a}) :
    ∀ b, (μ₁.map f) {b} ≤ (μ₂.map f) {b} := fun b => by
  rw [Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton _),
      Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton _),
      show (f ⁻¹' ({b} : Set β)) = ⋃ a ∈ {a | f a = b}, ({a} : Set α) from by ext; simp]
  rw [measure_biUnion (Set.to_countable _)
      (fun i _ j _ hij => by simpa [Set.disjoint_singleton] using hij)
      (fun _ _ => MeasurableSet.singleton _),
    measure_biUnion (Set.to_countable _)
      (fun i _ j _ hij => by simpa [Set.disjoint_singleton] using hij)
      (fun _ _ => MeasurableSet.singleton _)]
  exact ENNReal.tsum_le_tsum fun a => hμ a

/-- Rocq `distr_le_dmap_2`: injective pushforward reflects `≤` pointwise. -/
theorem distr_le_dmap_2 {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace α] [Countable α]
    {μ₁ μ₂ : Measure α} {f : α → β} (hf : Function.Injective f)
    (h : ∀ b, (μ₁.map f) {b} ≤ (μ₂.map f) {b}) :
    ∀ a, μ₁ {a} ≤ μ₂ {a} := fun a => by
  have := h (f a)
  rwa [dmap_elem_eq μ₁ a hf, dmap_elem_eq μ₂ a hf] at this

/-! ## Ports from `theories/prob/distribution.v` §12 (products/marginals) -/

/-- Rocq `ddiag`: the diagonal distribution. -/
def ddiag {α : Type _} [MeasurableSpace α] (μ : Measure α) : Measure (α × α) :=
  μ.bind (fun a => Measure.dirac (a, a))

/-- Rocq `ddiag_pmf`: pointwise formula. -/
theorem ddiag_pmf {α : Type _}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [DiscreteMeasurableSpace α] [Countable α]
    (μ : Measure α) (a a' : α) :
    (ddiag μ) {(a, a')} = if a = a' then μ {a} else 0 := by
  rw [ddiag, Measure.bind_apply (MeasurableSet.singleton _)
        Measurable.of_discrete.aemeasurable,
      lintegral_countable' (fun x => (Measure.dirac (x, x)) {(a, a')})]
  by_cases hne : a = a'
  · subst hne
    rw [ite_eq_left rfl, tsum_eq_single a]
    · rw [Measure.dirac_apply' _ (MeasurableSet.singleton _),
          Set.indicator_of_mem (Set.mem_singleton _), Pi.one_apply, one_mul]
    · intro b hba
      have hnotmem : (b, b) ∉ ({(a, a)} : Set (α × α)) := by
        rw [Set.mem_singleton_iff, Prod.mk.injEq, not_and]; intro h _; exact hba h
      rw [Measure.dirac_apply' _ (MeasurableSet.singleton _),
          Set.indicator_of_notMem hnotmem, zero_mul]
  · rw [ite_eq_right hne]
    refine ENNReal.tsum_eq_zero.mpr fun x => ?_
    have hnotmem : (x, x) ∉ ({(a, a')} : Set (α × α)) := by
      rw [Set.mem_singleton_iff, Prod.mk.injEq, not_and]
      rintro rfl; exact hne
    rw [Measure.dirac_apply' _ (MeasurableSet.singleton _),
        Set.indicator_of_notMem hnotmem, zero_mul]

/-- Rocq `dprod`: independent product of two measures via bind/dret. -/
def dprod {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    (μ₁ : Measure α) (μ₂ : Measure β) : Measure (α × β) :=
  μ₁.bind (fun a => μ₂.bind (fun b => Measure.dirac (a, b)))

/-- Rocq `dprod_pmf`: pointwise mass of a product. -/
theorem dprod_pmf {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β]
    [Countable α] [Countable β]
    (μ₁ : Measure α) (μ₂ : Measure β) (a : α) (b : β) :
    (dprod μ₁ μ₂) {(a, b)} = μ₁ {a} * μ₂ {b} := by
  have key : ∀ x : α, (μ₂.bind (fun y => Measure.dirac (x, y))) {(a, b)}
               = if x = a then μ₂ {b} else 0 := by
    intro x
    rw [Measure.bind_apply (MeasurableSet.singleton _) Measurable.of_discrete.aemeasurable,
        lintegral_countable' (fun y => (Measure.dirac (x, y)) {(a, b)})]
    by_cases hxa : x = a
    · rw [hxa, ite_eq_left rfl, tsum_eq_single b]
      · rw [Measure.dirac_apply' _ (MeasurableSet.singleton _),
            Set.indicator_of_mem (Set.mem_singleton _), Pi.one_apply, one_mul]
      · intro y hyb
        have hnotmem : (a, y) ∉ ({(a, b)} : Set (α × β)) := by
          rw [Set.mem_singleton_iff, Prod.mk.injEq, not_and]; intro _; exact hyb
        rw [Measure.dirac_apply' _ (MeasurableSet.singleton _),
            Set.indicator_of_notMem hnotmem, zero_mul]
    · rw [ite_eq_right hxa]
      refine ENNReal.tsum_eq_zero.mpr fun y => ?_
      have hnotmem : (x, y) ∉ ({(a, b)} : Set (α × β)) := by
        rw [Set.mem_singleton_iff, Prod.mk.injEq, not_and]
        intro hxa'; exact absurd hxa' hxa
      rw [Measure.dirac_apply' _ (MeasurableSet.singleton _),
          Set.indicator_of_notMem hnotmem, zero_mul]
  rw [dprod, Measure.bind_apply (MeasurableSet.singleton _)
        Measurable.of_discrete.aemeasurable,
      lintegral_countable' (fun x => (μ₂.bind (fun y => Measure.dirac (x, y))) {(a, b)})]
  simp_rw [key]
  rw [tsum_eq_single a]
  · rw [ite_eq_left rfl, mul_comm]
  · intro x hxa
    rw [ite_eq_right hxa, zero_mul]

/-- Rocq `dprod_pos`: support of the product is the conjunction of supports. -/
theorem dprod_pos {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β]
    [Countable α] [Countable β]
    (μ₁ : Measure α) (μ₂ : Measure β) (a : α) (b : β) :
    0 < (dprod μ₁ μ₂) {(a, b)} ↔ 0 < μ₁ {a} ∧ 0 < μ₂ {b} := by
  rw [dprod_pmf]
  simp only [pos_iff_ne_zero, ne_eq, mul_eq_zero, not_or]

/-- Rocq `dprod_mass`: total mass of a product. -/
theorem dprod_mass {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β]
    [Countable α] [Countable β]
    (μ₁ : Measure α) (μ₂ : Measure β) :
    (dprod μ₁ μ₂) Set.univ = μ₁ Set.univ * μ₂ Set.univ := by
  rw [dprod, dbind_mass]
  have h1 : ∀ a : α, (μ₂.bind (fun b => Measure.dirac (a, b))) Set.univ = μ₂ Set.univ := by
    intro a
    rw [dbind_mass]
    -- Each `dirac (a, b) Set.univ = 1`, so the integral is `μ₂ Set.univ * 1`.
    have hall : ∀ b : β, (Measure.dirac (a, b)) Set.univ = (1 : ENNReal) := fun b => by
      rw [Measure.dirac_apply' _ MeasurableSet.univ,
          Set.indicator_of_mem (Set.mem_univ _)]; rfl
    simp_rw [hall]
    rw [lintegral_const, one_mul]
  simp_rw [h1]
  rw [lintegral_const, mul_comm]

/-- Rocq `dswap`: coordinate swap. -/
def dswap {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure (α × β)) : Measure (β × α) :=
  μ.map Prod.swap

/-- Rocq `dswap_pos`: swap preserves singleton masses. -/
theorem dswap_pos {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace (α × β)] [Countable (α × β)]
    (μ : Measure (α × β)) (a : α) (b : β) :
    (dswap μ) {(b, a)} = μ {(a, b)} := by
  rw [dswap, Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton _)]
  congr 1
  ext ⟨x, y⟩
  constructor
  · rintro ⟨rfl, rfl⟩; rfl
  · rintro ⟨rfl, rfl⟩; rfl

/-- Rocq `lmarg`: left marginal. -/
def lmarg {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure (α × β)) : Measure α :=
  μ.map Prod.fst

/-- Rocq `rmarg`: right marginal. -/
def rmarg {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure (α × β)) : Measure β :=
  μ.map Prod.snd

/-- Rocq `lmarg_pmf`. -/
theorem lmarg_pmf {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace (α × β)] [Countable β]
    (μ : Measure (α × β)) (a : α) :
    (lmarg μ) {a} = ∑' b, μ {(a, b)} := by
  have hunion : (Prod.fst ⁻¹' ({a} : Set α)) = ⋃ b, ({(a, b)} : Set (α × β)) := by
    ext ⟨x, y⟩
    constructor
    · intro h
      have hxa : x = a := Set.mem_singleton_iff.mp h
      exact Set.mem_iUnion.mpr ⟨y, by rw [hxa]; rfl⟩
    · intro h
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp h
      rw [Set.mem_singleton_iff, Prod.mk.injEq] at hb
      exact Set.mem_singleton_iff.mpr hb.1
  have hdisj : Pairwise (Function.onFun Disjoint fun b : β => ({(a, b)} : Set (α × β))) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_singleton, Ne, Prod.mk.injEq, not_and]
    intro _; exact hij
  rw [lmarg, Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton _),
      hunion, measure_iUnion hdisj (fun _ => MeasurableSet.singleton _)]

/-- Rocq `rmarg_pmf`. -/
theorem rmarg_pmf {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace (α × β)] [Countable α]
    (μ : Measure (α × β)) (b : β) :
    (rmarg μ) {b} = ∑' a, μ {(a, b)} := by
  have hunion : (Prod.snd ⁻¹' ({b} : Set β)) = ⋃ a, ({(a, b)} : Set (α × β)) := by
    ext ⟨x, y⟩
    constructor
    · intro h
      have hyb : y = b := Set.mem_singleton_iff.mp h
      exact Set.mem_iUnion.mpr ⟨x, by rw [hyb]; rfl⟩
    · intro h
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp h
      rw [Set.mem_singleton_iff, Prod.mk.injEq] at ha
      exact Set.mem_singleton_iff.mpr ha.2
  have hdisj : Pairwise (Function.onFun Disjoint fun a : α => ({(a, b)} : Set (α × β))) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_singleton, Ne, Prod.mk.injEq, not_and]
    intro h; exact absurd h hij
  rw [rmarg, Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton _),
      hunion, measure_iUnion hdisj (fun _ => MeasurableSet.singleton _)]

/-- Rocq `lmarg_dprod_pmf`: marginal of a product, pointwise. -/
theorem lmarg_dprod_pmf {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β]
    [DiscreteMeasurableSpace (α × β)]
    [Countable α] [Countable β]
    (μ₁ : Measure α) (μ₂ : Measure β) (a : α) :
    (lmarg (dprod μ₁ μ₂)) {a} = μ₁ {a} * μ₂ Set.univ := by
  rw [lmarg_pmf]
  simp_rw [dprod_pmf]
  rw [ENNReal.tsum_mul_left, Measure.univ_eq_tsum_singletons]

/-- Rocq `rmarg_dprod_pmf`. -/
theorem rmarg_dprod_pmf {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β]
    [DiscreteMeasurableSpace (α × β)]
    [Countable α] [Countable β]
    (μ₁ : Measure α) (μ₂ : Measure β) (b : β) :
    (rmarg (dprod μ₁ μ₂)) {b} = μ₂ {b} * μ₁ Set.univ := by
  rw [rmarg_pmf]
  simp_rw [dprod_pmf]
  rw [ENNReal.tsum_mul_right, Measure.univ_eq_tsum_singletons, mul_comm]

/-- Rocq `lmarg_dprod`: left marginal of a product on a prob measure. -/
theorem lmarg_dprod {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β]
    [DiscreteMeasurableSpace (α × β)]
    [Countable α] [Countable β]
    (μ₁ : Measure α) (μ₂ : Measure β) (hμ₂ : μ₂ Set.univ = 1) :
    lmarg (dprod μ₁ μ₂) = μ₁ := by
  refine Measure.ext_of_singleton fun a => ?_
  rw [lmarg_dprod_pmf, hμ₂, mul_one]

/-- Rocq `rmarg_dprod`: right marginal of a product on a prob measure. -/
theorem rmarg_dprod {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β]
    [DiscreteMeasurableSpace (α × β)]
    [Countable α] [Countable β]
    (μ₁ : Measure α) (μ₂ : Measure β) (hμ₁ : μ₁ Set.univ = 1) :
    rmarg (dprod μ₁ μ₂) = μ₂ := by
  refine Measure.ext_of_singleton fun b => ?_
  rw [rmarg_dprod_pmf, hμ₁, mul_one]

/-- Rocq `ddiag_lmarg`: left marginal of the diagonal. -/
theorem ddiag_lmarg {α : Type _}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [DiscreteMeasurableSpace α] [Countable α]
    [DiscreteMeasurableSpace (α × α)]
    (μ : Measure α) :
    lmarg (ddiag μ) = μ := by
  refine Measure.ext_of_singleton fun a => ?_
  rw [lmarg_pmf]
  simp_rw [ddiag_pmf]
  rw [tsum_eq_single a]
  · rw [ite_eq_left rfl]
  · intro b hba
    exact ite_eq_right (fun h => hba h.symm)

/-- Rocq `ddiag_rmarg`: right marginal of the diagonal. -/
theorem ddiag_rmarg {α : Type _}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [DiscreteMeasurableSpace α] [Countable α]
    [DiscreteMeasurableSpace (α × α)]
    (μ : Measure α) :
    rmarg (ddiag μ) = μ := by
  refine Measure.ext_of_singleton fun a => ?_
  rw [rmarg_pmf]
  simp_rw [ddiag_pmf]
  rw [tsum_eq_single a]
  · rw [ite_eq_left rfl]
  · intro b hba
    exact ite_eq_right hba

/-- Rocq `lmarg_dswap`. -/
theorem lmarg_dswap {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace (α × β)] [DiscreteMeasurableSpace (β × α)]
    [Countable β]
    (μ : Measure (α × β)) :
    lmarg (dswap μ) = rmarg μ := by
  rw [lmarg, dswap, rmarg, Measure.map_map Measurable.of_discrete Measurable.of_discrete]; rfl

/-- Rocq `rmarg_dswap`. -/
theorem rmarg_dswap {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace (α × β)] [DiscreteMeasurableSpace (β × α)]
    [Countable α]
    (μ : Measure (α × β)) :
    rmarg (dswap μ) = lmarg μ := by
  rw [rmarg, dswap, lmarg, Measure.map_map Measurable.of_discrete Measurable.of_discrete]; rfl

/-! ## Ports from `theories/prob/distribution.v` §9 (iterM) -/

/-- Rocq `iterM`: iterated monadic bind, `n`-fold composition of a kernel. -/
def iterM {α : Type _} [MeasurableSpace α] (n : Nat) (f : α → Measure α) (a : α) :
    Measure α :=
  match n with
  | 0 => Measure.dirac a
  | n + 1 => (f a).bind (iterM n f)

@[simp] theorem iterM_O {α : Type _} [MeasurableSpace α] (f : α → Measure α) (a : α) :
    iterM 0 f a = Measure.dirac a := rfl

@[simp] theorem iterM_Sn {α : Type _} [MeasurableSpace α] (f : α → Measure α) (a : α) (n : Nat) :
    iterM (n + 1) f a = (f a).bind (iterM n f) := rfl

/-- Rocq `iterM_plus`: iterating by `n + m` equals composing iterations. -/
theorem iterM_plus {α : Type _}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [DiscreteMeasurableSpace α] [Countable α]
    (f : α → Measure α) (a : α) (n m : Nat) :
    iterM (n + m) f a = (iterM n f a).bind (iterM m f) := by
  induction n generalizing a with
  | zero =>
    rw [Nat.zero_add, iterM_O, Measure.dirac_bind Measurable.of_discrete]
  | succ n ih =>
    rw [Nat.succ_add, iterM_Sn, iterM_Sn,
        Measure.bind_bind Measurable.of_discrete.aemeasurable
          Measurable.of_discrete.aemeasurable]
    exact congrArg _ (funext ih)

/-- Rocq `iterM_mono`: iterated bind is monotone at a fixed endpoint singleton
in its kernel argument. -/
theorem iterM_mono {α : Type _}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [DiscreteMeasurableSpace α] [Countable α]
    (f g : α → Measure α) (n : Nat) (a a' : α)
    (h : ∀ x y : α, (f x) {y} ≤ (g x) {y}) :
    (iterM n f a) {a'} ≤ (iterM n g a) {a'} := by
  induction n generalizing a with
  | zero => exact le_refl _
  | succ n ih =>
    simp_rw [iterM_Sn, Measure.bind_apply (MeasurableSet.singleton _)
      Measurable.of_discrete.aemeasurable, lintegral_countable' _]
    exact ENNReal.tsum_le_tsum fun x => mul_le_mul' (ih x) (h a x)

/-! ## Ports from `theories/prob/distribution.v` §8 (strength) -/

/-- Rocq `strength_l`: monadic strength on the left. -/
def strength_l {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    (a : α) (μ : Measure β) : Measure (α × β) :=
  μ.map (fun b => (a, b))

/-- Rocq `strength_r`: monadic strength on the right. -/
def strength_r {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (b : β) : Measure (α × β) :=
  μ.map (fun a => (a, b))

/-- Rocq `dbind_strength_l`. -/
theorem dbind_strength_l {α β δ : Type _}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace δ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β]
    [DiscreteMeasurableSpace (α × β)] [Countable β]
    (f : α × β → Measure δ) (a : α) (μ : Measure β) :
    (strength_l a μ).bind f = μ.bind (fun b => f (a, b)) := by
  ext s hs
  rw [strength_l, Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
      lintegral_map Measurable.of_discrete Measurable.of_discrete,
      Measure.bind_apply hs Measurable.of_discrete.aemeasurable]

/-- Rocq `dbind_strength_r`. -/
theorem dbind_strength_r {α β δ : Type _}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace δ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β]
    [DiscreteMeasurableSpace (α × β)] [Countable α]
    (f : α × β → Measure δ) (μ : Measure α) (b : β) :
    (strength_r μ b).bind f = μ.bind (fun a => f (a, b)) := by
  ext s hs
  rw [strength_r, Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
      lintegral_map Measurable.of_discrete Measurable.of_discrete,
      Measure.bind_apply hs Measurable.of_discrete.aemeasurable]

/-- Rocq `strength_l_dbind`: strength_l distributes over bind. -/
theorem strength_l_dbind {α β δ : Type _}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace δ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [MeasurableSingletonClass δ]
    [DiscreteMeasurableSpace β] [DiscreteMeasurableSpace δ] [Countable β]
    (f : β → Measure δ) (a : α) (μ : Measure β) :
    strength_l a (μ.bind f) = μ.bind (fun b => strength_l a (f b)) := by
  unfold strength_l
  ext s hs
  rw [Measure.map_apply Measurable.of_discrete hs,
      Measure.bind_apply (Measurable.of_discrete hs)
        Measurable.of_discrete.aemeasurable,
      Measure.bind_apply hs Measurable.of_discrete.aemeasurable]
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only
  rw [Measure.map_apply Measurable.of_discrete hs]

/-- Rocq `strength_r_dbind`: strength_r distributes over bind. -/
theorem strength_r_dbind {α β δ : Type _}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace δ]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [MeasurableSingletonClass δ]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace δ] [Countable α]
    (f : α → Measure δ) (μ : Measure α) (b : β) :
    strength_r (μ.bind f) b = μ.bind (fun a => strength_r (f a) b) := by
  unfold strength_r
  ext s hs
  rw [Measure.map_apply Measurable.of_discrete hs,
      Measure.bind_apply (Measurable.of_discrete hs)
        Measurable.of_discrete.aemeasurable,
      Measure.bind_apply hs Measurable.of_discrete.aemeasurable]
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only
  rw [Measure.map_apply Measurable.of_discrete hs]

/-! ## Ports from `theories/prob/distribution.v` §4 (prob) -/

/-- Rocq `prob`: probability of a boolean event, as the measure of its true
preimage. -/
def prob {α : Type _} [MeasurableSpace α] (μ : Measure α) (P : α → Bool) : ENNReal :=
  μ {a | P a = true}

/-- Rocq `prob_dbind`: pushforward of `prob` through a monadic bind. -/
theorem prob_dbind {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Countable β]
    [DiscreteMeasurableSpace α] [Countable α]
    (μ : Measure α) (f : α → Measure β) (P : β → Bool) :
    prob (μ.bind f) P = ∫⁻ a, prob (f a) P ∂μ :=
  Measure.bind_apply
    (show MeasurableSet {b | P b = true} from MeasurableSet.of_discrete)
    Measurable.of_discrete.aemeasurable

/-- Rocq `union_bound`: probability of a disjunction is at most the sum. -/
theorem union_bound {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) (P Q : α → Bool) :
    prob μ (fun a => P a || Q a) ≤ prob μ P + prob μ Q := by
  have hsub : {a | (P a || Q a) = true} ⊆ {a | P a = true} ∪ {a | Q a = true} := by
    intro a ha
    -- `ha : (P a || Q a) = true`, which (by `Bool.or_eq_true`) says `P a = true ∨ Q a = true`.
    rcases Bool.or_eq_true_iff.mp ha with hPa | hQa
    · exact Or.inl hPa
    · exact Or.inr hQa
  calc prob μ (fun a => P a || Q a)
      = μ {a | (P a || Q a) = true} := rfl
    _ ≤ μ ({a | P a = true} ∪ {a | Q a = true}) := measure_mono hsub
    _ ≤ μ {a | P a = true} + μ {a | Q a = true} := measure_union_le _ _
    _ = prob μ P + prob μ Q := rfl

/-- Rocq `prob_Sup_seq`: monotone convergence for `prob`. -/
theorem prob_Sup_seq {α : Type _}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [DiscreteMeasurableSpace α] [Countable α]
    (μ : Measure α) (μ' : Nat → Measure α) (P : α → Bool)
    (hsup : ∀ a, μ {a} = ⨆ n, (μ' n) {a})
    (hmono : ∀ n a, (μ' n) {a} ≤ (μ' (n + 1)) {a}) :
    prob μ P = ⨆ n, prob (μ' n) P := by
  -- Express `prob` as a tsum over the true-preimage support, then use MCT.
  have hprob : ∀ (ν : Measure α),
      prob ν P = ∑' a, if P a = true then ν {a} else 0 := by
    intro ν
    have huniv : ({a | P a = true} : Set α) = ⋃ a ∈ {a | P a = true}, ({a} : Set α) := by
      ext x; constructor
      · intro hx; exact Set.mem_biUnion hx (Set.mem_singleton _)
      · intro hx
        obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp hx
        exact (Set.mem_singleton_iff.mp hxa) ▸ ha
    have hdisj : ({a | P a = true} : Set α).Pairwise
        (fun i j => Disjoint ({i} : Set α) ({j} : Set α)) := by
      intro i _ j _ hij; exact Set.disjoint_singleton.mpr hij
    rw [prob, huniv,
        measure_biUnion (Set.to_countable _) hdisj
          (fun _ _ => MeasurableSet.singleton _),
        tsum_subtype {a | P a = true} (fun a => ν {a})]
    refine tsum_congr fun a => ?_
    by_cases hP : P a = true
    · rw [Set.indicator_of_mem (show a ∈ {a | P a = true} from hP), ite_eq_left hP]
    · rw [Set.indicator_of_notMem (show a ∉ {a | P a = true} from hP), ite_eq_right hP]
  simp_rw [hprob]
  -- LHS: ∑' a, (if P a then μ {a} else 0)
  --    = ∑' a, (if P a then ⨆ n, (μ' n) {a} else 0)       [using hsup]
  --    = ∑' a, ⨆ n, (if P a then (μ' n) {a} else 0)        [pull in the iSup]
  --    = ⨆ n, ∑' a, (if P a then (μ' n) {a} else 0)        [MCT]
  have h1 : ∀ a, (if P a = true then μ {a} else 0) =
                 ⨆ n, (if P a = true then (μ' n) {a} else 0) := by
    intro a
    by_cases hP : P a = true
    · simp only [ite_eq_left hP]; exact hsup a
    · simp only [ite_eq_right hP, iSup_const]
  simp_rw [h1]
  rw [ENNReal.tsum_iSup_of_monotone'
    (fun a i j hij => by
      by_cases hP : P a = true
      · simp only [ite_eq_left hP]
        clear h1 hprob
        induction hij with
        | refl => exact le_refl _
        | step _ ih => exact ih.trans (hmono _ a)
      · show (if P a = true then (μ' i) {a} else 0) ≤ (if P a = true then (μ' j) {a} else 0)
        rw [ite_eq_right hP, ite_eq_right hP])]

/-- Rocq `SeriesC_zero_dzero`: a measure with zero total mass is the zero
measure. (We take the countable-singleton extensionality view.) -/
theorem SeriesC_zero_dzero {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] {μ : Measure α} (h : μ Set.univ = 0) : μ = 0 := by
  refine Measure.ext_of_singleton fun a => ?_
  rw [nonpos_iff_eq_zero.mp ((measure_mono (Set.subset_univ _)).trans_eq h),
      Measure.coe_zero, Pi.zero_apply]

/-- Rocq `not_dzero_gt_0`: a nonzero measure has positive total mass. -/
theorem not_dzero_gt_0 {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] {μ : Measure α} (h : μ ≠ 0) : 0 < μ Set.univ :=
  pos_iff_ne_zero.mpr fun hzero => h (SeriesC_zero_dzero hzero)

/-- Existential form: a nonzero measure has some singleton with positive mass. -/
theorem not_dzero_exists_pos {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] {μ : Measure α} (h : μ ≠ 0) : ∃ a, 0 < μ {a} :=
  let ⟨a, _, ha⟩ := Discrete.measure_pos_of_singleton_pos μ _ (not_dzero_gt_0 h)
  ⟨a, ha⟩

/-- Rocq `dbind_dzero_strong`: a bind is zero iff every kernel on the support
is zero. (The "only if" direction: from the pointwise hypothesis we conclude
the bind is zero; the converse is often easier via the singleton formulation
and is not usually required.) -/
theorem dbind_dzero_strong {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Countable β]
    [DiscreteMeasurableSpace α] [Countable α]
    (μ : Measure α) (f : α → Measure β)
    (h : ∀ a, 0 < μ {a} → f a = 0) :
    μ.bind f = 0 := by
  refine SeriesC_zero_dzero ?_
  rw [dbind_mass, lintegral_countable' (fun a => (f a) Set.univ)]
  refine ENNReal.tsum_eq_zero.mpr fun a => ?_
  by_cases hμa : 0 < μ {a}
  · rw [h a hμa]
    show (0 : Measure β) Set.univ * μ {a} = 0
    rw [Measure.coe_zero, Pi.zero_apply, zero_mul]
  · rw [le_antisymm (not_lt.mp hμa) bot_le, mul_zero]

/-- Rocq `dmap_dzero_inv`: if a pushforward is the zero measure, the source is
zero. -/
theorem dmap_dzero_inv {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]
    [Countable α]
    (f : α → β) {μ : Measure α} (h : μ.map f = 0) : μ = 0 := by
  refine SeriesC_zero_dzero ?_
  have h1 : (μ.map f) Set.univ = 0 := by
    rw [h, Measure.coe_zero, Pi.zero_apply]
  rwa [Measure.map_apply_of_aemeasurable Measurable.of_discrete.aemeasurable
        MeasurableSet.univ, Set.preimage_univ] at h1

/-- Rocq `dbind_eq`: congruence for `dbind` under pointwise equality on the
support and total agreement of the base measures. -/
theorem dbind_eq {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [Countable β]
    [DiscreteMeasurableSpace α] [Countable α]
    {f g : α → Measure β} {μ₁ μ₂ : Measure α}
    (hfg : ∀ a, 0 < μ₁ {a} → f a = g a)
    (hμ : μ₁ = μ₂) :
    μ₁.bind f = μ₂.bind g := by
  subst hμ
  refine Measure.ext_of_singleton fun b => ?_
  simp_rw [Measure.bind_apply (MeasurableSet.singleton _)
    Measurable.of_discrete.aemeasurable, lintegral_countable' _]
  refine tsum_congr fun a => ?_
  by_cases hμa : 0 < μ₁ {a}
  · rw [hfg a hμa]
  · rw [le_antisymm (not_lt.mp hμa) bot_le, mul_zero, mul_zero]

end
