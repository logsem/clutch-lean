module

public meta import Metrology.Meta.Discrete
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.Probability.Distributions.Uniform
public import Metrology.Couplings.Measure

@[expose] public section

noncomputable section
open Classical MeasureTheory ProbabilityTheory Measure

/-! # Measure-theory support for ProbLang

Support predicates for measures (`Possible`, `Concentrated`, `IsAtomicSupport`) used by the program
logics, and measurability of `Option`, `List`, Σ-types and kernels used by `CoreMeasures`. -/

/-! ## `Possible`: a positive-mass point of a measure -/

/-- `ρ` has positive mass under `μ`, stated without `{ρ}` so it needs no `MeasurableSingletonClass`
(equivalent to `0 < μ {ρ}` under it, `possible_iff_pos`). -/
def Possible {α : Type _} [MeasurableSpace α] (ρ : α) (μ : Measure α) : Prop :=
  ∃ p : ENNReal, 0 < p ∧ p • dirac ρ ≤ μ

theorem Possible.mono {α : Type _} [MeasurableSpace α] {ρ : α} {μ ν : Measure α}
    (hμν : μ ≤ ν) : Possible ρ μ → Possible ρ ν
  | ⟨p, hp, hle⟩ => ⟨p, hp, hle.trans hμν⟩

theorem Possible.of_dirac_le {α : Type _} [MeasurableSpace α] {ρ : α} {μ : Measure α}
    (h : dirac ρ ≤ μ) : Possible ρ μ :=
  ⟨1, one_pos, by rwa [one_smul]⟩

theorem Possible.ne_zero {α : Type _} [MeasurableSpace α] {ρ : α} {μ : Measure α}
    (h : Possible ρ μ) : μ ≠ 0 := by
  obtain ⟨p, hp, hle⟩ := h
  rintro rfl
  have hp0 : p ≤ 0 := by simpa [Measure.smul_apply] using hle Set.univ
  exact not_le.mpr hp hp0

theorem Possible.of_dirac_eq {α : Type _} [MeasurableSpace α] {ρ : α} {μ : Measure α}
    (h : μ = dirac ρ) : Possible ρ μ :=
  Possible.of_dirac_le (h ▸ le_refl _)

theorem Possible.map {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {g : α → β} (hg : Measurable g) {ρ : α} {μ : Measure α} :
    Possible ρ μ → Possible (g ρ) (μ.map g)
  | ⟨p, hp, hle⟩ => ⟨p, hp, by
      rw [Measure.le_iff]
      intro s hs
      rw [Measure.map_apply hg hs, Measure.smul_apply, dirac_apply' _ hs, smul_eq_mul]
      by_cases hmem : g ρ ∈ s
      · rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
        have hle' := Measure.le_iff.mp hle (g ⁻¹' s) (hg hs)
        simpa [dirac_apply' _ (hg hs), Set.indicator_of_mem (show ρ ∈ g ⁻¹' s from hmem)]
          using hle'
      · rw [Set.indicator_of_notMem hmem]; simp⟩

theorem possible_iff_pos {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α]
    {ρ : α} {μ : Measure α} : Possible ρ μ ↔ 0 < μ {ρ} := by
  have hdir : (dirac ρ) {ρ} = 1 := by
    rw [dirac_apply' _ (measurableSet_singleton ρ)]; simp
  constructor
  · rintro ⟨p, hp, hle⟩
    have hle' := Measure.le_iff.mp hle {ρ} (measurableSet_singleton ρ)
    rw [Measure.smul_apply, hdir, smul_eq_mul, mul_one] at hle'
    exact hp.trans_le hle'
  · intro hpos
    refine ⟨μ {ρ}, hpos, ?_⟩
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.smul_apply, dirac_apply' _ hs, smul_eq_mul]
    by_cases hρs : ρ ∈ s
    · rw [Set.indicator_of_mem hρs]
      simp only [Pi.one_apply, mul_one]
      exact measure_mono (Set.singleton_subset_iff.mpr hρs)
    · rw [Set.indicator_of_notMem hρs]; simp

/-- A positive-mass point of an injective pushforward comes from a positive-mass point.
Injectivity is essential: a constant `f` collapses non-atomic mass onto one point. -/
theorem map_singleton_pos {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {f : α → β} {μ : Measure α} {b : β} (hf : Measurable f) (hinj : Function.Injective f)
    (h : 0 < (μ.map f) {b}) :
    ∃ a, f a = b ∧ 0 < μ {a} := by
  rw [Measure.map_apply hf (measurableSet_singleton b)] at h
  by_cases hb : ∃ a, f a = b
  · obtain ⟨a, ha⟩ := hb
    refine ⟨a, ha, ?_⟩
    have hpre : f ⁻¹' {b} = {a} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hx => hinj (hx.trans ha.symm), fun hx => hx ▸ ha⟩
    rwa [hpre] at h
  · exfalso
    rw [Set.preimage_singleton_eq_empty.mpr hb] at h
    simp at h

namespace ProbLang

/-! ### `Concentrated`: the unary support-lifting

Unlike `Possible`, concentration also describes diffuse measures: a pushforward is
concentrated on the image of its source support (`Concentrated.map`). -/

/-- `μ` gives zero mass to the complement of `S`. -/
def Concentrated {α : Type _} [MeasurableSpace α] (μ : Measure α) (S : Set α) : Prop :=
  μ Sᶜ = 0

theorem Concentrated.univ {α : Type _} [MeasurableSpace α] {μ : Measure α} :
    Concentrated μ Set.univ := by simp [Concentrated]

theorem Concentrated.zero {α : Type _} [MeasurableSpace α] {S : Set α} :
    Concentrated (0 : Measure α) S := by simp [Concentrated]

theorem Concentrated.mono {α : Type _} [MeasurableSpace α] {μ : Measure α} {S T : Set α}
    (hST : S ⊆ T) (h : Concentrated μ S) : Concentrated μ T :=
  MeasureTheory.measure_mono_null (Set.compl_subset_compl.mpr hST) h

theorem Concentrated.dirac {α : Type _} [MeasurableSpace α] {a : α} {S : Set α}
    (hS : MeasurableSet S) (h : a ∈ S) : Concentrated (Measure.dirac a) S := by
  unfold Concentrated
  rw [Measure.dirac_apply' a hS.compl, Set.indicator_of_notMem (by simpa using h)]

theorem Concentrated.map {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f) {ν : Measure α} {T : Set α}
    (hfT : MeasurableSet (f '' T)) (h : Concentrated ν T) :
    Concentrated (ν.map f) (f '' T) := by
  unfold Concentrated at h ⊢
  rw [Measure.map_apply hf hfT.compl]
  refine MeasureTheory.measure_mono_null (fun x hx => ?_) h
  simp only [Set.mem_preimage, Set.mem_compl_iff] at hx ⊢
  exact fun hxT => hx ⟨x, hxT, rfl⟩

/-! ### Pure atomicity -/

/-- `μ` is purely atomic: the points of zero mass carry no mass together, so `μ` is concentrated
on its atoms (`concentrated_atoms`). Every head step but `urand` has this property
(`headStep_atomic`). -/
def IsAtomicSupport {α : Type _} [MeasurableSpace α] (μ : Measure α) : Prop :=
  μ {x | μ {x} = 0} = 0

theorem isAtomicSupport_zero {α : Type _} [MeasurableSpace α] :
    IsAtomicSupport (0 : Measure α) := by simp [IsAtomicSupport]

theorem PMF.toMeasure_isAtomicSupport {α : Type _} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) : IsAtomicSupport p.toMeasure := by
  unfold IsAtomicSupport
  have hset : {x : α | p.toMeasure {x} = 0} = (p.support : Set α)ᶜ := by
    ext x
    rw [Set.mem_ofPred_eq, p.toMeasure_apply_singleton x (measurableSet_singleton x),
      Set.mem_compl_iff, PMF.mem_support_iff, not_not]
  rw [hset, p.toMeasure_apply_eq_zero_iff p.support_countable.measurableSet.compl]
  exact disjoint_compl_right

theorem isAtomicSupport_dirac {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α]
    (a : α) : IsAtomicSupport (Measure.dirac a) := by
  unfold IsAtomicSupport
  refine measure_mono_null (t := {a}ᶜ) ?_ ?_
  · intro x hx
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    rw [Set.mem_ofPred_eq, Measure.dirac_apply_of_mem (Set.mem_singleton x)] at hx
    exact one_ne_zero hx
  · rw [Measure.dirac_apply' _ (measurableSet_singleton a).compl, Set.indicator_of_notMem (by simp)]

theorem IsAtomicSupport.concentrated_atoms {α : Type _} [MeasurableSpace α]
    {μ : Measure α} (h : IsAtomicSupport μ) : Concentrated μ {x | 0 < μ {x}} := by
  have hset : {x | 0 < μ {x}}ᶜ = {x | μ {x} = 0} := by
    ext x; simp [Set.mem_compl_iff, not_lt, nonpos_iff_eq_zero]
  rw [Concentrated, hset]; exact h

end ProbLang

/-! ## Measurability on `Option`

Cylinders `none` / `some S` generate the σ-algebra on `Option α`; a map into `Option α` is
measurable once its cylinder preimages are. -/

theorem MeasurableEmbedding.some_mk {α : Type _} [MeasurableSpace α] :
    MeasurableEmbedding (some : α → Option α) := by
  refine ⟨Option.some_injective _, measurable_some, fun s hs =>
    ⟨Sum.inl '' s, MeasurableSet.inl_image hs, ?_⟩⟩
  ext x; cases x <;> simp

@[measurability]
theorem MeasurableSet.image_some {α : Type _} [MeasurableSpace α] {S : Set α}
    (hS : MeasurableSet S) : MeasurableSet ((some : α → Option α) '' S) :=
  MeasurableEmbedding.some_mk.measurableSet_image' hS

/-- A cylinder for `Option α`: either `none` or `some` of a `Set α`. -/
abbrev OptionCyl (α : Type _) := Option (Set α)

/-- The set of `Option α` that a cylinder denotes. -/
@[simp] def OptionCyl.flatten {α : Type _} : OptionCyl α → Set (Option α)
  | none => {none}
  | some S => some '' S

/-- A cylinder whose `some` leaf is a measurable set. -/
inductive OptionCyl.HasMeasurableLeaves {α : Type _} [MeasurableSpace α] : OptionCyl α → Prop
  | none : HasMeasurableLeaves none
  | some {S : Set α} : MeasurableSet S → HasMeasurableLeaves (some S)

theorem Set.image_univ_some {α : Type _} :
    (some : α → Option α) '' Set.univ = ({none} : Set (Option α))ᶜ := by
  rw [Set.image_univ, ← Set.compl_range_some, compl_compl]

theorem Set.image_compl_some {α : Type _} (G : Set α) :
    (some : α → Option α) '' Gᶜ
      = ({none} : Set (Option α))ᶜ \ (some '' G) := by
  rw [← Set.image_univ_some, Set.compl_eq_univ_sdiff, Set.image_sdiff (Option.some_injective α)]

@[measurability]
theorem MeasurableSet.singleton_none {α : Type _} [MeasurableSpace α] :
    MeasurableSet ({none} : Set (Option α)) := by
  refine ⟨Sum.inr '' Set.univ, MeasurableSet.inr_image MeasurableSet.univ, ?_⟩
  ext x; cases x <;> simp

@[fun_prop]
theorem Option.measurable_getD {α : Type _} [MeasurableSpace α] (d : α) :
    Measurable (fun x : Option α => x.getD d) := by
  intro S hS
  have heq : (fun x : Option α => x.getD d) ⁻¹' S
       = (some '' S) ∪ (if d ∈ S then ({none} : Set (Option α)) else ∅) := by
    ext x; cases x <;> simp [Option.getD]
  rw [heq]
  refine MeasurableSet.union (MeasurableSet.image_some hS) ?_
  split_ifs
  · exact MeasurableSet.singleton_none
  · exact .empty

@[measurability]
theorem OptionCyl.flatten_measurable {α : Type _} [MeasurableSpace α]
    {c : OptionCyl α} (hc : c.HasMeasurableLeaves) :
    MeasurableSet (OptionCyl.flatten c) := by
  cases hc with
  | none => exact MeasurableSet.singleton_none
  | @some S hS => exact MeasurableEmbedding.some_mk.measurableSet_image.mpr hS

/-- A map into `Option α` is measurable if every cylinder with measurable leaves has a measurable
preimage. -/
theorem Measurable.option_of_cyl_preimages
    {X α : Type _} [MeasurableSpace X] [MeasurableSpace α]
    (f : X → Option α)
    (h : ∀ c : OptionCyl α, c.HasMeasurableLeaves → MeasurableSet (f ⁻¹' OptionCyl.flatten c)) :
    Measurable f := by
  refine measurable_comap_iff.mpr fun T hT => ?_
  have hsome_mset := h (some (Sum.inl ⁻¹' T)) (.some (measurable_inl hT))
  suffices h_union : (Equiv.optionEquivSumPUnit α ∘ f) ⁻¹' T
                   = f ⁻¹' OptionCyl.flatten (some (Sum.inl ⁻¹' T))
                   ∪ (if Sum.inr PUnit.unit ∈ T
                      then f ⁻¹' OptionCyl.flatten (none : OptionCyl α)
                      else ∅) by
    rw [h_union]; split_ifs
    · exact hsome_mset.union (h none .none)
    · simpa using hsome_mset
  ext x; cases hfx : f x <;> split_ifs <;> simp_all

/-- A map into `Option α` is measurable if the preimage of `none` is the complement of a measurable
`cov` and every `some`-image has measurable preimage. -/
theorem Measurable.option_of_cov
    {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {π : β → Option α}
    {cov : Set β}
    (h_cov_meas : MeasurableSet cov)
    (h_none : π ⁻¹' ({none} : Set (Option α)) = covᶜ)
    (h_some : ∀ S : Set α, MeasurableSet S → MeasurableSet (π ⁻¹' (some '' S))) :
    Measurable π := by
  apply Measurable.option_of_cyl_preimages
  rintro (_ | S) hc
  · change MeasurableSet (π ⁻¹' ({none} : Set (Option α)))
    rw [h_none]; exact h_cov_meas.compl
  · cases hc with
    | some hS => exact h_some _ hS

@[simp] theorem Option.map_preimage_some {α β : Type _} (f : α → β) (S : Set β) :
    Option.map f ⁻¹' (some '' S) = some '' (f ⁻¹' S) := by
  ext x; cases x <;> simp [Option.map]

@[fun_prop]
theorem Measurable.option_map {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f) : Measurable (Option.map f) :=
  Measurable.option_of_cov
    (cov := ({none} : Set (Option α))ᶜ)
    MeasurableSet.singleton_none.compl
    (by ext x; cases x <;> simp [Option.map])
    (fun S hS => by
      simp only [Option.map_preimage_some]
      exact MeasurableEmbedding.some_mk.measurableSet_image.mpr (hf hS))

/-! ## Shape-stratified measurability

Measurability is assembled from cells `{p | shape p = s ∧ f p ∈ U}`, one per shape. Cells are over
`β × T`, where `β` is a measurable parameter. Used by `CoreMeasures/Recurrences.lean` to prove
structural recursions on `Exp` measurable: split the preimage by top constructor (`shape`) and
prove each cell measurable. -/

namespace StructRec

variable {T α : Type _} [MeasurableSpace T] [MeasurableSpace α]
variable {Sh : Type _} (shape : T → Sh)

variable {β : Type _} [MeasurableSpace β]
variable {g : β → T → α}

/-- The cell of a constructor `ctor : γ → T` that carries data only: measurable when `g`
restricted to that constructor (`c`) is. -/
theorem cell_dataLeaf_param {γ : Type _} [MeasurableSpace γ]
    {ctor : γ → T} {s : Sh} {c : β → γ → α} {U : Set α}
    (h_emb : MeasurableEmbedding ctor)
    (h_shape : ∀ p : T, shape p = s ↔ ∃ d, p = ctor d)
    (h_eq : ∀ b d, g b (ctor d) = c b d)
    (h_c : Measurable (Function.uncurry c))
    (hU : MeasurableSet U) :
    MeasurableSet {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U} := by
  have heq : {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U}
      = (Prod.map id ctor) '' {p : β × γ | Function.uncurry c p ∈ U} := by
    ext ⟨b, p⟩
    constructor
    · rintro ⟨hs, hp⟩
      obtain ⟨d, rfl⟩ := (h_shape p).mp hs
      refine ⟨(b, d), ?_, rfl⟩
      simp only [Set.mem_ofPred_eq, Function.uncurry] at hp ⊢
      rw [h_eq] at hp; exact hp
    · rintro ⟨⟨b', d⟩, hd, heq⟩
      obtain ⟨rfl, rfl⟩ : b' = b ∧ ctor d = p := by simpa using heq
      refine ⟨(h_shape _).mpr ⟨d, rfl⟩, ?_⟩
      simp only [Set.mem_ofPred_eq, Function.uncurry] at hd ⊢
      rw [h_eq]; exact hd
  rw [heq]
  exact (MeasurableEmbedding.id.prodMap h_emb).measurableSet_image' (h_c hU)

/-- A map is measurable if each shape cell of every measurable preimage is. -/
theorem measurable_of_cells_param [Countable Sh]
    (h_cell : ∀ (s : Sh) {U : Set α}, MeasurableSet U →
      MeasurableSet {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U}) :
    Measurable (Function.uncurry g) := by
  intro S hS
  rw [show (Function.uncurry g ⁻¹' S)
        = ⋃ s : Sh, {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ S} from by
    ext q
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩]
  exact MeasurableSet.iUnion fun s => h_cell s hS

end StructRec

/-! ## Measurable space on `List X`

Induced by `List X ≃ Σ n, Fin n → X`: a set of lists is measurable iff each length-`n`
slice is measurable in the product σ-algebra. -/

/-- A list as its length and entries. -/
def List.toSigma {X : Type _} (l : List X) : Σ n, Fin n → X := ⟨l.length, l.get⟩

/-- The σ-algebra on lists pulled back along `List.toSigma`. -/
instance List.instMeasurableSpace {X : Type _} [MeasurableSpace X] :
    MeasurableSpace (List X) :=
  MeasurableSpace.comap List.toSigma inferInstance

@[fun_prop]
theorem List.measurable_toSigma {X : Type _} [MeasurableSpace X] :
    Measurable (List.toSigma : List X → Σ n, Fin n → X) :=
  fun _ hS => ⟨_, hS, rfl⟩

theorem measurable_sigma_iff {α : Type _} {β : α → Type _}
    [∀ a, MeasurableSpace (β a)] {γ : Type _} [MeasurableSpace γ]
    {f : (Σ a, β a) → γ} : Measurable f ↔ ∀ a, Measurable (fun b => f ⟨a, b⟩) := by
  refine ⟨fun hf a => hf.comp fun S hS => MeasurableSpace.measurableSet_iInf.mp hS a,
    fun h S hS => MeasurableSpace.measurableSet_iInf.mpr fun a => h a hS⟩

/-- `(List.ofFn g).foldl f a`, by recursion on `n`. -/
def List.foldlOfFn {α β : Type _} (f : α → β → α) : ∀ (n : ℕ), α → (Fin n → β) → α
  | 0, a, _ => a
  | n+1, a, g => List.foldlOfFn f n (f a (g 0)) (fun i => g i.succ)

theorem List.foldlOfFn_eq_foldl_ofFn {α β : Type _} (f : α → β → α) :
    ∀ (n : ℕ) (a : α) (g : Fin n → β), List.foldlOfFn f n a g = (List.ofFn g).foldl f a
  | 0, _, _ => rfl
  | n + 1, a, g => by
    rw [List.ofFn_succ, List.foldl_cons, ← List.foldlOfFn_eq_foldl_ofFn f n]; rfl

theorem List.measurable_foldlOfFn {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β → α} (hf : Measurable (Function.uncurry f)) :
    ∀ n, Measurable (fun (p : (Fin n → β) × α) => List.foldlOfFn f n p.2 p.1) := by
  intro n
  induction n with
  | zero => exact measurable_snd
  | succ n ih =>
    have h0 : Measurable fun p : (Fin (n+1) → β) × α => p.1 0 :=
      (measurable_pi_apply 0).comp measurable_fst
    have hsucc : Measurable fun p : (Fin (n+1) → β) × α => fun i : Fin n => p.1 i.succ :=
      Measurable.of_eval fun _ => (measurable_pi_apply _).comp measurable_fst
    have hfa : Measurable fun p : (Fin (n+1) → β) × α => f p.2 (p.1 0) :=
      hf.comp (measurable_snd.prodMk h0)
    exact ih.comp (hsucc.prodMk hfa)

theorem MeasurableEmbedding.sigmaMk {ι : Type _} {β : ι → Type _}
    [∀ i, MeasurableSpace (β i)] (i : ι) :
    MeasurableEmbedding (Sigma.mk i : β i → Σ j, β j) := by
  refine ⟨fun x y h => eq_of_heq (Sigma.mk.inj h).2,
    fun V hV => MeasurableSpace.measurableSet_iInf.mp hV i, fun s hs => ?_⟩
  refine MeasurableSpace.measurableSet_iInf.mpr fun j => ?_
  by_cases hj : j = i
  · subst hj
    show MeasurableSet ((Sigma.mk j) ⁻¹' (Sigma.mk j '' s))
    convert hs
    ext x
    refine ⟨?_, fun hx => ⟨x, hx, rfl⟩⟩
    rintro ⟨y, hy, h⟩
    exact eq_of_heq (Sigma.mk.inj h).2 ▸ hy
  · show MeasurableSet ((Sigma.mk j) ⁻¹' (Sigma.mk i '' s))
    convert MeasurableSet.empty
    ext x; simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false]
    rintro ⟨y, _, h⟩
    exact (hj (Sigma.mk.inj h).1.symm).elim

/-- A map out of `(Σ k, Fin k → β) × γ` is measurable if it is on each length-`k` slice. -/
private theorem measurable_sigmaFin_prod {β γ δ : Type _}
    [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    {F : (Σ k : ℕ, Fin k → β) × γ → δ}
    (hF : ∀ k, Measurable fun p : (Fin k → β) × γ => F (⟨k, p.1⟩, p.2)) : Measurable F := by
  intro U hU
  have hrw : F ⁻¹' U = ⋃ k : ℕ, Prod.map (@Sigma.mk ℕ (fun k => Fin k → β) k) (id : γ → γ)
      '' ((fun p : (Fin k → β) × γ => F (⟨k, p.1⟩, p.2)) ⁻¹' U) := by
    ext ⟨⟨k, g⟩, c⟩
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
    refine ⟨fun h => ⟨k, (g, c), h, rfl⟩, ?_⟩
    rintro ⟨k₀, ⟨g₀, c₀⟩, hU₀, hq⟩
    rw [Prod.mk.injEq, Sigma.mk.injEq] at hq
    obtain ⟨⟨rfl, hg⟩, rfl⟩ := hq
    cases hg
    exact hU₀
  rw [hrw]
  exact .iUnion fun k =>
    ((MeasurableEmbedding.sigmaMk k).prodMap MeasurableEmbedding.id).measurableSet_image' (hF k hU)

/-- `List.foldl` factors through the per-length slices `(Fin n → β) × α`, where it is
`n` applications of `f`. -/
@[fun_prop]
theorem List.measurable_foldl {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β → α} (hf : Measurable (Function.uncurry f)) :
    Measurable (fun (p : List β × α) => p.1.foldl f p.2) := by
  have hfoldlOfFn :
      Measurable fun q : (Σ k : ℕ, Fin k → β) × α => List.foldlOfFn f q.1.1 q.2 q.1.2 :=
    measurable_sigmaFin_prod fun n => List.measurable_foldlOfFn hf n
  have hrw : (fun p : List β × α => p.1.foldl f p.2)
      = (fun q : (Σ k : ℕ, Fin k → β) × α => List.foldlOfFn f q.1.1 q.2 q.1.2)
        ∘ (fun p : List β × α => (List.toSigma p.1, p.2)) := by
    funext p
    show p.1.foldl f p.2 = List.foldlOfFn f (List.toSigma p.1).1 p.2 (List.toSigma p.1).2
    rw [List.foldlOfFn_eq_foldl_ofFn]
    show p.1.foldl f p.2 = (List.ofFn p.1.get).foldl f p.2
    rw [List.ofFn_get]
  rw [hrw]
  exact hfoldlOfFn.comp (List.measurable_toSigma.comp measurable_fst |>.prodMk measurable_snd)

@[fun_prop]
theorem Fin.measurable_snoc {n : ℕ} {β : Type _} [MeasurableSpace β] :
    Measurable (fun (p : (Fin n → β) × β) => (@Fin.snoc n (fun _ => β) p.1 p.2) :
      (Fin n → β) × β → (Fin (n+1) → β)) := by
  refine Measurable.of_eval fun i => ?_
  by_cases h : i.val < n
  · have heq : ∀ p : (Fin n → β) × β,
        ((@Fin.snoc n (fun _ => β) p.1 p.2) i : β) = p.1 ⟨i.val, h⟩ := by
      intro p
      simp [Fin.snoc, h, Fin.castLT]
    rw [show (fun p : (Fin n → β) × β => ((@Fin.snoc n (fun _ => β) p.1 p.2) i : β))
          = fun p => p.1 ⟨i.val, h⟩ from funext heq]
    exact (measurable_pi_apply _).comp measurable_fst
  · push Not at h
    have hi : i = Fin.last n := Fin.ext (le_antisymm (Nat.lt_succ_iff.mp i.isLt) h)
    have heq : ∀ p : (Fin n → β) × β, ((@Fin.snoc n (fun _ => β) p.1 p.2) i : β) = p.2 := by
      intro p; rw [hi, Fin.snoc_last]
    rw [show (fun p : (Fin n → β) × β => ((@Fin.snoc n (fun _ => β) p.1 p.2) i : β))
          = fun p => p.2 from funext heq]
    exact measurable_snd

@[fun_prop]
theorem measurable_sigma_snoc {β : Type _} [MeasurableSpace β] :
    Measurable (fun (q : (Σ k : ℕ, Fin k → β) × β) =>
      (⟨q.1.1 + 1, Fin.snoc q.1.2 q.2⟩ : Σ k : ℕ, Fin k → β)) :=
  measurable_sigmaFin_prod fun k => (MeasurableEmbedding.sigmaMk (k + 1)).measurable.comp
    (Fin.measurable_snoc (n := k))

@[fun_prop]
theorem List.measurable_append_singleton {β : Type _} [MeasurableSpace β] :
    Measurable (fun (p : List β × β) => p.1 ++ [p.2]) := by
  rw [measurable_comap_iff (g := (List.toSigma : List β → Σ k, Fin k → β))]
  have hrw : (List.toSigma : List β → Σ k, Fin k → β) ∘ (fun p : List β × β => p.1 ++ [p.2])
      = (fun q : (Σ k, Fin k → β) × β =>
          (⟨q.1.1 + 1, Fin.snoc q.1.2 q.2⟩ : Σ k, Fin k → β))
        ∘ (fun p : List β × β => (List.toSigma p.1, p.2)) := by
    funext p
    obtain ⟨L, x⟩ := p
    show (@Sigma.mk ℕ (fun k => Fin k → β) (L ++ [x]).length (L ++ [x]).get)
        = ⟨L.length + 1, @Fin.snoc L.length (fun _ => β) L.get x⟩
    have hlen : (L ++ [x]).length = L.length + 1 := by simp
    refine Sigma.ext hlen <| (Fin.heq_fun_iff hlen).mpr fun i => ?_
    have hlt : i.val < L.length + 1 := hlen ▸ i.isLt
    show (L ++ [x]).get i = (@Fin.snoc L.length (fun _ => β) L.get x) ⟨i.val, hlt⟩
    by_cases hi : i.val < L.length
    · have hcast : (⟨i.val, hlt⟩ : Fin (L.length + 1))
          = ((⟨i.val, hi⟩ : Fin L.length).castSucc) := Fin.ext rfl
      rw [hcast, Fin.snoc_castSucc]
      simp [hi]
    · push Not at hi
      have hival : i.val = L.length := by omega
      have hcast : ((⟨i.val, hlt⟩ : Fin (L.length + 1)))
          = Fin.last L.length := Fin.ext hival
      rw [hcast, Fin.snoc_last]
      simp [hival]
  rw [hrw]
  exact measurable_sigma_snoc.comp
    ((List.measurable_toSigma).comp measurable_fst |>.prodMk measurable_snd)

/-! ## Measures and kernels

Pushforward and bind lemmas, and measurability of kernel-valued maps. -/

/-- Binding after a pushforward binds the composite kernel. -/
theorem Measure.bind_map {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {f : α → β} {g : β → Measure γ}
    (hf : Measurable f) (hg : Measurable g) : (μ.map f).bind g = μ.bind (g ∘ f) := by
  rw [Measure.bind, Measure.bind, Measure.map_map hg hf]

/-- Pushing a bind forward pushes each kernel measure forward. -/
theorem Measure.bind_map_comm {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (k : α → Measure β) (f : β → γ) (hf : Measurable f) (hk : AEMeasurable k μ) :
    (μ.bind k).map f = μ.bind (fun a => (k a).map f) := by
  refine Measure.ext fun S hS => ?_
  have hkmap : AEMeasurable (fun a ↦ map f (k a)) μ :=
    (measurable_map f hf).comp_aemeasurable' hk
  rw [Measure.map_apply hf hS, Measure.bind_apply (hf hS) hk, Measure.bind_apply hS hkmap]
  simp_rw [Measure.map_apply hf hS]

/-- Counting measure reweighted by the density `f`. -/
abbrev count (f : α → ENNReal) [MeasurableSpace α] := Measure.count.withDensity f

/-- For an s-finite measurable kernel `k` and a jointly measurable `h`,
`a ↦ (k a).map (h (a, ·))` is measurable. -/
theorem Measure.measurable_map_uncurry {α β γ : Type _}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {h : α × β → γ} (hh : Measurable h)
    {k : α → Measure β} (hk : Measurable k)
    [hSF : ProbabilityTheory.IsSFiniteKernel (ProbabilityTheory.Kernel.mk k hk)] :
    Measurable (fun a : α => (k a).map (fun b => h (a, b))) := by
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  have hpre : ∀ a, Measurable (fun b : β => h (a, b)) := fun a =>
    hh.comp (measurable_const.prodMk measurable_id)
  simp_rw [fun a => Measure.map_apply (hpre a) hS]
  set T := h ⁻¹' S
  have hT : MeasurableSet T := hh hS
  have hrw : ∀ a, (fun b => h (a, b)) ⁻¹' S = Prod.mk a ⁻¹' T := fun _ => rfl
  simp_rw [hrw]
  show Measurable (fun a => k a (Prod.mk a ⁻¹' T))
  have hker_eq : ∀ a, k a = (ProbabilityTheory.Kernel.mk k hk) a :=
    fun _ => by rw [ProbabilityTheory.Kernel.coe_mk]
  simp_rw [hker_eq]
  exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left hT

/-- A monotone sequence of measurable measure-valued maps has a measurable supremum. -/
theorem Measure.measurable_iSup_of_monotone {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : ℕ → α → Measure β} (hμ : ∀ i, Measurable (μ i))
    (hmono : ∀ a, Monotone (fun i => μ i a)) :
    Measurable (fun a : α => ⨆ i, μ i a) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [fun a => Measure.iSup_apply_of_monotone (hmono a) hs]
  exact Measurable.iSup fun i => (Measure.measurable_coe hs).comp (hμ i)
