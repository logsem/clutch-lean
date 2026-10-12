module

public meta import Metrology.Meta.Discrete
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

noncomputable section
open Classical MeasureTheory ProbabilityTheory Measure

/-! ## `Possible`: a measurability-free "positive-mass point" of a measure

`Possible ρ μ` says that `ρ` is a *possible outcome* of `μ` — a point carrying
positive mass — but states it as `∃ p > 0, p • dirac ρ ≤ μ` rather than the more
obvious `0 < μ {ρ}`. The two agree for discrete measures (`possible_iff_pos`),
yet because `Possible` never names the singleton `{ρ}` it is well-behaved — and
can be related to operational support facts — **without** assuming
`MeasurableSingletonClass`. This is what lets the support characterisations drop
the `[MeasurableSingletonClass rT]` hypothesis. -/
def Possible {α : Type _} [MeasurableSpace α] (ρ : α) (μ : Measure α) : Prop :=
  ∃ p : ENNReal, 0 < p ∧ p • dirac ρ ≤ μ

/-- `Possible` is monotone in the measure. -/
theorem Possible.mono {α : Type _} [MeasurableSpace α] {ρ : α} {μ ν : Measure α}
    (hμν : μ ≤ ν) : Possible ρ μ → Possible ρ ν
  | ⟨p, hp, hle⟩ => ⟨p, hp, hle.trans hμν⟩

/-- If `dirac ρ ≤ μ` then `ρ` is possible (take `p = 1`). Measurability-free. -/
theorem Possible.of_dirac_le {α : Type _} [MeasurableSpace α] {ρ : α} {μ : Measure α}
    (h : dirac ρ ≤ μ) : Possible ρ μ :=
  ⟨1, one_pos, by rwa [one_smul]⟩

/-- A possible outcome witnesses that the measure is nonzero. Measurability-free;
this is what discharges `HeadReducible` (`headStep … ≠ 0`) safety obligations. -/
theorem Possible.ne_zero {α : Type _} [MeasurableSpace α] {ρ : α} {μ : Measure α}
    (h : Possible ρ μ) : μ ≠ 0 := by
  obtain ⟨p, hp, hle⟩ := h
  rintro rfl
  have hu : p ≤ 0 := by simpa [Measure.smul_apply] using (hle Set.univ)
  exact absurd hu (not_le.mpr hp)

/-- A deterministic step (`μ = dirac ρ`) makes `ρ` possible. Measurability-free;
this is the `←` engine for the deterministic head-step constructors. -/
theorem Possible.of_dirac_eq {α : Type _} [MeasurableSpace α] {ρ : α} {μ : Measure α}
    (h : μ = dirac ρ) : Possible ρ μ :=
  Possible.of_dirac_le (h ▸ le_refl _)

/-- `Possible` transports along a measurable map. Needs only `Measurable g` — no
`MeasurableSingletonClass`. This is the `←` engine for the (non-deterministic)
`rand` constructors, whose head step is a pushforward of the uniform PMF. -/
theorem Possible.map {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {g : α → β} (hg : Measurable g) {ρ : α} {μ : Measure α} :
    Possible ρ μ → Possible (g ρ) (μ.map g)
  | ⟨p, hp, hle⟩ => ⟨p, hp, by
      rw [Measure.le_iff]
      intro s hs
      rw [Measure.map_apply hg hs, Measure.smul_apply, dirac_apply' _ hs, smul_eq_mul]
      by_cases hmem : g ρ ∈ s
      · rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
        have hρ : ρ ∈ g ⁻¹' s := hmem
        have hle' := Measure.le_iff.mp hle (g ⁻¹' s) (hg hs)
        simp only [Measure.smul_apply, dirac_apply' _ (hg hs), Set.indicator_of_mem hρ,
          Pi.one_apply, smul_eq_mul, mul_one] at hle'
        exact hle'
      · rw [Set.indicator_of_notMem hmem]; simp⟩

/-- On a space with measurable singletons, `Possible ρ μ` is exactly positive
mass at `ρ`. This is the bridge between the measurability-free `Possible` and the
discrete `0 < μ {ρ}` formulation. -/
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

instance [MeasurableSpace α] : MeasurableSpace (Option α) :=
  MeasurableSpace.comap (Equiv.optionEquivSumPUnit.{0, _} α) inferInstance

@[fun_prop]
theorem measurable_some [MeasurableSpace α] : Measurable (Option.some : α → _) := by
  refine measurable_comap_iff.mpr ?_
  unfold Function.comp
  simp [Equiv.optionEquivSumPUnit]
  fun_prop

/-! ### Option-cylinders and their measurable-leaf generator system. -/

/-- `some : α → Option α` is a measurable embedding. -/
theorem MeasurableEmbedding.some_mk {α : Type _} [MeasurableSpace α] :
    MeasurableEmbedding (some : α → Option α) := by
  refine ⟨Option.some_injective _, measurable_some, fun s hs =>
    ⟨Sum.inl '' s, MeasurableSet.inl_image hs, ?_⟩⟩
  ext x; cases x <;> simp

/-- `some '' S` is measurable when `S` is. -/
@[measurability]
theorem MeasurableSet.image_some {α : Type _} [MeasurableSpace α] {S : Set α}
    (hS : MeasurableSet S) : MeasurableSet ((some : α → Option α) '' S) :=
  MeasurableEmbedding.some_mk.measurableSet_image' hS

/-- A cylinder for `Option α`: either `none` or `some` of a `Set α`. -/
abbrev OptionCyl (α : Type _) := Option (Set α)

/-- Interpret an Option-cylinder as a subset of `Option α`. -/
@[simp] def OptionCyl.flatten {α : Type _} : OptionCyl α → Set (Option α)
  | none => {none}
  | some S => some '' S

/-- An Option-cylinder has measurable leaves iff its `Set α` payload (when present) is measurable. -/
inductive OptionCyl.HasMeasurableLeaves {α : Type _} [MeasurableSpace α] : OptionCyl α → Prop
  | none : HasMeasurableLeaves none
  | some {S : Set α} : MeasurableSet S → HasMeasurableLeaves (some S)

/-- Image of `Set.univ` under `some : α → Option α` is the complement of `{none}`. -/
theorem Set.image_univ_some {α : Type _} :
    (some : α → Option α) '' Set.univ = ({none} : Set (Option α))ᶜ := by
  rw [Set.image_univ, ← Set.compl_range_some, compl_compl]

/-- Image of a complement under `some`: `some '' Gᶜ = {none}ᶜ \ some '' G`.
Used in the compl-case of σ-algebra induction over `Option α`-valued projections. -/
theorem Set.image_compl_some {α : Type _} (G : Set α) :
    (some : α → Option α) '' Gᶜ
      = ({none} : Set (Option α))ᶜ \ (some '' G) := by
  rw [← Set.image_univ_some, Set.compl_eq_univ_sdiff, Set.image_sdiff (Option.some_injective α)]

/-- `{none} ⊆ Option α` is measurable. -/
@[measurability]
theorem MeasurableSet.singleton_none {α : Type _} [MeasurableSpace α] :
    MeasurableSet ({none} : Set (Option α)) := by
  refine ⟨Sum.inr '' Set.univ, MeasurableSet.inr_image MeasurableSet.univ, ?_⟩
  ext x; cases x <;> simp

/-- `Option.getD · d` is measurable for any default value. -/
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

/-- Every Option-cylinder is measurable in the project's `Option` σ-algebra. -/
@[measurability]
theorem OptionCyl.flatten_measurable {α : Type _} [MeasurableSpace α]
    {c : OptionCyl α} (hc : c.HasMeasurableLeaves) :
    MeasurableSet (OptionCyl.flatten c) := by
  cases hc with
  | none => exact MeasurableSet.singleton_none
  | @some S hS => exact MeasurableEmbedding.some_mk.measurableSet_image.mpr hS

/-- **Measurability via Option-cylinder generators.** To prove `Measurable (f : X → Option α)`,
it suffices to check preimages of Option-cylinders (`{none}` and `some '' M` for measurable `M`). -/
theorem Measurable.option_of_cyl_preimages
    {X α : Type _} [MeasurableSpace X] [MeasurableSpace α]
    (f : X → Option α)
    (h : ∀ c : OptionCyl α, c.HasMeasurableLeaves → MeasurableSet (f ⁻¹' OptionCyl.flatten c)) :
    Measurable f := by
  refine measurable_comap_iff.mpr fun T hT => ?_
  have hsome_mset := h (some (Sum.inl ⁻¹' T)) (.some (measurable_inl hT))
  -- The preimage `(Equiv ∘ f)⁻¹' T` always contains `f⁻¹' (some '' Sum.inl⁻¹' T)`, plus
  -- `f⁻¹' {none}` iff `Sum.inr ⋆ ∈ T`. Combine the two pieces; the second is empty otherwise.
  suffices h_union : (Equiv.optionEquivSumPUnit α ∘ f) ⁻¹' T
                   = f ⁻¹' OptionCyl.flatten (some (Sum.inl ⁻¹' T))
                   ∪ (if Sum.inr PUnit.unit ∈ T
                      then f ⁻¹' OptionCyl.flatten (none : OptionCyl α)
                      else ∅) by
    rw [h_union]; split_ifs
    · exact hsome_mset.union (h none .none)
    · simpa using hsome_mset
  ext x; cases hfx : f x <;> split_ifs <;> simp_all

/-- **Skeleton for `Option α`-valued measurability via cover + per-set hypothesis.**

To prove `Measurable π` where `π : β → Option α`, it suffices to provide:
  * a measurable "cover" `cov : Set β` whose complement is `π ⁻¹' {none}`, and
  * for every measurable `S : Set α`, measurability of `π ⁻¹' (some '' S)`. -/
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

/-- **Range-as-cover rewrite for `Option`-valued projections.** If `π : β → Option α` is the
metaprogrammed inverse of an injection `c : α → β` — returning `some x` on `c x` — then
`c '' T = range c ∩ π⁻¹' (some '' T)`. -/
theorem Set.image_eq_range_inter_preimage_option
    {α β : Type _} (c : α → β) (π : β → Option α)
    (hπ : ∀ x, π (c x) = some x) (T : Set α) :
    c '' T = Set.range c ∩ π ⁻¹' (some '' T) := by
  ext b; aesop

/-- `Option.map f` pulls a `some`-image back to a `some`-image of the preimage. -/
@[simp] theorem Option.map_preimage_some {α β : Type _} (f : α → β) (S : Set β) :
    Option.map f ⁻¹' (some '' S) = some '' (f ⁻¹' S) := by
  ext x; cases x <;> simp [Option.map]

/-- `Option.map f` is measurable when `f` is. -/
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

/-- Joint Option-pairing: `(none, none) ↦ none`, `(some a, some b) ↦ some (a, b)`,
mixed cases `↦ none`. -/
def Option.pair {α β : Type _} : Option α × Option β → Option (α × β)
  | (some a, some b) => some (a, b)
  | _ => none

/-- `Option.pair` pulls a `some`-image back to a `Prod.map some some`-image. -/
@[simp] theorem Option.pair_preimage_some {α β : Type _} (S : Set (α × β)) :
    Option.pair ⁻¹' (some '' S) = (Prod.map some some) '' S := by
  ext ⟨x, y⟩; cases x <;> cases y <;> simp [Option.pair, Prod.map]

/-- `Option.pair` is measurable as a function `Option α × Option β → Option (α × β)`. -/
@[fun_prop]
theorem Measurable.option_pair {α β : Type _} [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (Option.pair : Option α × Option β → Option (α × β)) :=
  Measurable.option_of_cov
    (cov := ({none} : Set (Option α))ᶜ ×ˢ ({none} : Set (Option β))ᶜ)
    (MeasurableSet.singleton_none.compl.prod MeasurableSet.singleton_none.compl)
    (by ext ⟨x, y⟩; cases x <;> cases y <;> simp [Option.pair])
    (fun S hS => by
      simp only [Option.pair_preimage_some]
      exact ((MeasurableEmbedding.some_mk (α := α)).prodMap
        MeasurableEmbedding.some_mk).measurableSet_image.mpr hS)

/-! ### Generic σ-algebra induction for cover-restricted measurability. -/

/-- **Generic σ-algebra induction for cover-restricted measurability.**

If the target's σ-algebra is `generateFrom 𝒞`, and `cov ∩ f⁻¹' G` is measurable for every
generator `G ∈ 𝒞`, then the same holds for every measurable `G`. The σ-algebra induction
threads `cov ∩ _` through the lattice operations. -/
theorem MeasurableSet.cover_inter_preimage_of_gen
    {α β : Type _} [MeasurableSpace α] [mβ : MeasurableSpace β]
    {𝒞 : Set (Set β)} (hβ : mβ = MeasurableSpace.generateFrom 𝒞)
    {cov : Set α} (hcov : MeasurableSet cov) (f : α → β)
    (hgen : ∀ G ∈ 𝒞, MeasurableSet (cov ∩ f ⁻¹' G)) :
    ∀ G : Set β, MeasurableSet G → MeasurableSet (cov ∩ f ⁻¹' G) := by
  intro G hG
  rw [hβ] at hG
  induction hG with
  | basic G' hG' => exact hgen G' hG'
  | empty => simp
  | compl G' _ ih =>
    rw [Set.preimage_compl, ← Set.sdiff_eq, ← Set.sdiff_self_inter]
    exact hcov.diff ih
  | iUnion G' _ ih =>
    rw [Set.preimage_iUnion, Set.inter_iUnion]
    exact .iUnion ih

private theorem subtype_preimage_eq {α β : Type _} {cov : Set α} (f : α → β) (G : Set β) :
    (fun (b : ↥cov) => f b.val) ⁻¹' G = (Subtype.val : ↥cov → α) ⁻¹' (cov ∩ f ⁻¹' G) := by
  ext ⟨b, hb⟩; simp

/-- **Subtype-restricted measurability from cover-restricted measurability.**

If `cov ⊆ α` is measurable and `cov ∩ f⁻¹' G` is measurable for every measurable `G ⊆ β`,
then the subtype-restricted function `↥cov → β` is measurable. -/
theorem Measurable.of_cover_inter_preimage
    {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {cov : Set α} {f : α → β}
    (h : ∀ G : Set β, MeasurableSet G → MeasurableSet (cov ∩ f ⁻¹' G)) :
    Measurable (fun (b : ↥cov) => f b.val) := fun G hG => by
  rw [subtype_preimage_eq]
  exact MeasurableSet.preimage (h G hG) measurable_subtype_coe

/-- **Cover-restricted measurability from subtype-restricted measurability** (the converse). -/
theorem MeasurableSet.cover_inter_preimage_of_subtype
    {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {cov : Set α} (hcov : MeasurableSet cov) {f : α → β}
    (h : Measurable (fun (b : ↥cov) => f b.val)) :
    ∀ G : Set β, MeasurableSet G → MeasurableSet (cov ∩ f ⁻¹' G) := fun G hG => by
  rw [← Set.inter_self cov, Set.inter_assoc, ← Subtype.image_preimage_coe]
  exact MeasurableSet.subtype_image hcov ((subtype_preimage_eq f G) ▸ h hG)

-- I think there's no good continuous version of this...
/-- Continuous variant of `Discrete.map_singleton_pos`. For an *injective* `f` the
fiber `f ⁻¹' {b}` is at most a single point, so positive pushforward mass on `{b}`
forces positive mass on that unique preimage — no countability/atoms needed. (The
general, non-injective statement is false: a constant `f` collapses non-atomic mass
onto one point.) -/
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

theorem Measure.bind_map {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [DiscreteMeasurableSpace β] {μ : Measure α} {f : α → β} {g : β → Measure γ}
    (hf : Measurable f) (hg : Measurable g) : g ∘ₘ (μ.map f) = (g ∘ f) ∘ₘ μ := by
  refine ext fun S HS => ?_
  unfold Measure.bind
  rw [map_map hg hf]

/-- `.map` distributes through `.bind`: mapping over a bind is a bind of maps. -/
theorem Measure.bind_map_comm {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (k : α → Measure β) (f : β → γ) (Hf : Measurable f) (Hae : AEMeasurable k μ):
    (μ.bind k).map f = μ.bind (fun a => (k a).map f) := by
  refine Measure.ext fun S hS => ?_
  have H1 : MeasurableSet (f ⁻¹' S) := MeasurableSet.preimage hS Hf
  have H2 : AEMeasurable (fun a ↦ map f (k a)) μ := by
    refine Measurable.comp_aemeasurable' ?_ Hae
    exact measurable_map f Hf
  rw [Measure.map_apply Hf hS,
      Measure.bind_apply H1 Hae,
      Measure.bind_apply hS H2]
  simp_rw [Measure.map_apply Hf hS]

abbrev count (f : α → ENNReal) [MeasurableSpace α] := Measure.count.withDensity f

/-! ### Building `MeasurableEmbedding` from a π-system of rectangles.

For an n-ary function `f : X₁ × ⋯ × Xₙ → Z`, given (i) injectivity, (ii) measurability,
(iii) a π-system on each factor whose product rectangles generate the product σ-algebra,
(iv) measurability of `f` on a basic rectangle, and (v) a measurable cover of `Set.range f`,
we get `MeasurableEmbedding f`. Each higher-arity version reduces to the binary one by
nesting rectangles on the right. -/

/-- Unary version. -/
theorem measurableEmbedding_of_piSystem₁
    {X Z : Type*} [mX : MeasurableSpace X] [MeasurableSpace Z]
    {f : X → Z} (h_inj : Function.Injective f) (h_meas : Measurable f)
    {𝓒 : Set (Set X)}
    (h_gen : mX = MeasurableSpace.generateFrom 𝓒)
    (h_pi : IsPiSystem 𝓒)
    (h_basic : ∀ ⦃A⦄, A ∈ 𝓒 → MeasurableSet (f '' A))
    {cov : Set Z} (h_cov_meas : MeasurableSet cov) (h_cov_range : cov = .range f) :
    MeasurableEmbedding f := by
  refine ⟨h_inj, h_meas, fun S hS => ?_⟩
  refine MeasurableSpace.induction_on_inter (C := fun S _ => MeasurableSet (f '' S))
      h_gen h_pi ?_ h_basic ?_ ?_ S hS
  · simp
  · intro T _ ih
    rw [Set.compl_eq_univ_sdiff, Set.image_sdiff h_inj, Set.image_univ, ← h_cov_range]
    exact h_cov_meas.diff ih
  · intro f _ _ ih
    rw [Set.image_iUnion]
    exact .iUnion ih

/-! ## Generic shape-stratified measurability helpers. -/

namespace StructRec

/-! The cell `{p | shape p = s ∧ f p ∈ U}` is the source-side workhorse. -/

variable {T α : Type _} [MeasurableSpace T] [MeasurableSpace α]
variable {Sh : Type _} (shape : T → Sh)
variable {f : T → α}

/-- **Shape-partition assembly**: glues per-shape cell measurability into global
measurability of `f`. Requires `Sh` countable. -/
theorem measurable_of_cells [Countable Sh]
    (h_cell : ∀ (s : Sh) {U : Set α}, MeasurableSet U →
      MeasurableSet {p : T | shape p = s ∧ f p ∈ U}) :
    Measurable f := by
  intro S hS
  rw [show (f ⁻¹' S) = ⋃ s : Sh, {p : T | shape p = s ∧ f p ∈ S} from by
    ext p
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩]
  exact MeasurableSet.iUnion fun s => h_cell s hS

/-! ## Param-threaded variants: an extra measurable parameter `β`; the cell is over `β × T`. -/

variable {β : Type _} [MeasurableSpace β]
variable {g : β → T → α}

/-- **Data-leaf cell (param)**: e.g. `lit (b' : β') (e : T)` where `β'` is data. -/
theorem cell_dataLeaf_param {γ : Type _} [MeasurableSpace γ]
    {ctor : γ → T} {s : Sh} {c : β → γ → α} {U : Set α}
    (h_emb : MeasurableEmbedding ctor)
    (h_shape : ∀ p : T, shape p = s ↔ ∃ d, p = ctor d)
    (h_eq : ∀ b d, g b (ctor d) = c b d)
    (h_c : Measurable (Function.uncurry c))
    (hU : MeasurableSet U) :
    MeasurableSet {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U} := by
  -- Cell = image of (b, d) ↦ (b, ctor d) over {(b, d) | c b d ∈ U}.
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
      have hbeq : b' = b := by simpa using (Prod.mk.injEq ..).mp heq |>.1
      have hpeq : ctor d = p := by simpa using (Prod.mk.injEq ..).mp heq |>.2
      subst hbeq hpeq
      refine ⟨(h_shape _).mpr ⟨d, rfl⟩, ?_⟩
      simp only [Set.mem_ofPred_eq, Function.uncurry] at hd ⊢
      rw [h_eq]; exact hd
  rw [heq]
  -- Prod.map id ctor is a measurable embedding.
  refine (MeasurableEmbedding.id.prodMap h_emb).measurableSet_image' ?_
  exact h_c hU

/-- **Shape-partition assembly (param)**: glues per-shape joint cell measurability
into global measurability of `Function.uncurry g`. -/
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

/-! ## Measurable space on `List X`.

`List X` is a countable disjoint union of products, parameterized by length:
`List X ≃ Σ n, Fin n → X`. We induce the σ-algebra via the forward map
`l ↦ ⟨l.length, l.get⟩` — i.e. as the comap of this map.

This gives us: a set `S ⊆ List X` is measurable iff the corresponding sets of
length-`n` lists are measurable in the product σ-algebra, for each `n`.

Downstream lemmas (measurability of `List.cons`, `List.foldl`, etc.) are
straightforward but voluminous; we add them as needed. -/

/-- Forward equivalence: a list to (length, indexed function). -/
def List.toSigma {X : Type _} (l : List X) : Σ n, Fin n → X := ⟨l.length, l.get⟩

/-- The σ-algebra on `List X`: comap from the `Σ n, Fin n → X` encoding. -/
instance List.instMeasurableSpace {X : Type _} [MeasurableSpace X] :
    MeasurableSpace (List X) :=
  MeasurableSpace.comap List.toSigma inferInstance

@[fun_prop]
theorem List.measurable_toSigma {X : Type _} [MeasurableSpace X] :
    Measurable (List.toSigma : List X → Σ n, Fin n → X) :=
  fun _ hS => ⟨_, hS, rfl⟩

/-- Sigma-fiber measurability: a function `f : (Σ a, β a) → γ` is measurable iff
its restriction to each fiber `fun b : β a => f ⟨a, b⟩` is measurable.

The Sigma σ-algebra is `⨅ a, (m a).map (Sigma.mk a)`, so this is direct from the
definition. Symmetric to `Sigma.instMeasurableSpace` being the coinduced σ-alg. -/
theorem measurable_sigma_iff {α : Type _} {β : α → Type _}
    [∀ a, MeasurableSpace (β a)] {γ : Type _} [MeasurableSpace γ]
    {f : (Σ a, β a) → γ} : Measurable f ↔ ∀ a, Measurable (fun b => f ⟨a, b⟩) := by
  refine ⟨fun hf a => hf.comp ?_, fun h S hS => MeasurableSpace.measurableSet_iInf.mpr fun a => h a hS⟩
  -- `Sigma.mk a` is measurable: target is `⨅ a', _.map (Sigma.mk a')`; under this,
  -- preimage of any set `S` under `Sigma.mk a` is required to be measurable.
  intro S hS
  exact MeasurableSpace.measurableSet_iInf.mp hS a

/-- Iterated application of `f` indexed by `Fin n`. Equals `(List.ofFn g).foldl f a`. -/
def List.foldlOfFn {α β : Type _} (f : α → β → α) : ∀ (n : ℕ), α → (Fin n → β) → α
  | 0, a, _ => a
  | n+1, a, g => List.foldlOfFn f n (f a (g 0)) (fun i => g i.succ)

theorem List.foldlOfFn_eq_foldl_ofFn {α β : Type _} (f : α → β → α) :
    ∀ (n : ℕ) (a : α) (g : Fin n → β), List.foldlOfFn f n a g = (List.ofFn g).foldl f a := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro a g
    show List.foldlOfFn f n (f a (g 0)) (fun i => g i.succ)
        = (List.ofFn g).foldl f a
    rw [ih]
    rw [List.ofFn_succ, List.foldl_cons]

theorem List.measurable_foldlOfFn {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β → α} (hf : Measurable (Function.uncurry f)) :
    ∀ n, Measurable (fun (p : (Fin n → β) × α) => List.foldlOfFn f n p.2 p.1) := by
  intro n
  induction n with
  | zero =>
    show Measurable (fun (p : (Fin 0 → β) × α) => p.2)
    exact measurable_snd
  | succ n ih =>
    have h0 : Measurable (fun p : (Fin (n+1) → β) × α => p.1 0) :=
      (measurable_pi_apply 0).comp measurable_fst
    have hsucc : Measurable
        (fun p : (Fin (n+1) → β) × α => (fun i : Fin n => p.1 i.succ)) := by
      refine Measurable.of_eval ?_
      intro i
      exact (measurable_pi_apply _).comp measurable_fst
    have hfa : Measurable (fun p : (Fin (n+1) → β) × α => f p.2 (p.1 0)) := by
      have hrw : (fun p : (Fin (n+1) → β) × α => f p.2 (p.1 0))
          = Function.uncurry f ∘ (fun p => (p.2, p.1 0)) := rfl
      rw [hrw]; exact hf.comp (measurable_snd.prodMk h0)
    have hcomp : Measurable
        (fun p : (Fin (n+1) → β) × α =>
          (((fun i : Fin n => p.1 i.succ) : Fin n → β), f p.2 (p.1 0))) :=
      hsucc.prodMk hfa
    exact ih.comp hcomp

/-- `Sigma.mk i` is a measurable embedding for the standard Σ σ-algebra. -/
theorem MeasurableEmbedding.sigmaMk {ι : Type _} {β : ι → Type _}
    [∀ i, MeasurableSpace (β i)] (i : ι) :
    MeasurableEmbedding (Sigma.mk i : β i → Σ j, β j) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Injective
    intro x y h; exact eq_of_heq (Sigma.mk.inj h).2
  · -- Measurable
    intro V hV
    exact MeasurableSpace.measurableSet_iInf.mp hV i
  · -- Image of measurable is measurable
    intro s hs
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

/-- **`List.foldl` is measurable** in `(list, init)` whenever the binary operation
`f` is jointly measurable.

Decomposition via `List.toSigma`: a function out of `List β` factors through the
per-length fibers `(Fin n → β) × α → α`, each of which is a finite composition
of `n` applications of `f`. Sigma-fiber measurability glues these together. -/
@[fun_prop]
theorem List.measurable_foldl {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β → α} (hf : Measurable (Function.uncurry f)) :
    Measurable (fun (p : List β × α) => p.1.foldl f p.2) := by
  -- Factor: foldl = H ∘ swap ∘ (toSigma × id), where
  --   H : Σ n, (Fin n → β) × α → α,   H ⟨n, (g, a)⟩ := List.foldlOfFn f n a g
  --   swap : (Σ n, Fin n → β) × α → Σ n, (Fin n → β) × α,
  --          swap ((⟨n, g⟩), a) := ⟨n, (g, a)⟩
  set H : (Σ n : ℕ, (Fin n → β) × α) → α :=
    fun s => List.foldlOfFn f s.1 s.2.2 s.2.1
  have hH : Measurable H := by
    rw [measurable_sigma_iff]
    intro n; exact List.measurable_foldlOfFn hf n
  -- Identity: foldl p = H (swap (toSigma p.1, p.2))
  have hgoal_eq : (fun p : List β × α => p.1.foldl f p.2)
      = H ∘ (fun q : (Σ k : ℕ, Fin k → β) × α =>
          (⟨q.1.1, (q.1.2, q.2)⟩ : Σ k : ℕ, (Fin k → β) × α))
        ∘ (fun p : List β × α => (List.toSigma p.1, p.2)) := by
    funext p
    show p.1.foldl f p.2 = List.foldlOfFn f (List.toSigma p.1).1 p.2 (List.toSigma p.1).2
    rw [List.foldlOfFn_eq_foldl_ofFn]
    show p.1.foldl f p.2 = (List.ofFn p.1.get).foldl f p.2
    rw [List.ofFn_get]
  rw [hgoal_eq]
  -- Compose measurabilities.
  refine hH.comp ?_
  refine Measurable.comp ?_
    ((List.measurable_toSigma).comp measurable_fst |>.prodMk measurable_snd)
  -- Prove `swap` measurable.
  intro U hU
  -- For each k₀, `Sigma.mk k₀ ⁻¹' U` is measurable in (Fin k₀ → β) × α.
  have hUfib : ∀ k₀, MeasurableSet
      ((@Sigma.mk ℕ (fun k => (Fin k → β) × α) k₀) ⁻¹' U) := by
    intro k₀
    exact MeasurableSpace.measurableSet_iInf.mp hU k₀
  -- swap ⁻¹' U = ⋃ k₀, (Sigma.mk k₀ × id) '' (Sigma.mk k₀ ⁻¹' U).
  have hrw : (fun q : (Σ k : ℕ, Fin k → β) × α =>
        (⟨q.1.1, (q.1.2, q.2)⟩ : Σ k : ℕ, (Fin k → β) × α)) ⁻¹' U
      = ⋃ k₀ : ℕ, (Prod.map (@Sigma.mk ℕ (fun k => Fin k → β) k₀) (id : α → α))
          '' ((@Sigma.mk ℕ (fun k => (Fin k → β) × α) k₀) ⁻¹' U) := by
    ext q
    obtain ⟨⟨k, g⟩, a⟩ := q
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
    constructor
    · intro h
      exact ⟨k, (g, a), h, rfl⟩
    · rintro ⟨k₀, ⟨g₀, a₀⟩, hga, hq⟩
      -- hq : (Sigma.mk k₀ g₀, a₀) = (⟨k, g⟩, a)
      rw [Prod.mk.injEq, Sigma.mk.injEq] at hq
      obtain ⟨⟨hk, hg⟩, ha⟩ := hq
      subst hk
      cases hg
      subst ha
      exact hga
  rw [hrw]
  refine MeasurableSet.iUnion fun k₀ => ?_
  -- Image of measurable under product of measurable embeddings.
  have hEmb : MeasurableEmbedding
      (Prod.map (@Sigma.mk ℕ (fun k => Fin k → β) k₀) (id : α → α)) :=
    (MeasurableEmbedding.sigmaMk k₀).prodMap MeasurableEmbedding.id
  exact hEmb.measurableSet_image' (hUfib k₀)

/-- Per-`n`, `Fin.snoc` is jointly measurable in `(g, b)`. -/
@[fun_prop]
theorem Fin.measurable_snoc {n : ℕ} {β : Type _} [MeasurableSpace β] :
    Measurable (fun (p : (Fin n → β) × β) => (@Fin.snoc n (fun _ => β) p.1 p.2) : (Fin n → β) × β → (Fin (n+1) → β)) := by
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

/-- The "snoc into Σ" function: `((⟨k, g⟩), b) ↦ ⟨k+1, Fin.snoc g b⟩`. Measurable. -/
@[fun_prop]
theorem measurable_sigma_snoc {β : Type _} [MeasurableSpace β] :
    Measurable (fun (q : (Σ k : ℕ, Fin k → β) × β) =>
      (⟨q.1.1 + 1, Fin.snoc q.1.2 q.2⟩ : Σ k : ℕ, Fin k → β)) := by
  intro U hU
  -- Strategy mirrors swap measurability in List.measurable_foldl.
  have hUfib : ∀ k₀, MeasurableSet
      ((@Sigma.mk ℕ (fun k => Fin k → β) k₀) ⁻¹' U) := by
    intro k₀
    exact MeasurableSpace.measurableSet_iInf.mp hU k₀
  -- Preimage decomposes by q.1.1 = k₀:
  have hrw : (fun q : (Σ k : ℕ, Fin k → β) × β =>
        (⟨q.1.1 + 1, Fin.snoc q.1.2 q.2⟩ : Σ k : ℕ, Fin k → β)) ⁻¹' U
      = ⋃ k₀ : ℕ, (Prod.map (@Sigma.mk ℕ (fun k => Fin k → β) k₀) (id : β → β))
          '' ((fun p : (Fin k₀ → β) × β => (@Fin.snoc k₀ (fun _ => β) p.1 p.2))
              ⁻¹' ((@Sigma.mk ℕ (fun k => Fin k → β) (k₀ + 1)) ⁻¹' U)) := by
    ext q
    obtain ⟨⟨k, g⟩, b⟩ := q
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
    constructor
    · intro h
      exact ⟨k, (g, b), h, rfl⟩
    · rintro ⟨k₀, ⟨g₀, b₀⟩, hsnoc, hq⟩
      rw [Prod.mk.injEq, Sigma.mk.injEq] at hq
      obtain ⟨⟨hk, hg⟩, hb⟩ := hq
      subst hk
      cases hg
      subst hb
      exact hsnoc
  rw [hrw]
  refine MeasurableSet.iUnion fun k₀ => ?_
  have hEmb : MeasurableEmbedding
      (Prod.map (@Sigma.mk ℕ (fun k => Fin k → β) k₀) (id : β → β)) :=
    (MeasurableEmbedding.sigmaMk k₀).prodMap MeasurableEmbedding.id
  refine hEmb.measurableSet_image' ?_
  exact Fin.measurable_snoc (hUfib (k₀ + 1))

/-- **`(L, x) ↦ L ++ [x]`** is measurable. -/
@[fun_prop]
theorem List.measurable_append_singleton {β : Type _} [MeasurableSpace β] :
    Measurable (fun (p : List β × β) => p.1 ++ [p.2]) := by
  rw [measurable_comap_iff (g := (List.toSigma : List β → Σ k, Fin k → β))]
  -- Goal: Measurable (toSigma ∘ (fun p => p.1 ++ [p.2])).
  -- Show equal to `measurable_sigma_snoc.fn ∘ (toSigma × id)`, which is measurable.
  have hrw : (List.toSigma : List β → Σ k, Fin k → β) ∘ (fun p : List β × β => p.1 ++ [p.2])
      = (fun q : (Σ k, Fin k → β) × β =>
          (⟨q.1.1 + 1, Fin.snoc q.1.2 q.2⟩ : Σ k, Fin k → β))
        ∘ (fun p : List β × β => (List.toSigma p.1, p.2)) := by
    funext p
    obtain ⟨L, x⟩ := p
    show (@Sigma.mk ℕ (fun k => Fin k → β) (L ++ [x]).length (L ++ [x]).get)
        = ⟨L.length + 1, @Fin.snoc L.length (fun _ => β) L.get x⟩
    have hlen : (L ++ [x]).length = L.length + 1 := by simp
    refine Sigma.ext hlen ?_
    refine (Fin.heq_fun_iff hlen).mpr ?_
    intro i
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
      have hi' : ¬ i.val < L.length := Nat.not_lt.mpr hi
      simp [hival]
  rw [hrw]
  exact measurable_sigma_snoc.comp
    ((List.measurable_toSigma).comp measurable_fst |>.prodMk measurable_snd)

/-- **Joint parameterized pushforward**. Given a jointly measurable function
`h : α × β → γ` and a kernel-valued source `k : α → Measure β` measurable that
is moreover an s-finite kernel, the parameterized pushforward
`fun a => (k a).map (fun b => h (a, b))` is measurable.

Proof: via `measurable_of_measurable_coe`, each `S`-evaluation reduces to
`fun a => k a (Prod.mk a ⁻¹' (h ⁻¹' S))`, which is exactly the section-measure
lemma `Kernel.measurable_kernel_prodMk_left` applied to the kernel `Kernel.mk k hk`.
The `IsSFiniteKernel` assumption ensures the section-measure machinery applies. -/
theorem Measure.measurable_map_uncurry {α β γ : Type _}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {h : α × β → γ} (hh : Measurable h)
    {k : α → Measure β} (hk : Measurable k)
    [hSF : ProbabilityTheory.IsSFiniteKernel (ProbabilityTheory.Kernel.mk k hk)] :
    Measurable (fun a : α => (k a).map (fun b => h (a, b))) := by
  refine Measure.measurable_of_measurable_coe _ ?_
  intro S hS
  have hpre : ∀ a, Measurable (fun b : β => h (a, b)) := fun a =>
    hh.comp (measurable_const.prodMk measurable_id)
  simp_rw [fun a => Measure.map_apply (hpre a) hS]
  set T := h ⁻¹' S with hT_def
  have hT : MeasurableSet T := hh hS
  have hrw : ∀ a, (fun b => h (a, b)) ⁻¹' S = Prod.mk a ⁻¹' T := fun _ => rfl
  simp_rw [hrw]
  show Measurable (fun a => k a (Prod.mk a ⁻¹' T))
  have hker_eq : ∀ a, k a = (ProbabilityTheory.Kernel.mk k hk) a :=
    fun _ => by rw [ProbabilityTheory.Kernel.coe_mk]
  simp_rw [hker_eq]
  exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left hT

/-- Candidate measure built pointwise from a `ℕ`-monotone family of measures.

For a monotone family `μ : ℕ → Measure α`, define `myν` via `Measure.ofMeasurable`
with `myν s := ⨆ i, μ i s` (for measurable `s`). The σ-additivity reduces to
swapping `⨆` past `∑'` on monotone ENNReal data. -/
noncomputable def Measure.monotoneSupNat {α : Type _} [MeasurableSpace α]
    (μ : ℕ → Measure α) (hmono : Monotone μ) : Measure α :=
  Measure.ofMeasurable (fun s _ => ⨆ i, μ i s)
    (by simp)
    (fun f hf hd => by
      have h1 : ∀ i, μ i (⋃ k, f k) = ∑' k, μ i (f k) :=
        fun i => measure_iUnion hd hf
      have hmono' : ∀ k, Monotone (fun i => μ i (f k)) :=
        fun k i j hij => hmono hij (f k)
      simp_rw [h1, ENNReal.tsum_eq_iSup_sum]
      rw [iSup_comm]
      refine iSup_congr fun s => ?_
      exact (ENNReal.finsetSum_iSup_of_monotone
        (s := s) (f := fun k i => μ i (f k)) hmono').symm)

theorem Measure.monotoneSupNat_apply {α : Type _} [MeasurableSpace α]
    (μ : ℕ → Measure α) (hmono : Monotone μ)
    {s : Set α} (hs : MeasurableSet s) :
    Measure.monotoneSupNat μ hmono s = ⨆ i, μ i s :=
  Measure.ofMeasurable_apply _ hs

/-- For a `ℕ`-monotone family of measures, the pointwise sup `(⨆ i, μ i) s` on
measurable sets `s` equals the sup of values `⨆ i, μ i s`. -/
theorem Measure.iSup_apply_of_monotone {α : Type _} [MeasurableSpace α]
    (μ : ℕ → Measure α) (hmono : Monotone μ)
    {s : Set α} (hs : MeasurableSet s) :
    (⨆ i, μ i) s = ⨆ i, μ i s := by
  have h : Measure.monotoneSupNat μ hmono = ⨆ i, μ i := by
    apply le_antisymm
    · rw [Measure.le_iff]; intro t ht
      rw [Measure.monotoneSupNat_apply _ _ ht]
      exact iSup_le fun i => Measure.le_iff.mp (le_iSup μ i) t ht
    · refine iSup_le fun i => ?_
      rw [Measure.le_iff]; intro t ht
      rw [Measure.monotoneSupNat_apply _ _ ht]
      exact le_iSup (fun j => μ j t) i
  rw [← h, Measure.monotoneSupNat_apply _ _ hs]

/-- **Pointwise `ℕ`-monotone sup of measure-valued functions is measurable**.

For a family `μ : ℕ → α → Measure β` of measurable maps, the pointwise
supremum `fun a => ⨆ i, μ i a` is measurable into `Measure β`, provided that at
every `a`, the family is monotone in `i`. -/
theorem Measure.measurable_iSup_countable {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : ℕ → α → Measure β} (hμ : ∀ i, Measurable (μ i))
    (hmono : ∀ a, Monotone (fun i => μ i a)) :
    Measurable (fun a : α => ⨆ i, μ i a) := by
  refine Measure.measurable_of_measurable_coe _ ?_
  intro s hs
  simp_rw [fun a => Measure.iSup_apply_of_monotone (μ · a) (hmono a) hs]
  exact Measurable.iSup fun i => (Measure.measurable_coe hs).comp (hμ i)
