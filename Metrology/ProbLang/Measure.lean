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

/-! ## `Possible`: a positive-mass point of a measure

Stated as `∃ p > 0, p • dirac ρ ≤ μ` rather than `0 < μ {ρ}` so that it never names `{ρ}`
and needs no `MeasurableSingletonClass`; the two agree under it (`possible_iff_pos`). -/
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

instance [MeasurableSpace α] : MeasurableSpace (Option α) :=
  MeasurableSpace.comap (Equiv.optionEquivSumPUnit.{0, _} α) inferInstance

@[fun_prop]
theorem measurable_some [MeasurableSpace α] : Measurable (Option.some : α → _) := by
  refine measurable_comap_iff.mpr ?_
  unfold Function.comp
  simp [Equiv.optionEquivSumPUnit]
  fun_prop

/-! ### Option-cylinders -/

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

@[simp] def OptionCyl.flatten {α : Type _} : OptionCyl α → Set (Option α)
  | none => {none}
  | some S => some '' S

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

theorem Set.image_eq_range_inter_preimage_option
    {α β : Type _} (c : α → β) (π : β → Option α)
    (hπ : ∀ x, π (c x) = some x) (T : Set α) :
    c '' T = Set.range c ∩ π ⁻¹' (some '' T) := by
  ext b; aesop

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

def Option.pair {α β : Type _} : Option α × Option β → Option (α × β)
  | (some a, some b) => some (a, b)
  | _ => none

@[simp] theorem Option.pair_preimage_some {α β : Type _} (S : Set (α × β)) :
    Option.pair ⁻¹' (some '' S) = (Prod.map some some) '' S := by
  ext ⟨x, y⟩; cases x <;> cases y <;> simp [Option.pair, Prod.map]

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

/-! ### Cover-restricted measurability -/

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

theorem Measurable.of_cover_inter_preimage
    {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {cov : Set α} {f : α → β}
    (h : ∀ G : Set β, MeasurableSet G → MeasurableSet (cov ∩ f ⁻¹' G)) :
    Measurable (fun (b : ↥cov) => f b.val) := fun G hG => by
  rw [subtype_preimage_eq]
  exact MeasurableSet.preimage (h G hG) measurable_subtype_coe

theorem MeasurableSet.cover_inter_preimage_of_subtype
    {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {cov : Set α} (hcov : MeasurableSet cov) {f : α → β}
    (h : Measurable (fun (b : ↥cov) => f b.val)) :
    ∀ G : Set β, MeasurableSet G → MeasurableSet (cov ∩ f ⁻¹' G) := fun G hG => by
  rw [← Set.inter_self cov, Set.inter_assoc, ← Subtype.image_preimage_coe]
  exact MeasurableSet.subtype_image hcov ((subtype_preimage_eq f G) ▸ h hG)

/-- Non-discrete variant of `Discrete.map_singleton_pos`. Injectivity is essential: a constant
`f` collapses non-atomic mass onto one point. -/
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

theorem Measure.bind_map_comm {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (k : α → Measure β) (f : β → γ) (Hf : Measurable f) (Hae : AEMeasurable k μ):
    (μ.bind k).map f = μ.bind (fun a => (k a).map f) := by
  refine Measure.ext fun S hS => ?_
  have H1 : MeasurableSet (f ⁻¹' S) := MeasurableSet.preimage hS Hf
  have H2 : AEMeasurable (fun a ↦ map f (k a)) μ :=
    (measurable_map f Hf).comp_aemeasurable' Hae
  rw [Measure.map_apply Hf hS,
      Measure.bind_apply H1 Hae,
      Measure.bind_apply hS H2]
  simp_rw [Measure.map_apply Hf hS]

abbrev count (f : α → ENNReal) [MeasurableSpace α] := Measure.count.withDensity f

/-! ### `MeasurableEmbedding` from a generating π-system -/

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

/-! ## Shape-stratified measurability

Measurability is assembled from cells `{p | shape p = s ∧ f p ∈ U}`, one per shape. -/

namespace StructRec

variable {T α : Type _} [MeasurableSpace T] [MeasurableSpace α]
variable {Sh : Type _} (shape : T → Sh)
variable {f : T → α}

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

/-! Variants with an extra measurable parameter `β`; the cell is over `β × T`. -/

variable {β : Type _} [MeasurableSpace β]
variable {g : β → T → α}

/-- Cell of a data leaf such as `lit (b' : β') (e : T)`. -/
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

def List.toSigma {X : Type _} (l : List X) : Σ n, Fin n → X := ⟨l.length, l.get⟩

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

/-- A map out of `(Σ k, Fin k → β) × γ` is measurable if it is measurable on each length-`k` slice. -/
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
  have hfoldlOfFn : Measurable fun q : (Σ k : ℕ, Fin k → β) × α => List.foldlOfFn f q.1.1 q.2 q.1.2 :=
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

/-- Each evaluation is `a ↦ k a (Prod.mk a ⁻¹' (h ⁻¹' S))`, a section measure of the s-finite
kernel `Kernel.mk k hk`. -/
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

/-- `s ↦ ⨆ i, μ i s` for a monotone family; σ-additivity swaps `⨆` past `∑'`. -/
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
      exact iSup_congr fun s => (ENNReal.finsetSum_iSup_of_monotone hmono').symm)

theorem Measure.monotoneSupNat_apply {α : Type _} [MeasurableSpace α]
    (μ : ℕ → Measure α) (hmono : Monotone μ)
    {s : Set α} (hs : MeasurableSet s) :
    Measure.monotoneSupNat μ hmono s = ⨆ i, μ i s :=
  Measure.ofMeasurable_apply _ hs

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

theorem Measure.measurable_iSup_countable {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : ℕ → α → Measure β} (hμ : ∀ i, Measurable (μ i))
    (hmono : ∀ a, Monotone (fun i => μ i a)) :
    Measurable (fun a : α => ⨆ i, μ i a) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [fun a => Measure.iSup_apply_of_monotone (μ · a) (hmono a) hs]
  exact Measurable.iSup fun i => (Measure.measurable_coe hs).comp (hμ i)
