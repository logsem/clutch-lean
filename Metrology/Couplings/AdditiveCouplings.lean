module

public import Metrology.Couplings.ApproximateCouplings

/-! # Additive couplings

Approxis-style couplings with additive slack `ε`, identified with `codensity tv` in
`Bridges/AddCoupl.lean`. -/

@[expose] public section

section AdditiveCoupling

open MeasureTheory Measure Set

variable {α β α' β' : Type _}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace α'] [MeasurableSpace β']

/-! ## Definitions -/

/-- Approximate relational coupling with additive error slack `ε`. -/
def AddCoupl (ε : ENNReal) (Φ : Set (α × β)) (μₗ : Measure α) (μᵣ : Measure β) : Prop :=
  ARCoupling (· + ε) Φ μₗ μᵣ

-- reducible so an `ExpCoupl` hypothesis still applies directly to its test functions and hypotheses
/-- Coupling in expectation at cost `E₂`: the test form of `tv.codensity ε E₂` for sub-probability
`μ₁` (`expCoupl_iff_codensity_tv`). -/
@[reducible] def ExpCoupl (ε : ENNReal) (E₂ : α → β → ENNReal)
    (μ₁ : Measure α) (μ₂ : Measure β) : Prop :=
  ∀ h₁ h₂, Measurable h₁ → Measurable h₂ →
    (∀ a, h₁ a ≤ 1) → (∀ b, h₂ b ≤ 1) → (∀ a b, h₁ a ≤ h₂ b + E₂ a b) →
    ∫⁻ a, h₁ a ∂μ₁ ≤ ∫⁻ b, h₂ b ∂μ₂ + ε

namespace AddCoupl

variable {ε ε' : ENNReal}

/-! ## Basic rules -/

/-- Every measure is additively coupled with itself along equality. -/
theorem refl (μ : Measure α) : AddCoupl ε (fun v => v.1 = v.2) μ μ :=
  ARCoupling.refl μ le_self_add

/-- Dirac measures at related points are additively coupled. -/
theorem dirac {a : α} {b : β} (S : Set (α × β)) (H : S (a, b)) :
    AddCoupl ε S (.dirac a) (.dirac b) :=
  ARCoupling.dirac le_self_add S H

/-- The zero measure on the left is coupled with anything (Rocq `ARcoupl_dzero`). -/
theorem zero_left (S : Set (α × β)) (μᵣ : Measure β) : AddCoupl ε S 0 μᵣ :=
  ARCoupling.zero_left S μᵣ

/-- A measure of mass at most the slack is coupled with the zero measure on the right. -/
theorem zero_right (S : Set (α × β)) {μₗ : Measure α} (Hε : μₗ .univ ≤ ε) : AddCoupl ε S μₗ 0 :=
  ARCoupling.zero_right S (by simpa using Hε)

variable {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}

/-- Additive couplings are monotone in the relation. -/
theorem mono_rel {S' : Set (α × β)} (HS : S ⊆ S') (H : AddCoupl ε S μₗ μᵣ) : AddCoupl ε S' μₗ μᵣ :=
  ARCoupling.mono_rel HS H

/-- Additive couplings are monotone in the slack. -/
theorem mono_grading (Hε : ε ≤ ε') (H : AddCoupl ε S μₗ μᵣ) : AddCoupl ε' S μₗ μᵣ :=
  ARCoupling.mono_F (fun x => by gcongr) H

/-- An `ARCoupling` up to the identity is an additive coupling at any slack. -/
theorem of_arCoupling_id (H : ARCoupling (fun x => x) S μₗ μᵣ) : AddCoupl ε S μₗ μᵣ :=
  ARCoupling.mono_F (fun _ => le_self_add) H

/-- A coupling at every `ε + δ`, `δ > 0`, is one at `ε`. -/
theorem limit (H : ∀ δ, 0 < δ → AddCoupl (ε + δ) S μₗ μᵣ) : AddCoupl ε S μₗ μᵣ := by
  intro f g Hfg
  refine ENNReal.le_of_forall_pos_le_add fun δ Hδ _ => ?_
  rw [add_assoc]
  exact H δ (by exact_mod_cast Hδ) f g Hfg

/-- The left mass is at most the right mass plus `ε`. -/
theorem measure_univ_le_add (H : AddCoupl ε S μₗ μᵣ) : μₗ .univ ≤ μᵣ .univ + ε := by
  let oneA : CouplingFunction α := .mk (fun _ => 1) ⟨measurable_const, fun _ => le_refl _⟩
  let oneB : CouplingFunction β := .mk (fun _ => 1) ⟨measurable_const, fun _ => le_refl _⟩
  simpa [oneA, oneB] using H oneA oneB (fun _ => le_refl _)

/-- A coupling with the zero measure on the right bounds the left mass by `ε`. -/
theorem measure_univ_le_of_zero_right (H : AddCoupl ε S μₗ 0) : μₗ .univ ≤ ε := by
  simpa using measure_univ_le_add H

/-- A coupling with slack at least one holds for any left measure of mass at most one (Rocq
`ARcoupl_1`). -/
theorem trivial_of_one_le (Hε : 1 ≤ ε) (Hmass : μₗ univ ≤ 1) : AddCoupl ε S μₗ μᵣ := by
  rintro ⟨f, Hfm, Hfb⟩ ⟨g, Hgm, Hgb⟩ _
  calc ∫⁻ x, f x ∂μₗ
      _ ≤ μₗ univ := lintegral_le_meas Hfb (by simp)
      _ ≤ 1 := Hmass
      _ ≤ ε := Hε
      _ ≤ ∫⁻ y, g y ∂μᵣ + ε := le_add_self

/-! ## Bind rules -/

section Bind

variable {T : Set (α' × β')} {f : α → Measure α'} {g : β → Measure β'} (Hfm : Measurable f)
  (Hgm : Measurable g)

include Hfm Hgm

/-- Advanced-composition bind: the continuation's slack `E₂ b` depends on the right sample and
only its expectation is charged. -/
theorem bind_adv {E₂ : β → ENNReal} (HE₂m : Measurable E₂) (Hfsprob : ∀ a, (f a) .univ ≤ 1)
    (HE₂sum : ∫⁻ b, E₂ b ∂μᵣ ≤ ε') (Hcpl : AddCoupl ε S μₗ μᵣ)
    (Hbind : ∀ {a b}, S (a, b) → AddCoupl (E₂ b) T (f a) (g b)) :
    AddCoupl (ε + ε') T (μₗ.bind f) (μᵣ.bind g) := by
  rintro ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'
  have HFle a : ∫⁻ y, f' y ∂f a ≤ 1 := (lintegral_le_meas Hf'b (by simp)).trans (Hfsprob a)
  -- outer test pair: left test as is, right test plus E₂, capped at 1; ordered on S by Hbind
  let Fh : CouplingFunction α := .mk (fun a => ∫⁻ y, f' y ∂(f a)) ⟨?Fm, fun a => ?Fb⟩
  case Fm => exact measurable_lintegral Hf'm |>.comp Hfm
  case Fb => exact HFle a
  let Gh : CouplingFunction β := .mk (fun b => (∫⁻ y, g' y ∂(g b) + E₂ b) ⊓ 1) ⟨?Gm, fun b => ?Gb⟩
  case Gm => exact (((measurable_lintegral Hg'm).comp Hgm).add HE₂m).inf measurable_const
  case Gb => exact inf_le_right
  have HFhGh {a b} (HS : S (a, b)) : Fh.1 a ≤ Gh.1 b := by
    simp only [Gh, le_inf_iff]
    exact ⟨Hbind HS ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g', (HFle a).trans (by simp)⟩
  rw [lintegral_bind Hfm.aemeasurable Hf'm.aemeasurable,
      lintegral_bind Hgm.aemeasurable Hg'm.aemeasurable]
  calc ∫⁻ a, ∫⁻ x, f' x ∂(f a) ∂μₗ
      _ = ∫⁻ a, Fh.1 a ∂μₗ := rfl
      _ ≤ ∫⁻ b, Gh.1 b ∂μᵣ + ε := Hcpl Fh Gh HFhGh
      _ ≤ ∫⁻ b, (∫⁻ x, g' x ∂(g b) + E₂ b) ∂μᵣ + ε := by
            gcongr with b
            exact inf_le_left
      _ = ∫⁻ b, ∫⁻ x, g' x ∂(g b) ∂μᵣ + ∫⁻ b, E₂ b ∂μᵣ + ε := by
            rw [lintegral_add_right _ HE₂m]
      _ ≤ ∫⁻ b, ∫⁻ x, g' x ∂(g b) ∂μᵣ + ε' + ε := by
            gcongr
      _ = ∫⁻ b, ∫⁻ x, g' x ∂(g b) ∂μᵣ + (ε + ε') := by
            rw [add_assoc, add_comm ε' ε]

/-- `bind_adv` with the continuation's slack `E₂ a` indexed by the left sample. -/
theorem bind_adv_lhs {E₂ : α → ENNReal} (HE₂m : Measurable E₂) (Hfsprob : ∀ a, (f a) .univ ≤ 1)
    (HE₂sum : ∫⁻ a, E₂ a ∂μₗ ≤ ε') (Hcpl : AddCoupl ε S μₗ μᵣ)
    (Hbind : ∀ {a b}, S (a, b) → AddCoupl (E₂ a) T (f a) (g b)) :
    AddCoupl (ε + ε') T (μₗ.bind f) (μᵣ.bind g) := by
  rintro ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'
  have HFle a : ∫⁻ y, f' y ∂f a ≤ 1 := (lintegral_le_meas Hf'b (by simp)).trans (Hfsprob a)
  -- outer test pair: left test minus the inner slack E₂ a, right test capped at 1; ordered on S
  -- by Hbind
  let Fh : CouplingFunction α := .mk (fun a => ∫⁻ y, f' y ∂(f a) - E₂ a) ⟨?Fm, fun a => ?Fb⟩
  case Fm => exact (measurable_lintegral Hf'm |>.comp Hfm).sub HE₂m
  case Fb => exact tsub_le_self.trans (HFle a)
  let Gh : CouplingFunction β := .mk (fun b => (∫⁻ y, g' y ∂(g b)) ⊓ 1) ⟨?Gm, fun b => ?Gb⟩
  case Gm => exact (measurable_lintegral Hg'm |>.comp Hgm).inf measurable_const
  case Gb => exact inf_le_right
  have HFhGh {a b} (HS : S (a, b)) : Fh.1 a ≤ Gh.1 b := by
    simp only [Gh, le_inf_iff]
    exact ⟨tsub_le_iff_right.mpr (Hbind HS ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'),
      tsub_le_self.trans (HFle a)⟩
  rw [lintegral_bind Hfm.aemeasurable Hf'm.aemeasurable,
      lintegral_bind Hgm.aemeasurable Hg'm.aemeasurable]
  calc ∫⁻ a, ∫⁻ x, f' x ∂(f a) ∂μₗ
      _ ≤ ∫⁻ a, Fh.1 a + E₂ a ∂μₗ := lintegral_mono fun _ => le_tsub_add
      _ = ∫⁻ a, Fh.1 a ∂μₗ + ∫⁻ a, E₂ a ∂μₗ := by
            rw [lintegral_add_right _ HE₂m]
      _ ≤ ∫⁻ a, Fh.1 a ∂μₗ + ε' := by gcongr
      _ ≤ (∫⁻ b, Gh.1 b ∂μᵣ + ε) + ε' := by
            gcongr
            exact Hcpl Fh Gh HFhGh
      _ ≤ (∫⁻ b, ∫⁻ x, g' x ∂(g b) ∂μᵣ + ε) + ε' := by
            gcongr with b
            exact inf_le_left
      _ = ∫⁻ b, ∫⁻ x, g' x ∂(g b) ∂μᵣ + (ε + ε') := by
            rw [add_assoc]

/-- Couplings of the heads and of the continuations at related points couple the binds. -/
theorem bind (Hμₗ : μₗ .univ ≤ 1) (Hfsprob : ∀ a, (f a) .univ ≤ 1) (Hcpl : AddCoupl ε S μₗ μᵣ)
    (Hbind : ∀ {a b}, S (a, b) → AddCoupl ε' T (f a) (g b)) :
    AddCoupl (ε + ε') T (μₗ.bind f) (μᵣ.bind g) :=
  bind_adv_lhs Hfm Hgm measurable_const Hfsprob
    (by rw [lintegral_const]; exact mul_le_of_le_one_right' Hμₗ) Hcpl Hbind

/-- Kantorovich-style bind with slack `E₂ a b` depending on both samples
(Rocq `ARcoupl_dbind_adv_kanto_plain`). -/
theorem bind_adv_kanto {E₂ : α → β → ENNReal} (Hfsprob : ∀ a, (f a) .univ ≤ 1)
    (Hgsprob : ∀ b, (g b) .univ ≤ 1) (Hexp : ExpCoupl ε E₂ μₗ μᵣ)
    (Hcont : ∀ a b, AddCoupl (E₂ a b) T (f a) (g b)) : AddCoupl ε T (μₗ.bind f) (μᵣ.bind g) := by
  rintro ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'
  let X := fun a => ∫⁻ x, f' x ∂(f a)
  let Y := fun b => ∫⁻ y, g' y ∂(g b)
  have HXm : Measurable X := (measurable_lintegral Hf'm).comp Hfm
  have HYm : Measurable Y := (measurable_lintegral Hg'm).comp Hgm
  have HXb a : X a ≤ 1 := (lintegral_le_meas Hf'b (by simp)).trans (Hfsprob a)
  have HYb b : Y b ≤ 1 := (lintegral_le_meas Hg'b (by simp)).trans (Hgsprob b)
  have HXY a b : X a ≤ Y b + E₂ a b := Hcont a b ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'
  rw [lintegral_bind Hfm.aemeasurable Hf'm.aemeasurable,
      lintegral_bind Hgm.aemeasurable Hg'm.aemeasurable]
  exact Hexp X Y HXm HYm HXb HYb HXY

end Bind

/-! ## Chaining with equality couplings -/

/-- Chaining an equality coupling with a coupling adds the slacks. -/
theorem eq_trans_l {ε₁ ε₂ : ENNReal} {R : Set (α × β)} {μ₁ μ₂ : Measure α} {μ₃ : Measure β}
    (Heq : AddCoupl ε₁ (fun v => v.1 = v.2) μ₁ μ₂) (HR : AddCoupl ε₂ R μ₂ μ₃) :
    AddCoupl (ε₁ + ε₂) R μ₁ μ₃ := by
  intro f g Hfg
  calc ∫⁻ x, f.1 x ∂μ₁
      _ ≤ ∫⁻ x, f.1 x ∂μ₂ + ε₁ := Heq f f (fun {a b} (h : a = b) => h ▸ le_refl _)
      _ ≤ (∫⁻ x, g.1 x ∂μ₃ + ε₂) + ε₁ := by gcongr; exact HR f g Hfg
      _ = ∫⁻ x, g.1 x ∂μ₃ + (ε₁ + ε₂) := by rw [add_assoc, add_comm ε₂ ε₁]

/-- Chaining a coupling with an equality coupling adds the slacks. -/
theorem eq_trans_r {ε₁ ε₂ : ENNReal} {R : Set (α × β)} {μ₁ : Measure α} {μ₂ μ₃ : Measure β}
    (HR : AddCoupl ε₁ R μ₁ μ₂) (Heq : AddCoupl ε₂ (fun v => v.1 = v.2) μ₂ μ₃) :
    AddCoupl (ε₁ + ε₂) R μ₁ μ₃ := by
  intro f g Hfg
  calc ∫⁻ x, f.1 x ∂μ₁
      _ ≤ ∫⁻ x, g.1 x ∂μ₂ + ε₁ := HR f g Hfg
      _ ≤ (∫⁻ x, g.1 x ∂μ₃ + ε₂) + ε₁ := by
            gcongr; exact Heq g g (fun {a b} (h : a = b) => h ▸ le_refl _)
      _ = ∫⁻ x, g.1 x ∂μ₃ + (ε₁ + ε₂) := by rw [add_assoc, add_comm ε₂ ε₁]

/-! ## Pushforward and limits of measures -/

/-- Additive couplings push forward along measurable maps that preserve the relation. -/
theorem map {R : Set (α' × β')} (f : α → α') (g : β → β') (Hfm : Measurable f) (Hgm : Measurable g)
    (HR : ∀ {a b}, S (a, b) → R (f a, g b)) (H : AddCoupl ε S μₗ μᵣ) :
    AddCoupl ε R (μₗ.map f) (μᵣ.map g) := by
  rintro ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hle
  let F : CouplingFunction α := .mk (f' ∘ f) ⟨Hf'm.comp Hfm, fun _ => Hf'b _⟩
  let G : CouplingFunction β := .mk (g' ∘ g) ⟨Hg'm.comp Hgm, fun _ => Hg'b _⟩
  rw [lintegral_map Hf'm Hfm, lintegral_map Hg'm Hgm]
  exact H F G fun HS => Hle (HR HS)

/-- A left measure dominated on measurable tests by a family of coupled `ν i` is coupled too. -/
theorem iSup_left {ι : Sort _} {ν : ι → Measure α}
    (hle : ∀ f, Measurable f → ∫⁻ a, f a ∂μₗ ≤ ⨆ i, ∫⁻ a, f a ∂(ν i))
    (H : ∀ i, AddCoupl ε S (ν i) μᵣ) : AddCoupl ε S μₗ μᵣ := by
  rintro ⟨f, hfm, hfb⟩ G hfg
  exact (hle f hfm).trans (iSup_le fun i => H i ⟨f, hfm, hfb⟩ G hfg)

-- discreteness is essential: fibrewise sup/inf lifts of test functions are not measurable in
-- general; to take a limit under a pushforward use `iSup_left`
/-- Inverse of `map`: a coupling of images pulls back along the maps. -/
theorem map_inv [DiscreteMeasurableSpace α'] [DiscreteMeasurableSpace β'] {R : Set (α' × β')}
    (f : α → α') (g : β → β') (Hfm : Measurable f) (Hgm : Measurable g)
    (H : AddCoupl ε R (μₗ.map f) (μᵣ.map g)) : AddCoupl ε (fun v => R (f v.1, g v.2)) μₗ μᵣ := by
  rintro ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hle
  let fT := fun a' => ⨆ (a : α) (_ : f a = a'), f' a
  let gT := fun b' => (⨅ (b : β) (_ : g b = b'), g' b) ⊓ 1
  have HfTm : Measurable fT := .of_discrete
  have HgTm : Measurable gT := .of_discrete
  have HfTb a' : fT a' ≤ 1 := iSup_le fun a => iSup_le fun _ => Hf'b a
  let FT : CouplingFunction α' := ⟨fT, HfTm, HfTb⟩
  let GT : CouplingFunction β' := ⟨gT, HgTm, fun _ => inf_le_right⟩
  have HFG {a' b'} (HR : R (a', b')) : FT.1 a' ≤ GT.1 b' := by
    simp only [FT, GT, gT, le_inf_iff]
    refine ⟨?_, HfTb a'⟩
    refine iSup_le fun a => iSup_le fun Ha => le_iInf fun b => le_iInf fun Hb => ?_
    subst Ha Hb
    exact Hle HR
  have Hf'_le a : f' a ≤ fT (f a) := le_iSup₂_of_le a rfl le_rfl
  have HgT_le b : gT (g b) ≤ g' b := calc (⨅ (b' : β) (_ : g b' = g b), g' b') ⊓ 1
      _ ≤ ⨅ (b' : β) (_ : g b' = g b), g' b' := inf_le_left
      _ ≤ g' b := iInf_le_of_le b (iInf_le_of_le rfl le_rfl)
  calc ∫⁻ a, f' a ∂μₗ
      _ ≤ ∫⁻ a, fT (f a) ∂μₗ := lintegral_mono Hf'_le
      _ = ∫⁻ a', fT a' ∂(μₗ.map f) := (lintegral_map HfTm Hfm).symm
      _ ≤ ∫⁻ b', gT b' ∂(μᵣ.map g) + ε := H FT GT HFG
      _ = ∫⁻ b, gT (g b) ∂μᵣ + ε := by rw [lintegral_map HgTm Hgm]
      _ ≤ ∫⁻ b, g' b ∂μᵣ + ε := by gcongr; exact HgT_le _

/-! ## Restricting the relation to where the measures live -/

-- countability-free: for `μᵣ = dirac b`, `T = {b}` pins the right sample with no atom enumeration
/-- Strengthen the relation with `v.2 ∈ T` for a set `T` carrying all of `μᵣ`. -/
theorem concentrated_R {T : Set β} (hT : MeasurableSet T) (hconc : μᵣ Tᶜ = 0)
    (H : AddCoupl ε S μₗ μᵣ) : AddCoupl ε (fun v => S v ∧ v.2 ∈ T) μₗ μᵣ := by
  classical
  rintro ⟨f, Hfm, Hfb⟩ ⟨g, Hgm, Hgb⟩ Hle
  let g' := fun b => if b ∈ T then g b else 1
  have Hg'm : Measurable g' := Measurable.ite hT Hgm measurable_const
  have Hg'b b : g' b ≤ 1 := by
    simp only [g']
    split_ifs
    exacts [Hgb b, le_refl _]
  let G : CouplingFunction β := ⟨g', Hg'm, Hg'b⟩
  have HFG {a b} (HS : S (a, b)) : f a ≤ G.1 b := by
    simp only [G, g']
    split_ifs with hbT
    exacts [Hle ⟨HS, hbT⟩, Hfb a]
  have hae : g =ᶠ[ae μᵣ] g' := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun b hb => ?_) hconc
    simp only [mem_compl_iff]
    intro hbT
    exact hb (by simp only [g', ite_eq_left hbT])
  rw [lintegral_congr_ae hae]
  exact H ⟨f, Hfm, Hfb⟩ G HFG

/-- Strengthen the relation with `v.1 ∈ T` for a set `T` carrying all of `μₗ`. -/
theorem concentrated_L {T : Set α} (hT : MeasurableSet T) (hconc : μₗ Tᶜ = 0)
    (H : AddCoupl ε S μₗ μᵣ) : AddCoupl ε (fun v => S v ∧ v.1 ∈ T) μₗ μᵣ := by
  classical
  rintro ⟨f, Hfm, Hfb⟩ ⟨g, Hgm, Hgb⟩ Hle
  let f' := fun a => if a ∈ T then f a else 0
  have Hf'm : Measurable f' := Measurable.ite hT Hfm measurable_const
  have Hf'b a : f' a ≤ 1 := by
    simp only [f']
    split_ifs
    exacts [Hfb a, zero_le_one]
  let F : CouplingFunction α := ⟨f', Hf'm, Hf'b⟩
  have HFG {a b} (HS : S (a, b)) : F.1 a ≤ g b := by
    simp only [F, f']
    split_ifs with haT
    exacts [Hle ⟨HS, haT⟩, zero_le]
  have hae : f =ᶠ[ae μₗ] f' := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun a ha => ?_) hconc
    simp only [mem_compl_iff]
    intro haT
    exact ha (by simp only [f', ite_eq_left haT])
  rw [lintegral_congr_ae hae]
  exact H F ⟨g, Hgm, Hgb⟩ HFG

/-- A measure on a countable space lives on its atoms. -/
private theorem measure_compl_atoms_null [Countable α] (μ : Measure α) : μ {a | μ {a} ≠ 0}ᶜ = 0 :=
  mem_ae_iff.1 (ae_iff_of_countable.2 fun _ h => h)

-- false for diffuse measures, hence the countability
/-- Strengthen the relation to the product of the atoms of both measures. -/
theorem pos_R [Countable α] [Countable β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (H : AddCoupl ε S μₗ μᵣ) : AddCoupl ε (fun v => S v ∧ μₗ {v.1} ≠ 0 ∧ μᵣ {v.2} ≠ 0) μₗ μᵣ :=
  mono_rel (by rintro ⟨a, b⟩ ⟨⟨hS, haL⟩, hbR⟩; exact ⟨hS, haL, hbR⟩) <|
    concentrated_R (to_countable _).measurableSet (measure_compl_atoms_null μᵣ) <|
    concentrated_L (to_countable _).measurableSet (measure_compl_atoms_null μₗ) H

/-! ## Equality couplings and sets -/

/-- A coupling bounds `μₗ T` by `μᵣ T'` up to the slack when related points send `T` into `T'`. -/
theorem measure_le_add {T : Set α} {T' : Set β} (hT : MeasurableSet T) (hT' : MeasurableSet T')
    (Hcpl : AddCoupl ε S μₗ μᵣ) (Himp : ∀ a b, S (a, b) → a ∈ T → b ∈ T') : μₗ T ≤ μᵣ T' + ε := by
  classical
  let fInd : CouplingFunction α :=
    .mk (T.indicator 1) ⟨measurable_const.indicator hT, fun x => indicator_le_self _ _ x⟩
  let gInd : CouplingFunction β :=
    .mk (T'.indicator 1) ⟨measurable_const.indicator hT', fun x => indicator_le_self _ _ x⟩
  have hMain := Hcpl fInd gInd fun {a b} hS => by
    by_cases ha : a ∈ T
    · simp [fInd, gInd, indicator_of_mem ha, indicator_of_mem (Himp a b hS ha)]
    · simp [fInd, indicator_of_notMem ha]
  simpa [fInd, gInd, lintegral_indicator_one hT, lintegral_indicator_one hT'] using hMain

/-- An equality coupling bounds the measure of every measurable set (Rocq `ARcoupl_eq_elim`). -/
theorem eq_elim {μ ν : Measure α} (h : AddCoupl ε {p : α × α | p.1 = p.2} μ ν) {T : Set α}
    (hT : MeasurableSet T) : μ T ≤ ν T + ε :=
  measure_le_add hT hT h fun a b (hab : a = b) ha => hab ▸ ha

/-- Equality couplings of error zero both ways force equal measures (Rocq `ARcoupl_antisym`). -/
theorem eq_of_eq_zero {μ ν : Measure α}
    (h₁ : AddCoupl 0 {p : α × α | p.1 = p.2} μ ν)
    (h₂ : AddCoupl 0 {p : α × α | p.1 = p.2} ν μ) :
    μ = ν := by
  refine ext fun S hS => le_antisymm ?_ ?_
  · simpa using eq_elim h₁ hS
  · simpa using eq_elim h₂ hS

/-! ## Swapping sides -/

/-- Additive couplings of measures of equal mass at most one swap sides. -/
theorem swap (Hmass : μₗ .univ = μᵣ .univ) (HμₗP : μₗ .univ ≤ 1) (HμᵣP : μᵣ .univ ≤ 1)
    (H : AddCoupl ε S μₗ μᵣ) : AddCoupl ε (fun v => S (v.2, v.1)) μᵣ μₗ := by
  rintro ⟨f, Hfm, Hfb⟩ ⟨g, Hgm, Hgb⟩ Hle
  -- test with the complements 1 - g, 1 - f; with equal finite masses, ∫(1-g)dμₗ ≤ ∫(1-f)dμᵣ + ε
  -- rearranges to ∫f dμᵣ ≤ ∫g dμₗ + ε
  let F : CouplingFunction α := ⟨fun a => 1 - g a, measurable_const.sub Hgm, fun _ => tsub_le_self⟩
  let G : CouplingFunction β := ⟨fun b => 1 - f b, measurable_const.sub Hfm, fun _ => tsub_le_self⟩
  have Hcpl := H F G fun HS => tsub_le_tsub_left (Hle HS) 1
  have Hgint_le : ∫⁻ a, g a ∂μₗ ≤ μₗ .univ := lintegral_le_meas Hgb (by simp)
  have Hfint_le : ∫⁻ b, f b ∂μᵣ ≤ μᵣ .univ := lintegral_le_meas Hfb (by simp)
  have HμL_ne : μₗ .univ ≠ ⊤ := ne_top_of_le_ne_top (by simp) HμₗP
  have HμR_ne : μᵣ .univ ≠ ⊤ := ne_top_of_le_ne_top (by simp) HμᵣP
  have HFint : ∫⁻ a, (1 - g a) ∂μₗ = μₗ .univ - ∫⁻ a, g a ∂μₗ := by
    rw [lintegral_sub Hgm (Hgint_le.trans_lt HμL_ne.lt_top).ne (ae_of_all _ Hgb)]
    simp
  have HGint : ∫⁻ b, (1 - f b) ∂μᵣ = μᵣ .univ - ∫⁻ b, f b ∂μᵣ := by
    rw [lintegral_sub Hfm (Hfint_le.trans_lt HμR_ne.lt_top).ne (ae_of_all _ Hfb)]
    simp
  rw [HFint, HGint, ← Hmass] at Hcpl
  rw [← Hmass] at Hfint_le
  set IF := ∫⁻ b, f b ∂μᵣ
  set IG := ∫⁻ a, g a ∂μₗ
  set M := μₗ .univ
  have hM : M ≤ (M - IF) + ε + IG := calc M = (M - IG) + IG := (tsub_add_cancel_of_le Hgint_le).symm
      _ ≤ (M - IF) + ε + IG := by gcongr
  refine ENNReal.le_of_add_le_add_left HμL_ne ?_
  calc M + IF ≤ (M - IF) + ε + IG + IF := by gcongr
    _ = (M - IF + IF) + (IG + ε) := by ac_rfl
    _ = M + (IG + ε) := by rw [tsub_add_cancel_of_le Hfint_le]

end AddCoupl
