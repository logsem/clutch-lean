module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.UnitInterval
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Analysis.Real.OfDigits

public import Metrology.Couplings.ApproximateCouplings

/-! # Additive couplings

Approximate couplings up to `x ↦ x + ε`, with their bind, map and limit rules. -/

@[expose] public section

section AdditiveCoupling

open MeasureTheory Measure

variable {α β α' β' : Type _}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace α'] [MeasurableSpace β']

/-- Approximate relational coupling with additive error slack `ε`. -/
def AddCoupl (ε : ENNReal) (Φ : Set (α × β)) (μₗ : Measure α) (μᵣ : Measure β) : Prop :=
  ARCoupling (· + ε) Φ μₗ μᵣ

-- reducible so an `ExpCoupl` hypothesis still applies directly to its six arguments
/-- Kantorovich-dual form of an additive coupling with variable cost `E₂` (for `bind_adv_kanto`). -/
@[reducible] def ExpCoupl (ε : ENNReal) (E₂ : α → β → ENNReal)
    (μ₁ : Measure α) (μ₂ : Measure β) : Prop :=
  ∀ (h₁ : α → ENNReal) (h₂ : β → ENNReal), Measurable h₁ → Measurable h₂ →
    (∀ a, h₁ a ≤ 1) → (∀ b, h₂ b ≤ 1) → (∀ a b, h₁ a ≤ h₂ b + E₂ a b) →
    ∫⁻ a, h₁ a ∂μ₁ ≤ ∫⁻ b, h₂ b ∂μ₂ + ε

namespace AddCoupl

theorem refl {ε : ENNReal} (μ : Measure α) : AddCoupl ε (fun v => v.1 = v.2) μ μ :=
  ARCoupling.refl μ le_self_add

theorem dirac {ε : ENNReal} {a : α} {b : β} (S : Set (α × β)) (H : S (a, b)) :
    AddCoupl ε S (.dirac a) (.dirac b) :=
  ARCoupling.dirac le_self_add S H

theorem mono_rel {ε : ENNReal} {S S' : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    (HS : S ⊆ S') (H : AddCoupl ε S μₗ μᵣ) : AddCoupl ε S' μₗ μᵣ :=
  ARCoupling.mono_rel HS H

theorem mono_grading {ε ε' : ENNReal} {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    (Hε : ε ≤ ε') (H : AddCoupl ε S μₗ μᵣ) : AddCoupl ε' S μₗ μᵣ :=
  ARCoupling.mono_F (fun x => by gcongr) H

/-- The zero measure on the left is coupled with anything (Rocq `ARcoupl_dzero`). -/
theorem zero_left {ε : ENNReal} (S : Set (α × β)) (μᵣ : Measure β) : AddCoupl ε S 0 μᵣ :=
  ARCoupling.zero_left S μᵣ

theorem zero_right {ε : ENNReal} (S : Set (α × β)) {μₗ : Measure α} (Hε : μₗ .univ ≤ ε) :
    AddCoupl ε S μₗ 0 :=
  ARCoupling.zero_right S (by simpa using Hε)

theorem bind {ε ε' : ENNReal} {S : Set (α × β)} {T : Set (α' × β')}
    {μₗ : Measure α} {μᵣ : Measure β} {f : α → Measure α'} {g : β → Measure β'}
    (Hfm : Measurable f) (Hgm : Measurable g)
    (Hμₗ : μₗ .univ ≤ 1) (Hfsprob : ∀ a, (f a) .univ ≤ 1)
    (Hcpl : AddCoupl ε S μₗ μᵣ)
    (Hbind : ∀ {a b}, S (a, b) → AddCoupl ε' T (f a) (g b)) :
    AddCoupl (ε + ε') T (μₗ.bind f) (μᵣ.bind g) := by
  rintro ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'
  have HFle a : ∫⁻ y, f' y ∂f a ≤ 1 := (lintegral_le_meas Hf'b (by simp)).trans (Hfsprob a)
  let Fh : CouplingFunction α := .mk (fun a => ∫⁻ y, f' y ∂(f a) - ε') ⟨?Fm, fun a => ?Fb⟩
  case Fm => exact (measurable_lintegral Hf'm |>.comp Hfm).sub measurable_const
  case Fb => exact tsub_le_self.trans (HFle a)
  let Gh : CouplingFunction β := .mk (fun b => (∫⁻ y, g' y ∂(g b)) ⊓ 1) ⟨?Gm, fun b => ?Gb⟩
  case Gm => exact (measurable_lintegral Hg'm |>.comp Hgm).inf measurable_const
  case Gb => exact inf_le_right
  have HFhGh {a b} (HS : S (a, b)) : Fh.1 a ≤ Gh.1 b := by
    simp only [Gh, le_inf_iff]
    exact ⟨tsub_le_iff_right.mpr (Hbind HS ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'),
      tsub_le_iff_right.mpr ((HFle a).trans le_self_add)⟩
  rw [lintegral_bind Hfm.aemeasurable Hf'm.aemeasurable,
      lintegral_bind Hgm.aemeasurable Hg'm.aemeasurable]
  calc  ∫⁻ a, ∫⁻ x, f' x ∂(f a) ∂μₗ
      _ ≤ ∫⁻ a, Fh.1 a + ε' ∂μₗ := lintegral_mono fun _ => le_tsub_add
      _ = ∫⁻ a, Fh.1 a ∂μₗ + ε' * μₗ .univ := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, mul_comm]
      _ ≤ ∫⁻ a, Fh.1 a ∂μₗ + ε' := by
            gcongr
            exact mul_le_of_le_one_right' Hμₗ
      _ ≤ (∫⁻ b, Gh.1 b ∂μᵣ + ε) + ε' := by
            gcongr
            exact Hcpl Fh Gh HFhGh
      _ ≤ (∫⁻ b, ∫⁻ x, g' x ∂(g b) ∂μᵣ + ε) + ε' := by
            gcongr with b
            exact inf_le_left
      _ = ∫⁻ b, ∫⁻ x, g' x ∂(g b) ∂μᵣ + (ε + ε') := by
            rw [add_assoc]

/-- Advanced-composition bind: the continuation's slack `E₂ b` depends on the right sample and
only its expectation is charged. -/
theorem bind_adv {ε ε' : ENNReal} {S : Set (α × β)} {T : Set (α' × β')}
    {μₗ : Measure α} {μᵣ : Measure β}
    {f : α → Measure α'} {g : β → Measure β'} {E₂ : β → ENNReal}
    (Hfm : Measurable f) (Hgm : Measurable g) (HE₂m : Measurable E₂)
    (Hfsprob : ∀ a, (f a) .univ ≤ 1)
    (HE₂sum : ∫⁻ b, E₂ b ∂μᵣ ≤ ε')
    (Hcpl : AddCoupl ε S μₗ μᵣ)
    (Hbind : ∀ {a b}, S (a, b) → AddCoupl (E₂ b) T (f a) (g b)) :
    AddCoupl (ε + ε') T (μₗ.bind f) (μᵣ.bind g) := by
  rintro ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'
  have HFle a : ∫⁻ y, f' y ∂f a ≤ 1 := (lintegral_le_meas Hf'b (by simp)).trans (Hfsprob a)
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
theorem bind_adv_lhs {ε ε' : ENNReal} {S : Set (α × β)} {T : Set (α' × β')}
    {μₗ : Measure α} {μᵣ : Measure β}
    {f : α → Measure α'} {g : β → Measure β'} {E₂ : α → ENNReal}
    (Hfm : Measurable f) (Hgm : Measurable g) (HE₂m : Measurable E₂)
    (Hfsprob : ∀ a, (f a) .univ ≤ 1)
    (HE₂sum : ∫⁻ a, E₂ a ∂μₗ ≤ ε')
    (Hcpl : AddCoupl ε S μₗ μᵣ)
    (Hbind : ∀ {a b}, S (a, b) → AddCoupl (E₂ a) T (f a) (g b)) :
    AddCoupl (ε + ε') T (μₗ.bind f) (μᵣ.bind g) := by
  rintro ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'
  have HFle a : ∫⁻ y, f' y ∂f a ≤ 1 := (lintegral_le_meas Hf'b (by simp)).trans (Hfsprob a)
  let Fh : CouplingFunction α := .mk (fun a => ∫⁻ y, f' y ∂(f a) - E₂ a)
    ⟨?Fm, fun a => ?Fb⟩
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

/-- Kantorovich-style bind with slack `E₂ a b` depending on both samples
(Rocq `ARcoupl_dbind_adv_kanto_plain`). -/
theorem bind_adv_kanto {ε : ENNReal} {S : Set (α' × β')}
    {μ₁ : Measure α} {μ₂ : Measure β}
    {f : α → Measure α'} {g : β → Measure β'} {E₂ : α → β → ENNReal}
    (Hfm : Measurable f) (Hgm : Measurable g)
    (Hfsprob : ∀ a, (f a) .univ ≤ 1) (Hgsprob : ∀ b, (g b) .univ ≤ 1)
    (Hexp : ExpCoupl ε E₂ μ₁ μ₂)
    (Hcont : ∀ a b, AddCoupl (E₂ a b) S (f a) (g b)) :
    AddCoupl ε S (μ₁.bind f) (μ₂.bind g) := by
  rintro ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'
  let X : α → ENNReal := fun a => ∫⁻ x, f' x ∂(f a)
  let Y : β → ENNReal := fun b => ∫⁻ y, g' y ∂(g b)
  have HXm : Measurable X := (measurable_lintegral Hf'm).comp Hfm
  have HYm : Measurable Y := (measurable_lintegral Hg'm).comp Hgm
  have HXb a : X a ≤ 1 := (lintegral_le_meas Hf'b (by simp)).trans (Hfsprob a)
  have HYb b : Y b ≤ 1 := (lintegral_le_meas Hg'b (by simp)).trans (Hgsprob b)
  have HXY a b : X a ≤ Y b + E₂ a b := Hcont a b ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'
  rw [lintegral_bind Hfm.aemeasurable Hf'm.aemeasurable,
      lintegral_bind Hgm.aemeasurable Hg'm.aemeasurable]
  exact Hexp X Y HXm HYm HXb HYb HXY

theorem mass_leq {ε : ENNReal} {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    (H : AddCoupl ε S μₗ μᵣ) : μₗ .univ ≤ μᵣ .univ + ε := by
  let oneA : CouplingFunction α := .mk (fun _ => 1) ⟨measurable_const, fun _ => le_refl _⟩
  let oneB : CouplingFunction β := .mk (fun _ => 1) ⟨measurable_const, fun _ => le_refl _⟩
  simpa [oneA, oneB] using H oneA oneB (fun _ => le_refl _)

theorem set_leq_zero {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β} {T : Set α}
    {T' : Set β} (hT : MeasurableSet T) (hT' : MeasurableSet T') (Hcpl : AddCoupl 0 S μₗ μᵣ)
    (Himp : ∀ a b, S (a, b) → a ∈ T → b ∈ T') : μₗ T ≤ μᵣ T' := by
  classical
  let fInd : CouplingFunction α :=
    .mk (T.indicator 1) ⟨measurable_const.indicator hT, fun x => Set.indicator_le_self _ _ x⟩
  let gInd : CouplingFunction β :=
    .mk (T'.indicator 1) ⟨measurable_const.indicator hT', fun x => Set.indicator_le_self _ _ x⟩
  have hMain := Hcpl fInd gInd fun {a b} hS => by
    by_cases ha : a ∈ T
    · simp [fInd, gInd, Set.indicator_of_mem ha, Set.indicator_of_mem (Himp a b hS ha)]
    · simp [fInd, Set.indicator_of_notMem ha]
  simpa [fInd, gInd, lintegral_indicator_one hT, lintegral_indicator_one hT'] using hMain

theorem eq_trans_l {ε₁ ε₂ : ENNReal} {R : Set (α × β)} {μ₁ μ₂ : Measure α} {μ₃ : Measure β}
    (Heq : AddCoupl ε₁ (fun v => v.1 = v.2) μ₁ μ₂) (HR : AddCoupl ε₂ R μ₂ μ₃) :
    AddCoupl (ε₁ + ε₂) R μ₁ μ₃ := by
  intro f g Hfg
  calc ∫⁻ x, f.1 x ∂μ₁
      _ ≤ ∫⁻ x, f.1 x ∂μ₂ + ε₁ := Heq f f (fun {a b} (h : a = b) => h ▸ le_refl _)
      _ ≤ (∫⁻ x, g.1 x ∂μ₃ + ε₂) + ε₁ := by gcongr; exact HR f g Hfg
      _ = ∫⁻ x, g.1 x ∂μ₃ + (ε₁ + ε₂) := by rw [add_assoc, add_comm ε₂ ε₁]

theorem eq_trans_r {ε₁ ε₂ : ENNReal} {R : Set (α × β)} {μ₁ : Measure α} {μ₂ μ₃ : Measure β}
    (HR : AddCoupl ε₁ R μ₁ μ₂) (Heq : AddCoupl ε₂ (fun v => v.1 = v.2) μ₂ μ₃) :
    AddCoupl (ε₁ + ε₂) R μ₁ μ₃ := by
  intro f g Hfg
  calc ∫⁻ x, f.1 x ∂μ₁
      _ ≤ ∫⁻ x, g.1 x ∂μ₂ + ε₁ := HR f g Hfg
      _ ≤ (∫⁻ x, g.1 x ∂μ₃ + ε₂) + ε₁ := by
            gcongr; exact Heq g g (fun {a b} (h : a = b) => h ▸ le_refl _)
      _ = ∫⁻ x, g.1 x ∂μ₃ + (ε₁ + ε₂) := by rw [add_assoc, add_comm ε₂ ε₁]

omit [MeasurableSpace α] [MeasurableSpace β] in
theorem dret {ε : ENNReal} {R : α' → β' → Prop} {a : α} {b : β}
    (f : α → α') (g : β → β') (H : R (f a) (g b)) :
    AddCoupl ε (fun v => R v.1 v.2) (Measure.dirac (f a)) (Measure.dirac (g b)) :=
  AddCoupl.dirac _ H

theorem map {ε : ENNReal} {S : Set (α × β)} {R : Set (α' × β')}
    {μₗ : Measure α} {μᵣ : Measure β} (f : α → α') (g : β → β')
    (Hfm : Measurable f) (Hgm : Measurable g)
    (HR : ∀ {a b}, S (a, b) → R (f a, g b))
    (H : AddCoupl ε S μₗ μᵣ) :
    AddCoupl ε R (μₗ.map f) (μᵣ.map g) := by
  rintro ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hle
  let F : CouplingFunction α := .mk (f' ∘ f) ⟨Hf'm.comp Hfm, fun _ => Hf'b _⟩
  let G : CouplingFunction β := .mk (g' ∘ g) ⟨Hg'm.comp Hgm, fun _ => Hg'b _⟩
  rw [lintegral_map Hf'm Hfm, lintegral_map Hg'm Hgm]
  exact H F G fun HS => Hle (HR HS)

-- unlike `map_inv`, survives a pushforward: limits under `map` need no discreteness
/-- A left measure dominated on measurable tests by a family of coupled `ν i` is coupled too. -/
theorem iSup_left {ι : Sort _} {ε : ENNReal} {S : Set (α × β)}
    {μₗ : Measure α} {ν : ι → Measure α} {μᵣ : Measure β}
    (hle : ∀ f : α → ENNReal, Measurable f → ∫⁻ a, f a ∂μₗ ≤ ⨆ i, ∫⁻ a, f a ∂(ν i))
    (H : ∀ i, AddCoupl ε S (ν i) μᵣ) :
    AddCoupl ε S μₗ μᵣ := by
  rintro ⟨f, hfm, hfb⟩ G hfg
  exact (hle f hfm).trans (iSup_le fun i => H i ⟨f, hfm, hfb⟩ G hfg)

-- discreteness is essential: fibrewise sup/inf lifts of test functions are not measurable in
-- general; to take a limit under a pushforward use `iSup_left`
/-- Inverse of `map`: a coupling of images pulls back along the maps. -/
theorem map_inv [DiscreteMeasurableSpace α'] [DiscreteMeasurableSpace β']
    {ε : ENNReal} {R : Set (α' × β')}
    {μₗ : Measure α} {μᵣ : Measure β} (f : α → α') (g : β → β')
    (Hfm : Measurable f) (Hgm : Measurable g)
    (H : AddCoupl ε R (μₗ.map f) (μᵣ.map g)) :
    AddCoupl ε (fun v => R (f v.1, g v.2)) μₗ μᵣ := by
  rintro ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hle
  let fT : α' → ENNReal := fun a' => ⨆ (a : α) (_ : f a = a'), f' a
  let gT : β' → ENNReal := fun b' => (⨅ (b : β) (_ : g b = b'), g' b) ⊓ 1
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
  have HgT_le b : gT (g b) ≤ g' b :=
    calc (⨅ (b' : β) (_ : g b' = g b), g' b') ⊓ 1
        ≤ (⨅ (b' : β) (_ : g b' = g b), g' b') := inf_le_left
      _ ≤ g' b := iInf_le_of_le b (iInf_le_of_le rfl le_rfl)
  calc ∫⁻ a, f' a ∂μₗ
      ≤ ∫⁻ a, fT (f a) ∂μₗ := lintegral_mono Hf'_le
    _ = ∫⁻ a', fT a' ∂(μₗ.map f) := (lintegral_map HfTm Hfm).symm
    _ ≤ ∫⁻ b', gT b' ∂(μᵣ.map g) + ε := H FT GT HFG
    _ = ∫⁻ b, gT (g b) ∂μᵣ + ε := by rw [lintegral_map HgTm Hgm]
    _ ≤ ∫⁻ b, g' b ∂μᵣ + ε := by gcongr; exact HgT_le _

-- countability-free: for `μᵣ = dirac b`, `T = {b}` pins the right sample with no atom enumeration
/-- Strengthen the relation with `v.2 ∈ T` for a set `T` carrying all of `μᵣ`. -/
theorem concentrated_R {ε : ENNReal} {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    {T : Set β} (hT : MeasurableSet T) (hconc : μᵣ Tᶜ = 0)
    (H : AddCoupl ε S μₗ μᵣ) :
    AddCoupl ε (fun v => S v ∧ v.2 ∈ T) μₗ μᵣ := by
  classical
  rintro ⟨f, Hfm, Hfb⟩ ⟨g, Hgm, Hgb⟩ Hle
  let g' : β → ENNReal := fun b => if b ∈ T then g b else 1
  have Hg'm : Measurable g' := Measurable.ite hT Hgm measurable_const
  have Hg'b b : g' b ≤ 1 := by
    simp only [g']; split_ifs
    exacts [Hgb b, le_refl _]
  let G : CouplingFunction β := ⟨g', Hg'm, Hg'b⟩
  have HFG {a b} (HS : S (a, b)) : f a ≤ G.1 b := by
    simp only [G, g']
    split_ifs with hbT
    exacts [Hle ⟨HS, hbT⟩, Hfb a]
  have hae : g =ᶠ[ae μᵣ] g' := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun b hb => ?_) hconc
    simp only [Set.mem_compl_iff]
    intro hbT
    exact hb (by simp only [g', ite_eq_left hbT])
  rw [lintegral_congr_ae hae]
  exact H ⟨f, Hfm, Hfb⟩ G HFG

/-- Strengthen the relation with `v.1 ∈ T` for a set `T` carrying all of `μₗ`. -/
theorem concentrated_L {ε : ENNReal} {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    {T : Set α} (hT : MeasurableSet T) (hconc : μₗ Tᶜ = 0)
    (H : AddCoupl ε S μₗ μᵣ) :
    AddCoupl ε (fun v => S v ∧ v.1 ∈ T) μₗ μᵣ := by
  classical
  rintro ⟨f, Hfm, Hfb⟩ ⟨g, Hgm, Hgb⟩ Hle
  let f' : α → ENNReal := fun a => if a ∈ T then f a else 0
  have Hf'm : Measurable f' := Measurable.ite hT Hfm measurable_const
  have Hf'b a : f' a ≤ 1 := by
    simp only [f']; split_ifs
    exacts [Hfb a, zero_le_one]
  let F : CouplingFunction α := ⟨f', Hf'm, Hf'b⟩
  have HFG {a b} (HS : S (a, b)) : F.1 a ≤ g b := by
    simp only [F, f']
    split_ifs with haT
    exacts [Hle ⟨HS, haT⟩, zero_le]
  have hae : f =ᶠ[ae μₗ] f' := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun a ha => ?_) hconc
    simp only [Set.mem_compl_iff]
    intro haT
    exact ha (by simp only [f', ite_eq_left haT])
  rw [lintegral_congr_ae hae]
  exact H F ⟨g, Hgm, Hgb⟩ HFG

/-- A measure on a countable space lives on its atoms. -/
theorem _root_.MeasureTheory.measure_compl_atoms_null [Countable α] (μ : Measure α) :
    μ {a | μ {a} ≠ 0}ᶜ = 0 := by
  rw [show {a | μ {a} ≠ 0}ᶜ = ⋃ a ∈ {a | μ {a} = 0}, ({a} : Set α) by ext; simp,
    measure_biUnion_null_iff (Set.to_countable _)]
  exact fun _ ha => ha

-- false for diffuse measures, hence the countability
/-- Strengthen the relation to the product of the atoms of both measures. -/
theorem pos_R [Countable α] [Countable β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {ε : ENNReal} {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    (H : AddCoupl ε S μₗ μᵣ) :
    AddCoupl ε (fun v => S v ∧ μₗ {v.1} ≠ 0 ∧ μᵣ {v.2} ≠ 0) μₗ μᵣ :=
  mono_rel (by rintro ⟨a, b⟩ ⟨⟨hS, haL⟩, hbR⟩; exact ⟨hS, haL, hbR⟩) <|
    concentrated_R (Set.to_countable _).measurableSet
      (MeasureTheory.measure_compl_atoms_null μᵣ) <|
    concentrated_L (Set.to_countable _).measurableSet
      (MeasureTheory.measure_compl_atoms_null μₗ) H

/-- An equality coupling bounds the measure of every measurable set (Rocq `ARcoupl_eq_elim`). -/
theorem eq_elim {ε : ENNReal} {μ ν : Measure α}
    (h : AddCoupl ε {p : α × α | p.1 = p.2} μ ν) {S : Set α} (hS : MeasurableSet S) :
    μ S ≤ ν S + ε := by
  have hind : Measurable (S.indicator (1 : α → ENNReal)) := measurable_one.indicator hS
  have hb : BoundedFunction (S.indicator (1 : α → ENNReal)) :=
    fun _ => Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le)
  have key := h ⟨_, hind, hb⟩ ⟨_, hind, hb⟩ fun {a b} (hab : a = b) => hab ▸ le_rfl
  rwa [lintegral_indicator_one hS, lintegral_indicator_one hS] at key

/-- Equality couplings of error zero both ways force equal measures (Rocq `ARcoupl_antisym`). -/
theorem eq_of_eq_zero {μ ν : Measure α}
    (h₁ : AddCoupl 0 {p : α × α | p.1 = p.2} μ ν)
    (h₂ : AddCoupl 0 {p : α × α | p.1 = p.2} ν μ) :
    μ = ν := by
  refine Measure.ext fun S hS => le_antisymm ?_ ?_
  · simpa using eq_elim h₁ hS
  · simpa using eq_elim h₂ hS

theorem of_RelCoupl {ε : ENNReal} {S : Set (α × β)}
    {μₗ : Measure α} {μᵣ : Measure β}
    (H : ARCoupling (fun x => x) S μₗ μᵣ) :
    AddCoupl ε S μₗ μᵣ :=
  ARCoupling.mono_F (fun _ => le_self_add) H

theorem limit {ε : ENNReal} {S : Set (α × β)}
    {μₗ : Measure α} {μᵣ : Measure β}
    (H : ∀ δ : ENNReal, 0 < δ → AddCoupl (ε + δ) S μₗ μᵣ) :
    AddCoupl ε S μₗ μᵣ := by
  intro f g Hfg
  refine ENNReal.le_of_forall_pos_le_add fun δ Hδ _ => ?_
  rw [add_assoc]
  exact H δ (by exact_mod_cast Hδ) f g Hfg

theorem dzero_r_inv {ε : ENNReal} {S : Set (α × β)} {μₗ : Measure α}
    (H : AddCoupl ε S μₗ (0 : Measure β)) : μₗ .univ ≤ ε := by
  simpa using AddCoupl.mass_leq H

/-- Additive couplings of measures of equal mass at most one swap sides. -/
theorem swap {ε : ENNReal} {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    (Hmass : μₗ .univ = μᵣ .univ) (HμₗP : μₗ .univ ≤ 1) (HμᵣP : μᵣ .univ ≤ 1)
    (H : AddCoupl ε S μₗ μᵣ) :
    AddCoupl ε (fun v => S (v.2, v.1)) μᵣ μₗ := by
  rintro ⟨f, Hfm, Hfb⟩ ⟨g, Hgm, Hgb⟩ Hle
  let F : CouplingFunction α :=
    ⟨fun a => 1 - g a, measurable_const.sub Hgm, fun _ => tsub_le_self⟩
  let G : CouplingFunction β :=
    ⟨fun b => 1 - f b, measurable_const.sub Hfm, fun _ => tsub_le_self⟩
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
  have hM : M ≤ (M - IF) + ε + IG :=
    calc M = (M - IG) + IG := (tsub_add_cancel_of_le Hgint_le).symm
      _ ≤ (M - IF) + ε + IG := by gcongr
  refine ENNReal.le_of_add_le_add_left HμL_ne ?_
  calc M + IF ≤ (M - IF) + ε + IG + IF := by gcongr
    _ = (M - IF + IF) + (IG + ε) := by ac_rfl
    _ = M + (IG + ε) := by rw [tsub_add_cancel_of_le Hfint_le]

/-- Slack at least one makes any coupling trivial (Rocq `ARcoupl_1`). -/
theorem trivial_of_one_le {ε : ENNReal} {S : Set (α × β)} {μₗ : Measure α}
    {μᵣ : Measure β} (Hε : 1 ≤ ε) (Hmass : μₗ Set.univ ≤ 1) :
    AddCoupl ε S μₗ μᵣ := by
  rintro ⟨f, Hfm, Hfb⟩ ⟨g, Hgm, Hgb⟩ _
  calc ∫⁻ x, f x ∂μₗ
      _ ≤ μₗ Set.univ := lintegral_le_meas Hfb (by simp)
      _ ≤ 1 := Hmass
      _ ≤ ε := Hε
      _ ≤ ∫⁻ y, g y ∂μᵣ + ε := le_add_self

end AddCoupl
