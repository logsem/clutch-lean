module

public import Metrology.Couplings.GradedDivergence
public import Metrology.Couplings.Span

/-! Approximate span liftings (Approximate Span Liftings, §5). -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal

namespace Span

open GradedDivergence

section WitnessSpace

variable {ι : Type v} (Δ : GradedDivergence.{u} ι)

/-- A pair of subprobability measures at divergence at most `δ`. -/
structure IsWitness (α : ι) (δ : ℝ≥0∞) {Φ : Type u} [MeasurableSpace Φ]
    (p : Measure Φ × Measure Φ) : Prop where
  fst : IsSubProbabilityMeasure p.1
  snd : IsSubProbabilityMeasure p.2
  le : Δ α p.1 p.2 ≤ δ

/-- The witness space `W(Φ, Δ, α, δ)` of an approximate span lifting (Def. 5.1). -/
def Witness (α : ι) (δ : ℝ≥0∞) (Φ : Type u) [MeasurableSpace Φ] : Type u :=
  { p : Measure Φ × Measure Φ // IsWitness Δ α δ p }

namespace Witness

variable {Δ} {α : ι} {δ : ℝ≥0∞} {Φ : Type u} [MeasurableSpace Φ]

instance instMeasurableSpace : MeasurableSpace (Witness Δ α δ Φ) :=
  inferInstanceAs <| MeasurableSpace (Subtype _)

/-- The first measure of a witness pair. -/
def fst (w : Witness Δ α δ Φ) : Measure Φ := w.1.1

/-- The second measure of a witness pair. -/
def snd (w : Witness Δ α δ Φ) : Measure Φ := w.1.2

@[simp] theorem fst_mk (p : Measure Φ × Measure Φ) (h : IsWitness Δ α δ p) :
    fst ⟨p, h⟩ = p.1 := rfl

@[simp] theorem snd_mk (p : Measure Φ × Measure Φ) (h : IsWitness Δ α δ p) :
    snd ⟨p, h⟩ = p.2 := rfl

theorem le (w : Witness Δ α δ Φ) : Δ α w.fst w.snd ≤ δ := w.2.le

instance isSubProbabilityMeasure_fst (w : Witness Δ α δ Φ) : IsSubProbabilityMeasure w.fst :=
  w.2.fst

instance isSubProbabilityMeasure_snd (w : Witness Δ α δ Φ) : IsSubProbabilityMeasure w.snd :=
  w.2.snd

@[fun_prop]
theorem measurable_fst : Measurable (fst : Witness Δ α δ Φ → Measure Φ) :=
  _root_.measurable_fst.comp measurable_subtype_coe

@[fun_prop]
theorem measurable_snd : Measurable (snd : Witness Δ α δ Φ → Measure Φ) :=
  _root_.measurable_snd.comp measurable_subtype_coe

end Witness

end WitnessSpace

variable {ι : Type v} {Δ : GradedDivergence.{u} ι}
variable {X Y X' Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X']
  [MeasurableSpace Y']
variable {Φ Ψ : Type u} [MeasurableSpace Φ] [MeasurableSpace Ψ]

namespace Witness

/-- The first measures of a measurable family of witnesses, as a kernel. -/
noncomputable def fstKernel {α : ι} {δ : ℝ≥0∞} (κ : Φ → Witness Δ α δ Ψ)
    (hκ : Measurable κ := by fun_prop) : Kernel Φ Ψ :=
  ⟨fun φ ↦ (κ φ).fst, by fun_prop⟩

/-- The second measures of a measurable family of witnesses, as a kernel. -/
noncomputable def sndKernel {α : ι} {δ : ℝ≥0∞} (κ : Φ → Witness Δ α δ Ψ)
    (hκ : Measurable κ := by fun_prop) : Kernel Φ Ψ :=
  ⟨fun φ ↦ (κ φ).snd, by fun_prop⟩

instance isSubMarkovKernel_fstKernel {α : ι} {δ : ℝ≥0∞} (κ : Φ → Witness Δ α δ Ψ)
    (hκ : Measurable κ) : IsSubMarkovKernel (fstKernel κ hκ) :=
  ⟨fun φ ↦ isSubProbabilityMeasure_fst (κ φ)⟩

instance isSubMarkovKernel_sndKernel {α : ι} {δ : ℝ≥0∞} (κ : Φ → Witness Δ α δ Ψ)
    (hκ : Measurable κ) : IsSubMarkovKernel (sndKernel κ hκ) :=
  ⟨fun φ ↦ isSubProbabilityMeasure_snd (κ φ)⟩

variable [Mul ι] {α β : ι} {δ γ : ℝ≥0∞}

section Bind

variable [Δ.IsComposable]

/-- Binding a witness with a measurable family of witnesses stays a witness, with the grades
multiplied and the bounds added (composability). -/
theorem isWitness_bind (w : Witness Δ β γ Φ) {κ : Φ → Witness Δ α δ Ψ}
    (hκ : Measurable κ := by fun_prop) :
    IsWitness Δ (β * α) (γ + δ)
      (w.fst.bind fun φ ↦ (κ φ).fst, w.snd.bind fun φ ↦ (κ φ).snd) where
  fst := isSubProbabilityMeasure_bind _ _
  snd := isSubProbabilityMeasure_bind _ _
  le :=
    calc Δ (β * α) (w.fst.bind fun φ ↦ (κ φ).fst) (w.snd.bind fun φ ↦ (κ φ).snd)
        ≤ Δ β w.fst w.snd + ⨆ φ, Δ α (κ φ).fst (κ φ).snd :=
          IsComposable.bind_le β α _ _ (fstKernel κ hκ) (sndKernel κ hκ)
      _ ≤ γ + δ := add_le_add w.le (iSup_le fun φ ↦ (κ φ).le)

/-- Binding a witness with a measurable family of witnesses. -/
noncomputable def bind (w : Witness Δ β γ Φ) (κ : Φ → Witness Δ α δ Ψ)
    (hκ : Measurable κ := by fun_prop) : Witness Δ (β * α) (γ + δ) Ψ :=
  ⟨_, w.isWitness_bind hκ⟩

@[simp] theorem fst_bind (w : Witness Δ β γ Φ) {κ : Φ → Witness Δ α δ Ψ} (hκ : Measurable κ) :
    (w.bind κ hκ).fst = w.fst.bind fun φ ↦ (κ φ).fst := rfl

@[simp] theorem snd_bind (w : Witness Δ β γ Φ) {κ : Φ → Witness Δ α δ Ψ} (hκ : Measurable κ) :
    (w.bind κ hκ).snd = w.snd.bind fun φ ↦ (κ φ).snd := rfl

@[fun_prop]
theorem measurable_bind {κ : Φ → Witness Δ α δ Ψ} (hκ : Measurable κ) :
    Measurable fun w : Witness Δ β γ Φ ↦ w.bind κ := by
  unfold bind
  fun_prop

end Bind

/-- The product of two witnesses is a witness, with the grades multiplied and the bounds added
(additivity). -/
theorem isWitness_prod [Δ.IsAdditive] (w : Witness Δ α δ Φ) (w' : Witness Δ β γ Ψ) :
    IsWitness Δ (α * β) (δ + γ) (w.fst.prod w'.fst, w.snd.prod w'.snd) where
  fst := inferInstance
  snd := inferInstance
  le := (IsAdditive.prod_le α β _ _ _ _).trans (add_le_add w.le w'.le)

/-- The product of two witnesses. -/
noncomputable def prod [Δ.IsAdditive] (w : Witness Δ α δ Φ) (w' : Witness Δ β γ Ψ) :
    Witness Δ (α * β) (δ + γ) (Φ × Ψ) :=
  ⟨_, w.isWitness_prod w'⟩

@[simp] theorem fst_prod [Δ.IsAdditive] (w : Witness Δ α δ Φ) (w' : Witness Δ β γ Ψ) :
    (w.prod w').fst = w.fst.prod w'.fst := rfl

@[simp] theorem snd_prod [Δ.IsAdditive] (w : Witness Δ α δ Φ) (w' : Witness Δ β γ Ψ) :
    (w.prod w').snd = w.snd.prod w'.snd := rfl

@[fun_prop]
theorem measurable_prod [Δ.IsAdditive] :
    Measurable fun p : Witness Δ α δ Φ × Witness Δ β γ Ψ ↦ p.1.prod p.2 := by
  unfold prod
  fun_prop

end Witness

/-- The approximate span lifting `s♯[Δ, α, δ]`: witness pairs on `Φ`, pushed forward along the
legs of `s` (Def. 5.1). -/
noncomputable def lift (s : Span X Y Φ) (Δ : GradedDivergence.{u} ι) (α : ι) (δ : ℝ≥0∞) :
    Span (Measure X) (Measure Y) (Witness Δ α δ Φ) where
  left w := w.fst.map s.left
  right w := w.snd.map s.right

@[inherit_doc] scoped notation:max s "♯[" Δ ", " α ", " δ "]" => lift s Δ α δ

/-- Lifting the diagonal relates exactly the pairs at divergence at most `δ` (Thm. 5.2). -/
theorem rel_lift_diag {α : ι} {δ : ℝ≥0∞} {μ ν : Measure Φ} :
    ((diag Φ)♯[Δ, α, δ]).Rel μ ν ↔ IsWitness Δ α δ (μ, ν) := by
  simp only [Rel, lift, diag, map_id]
  exact ⟨fun ⟨w, h₁, h₂⟩ ↦ h₁ ▸ h₂ ▸ w.2, fun h ↦ ⟨⟨_, h⟩, rfl, rfl⟩⟩

namespace Hom

variable {s : Span X Y Φ} {t : Span X' Y' Ψ}

/-- The functor action of the lifting (Thm. 5.3). -/
noncomputable def lift [Δ.IsFunctorial] (m : s →ₛ t) (α : ι) (δ : ℝ≥0∞) :
    s♯[Δ, α, δ] →ₛ t♯[Δ, α, δ] where
  leftMap := map m.leftMap
  rightMap := map m.rightMap
  witnessMap w := ⟨(w.fst.map m.witnessMap, w.snd.map m.witnessMap),
    inferInstance, inferInstance, (IsFunctorial.map_le α _ _ m.witnessMeasurable).trans w.le⟩
  comm_left _ := map_map_of_comm m.comm_left _
  comm_right _ := map_map_of_comm m.comm_right _

/-- The unit of the lifting: Dirac measures (Thm. 5.3). -/
noncomputable def unit [One ι] [Δ.IsReflexive] (s : Span X Y Φ) : s →ₛ s♯[Δ, 1, 0] where
  leftMap := dirac
  rightMap := dirac
  witnessMap φ := ⟨(dirac φ, dirac φ), inferInstance, inferInstance, IsReflexive.self_le_zero _⟩
  comm_left φ := (map_dirac' (by fun_prop) φ).symm
  comm_right φ := (map_dirac' (by fun_prop) φ).symm

/-- The graded Kleisli lifting: bind with the witnesses chosen by `m` (Thm. 5.3). -/
noncomputable def bind [Mul ι] [Δ.IsComposable] {α : ι} {δ : ℝ≥0∞} (m : s →ₛ t♯[Δ, α, δ])
    (β : ι) (γ : ℝ≥0∞) : s♯[Δ, β, γ] →ₛ t♯[Δ, β * α, γ + δ] where
  leftMap μ := μ.bind m.leftMap
  rightMap μ := μ.bind m.rightMap
  witnessMap w := w.bind m.witnessMap
  comm_left _ := bind_map_of_comm m.comm_left _
  comm_right _ := bind_map_of_comm m.comm_right _

/-- Weakening the grade and the bound (Thm. 5.3). -/
def inclusion [Preorder ι] [Δ.IsGraded] (s : Span X Y Φ) {α β : ι} {δ γ : ℝ≥0∞} (hα : α ≤ β)
    (hδ : δ ≤ γ) : s♯[Δ, α, δ] →ₛ s♯[Δ, β, γ] where
  leftMap := _root_.id
  rightMap := _root_.id
  witnessMap w := ⟨w.1, w.2.fst, w.2.snd, (IsGraded.anti hα w.fst w.snd).trans (w.le.trans hδ)⟩
  comm_left _ := rfl
  comm_right _ := rfl

/-- The double strength: product measures (Thm. 5.3). -/
noncomputable def doubleStrength [Mul ι] [Δ.IsAdditive] (s : Span X Y Φ) (t : Span X' Y' Ψ)
    (α β : ι) (δ γ : ℝ≥0∞) :
    s♯[Δ, α, δ] ×̇ t♯[Δ, β, γ] →ₛ (s ×̇ t)♯[Δ, α * β, δ + γ] where
  leftMap p := p.1.finiteOrZero.prod p.2.finiteOrZero
  rightMap p := p.1.finiteOrZero.prod p.2.finiteOrZero
  witnessMap p := p.1.prod p.2
  comm_left p := by
    change (p.1.fst.map s.left).finiteOrZero.prod (p.2.fst.map t.left).finiteOrZero =
      (p.1.fst.prod p.2.fst).map (Prod.map s.left t.left)
    rw [finiteOrZero_eq, finiteOrZero_eq]
    exact map_prod_map _ _ (by fun_prop) (by fun_prop)
  comm_right p := by
    change (p.1.snd.map s.right).finiteOrZero.prod (p.2.snd.map t.right).finiteOrZero =
      (p.1.snd.prod p.2.snd).map (Prod.map s.right t.right)
    rw [finiteOrZero_eq, finiteOrZero_eq]
    exact map_prod_map _ _ (by fun_prop) (by fun_prop)

end Hom

end Span
