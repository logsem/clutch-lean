module

public import Metrology.Couplings.Lifting

/-! # Bind laws

Ways to compose a lifted step with lifted continuations (Rocq `bind_law.v`). -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory

namespace GradedLifting

/-- One way to compose a step with its continuations: a head premise on the step, a side condition
on the continuation kernels, and soundness (Rocq `GradedBindLaw`). -/
structure BindLaw {B : Type v} [Preorder B] [Top B] (L : GradedLifting.{u} B) where
  /-- The premise on the step's two measures, per-pair leftovers and output budget. -/
  head : ∀ {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y],
    Measure X → Measure Y → (X → Y → B) → B → Prop
  /-- The side condition on both step measures, the leftovers and both continuation kernels; it
  sees the leftovers so it can constrain the kernels at related pairs only. -/
  side : ∀ {X Y X' Y' : Type u} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X']
    [MeasurableSpace Y'], Measure X → Measure Y → (X → Y → B) → Kernel X X' → Kernel Y Y' → Prop
  /-- A head and side bind with continuations lifted wherever the leftover is finite. -/
  sound {X Y X' Y' : Type u} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X']
    [MeasurableSpace Y'] {b : B} {R : X → Y → B} {R' : X' → Y' → B} {μ : Measure X}
    {ν : Measure Y} {f : Kernel X X'} {g : Kernel Y Y'} [IsSubMarkovKernel f]
    [IsSubMarkovKernel g] :
    head μ ν R b → side μ ν R f g → (∀ x y, R x y < ⊤ → L (R x y) R' (f x) (g y)) →
      L b R' (f ∘ₘ μ) (g ∘ₘ ν)
  /-- A head holds at every larger output budget (Rocq `gbl_mono_out`). -/
  mono_out {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {b b' : B} {R : X → Y → B}
    {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    head μ ν R b → b ≤ b' → head μ ν R b'
  /-- Leftovers of a head may be set to `⊤` off a set carrying the left measure (Rocq
  `gbl_head_supp`). -/
  head_supp {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {b : B} {R : X → Y → B}
    {μ : Measure X} {ν : Measure Y} {A : Set X} [DecidablePred (· ∈ A)] (hA : MeasurableSet A)
    (hμ : μ Aᶜ = 0) : head μ ν R b → head μ ν (A.piecewise R fun _ _ ↦ ⊤) b
  /-- The side condition survives setting leftovers to `⊤` off a set, as `head_supp` does. -/
  side_supp {X Y X' Y' : Type u} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X']
    [MeasurableSpace Y'] {R : X → Y → B} {μ : Measure X} {ν : Measure Y} {f : Kernel X X'}
    {g : Kernel Y Y'} {A : Set X} [DecidablePred (· ∈ A)] :
    side μ ν R f g → side μ ν (A.piecewise R fun _ _ ↦ ⊤) f g

namespace BindLaw

variable {B : Type v} [Preorder B] [Top B] {L : GradedLifting.{u} B} {X Y X' Y' : Type u}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X'] [MeasurableSpace Y']

variable (L) in
/-- The law whose head is a lifting of the step, bound unconditionally (Rocq `GBL_uniform`). -/
def canonical [Add B] [L.IsLawful] [L.HasBind] [L.IsSupportLocal] : BindLaw L where
  head μ ν R b := L b R μ ν
  side _ _ _ _ _ := True
  sound h _ hk := HasBind.bind h hk
  mono_out h hb := IsLawful.mono h hb le_rfl
  head_supp hA hμ h := IsSupportLocal.restrict hA hμ h
  side_supp _ := trivial

@[simp]
theorem head_canonical [Add B] [L.IsLawful] [L.HasBind] [L.IsSupportLocal] {b : B}
    {R : X → Y → B} {μ : Measure X} {ν : Measure Y} : (canonical L).head μ ν R b ↔ L b R μ ν :=
  Iff.rfl

@[simp]
theorem side_canonical [Add B] [L.IsLawful] [L.HasBind] [L.IsSupportLocal] {μ : Measure X}
    {ν : Measure Y} {R : X → Y → B} {f : Kernel X X'} {g : Kernel Y Y'} :
    (canonical L).side μ ν R f g :=
  trivial

variable (L) in
/-- The no-progress step: point masses on both sides, continued at a finite leftover below the
output budget (Rocq `GBL_unit_law`). -/
def unit [Add B] [L.IsLawful] : BindLaw L where
  head μ ν R b := ∃ x y, μ = dirac x ∧ ν = dirac y ∧ R x y < ⊤ ∧ R x y ≤ b
  side _ _ _ _ _ := True
  sound := by
    rintro _ _ _ _ _ _ _ _ _ _ _ _ _ f g _ _ ⟨x, y, rfl, rfl, hlt, hle⟩ _ hk
    rw [Measure.dirac_bind f.measurable, Measure.dirac_bind g.measurable]
    exact IsLawful.mono (hk x y hlt) hle le_rfl
  mono_out := fun ⟨x, y, hμ, hν, hlt, hle⟩ hb ↦ ⟨x, y, hμ, hν, hlt, hle.trans hb⟩
  head_supp := by
    rintro _ _ _ _ _ _ _ _ A _ _ hμ ⟨x, y, rfl, rfl, hlt, hle⟩
    have hx : x ∈ A := by_contra fun hx ↦ by simp [dirac_apply_of_mem (s := Aᶜ) hx] at hμ
    exact ⟨x, y, rfl, rfl, by simpa [hx] using hlt, by simpa [hx] using hle⟩
  side_supp _ := trivial

theorem unit_head_dirac [Add B] [L.IsLawful] {b : B} {R : X → Y → B} {x : X} {y : Y}
    (hlt : R x y < ⊤) (hle : R x y ≤ b) : (unit L).head (dirac x) (dirac y) R b :=
  ⟨x, y, rfl, rfl, hlt, hle⟩

@[simp]
theorem side_unit [Add B] [L.IsLawful] {μ : Measure X} {ν : Measure Y} {R : X → Y → B}
    {f : Kernel X X'} {g : Kernel Y Y'} : (unit L).side μ ν R f g :=
  trivial

/-- A bind law applied to measurable families of sub-probability measures. -/
theorem bind_fun (law : BindLaw L) {b : B} {R : X → Y → B} {R' : X' → Y' → B} {μ : Measure X}
    {ν : Measure Y} (h : law.head μ ν R b) {f : X → Measure X'} {g : Y → Measure Y'}
    [∀ x, IsSubProbabilityMeasure (f x)] [∀ y, IsSubProbabilityMeasure (g y)]
    (hf : Measurable f) (hg : Measurable g) (hside : law.side μ ν R ⟨f, hf⟩ ⟨g, hg⟩)
    (hk : ∀ x y, R x y < ⊤ → L (R x y) R' (f x) (g y)) : L b R' (μ.bind f) (ν.bind g) :=
  law.sound (f := ⟨f, hf⟩) (g := ⟨g, hg⟩) h hside hk

/-! ## Optional properties of a law -/

/-- A head survives adding a finite budget to every leftover and to the output budget; the credit
rules ask this of a law (Rocq `gbl_head_shift`). -/
class HeadShift [Add B] (law : BindLaw L) : Prop where
  shift {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {b c : B} {R : X → Y → B}
    {μ : Measure X} {ν : Measure Y} :
    c < ⊤ → law.head μ ν R b → law.head μ ν (fun x y ↦ R x y + c) (b + c)

/-- A probability measure is a head against itself along the diagonal at any finite budget, and
the side holds for a measure against itself; program steps that leave the spec in place ask this
of a law (Rocq `gbl_head_diag`, `GCFamLeftStep`). -/
class HeadDiag [Zero B] [Add B] (law : BindLaw L) : Prop where
  diag {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] {b : B} :
    b < ⊤ → law.head μ μ (fun x y ↦ relCost (· = ·) x y + b) b
  side_diag {X X' Y' : Type u} [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y']
    (μ : Measure X) (R : X → X → B) (f : Kernel X X') (g : Kernel X Y') : law.side μ μ R f g

/-- The canonical law shifts heads by `IsLawful.frame`. -/
instance headShift_canonical [Add B] [L.IsLawful] [L.HasBind] [L.IsSupportLocal] :
    (canonical L).HeadShift :=
  ⟨fun hc h ↦ IsLawful.frame hc h⟩

/-- The canonical law has diagonal heads by reflexivity of the lifting. -/
instance headDiag_canonical [AddZeroClass B] [L.IsLawful] [L.HasBind] [L.IsSupportLocal]
    [L.IsReflexive] : (canonical L).HeadDiag where
  diag μ _ _ hb := by simpa using IsLawful.frame hb (IsReflexive.refl (L := L) μ)
  side_diag _ _ _ _ := trivial

end BindLaw

end GradedLifting
