module

public import Metrology.Couplings.Lifting

/-! Bind laws: ways to compose a lifted step with lifted continuations (Rocq `GradedBindLaw`). -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory GradedLifting

/-- One way to compose a step with its continuations; the side condition sees only the spec side
(Rocq `GradedBindLaw`). -/
structure BindLaw {B : Type v} [LT B] [Top B] (L : GradedLifting.{u} B) where
  /-- The side condition on the spec measure and its continuation kernel. -/
  side : ∀ {Y Y' : Type u} [MeasurableSpace Y] [MeasurableSpace Y'], Measure Y → Kernel Y Y' → Prop
  /-- Under the side condition, a lifted step binds with continuations lifted wherever the
  leftover is finite. -/
  sound {X Y X' Y' : Type u} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X']
    [MeasurableSpace Y'] {b : B} {R : X → Y → B} {R' : X' → Y' → B} {μ : Measure X}
    {ν : Measure Y} {f : Kernel X X'} {g : Kernel Y Y'} [IsSubMarkovKernel f]
    [IsSubMarkovKernel g] :
    L b R μ ν → side ν g → (∀ x y, R x y < ⊤ → L (R x y) R' (f x) (g y)) →
      L b R' (f ∘ₘ μ) (g ∘ₘ ν)

namespace BindLaw

variable {B : Type v} [LT B] [Top B] {L : GradedLifting.{u} B} {X Y X' Y' : Type u}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X'] [MeasurableSpace Y']

variable (L) in
/-- The law without a side condition, given by an unconditional bind. -/
def canonical [L.HasBind] : BindLaw L :=
  ⟨fun _ _ ↦ True, fun h _ hk ↦ HasBind.bind h hk⟩

@[simp]
theorem side_canonical [L.HasBind] {ν : Measure Y} {g : Kernel Y Y'} : (canonical L).side ν g :=
  trivial

/-- A bind law applied to measurable families of sub-probability measures. -/
theorem bind_fun (law : BindLaw L) {b : B} {R : X → Y → B} {R' : X' → Y' → B} {μ : Measure X}
    {ν : Measure Y} (h : L b R μ ν) {f : X → Measure X'} {g : Y → Measure Y'}
    [∀ x, IsSubProbabilityMeasure (f x)] [∀ y, IsSubProbabilityMeasure (g y)]
    (hf : Measurable f) (hg : Measurable g) (hside : law.side ν ⟨g, hg⟩)
    (hk : ∀ x y, R x y < ⊤ → L (R x y) R' (f x) (g y)) : L b R' (μ.bind f) (ν.bind g) :=
  law.sound (f := ⟨f, hf⟩) (g := ⟨g, hg⟩) h hside hk

end BindLaw
