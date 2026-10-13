module

public import Mathlib.Data.EReal.Operations
public import Metrology.Couplings.SubProbability

/-! Graded divergences (Approximate Span Liftings, §4). -/

@[expose] public section

universe u v

open MeasureTheory Measure

/-- A family of divergences between measures, indexed by a grade and a space (Defs. 4.1, 4.2). -/
def GradedDivergence (ι : Type v) : Type (max v (u + 1)) :=
  ι → ∀ {X : Type u} [MeasurableSpace X], Measure X → Measure X → EReal

namespace GradedDivergence

variable {ι : Type v} (Δ : GradedDivergence.{u} ι)

/-- Larger grades give smaller divergences (Def. 4.2). -/
class IsGraded [Preorder ι] : Prop where
  anti ⦃α β : ι⦄ (h : α ≤ β) {X : Type u} [MeasurableSpace X] (μ ν : Measure X)
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] : Δ β μ ν ≤ Δ α μ ν

/-- A measure is at divergence at most zero from itself at the unit grade (Def. 4.3). -/
class IsReflexive [One ι] : Prop where
  self_le_zero {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsSubProbabilityMeasure μ] :
    Δ 1 μ μ ≤ 0

/-- Pushing forward along a measurable map does not increase the divergence (Def. 4.3). -/
class IsFunctorial : Prop where
  map_le (α : ι) {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {k : X → Y}
    (μ ν : Measure X) [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    (hk : Measurable k := by fun_prop) : Δ α (μ.map k) (ν.map k) ≤ Δ α μ ν

/-- Binding with a measurable kernel does not increase the divergence (Def. 4.3). -/
class IsSubstitutive : Prop where
  bind_le (α : ι) {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {f : X → Measure Y}
    [∀ x, IsSubProbabilityMeasure (f x)] (μ ν : Measure X) [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] (hf : Measurable f := by fun_prop) :
    Δ α (μ.bind f) (ν.bind f) ≤ Δ α μ ν

/-- The divergence of product measures is at most the sum of the divergences (Def. 4.3). -/
class IsAdditive [Mul ι] : Prop where
  prod_le (α β : ι) {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] (μ₁ μ₂ : Measure X)
    (ν₁ ν₂ : Measure Y) [IsSubProbabilityMeasure μ₁] [IsSubProbabilityMeasure μ₂]
    [IsSubProbabilityMeasure ν₁] [IsSubProbabilityMeasure ν₂] :
    Δ (α * β) (μ₁.prod ν₁) (μ₂.prod ν₂) ≤ Δ α μ₁ μ₂ + Δ β ν₁ ν₂

/-- The divergence after binding with two kernels is at most the divergence before, plus the
largest divergence between the kernels (Def. 4.3). -/
class IsComposable [Mul ι] : Prop where
  bind_le (α β : ι) {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] (μ₁ μ₂ : Measure X)
    [IsSubProbabilityMeasure μ₁] [IsSubProbabilityMeasure μ₂] {f g : X → Measure Y}
    [∀ x, IsSubProbabilityMeasure (f x)] [∀ x, IsSubProbabilityMeasure (g x)]
    (hf : Measurable f := by fun_prop) (hg : Measurable g := by fun_prop) :
    Δ (α * β) (μ₁.bind f) (μ₂.bind g) ≤ Δ α μ₁ μ₂ + ⨆ x, Δ β (f x) (g x)

/-- The divergence is the supremum of its pushforwards to finite spaces (Def. 4.3). -/
class IsContinuous : Prop where
  eq_iSup (α : ι) {X : Type u} [MeasurableSpace X] (μ ν : Measure X)
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    Δ α μ ν = ⨆ (n : ℕ) (k : X → ULift.{u} (Fin n)) (_ : Measurable k),
      Δ α (μ.map k) (ν.map k)

/-- Reflexive and composable implies substitutive. -/
instance IsComposable.toIsSubstitutive [MulOneClass ι] [Δ.IsReflexive] [Δ.IsComposable] :
    Δ.IsSubstitutive where
  bind_le α X Y _ _ f _ μ ν _ _ hf :=
    calc Δ α (μ.bind f) (ν.bind f)
        = Δ (α * 1) (μ.bind f) (ν.bind f) := by rw [mul_one]
      _ ≤ Δ α μ ν + ⨆ x, Δ 1 (f x) (f x) := IsComposable.bind_le α 1 μ ν
      _ ≤ Δ α μ ν + 0 := add_le_add le_rfl (iSup_le fun x ↦ IsReflexive.self_le_zero _)
      _ = Δ α μ ν := add_zero _

/-- Substitutive implies functorial. -/
instance IsSubstitutive.toIsFunctorial [Δ.IsSubstitutive] : Δ.IsFunctorial where
  map_le α X Y _ _ k μ ν _ _ hk := by
    rw [← bind_dirac_eq_map μ hk, ← bind_dirac_eq_map ν hk]
    exact IsSubstitutive.bind_le (f := fun x ↦ dirac (k x)) α μ ν

end GradedDivergence
