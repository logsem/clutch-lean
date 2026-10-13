module

public import Mathlib.Data.EReal.Operations
public import Metrology.Couplings.SubProbability

/-! Graded divergences (Approximate Span Liftings, §4). -/

@[expose] public section

universe u v

open MeasureTheory Measure Filter Topology

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

/-- Divergences after binding into a finite space are limits of divergences after discretizing
the input space (Def. 4.5). -/
class IsApproximable : Prop where
  tendsto (α : ι) {X : Type u} [MeasurableSpace X] (N : ℕ)
    {f g : X → Measure (ULift.{u} (Fin N))} [∀ x, IsSubProbabilityMeasure (f x)]
    [∀ x, IsSubProbabilityMeasure (g x)] (μ₁ μ₂ : Measure X) [IsSubProbabilityMeasure μ₁]
    [IsSubProbabilityMeasure μ₂] (hf : Measurable f := by fun_prop)
    (hg : Measurable g := by fun_prop) :
    ∃ (J : ℕ → ℕ) (d : ∀ n, X → ULift.{u} (Fin (J n))) (e : ∀ n, ULift.{u} (Fin (J n)) → X),
      (∀ n, Measurable (d n)) ∧ (∀ n, Measurable (e n)) ∧
      Tendsto (fun n ↦ Δ α (μ₁.bind (f ∘ e n ∘ d n)) (μ₂.bind (g ∘ e n ∘ d n))) atTop
        (𝓝 (Δ α (μ₁.bind f) (μ₂.bind g)))

/-- Composability between finite spaces (Def. 4.5). -/
class IsFiniteComposable [Mul ι] : Prop where
  bind_le (α β : ι) (M N : ℕ) (μ₁ μ₂ : Measure (ULift.{u} (Fin M)))
    [IsSubProbabilityMeasure μ₁] [IsSubProbabilityMeasure μ₂]
    {f g : ULift.{u} (Fin M) → Measure (ULift.{u} (Fin N))} [∀ i, IsSubProbabilityMeasure (f i)]
    [∀ i, IsSubProbabilityMeasure (g i)] (hf : Measurable f := by fun_prop)
    (hg : Measurable g := by fun_prop) :
    Δ (α * β) (μ₁.bind f) (μ₂.bind g) ≤ Δ α μ₁ μ₂ + ⨆ i, Δ β (f i) (g i)

/-- Composable implies finite-composable. -/
instance IsComposable.toIsFiniteComposable [Mul ι] [Δ.IsComposable] : Δ.IsFiniteComposable where
  bind_le α β _ _ μ₁ μ₂ _ _ _ _ _ _ hf hg := IsComposable.bind_le α β μ₁ μ₂ hf hg

/-- A continuous divergence does not increase under pushforward to a finite space. -/
theorem IsContinuous.map_le [Δ.IsContinuous] (α : ι) {X : Type u} [MeasurableSpace X] {n : ℕ}
    {k : X → ULift.{u} (Fin n)} (μ ν : Measure X) [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] (hk : Measurable k := by fun_prop) :
    Δ α (μ.map k) (ν.map k) ≤ Δ α μ ν := by
  rw [IsContinuous.eq_iSup (Δ := Δ) α μ ν]
  exact le_iSup_of_le n <| le_iSup_of_le k <| le_iSup_of_le hk le_rfl

/-- Continuous, approximable and finite-composable implies composable (Thm. 4.6). -/
theorem IsComposable.of_finite [Mul ι] [Δ.IsContinuous] [Δ.IsApproximable]
    [Δ.IsFiniteComposable] : Δ.IsComposable where
  bind_le α β X Y _ _ μ₁ μ₂ _ _ f g _ _ hf hg := by
    have := isSubProbabilityMeasure_bind (μ := μ₁) (f := f) inferInstance
    have := isSubProbabilityMeasure_bind (μ := μ₂) (f := g) inferInstance
    rw [IsContinuous.eq_iSup (Δ := Δ) (α * β) (μ₁.bind f) (μ₂.bind g)]
    refine iSup_le fun N ↦ iSup_le fun k ↦ iSup_le fun hk ↦ ?_
    rw [map_bind_eq μ₁, map_bind_eq μ₂]
    obtain ⟨J, d, e, hd, he, hlim⟩ := IsApproximable.tendsto (Δ := Δ) (α * β) N
      (f := fun x ↦ (f x).map k) (g := fun x ↦ (g x).map k) μ₁ μ₂
    refine le_of_tendsto' hlim fun n ↦ ?_
    have := hd n
    have := he n
    have h₁ := bind_map_eq μ₁ (hd n) (h := (fun x ↦ (f x).map k) ∘ e n)
    have h₂ := bind_map_eq μ₂ (hd n) (h := (fun x ↦ (g x).map k) ∘ e n)
    refine (congrArg₂ (fun a b ↦ Δ (α * β) a b) h₁ h₂).symm.trans_le ?_
    calc Δ (α * β) ((μ₁.map (d n)).bind fun j ↦ (f (e n j)).map k)
          ((μ₂.map (d n)).bind fun j ↦ (g (e n j)).map k)
        ≤ Δ α (μ₁.map (d n)) (μ₂.map (d n)) + ⨆ j, Δ β ((f (e n j)).map k) ((g (e n j)).map k) :=
          IsFiniteComposable.bind_le α β _ _ _ _
      _ ≤ Δ α μ₁ μ₂ + ⨆ x, Δ β (f x) (g x) :=
          add_le_add (IsContinuous.map_le Δ α μ₁ μ₂)
            (iSup_le fun j ↦ le_iSup_of_le (e n j) (IsContinuous.map_le Δ β _ _))

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

/-- Composable and functorial implies additive (cf. Thm. 4.4): a product measure is a bind. -/
instance IsComposable.toIsAdditive [Mul ι] [Δ.IsComposable] [Δ.IsFunctorial] : Δ.IsAdditive where
  prod_le α β X Y _ _ μ₁ μ₂ ν₁ ν₂ _ _ _ _ := by
    have hk (ν : Measure Y) [IsFiniteMeasure ν] : Measurable fun x : X ↦ ν.map (Prod.mk x) :=
      measurable_of_measurable_coe _ fun s hs ↦ by
        simp_rw [map_apply measurable_prodMk_left hs]
        exact measurable_measure_prodMk_left hs
    rw [Measure.prod_def, Measure.prod_def]
    calc Δ (α * β) (μ₁.bind fun x ↦ ν₁.map (Prod.mk x)) (μ₂.bind fun x ↦ ν₂.map (Prod.mk x))
        ≤ Δ α μ₁ μ₂ + ⨆ x, Δ β (ν₁.map (Prod.mk x)) (ν₂.map (Prod.mk x)) :=
          IsComposable.bind_le α β μ₁ μ₂ (hk ν₁) (hk ν₂)
      _ ≤ Δ α μ₁ μ₂ + Δ β ν₁ ν₂ := add_le_add le_rfl (iSup_le fun _ ↦ IsFunctorial.map_le β ν₁ ν₂)

end GradedDivergence
