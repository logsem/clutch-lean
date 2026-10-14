module

public import Metrology.Couplings.SubProbability

/-! Graded divergences (Approximate Span Liftings, §4). -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory Filter Topology
open scoped ENNReal

/-- A family of divergences between measures, indexed by a grade and a space (Defs. 4.1, 4.2). -/
def GradedDivergence (ι : Type v) : Type (max v (u + 1)) :=
  ι → ∀ {X : Type u} [MeasurableSpace X], Measure X → Measure X → ℝ≥0∞

namespace GradedDivergence

variable {ι : Type v} (Δ : GradedDivergence.{u} ι)

/-- Larger grades give smaller divergences (Def. 4.2). -/
class IsGraded [Preorder ι] : Prop where
  anti ⦃α β : ι⦄ (h : α ≤ β) {X : Type u} [MeasurableSpace X] (μ ν : Measure X)
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] : Δ β μ ν ≤ Δ α μ ν

/-- A subprobability measure is at divergence zero from itself at the unit grade (Def. 4.3). The
paper only asks this of Dirac measures; asking it of all of them gives data processing. -/
class IsReflexive [One ι] : Prop where
  self_le_zero {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsSubProbabilityMeasure μ] :
    Δ 1 μ μ ≤ 0

/-- Pushing forward along a measurable map does not increase the divergence (Def. 4.3). -/
class IsFunctorial : Prop where
  map_le (α : ι) {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {k : X → Y}
    (μ ν : Measure X) [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    (hk : Measurable k := by fun_prop) : Δ α (μ.map k) (ν.map k) ≤ Δ α μ ν

/-- Composing with a kernel does not increase the divergence (Def. 4.3). -/
class IsSubstitutive : Prop where
  bind_le (α : ι) {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] (κ : Kernel X Y)
    [IsSubMarkovKernel κ] (μ ν : Measure X) [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] : Δ α (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ Δ α μ ν

/-- The divergence of product measures is at most the sum of the divergences (Def. 4.3). -/
class IsAdditive [Mul ι] : Prop where
  prod_le (α β : ι) {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] (μ₁ μ₂ : Measure X)
    (ν₁ ν₂ : Measure Y) [IsSubProbabilityMeasure μ₁] [IsSubProbabilityMeasure μ₂]
    [IsSubProbabilityMeasure ν₁] [IsSubProbabilityMeasure ν₂] :
    Δ (α * β) (μ₁.prod ν₁) (μ₂.prod ν₂) ≤ Δ α μ₁ μ₂ + Δ β ν₁ ν₂

/-- The divergence after composing with two kernels is at most the divergence before, plus the
largest divergence between the kernels (Def. 4.3). -/
class IsComposable [Mul ι] : Prop where
  bind_le (α β : ι) {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] (μ₁ μ₂ : Measure X)
    [IsSubProbabilityMeasure μ₁] [IsSubProbabilityMeasure μ₂] (κ η : Kernel X Y)
    [IsSubMarkovKernel κ] [IsSubMarkovKernel η] :
    Δ (α * β) (κ ∘ₘ μ₁) (η ∘ₘ μ₂) ≤ Δ α μ₁ μ₂ + ⨆ x, Δ β (κ x) (η x)

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
    (κ η : Kernel (ULift.{u} (Fin M)) (ULift.{u} (Fin N))) [IsSubMarkovKernel κ]
    [IsSubMarkovKernel η] : Δ (α * β) (κ ∘ₘ μ₁) (η ∘ₘ μ₂) ≤ Δ α μ₁ μ₂ + ⨆ i, Δ β (κ i) (η i)

/-- The zero measure is at divergence zero from any measure. -/
class IsZeroLeft : Prop where
  zero_left_le (α : ι) {X : Type u} [MeasurableSpace X] (ν : Measure X) : Δ α 0 ν ≤ 0

/-- The divergence is at most the mass of the left measure. -/
class IsMassBounded : Prop where
  le_measure_univ (α : ι) {X : Type u} [MeasurableSpace X] (μ ν : Measure X)
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] : Δ α μ ν ≤ μ .univ

/-- The divergence from the limit of an increasing sequence is at most the limit of the
divergences. -/
class IsLeftContinuous : Prop where
  iSup_left_le (α : ι) {X : Type u} [MeasurableSpace X] {μ : ℕ → Measure X}
    [∀ n, IsSubProbabilityMeasure (μ n)] (hμ : Monotone μ) (ν : Measure X)
    [IsSubProbabilityMeasure ν] : Δ α (⨆ n, μ n) ν ≤ ⨆ n, Δ α (μ n) ν

/-- Composable implies finite-composable. -/
instance IsComposable.toIsFiniteComposable [Mul ι] [Δ.IsComposable] : Δ.IsFiniteComposable where
  bind_le α β _ _ μ₁ μ₂ _ _ κ η _ _ := IsComposable.bind_le α β μ₁ μ₂ κ η

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
  bind_le α β X Y _ _ μ₁ μ₂ _ _ κ η _ _ := by
    rw [IsContinuous.eq_iSup (Δ := Δ) (α * β) (κ ∘ₘ μ₁) (η ∘ₘ μ₂)]
    refine iSup_le fun N ↦ iSup_le fun k ↦ iSup_le fun hk ↦ ?_
    rw [map_comp μ₁ κ hk, map_comp μ₂ η hk]
    obtain ⟨J, d, e, hd, he, hlim⟩ :=
      IsApproximable.tendsto (Δ := Δ) (α * β) N (f := κ.map k) (g := η.map k) μ₁ μ₂
    refine le_of_tendsto' hlim fun n ↦ ?_
    calc _ = Δ (α * β) ((κ.map k).comap (e n) (he n) ∘ₘ μ₁.map (d n))
          ((η.map k).comap (e n) (he n) ∘ₘ μ₂.map (d n)) := by
          rw [bind_map_eq μ₁ (hd n), bind_map_eq μ₂ (hd n)]
          rfl
      _ ≤ Δ α (μ₁.map (d n)) (μ₂.map (d n)) +
            ⨆ j, Δ β ((κ.map k).comap (e n) (he n) j) ((η.map k).comap (e n) (he n) j) :=
          IsFiniteComposable.bind_le α β _ _ _ _ _ _
      _ ≤ Δ α μ₁ μ₂ + ⨆ x, Δ β (κ x) (η x) := by
          refine add_le_add (IsContinuous.map_le Δ α μ₁ μ₂ (hd n)) (iSup_le fun j ↦ ?_)
          simp only [Kernel.comap_apply, Kernel.map_apply _ hk]
          exact le_iSup_of_le (e n j) (IsContinuous.map_le Δ β _ _)

/-- Reflexive and composable implies substitutive. -/
instance IsComposable.toIsSubstitutive [MulOneClass ι] [Δ.IsReflexive] [Δ.IsComposable] :
    Δ.IsSubstitutive where
  bind_le α X Y _ _ κ _ μ ν _ _ :=
    calc Δ α (κ ∘ₘ μ) (κ ∘ₘ ν)
        = Δ (α * 1) (κ ∘ₘ μ) (κ ∘ₘ ν) := by rw [mul_one]
      _ ≤ Δ α μ ν + ⨆ x, Δ 1 (κ x) (κ x) := IsComposable.bind_le α 1 μ ν κ κ
      _ ≤ Δ α μ ν + 0 := add_le_add le_rfl (iSup_le fun x ↦ IsReflexive.self_le_zero _)
      _ = Δ α μ ν := add_zero _

/-- Substitutive implies functorial. -/
instance IsSubstitutive.toIsFunctorial [Δ.IsSubstitutive] : Δ.IsFunctorial where
  map_le α X Y _ _ k μ ν _ _ hk := by
    rw [← deterministic_comp_eq_map hk, ← deterministic_comp_eq_map hk]
    exact IsSubstitutive.bind_le α (.deterministic k hk) μ ν

/-- Composable and functorial implies additive (cf. Thm. 4.4): a product measure is a bind. -/
instance IsComposable.toIsAdditive [Mul ι] [Δ.IsComposable] [Δ.IsFunctorial] : Δ.IsAdditive where
  prod_le α β X Y _ _ μ₁ μ₂ ν₁ ν₂ _ _ _ _ := by
    let K (ν : Measure Y) [IsFiniteMeasure ν] : Kernel X (X × Y) :=
      ⟨fun x ↦ ν.map (Prod.mk x), measurable_of_measurable_coe _ fun s hs ↦ by
        simp_rw [map_apply measurable_prodMk_left hs]
        exact measurable_measure_prodMk_left hs⟩
    calc Δ (α * β) (μ₁.prod ν₁) (μ₂.prod ν₂)
        = Δ (α * β) (K ν₁ ∘ₘ μ₁) (K ν₂ ∘ₘ μ₂) := by
          rw [Measure.prod_def, Measure.prod_def]
          rfl
      _ ≤ Δ α μ₁ μ₂ + ⨆ x, Δ β (ν₁.map (Prod.mk x)) (ν₂.map (Prod.mk x)) :=
          IsComposable.bind_le α β μ₁ μ₂ (K ν₁) (K ν₂)
      _ ≤ Δ α μ₁ μ₂ + Δ β ν₁ ν₂ := add_le_add le_rfl (iSup_le fun _ ↦ IsFunctorial.map_le β ν₁ ν₂)

end GradedDivergence
