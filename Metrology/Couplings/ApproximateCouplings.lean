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

/-! # Approximate couplings

Couplings up to `F`, tested by measurable functions into `[0, 1]` (`Bridges/AddCoupl.lean` relates
them to codensity). -/

@[expose] public section

/-- A function into `[0, 1]`. -/
def BoundedFunction {α : Type _} (f : α → ENNReal) : Prop :=
  ∀ a, f a ≤ 1

/-- A measurable test function into `[0, 1]`. -/
def CouplingFunction (α : Type _) [MeasurableSpace α] :=
  { f : α → ENNReal // Measurable f ∧ BoundedFunction f }

section ApproximateCoupling

variable {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]

namespace CouplingFunction

/-- Coupling functions are measurable. -/
theorem measurable (f : CouplingFunction α) : Measurable f.1 := f.property.1

/-- Coupling functions are bounded by one. -/
theorem bounded (f : CouplingFunction α) : ∀ a, f.1 a ≤ 1 := f.property.2

instance instCoeFun : CoeFun (CouplingFunction α) (fun _ => α → ENNReal) where
  coe := (·.1)

end CouplingFunction

open MeasureTheory

/-- A coupling up to `F`: every pair of tests ordered on `Φ` has its left integral below `F` of
the right one. -/
def ARCoupling (F : ENNReal → ENNReal) (Φ : Set (α × β)) (μₗ : Measure α) (μᵣ : Measure β) :=
  ∀ (f : CouplingFunction α) (g : CouplingFunction β),
    (∀ {a b}, Φ (a, b) → f a ≤ g b) →
    ∫⁻ x, f x ∂μₗ ≤ F (∫⁻ x, g x ∂μᵣ)

namespace ARCoupling

variable {F : ENNReal → ENNReal}

open Measure

/-- Every measure couples with itself along equality when `F` is inflationary (`HF`). -/
theorem refl (μ : Measure α) (HF : ∀ {x}, x ≤ F x) : ARCoupling F (fun v => v.1 = v.2) μ μ :=
  fun _ _ Hle => (lintegral_mono fun _ => Hle rfl).trans HF

/-- Dirac measures at related points couple when `F` is inflationary (`HF`). -/
theorem dirac {a : α} {b : β} (HF : ∀ {x}, x ≤ F x) (Φ : Set (α × β)) (H : Φ (a, b)) :
    ARCoupling F Φ (.dirac a) (.dirac b) := by
  refine fun ⟨f, Hf, _⟩ ⟨g, Hg, _⟩ Hle => ?_
  refine .trans ?_ HF
  rw [lintegral_dirac' _ Hf, lintegral_dirac' _ Hg]
  exact Hle H

/-- A coupling up to `F` is a coupling up to any larger `F'`. -/
theorem mono_F {F' : ENNReal → ENNReal} {Φ : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    (HF : ∀ x, F x ≤ F' x) (H : ARCoupling F Φ μₗ μᵣ) : ARCoupling F' Φ μₗ μᵣ :=
  fun f g Hle => (H f g Hle).trans (HF _)

/-- A coupling along a relation is a coupling along any larger relation. -/
theorem mono_rel {Φ Φ' : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β} (HS : Φ ⊆ Φ')
    (H : ARCoupling F Φ μₗ μᵣ) : ARCoupling F Φ' μₗ μᵣ :=
  fun f g Hle => H f g fun hab => Hle (HS hab)

/-- The zero measure on the left is coupled with anything. -/
theorem zero_left (S : Set (α × β)) (μᵣ : Measure β) : ARCoupling F S 0 μᵣ := by
  intro _ _ _
  simp

/-- Any measure couples with the zero measure on the right when its mass is at most `F 0`. -/
theorem zero_right (S : Set (α × β)) {μₗ : Measure α}
    (HF : μₗ .univ ≤ F 0) : ARCoupling F S μₗ 0 := by
  refine fun ⟨f, _, Hfb⟩ g Hle => ?_
  calc ∫⁻ x, f x ∂μₗ
    _ ≤ μₗ .univ := lintegral_le_meas Hfb (by simp)
    _ ≤ F 0 := HF
    _ ≤ F (∫⁻ x, g x ∂0) := by simp

end ARCoupling
end ApproximateCoupling
