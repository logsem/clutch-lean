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

public import Metrology.Couplings.AdditiveCouplings

@[expose] public section

section DifferentialPrivacy

open MeasureTheory ProbabilityTheory NNReal ENNReal

-- Page 3

abbrev Mechanism (X Y : Type _) [MeasurableSpace X] [MeasurableSpace Y] :=
  Kernel X Y

abbrev Adjacency (X : Type _) := X → X → Prop

def Renyi {X : Type _} [MeasurableSpace X] (μ₁ μ₂ : Measure X) : ENNReal := sorry

section DifferentialPrivacy

variable {X Y : Type _} [MeasurableSpace X] [MeasurableSpace Y]

def DP (m : Mechanism X Y) (Φ : Adjacency X) (ε δ : ℝ≥0∞) : Prop :=
  ∀ {x x'}, Φ x x' → sorry

def RDP (m : Mechanism X Y) (Φ : Adjacency X) (α ρ : ℝ≥0∞) : Prop := sorry

def zCDP (m : Mechanism X Y) (Φ : Adjacency X) (ζ ρ : ℝ≥0∞) : Prop := sorry

def tCDP (m : Mechanism X Y) (Φ : Adjacency X) (ρ ω : ℝ≥0∞) : Prop := sorry

-- Privacy loss random variable
-- DP bounds the max loss
-- RDP bounds the alpha moment
-- zCDP bounds all moments
-- tCDP bounds the moments up to ω

end DifferentialPrivacy

section RelationalLiftings

variable {X Y : Type _} [MeasurableSpace X] [MeasurableSpace Y]

abbrev WeightFunction := ℝ → ℝ≥0

def FDiv (f : WeightFunction) (μ₁ μ₂ : Measure X) : ℝ≥0∞ := sorry

def WeightDP (ε : ℝ≥0∞) : WeightFunction := sorry

theorem DP_iff_FDiv_DeltaDP {Φ ε δ} {m : Mechanism X Y} :
  DP m Φ ε δ ↔ ∀ x x', FDiv (WeightDP ε) (m x) (m x') ≤ δ := sorry

def TWRL (R : X → Y → Prop) (f : WeightFunction) (δ : ℝ≥0∞) :
    Measure X → Measure Y → Prop := sorry

theorem TWRL_eq_iff_div {μ₁ μ₂ : Measure X} :
  TWRL (· = ·) f δ μ₁ μ₂ ↔ FDiv f μ₁ μ₂ ≤ δ := sorry

end RelationalLiftings

-- Page 6

-- Limits and colimits in Meas: what are they as a theorem in Mathlib?

-- Page 7
-- Graded monads: Unclear what we really need out of this.

-- Namespaced so this sketch's `Span` does not clash with `ApproximateSpanLifting`'s.
namespace DifferentialPrivacy

section Spans

structure SpanData (X Y Φ : Type _) : Type _ where
  ρ₁ : Φ → X
  ρ₂ : Φ → Y

structure Span (X Y Φ) [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Φ] : Type _
    extends SpanData X Y Φ where
  [measurable₁ : Measurable ρ₁]
  [measurable₂ : Measurable ρ₂ ]

structure SpanMorData (X Y Φ : Type _) (Z W Ψ : Type _) where
  h : X → Z
  k : Y → W
  l : Φ → Ψ

structure SpanMor (X Y Φ W Z Ψ) [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Φ]
    [MeasurableSpace W] [MeasurableSpace Z] [MeasurableSpace Ψ] : Type _
    extends SpanMorData X Y Φ W Z Ψ where
  [measurableh : Measurable h]
  [measurablek : Measurable k]
  [measurablel : Measurable l]
  comp₁ (S₁ : Span X Y Φ) (S₂ : Span Z W Ψ) : True
  comp₂ (S₁ : Span X Y Φ) (S₂ : Span Z W Ψ) : True

-- Coproducts
-- Binary relations to spans





end Spans

end DifferentialPrivacy
