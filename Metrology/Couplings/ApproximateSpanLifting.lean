module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad

@[expose] public section

section ApproximateSpanLifting

open MeasureTheory

structure Span (α β Φ : Type _) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace Φ] where
  left : Φ → α
  right : Φ → β
  leftMeasurable : Measurable left
  rightMeasurable : Measurable right

structure SpanMap [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace Φ] [MeasurableSpace α']
  [MeasurableSpace β'] [MeasurableSpace Φ'] (s₁ : Span α β Φ) (s₂ : Span α' β' Φ') where
  leftMap : α → α'
  rightMap : β → β'
  witnessMap : Φ → Φ'
  leftMeasurable : Measurable leftMap
  rightMeasurable : Measurable rightMap
  witnessMeasurable : Measurable witnessMap
  comm_left : leftMap ∘ s₁.left = s₂.left ∘ witnessMap
  comm_right : rightMap ∘ s₁.right = s₂.right ∘ witnessMap

section Span

variable {α α' β β' Φ Φ' : Type _}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace Φ]
variable [MeasurableSpace α'] [MeasurableSpace β'] [MeasurableSpace Φ']

def Span.prod (s₁ : Span α β Φ) (s₂ : Span α' β' Φ') : Span (α × α') (β × β') (Φ × Φ') where
  left := fun ⟨p, p'⟩ => ⟨s₁.left p, s₂.left p'⟩
  right := fun ⟨p, p'⟩ => ⟨s₁.right p, s₂.right p'⟩
  leftMeasurable :=
    .prodMk (s₁.leftMeasurable.comp measurable_fst) (s₂.leftMeasurable.comp measurable_snd)
  rightMeasurable :=
    .prodMk (s₁.rightMeasurable.comp measurable_fst) (s₂.rightMeasurable.comp measurable_snd)

end Span
end ApproximateSpanLifting
