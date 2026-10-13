module

public import Metrology.Couplings.DP.Divergence

/-! Approximate span liftings for differential privacy (Approximate Span Liftings, Thms. 5.2, 5.4,
§6.6, and the [DP-Trans] rule). -/

@[expose] public section

open MeasureTheory Set GradedDivergence Span
open scoped ENNReal NNReal

namespace DPDiv

universe u

variable {X Y X' Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X']
  [MeasurableSpace Y']
variable {Φ Ψ : Type u} [MeasurableSpace Φ] [MeasurableSpace Ψ]

/-- The DP span lifting `s♯(Δ_DP, ε, δ)` (Thm. 5.4). -/
noncomputable abbrev dpLift (s : Span X Y Φ) (ε : ℝ≥0) (δ : EReal) :
    Span (Measure X) (Measure Y) (Witness dp.{u} (.ofAdd ε) δ Φ) :=
  s♯[dp, .ofAdd ε, δ]

/-- Lifting the diagonal relates exactly the subprobability measures satisfying the DP inequality
(Thm. 5.2). -/
theorem rel_lift_diag_iff {ε : ℝ≥0} {δ : ℝ≥0∞} {μ ν : Measure Φ} :
    (dpLift (diag Φ) ε δ).Rel μ ν ↔ IsSubProbabilityMeasure μ ∧ IsSubProbabilityMeasure ν ∧
      Bound (ENNReal.ofReal (Real.exp ε)) δ μ ν := by
  rw [dpLift, rel_lift_diag]
  exact ⟨fun h ↦ ⟨h.fst, h.snd, dp_le_iff.1 h.le⟩, fun ⟨h₁, h₂, h⟩ ↦ ⟨h₁, h₂, dp_le_iff.2 h⟩⟩

namespace Hom

variable {s : Span X Y Φ} {t : Span X' Y' Ψ}

/-- The unit of the DP lifting, at budget `(0, 0)` (Thm. 5.4). -/
noncomputable def unit (s : Span X Y Φ) : s →ₛ dpLift s 0 0 :=
  Span.Hom.unit s

/-- Sequential composition of DP liftings adds budgets and slacks (Thm. 5.4). -/
noncomputable def bind {ε : ℝ≥0} {δ : EReal} (m : s →ₛ dpLift t ε δ) (ε' : ℝ≥0) (δ' : EReal) :
    dpLift s ε' δ' →ₛ dpLift t (ε' + ε) (δ' + δ) :=
  Span.Hom.bind m _ _

/-- Weakening the DP budget and slack (Thm. 5.4). -/
noncomputable def inclusion (s : Span X Y Φ) {ε ε' : ℝ≥0} {δ δ' : EReal} (hε : ε ≤ ε')
    (hδ : δ ≤ δ') :
    dpLift s ε δ →ₛ dpLift s ε' δ' :=
  Span.Hom.inclusion s (Multiplicative.ofAdd_le.2 hε) hδ

/-- Independent products of DP liftings add budgets and slacks (Thm. 5.4). -/
noncomputable def doubleStrength (s : Span X Y Φ) (t : Span X' Y' Ψ) (ε ε' : ℝ≥0) (δ δ' : EReal) :
    dpLift s ε δ ×̇ dpLift t ε' δ' →ₛ dpLift (s ×̇ t) (ε + ε') (δ + δ') :=
  Span.Hom.doubleStrength s t _ _ _ _

end Hom

/-- A mechanism is `(ε, δ)`-DP exactly when it extends to a span morphism from the adjacency
relation into the DP lifting of equality, so that a measurable witness choice exists (§6.6). -/
theorem DP_iff_exists_hom {Z : Type u} [MeasurableSpace Z] (m : Mechanism X Z)
    [∀ x, IsSubProbabilityMeasure (m x)] (Φ : Adjacency X) (ε : ℝ≥0) (δ : ℝ≥0∞) :
    DP m Φ ε δ ↔ ∃ H : ofRel {p | Φ p.1 p.2} →ₛ dpLift (diag Z) ε δ,
      H.leftMap = m ∧ H.rightMap = m := by
  constructor
  · intro h
    refine ⟨⟨m, m, fun p ↦ ⟨(m p.1.1, m p.1.2), inferInstance, inferInstance,
      dp_le_iff.2 (h p.2)⟩, m.measurable, m.measurable, by fun_prop,
      fun _ ↦ Measure.map_id.symm, fun _ ↦ Measure.map_id.symm⟩, rfl, rfl⟩
  · rintro ⟨H, hl, hr⟩ x x' hx S hS
    have := H.rel (a := x) (b := x') ⟨⟨(x, x'), hx⟩, rfl, rfl⟩
    rw [hl, hr, rel_lift_diag_iff] at this
    exact this.2.2 S hS

omit [MeasurableSpace X] in
/-- Group privacy: DP bounds chain along composed relations ([DP-Trans]). -/
theorem dp_trans {k₁ k₂ k₃ : X → Measure Y} {R₁ R₂ : X → X → Prop} {ε₁ ε₂ : ℝ≥0}
    {δ₁ δ₂ : ℝ≥0∞}
    (h₁ : ∀ ⦃x y⦄, R₁ x y → Bound (ENNReal.ofReal (Real.exp ε₁)) δ₁ (k₁ x) (k₂ y))
    (h₂ : ∀ ⦃y z⦄, R₂ y z → Bound (ENNReal.ofReal (Real.exp ε₂)) δ₂ (k₂ y) (k₃ z))
    {x z : X} (h : ∃ y, R₁ x y ∧ R₂ y z) :
    Bound (ENNReal.ofReal (Real.exp (ε₁ + ε₂)))
      (max (ENNReal.ofReal (Real.exp ε₂) * δ₁ + δ₂) (ENNReal.ofReal (Real.exp ε₁) * δ₂ + δ₁))
      (k₁ x) (k₃ z) := by
  obtain ⟨y, hxy, hyz⟩ := h
  refine ((h₁ hxy).trans (h₂ hyz)).mono (le_of_eq ?_) (le_max_right _ _)
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]

end DPDiv
