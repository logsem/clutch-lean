module

public import Metrology.Couplings.Divergences.Renyi

/-! # Rényi curves

A Rényi bound at every order `α > 1` at once (Approximate Span Liftings, §4); its codensity
lifting is the order-wise one (`codensity_renyiCurve_iff`). -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory GradedLifting Set Function
open scoped ENNReal

/-- Rényi orders are above one. -/
instance fact_one_lt_coe_ioi (α : Ioi (1 : ℝ)) : Fact (1 < (α : ℝ)) :=
  ⟨α.2⟩

namespace GradedDivergence

/-! ## The curve -/

/-- A budget `ρ α` for every order `α > 1`, with the pointwise order and addition of `ℝ≥0∞`. -/
abbrev RenyiBudget :=
  Ioi (1 : ℝ) → ℝ≥0∞

/-- A Rényi bound at every order, each within its own budget (Rocq `RDPcoupl_curve`). -/
noncomputable def renyiCurve : GradedDivergence.{u} RenyiBudget :=
  pi fun α ↦ renyiDivergence α

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]

/-- A Rényi curve bound is a Rényi bound at every order. -/
theorem renyiCurve_iff {ρ : RenyiBudget} {μ ν : Measure X} :
    renyiCurve ρ μ ν ↔ ∀ α : Ioi (1 : ℝ), renyiDivergence α (ρ α) μ ν :=
  Iff.rfl

/-! ## Class instances, inherited from `pi` -/

/-- Rényi curves are graded order by order. -/
instance isGraded_renyiCurve : renyiCurve.{u}.IsGraded :=
  isGraded_pi

/-- Rényi curves are reflexive order by order. -/
instance isReflexive_renyiCurve : renyiCurve.{u}.IsReflexive :=
  isReflexive_pi

/-- Rényi curves compose order by order. -/
instance isComposable_renyiCurve : renyiCurve.{u}.IsComposable :=
  isComposable_pi

/-- The zero measure is within every Rényi curve of every measure. -/
instance isZeroLeft_renyiCurve : renyiCurve.{u}.IsZeroLeft :=
  isZeroLeft_pi

/-- Rényi curves are left continuous (Rocq `GCFamLim_curve`). -/
instance isLeftContinuous_renyiCurve : renyiCurve.{u}.IsLeftContinuous :=
  isLeftContinuous_pi

/-- Rényi curves are monotone in the right measure, order by order. -/
instance isRightMonotone_renyiCurve : renyiCurve.{u}.IsRightMonotone :=
  isRightMonotone_pi

/-- Rényi curves are antitone in the left measure, order by order. -/
instance isLeftAntitone_renyiCurve : renyiCurve.{u}.IsLeftAntitone :=
  isLeftAntitone_pi

/-- Rényi curve bounds are closed under decreasing limits of the budget. -/
instance isBudgetClosed_renyiCurve : renyiCurve.{u}.IsBudgetClosed :=
  isBudgetClosed_pi

/-! ## The codensity lifting of a curve -/

/-- A codensity lifting of a Rényi curve is one at every order. -/
theorem codensity_renyiCurve_iff {ρ : RenyiBudget} {R : X → Y → RenyiBudget} {μ : Measure X}
    {ν : Measure Y} : renyiCurve.codensity ρ R μ ν ↔
      ∀ α : Ioi (1 : ℝ), (renyiDivergence α).codensity (ρ α) (fun x y ↦ R x y α) μ ν := by
  classical
  refine ⟨fun h α I _ c hc k l _ _ hkl ↦ ?_, fun h I _ c _ k l _ _ hkl α ↦ ?_⟩
  · -- slack `c` at order `α`, `⊤` elsewhere: other orders pass by `renyiDivergence_top`
    have hlt : ρ + update ⊤ α c < ⊤ := lt_top_iff_ne_top.2 fun htop ↦
      hc.ne (by simpa using congrFun htop α)
    have hkl' (x : X) (y : Y) (β : Ioi (1 : ℝ)) :
        renyiDivergence β ((R x y + update (⊤ : RenyiBudget) α c) β) (k x) (l y) := by
      rcases eq_or_ne β α with rfl | hβ
      · simpa using hkl x y
      · simpa [hβ] using renyiDivergence_top β.2 (k x) (l y)
    simpa using h hlt hkl' α
  -- order by order; infinite orders are free
  rcases eq_or_ne (ρ α + c α) ⊤ with htop | hlt
  · simpa [htop] using renyiDivergence_top α.2 _ _
  · exact h α (lt_top_iff_ne_top.2 hlt) fun x y ↦ hkl x y α

/-- A curve is absorbing exactly at `⊤` (Rocq `GCF_curve_top_exact`). -/
theorem absorbing_codensity_renyiCurve_iff {ρ : RenyiBudget} :
    (codensity renyiCurve.{u}).Absorbing ρ ↔ ρ = ⊤ := by
  classical
  refine ⟨fun h ↦ by_contra fun hρ ↦ ?_,
    fun h ↦ h ▸ IsTopAbsorbing.absorbing_top (L := codensity _)⟩
  obtain ⟨α, hα⟩ := ne_iff.1 hρ
  refine not_absorbing_codensity_renyi α.2 (lt_top_iff_ne_top.2 hα) fun R μ ν _ _ ↦ ?_
  simpa using codensity_renyiCurve_iff.1 (h (fun x y ↦ update ⊤ α (R x y)) μ ν) α

end GradedDivergence
