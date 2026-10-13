module

public import Metrology.Couplings.DP.Concentrated
public import Metrology.Couplings.DP.Conversions
public import Metrology.Couplings.DP.Lifting

/-! The hierarchy of differential privacy notions (Approximate Span Liftings, §§2, 4.3, 5, Fig. 4).

Each notion bounds a graded divergence between the outputs of a mechanism on adjacent inputs:

* `(ε, δ)`-DP: `dp` at grade `ε`, bound `δ`. This is the `f`-divergence of
  `t ↦ max 0 (t - e^ε)`.
* `(α, ρ)`-RDP: `renyiDivergence α`, bound `ρ`. This is `log (·) / (α - 1)` of the `f`-divergence
  of `t ↦ t ^ α`.
* `(ξ, ρ)`-zCDP: `zcdpDivergence = sup_{α > 1} (D_α - ξ) / α` at grade `ξ`, bound `ρ`.
* `(ρ, ω)`-tCDP: `tcdpDivergence ω = sup_{1 < α < ω} D_α / α`, bound `ρ`.

Divergences take values in `ℝ≥0∞`, so the Rényi bounds `ρ` are nonnegative.

All four are reflexive, functorial and composable, so their span liftings `s♯[Δ, a, δ]` carry a
unit, a Kleisli extension and a double strength (Thm. 5.4). A mechanism satisfies a notion exactly
when it is a span morphism from adjacency into the lifting of the diagonal
(`bound_iff_exists_hom`). The conversions of Fig. 4 are morphisms between liftings of one span
(`Span.Hom.change`):

* `DP(ε, 0) → zCDP(ε, 0)`, `zCDP(ξ, ρ) → RDP(α, ξ + α ρ)`, `tCDP(ρ, ω) → RDP(α, α ρ)`;
* `RDP`, `zCDP` and `tCDP` each map to `DP` at every slack `δ > 0`. -/

@[expose] public section

open MeasureTheory Set GradedDivergence Span Real Renyi DPDiv
open scoped ENNReal NNReal

universe u

variable {ι ι' : Type*} {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {Ψ Z : Type u} [MeasurableSpace Ψ] [MeasurableSpace Z]

/-! ### Mechanisms as span morphisms -/

/-- A pointwise implication between divergence bounds is a morphism between liftings. -/
def Span.Hom.change {Δ : GradedDivergence.{u} ι} {Δ' : GradedDivergence.{u} ι'}
    (s : Span X Y Ψ) {α : ι} {α' : ι'} {δ δ' : ℝ≥0∞}
    (h : ∀ (μ ν : Measure Ψ) [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν],
      Δ α μ ν ≤ δ → Δ' α' μ ν ≤ δ') :
    s♯[Δ, α, δ] →ₛ s♯[Δ', α', δ'] where
  leftMap := _root_.id
  rightMap := _root_.id
  witnessMap w := ⟨w.1, w.2.fst, w.2.snd, @h _ _ w.2.fst w.2.snd w.le⟩
  comm_left _ := rfl
  comm_right _ := rfl

/-- A mechanism bounds the divergence between its outputs on adjacent inputs exactly when it
extends to a span morphism from adjacency into the lifting of the diagonal (Thm. 5.2, §6.6). -/
theorem bound_iff_exists_hom (Δ : GradedDivergence.{u} ι) (α : ι) (δ : ℝ≥0∞)
    (m : Mechanism X Z) [∀ x, IsSubProbabilityMeasure (m x)] (Φ : Adjacency X) :
    (∀ ⦃x x'⦄, Φ x x' → Δ α (m x) (m x') ≤ δ) ↔
      ∃ H : ofRel {p | Φ p.1 p.2} →ₛ (diag Z)♯[Δ, α, δ], H.leftMap = m ∧ H.rightMap = m := by
  constructor
  · intro h
    exact ⟨⟨m, m, fun p ↦ ⟨(m p.1.1, m p.1.2), inferInstance, inferInstance, h p.2⟩,
      m.measurable, m.measurable, by fun_prop, fun _ ↦ Measure.map_id.symm,
      fun _ ↦ Measure.map_id.symm⟩, rfl, rfl⟩
  · rintro ⟨H, hl, hr⟩ x x' hx
    have := H.rel (a := x) (b := x') ⟨⟨(x, x'), hx⟩, rfl, rfl⟩
    rw [hl, hr, rel_lift_diag] at this
    exact this.le

/-! ### Each notion is a divergence bound -/

section Notions

variable (m : Mechanism X Z) (Φ : Adjacency X)

theorem DP_iff_dp (ε : ℝ≥0) (δ : ℝ≥0∞) :
    DP m Φ ε δ ↔ ∀ ⦃x x'⦄, Φ x x' → dp (.ofAdd ε) (m x) (m x') ≤ δ :=
  forall₃_congr fun _ _ _ ↦ dp_le_iff.symm

theorem RDP_iff (α : ℝ) (ρ : ℝ≥0) :
    RDP m Φ α ρ ↔ ∀ ⦃x x'⦄, Φ x x' → renyiDivergence α () (m x) (m x') ≤ ρ :=
  forall₃_congr fun _ _ _ ↦ renyiDivergence.le_coe_iff.symm

theorem zCDP_iff (ξ ρ : ℝ≥0) :
    zCDP m Φ ξ ρ ↔ ∀ ⦃x x'⦄, Φ x x' → zcdpDivergence (.ofAdd ξ) (m x) (m x') ≤ ρ :=
  forall₃_congr fun _ _ _ ↦ (zcdpDivergence.le_iff ξ).symm

theorem tCDP_iff (ρ : ℝ≥0) (ω : ℝ) :
    tCDP m Φ ρ ω ↔ ∀ ⦃x x'⦄, Φ x x' → tcdpDivergence ω () (m x) (m x') ≤ ρ :=
  forall₃_congr fun _ _ _ ↦ tcdpDivergence.le_iff.symm

variable [∀ x, IsSubProbabilityMeasure (m x)]

theorem RDP_iff_exists_hom (α : ℝ) (ρ : ℝ≥0) :
    RDP m Φ α ρ ↔ ∃ H : ofRel {p | Φ p.1 p.2} →ₛ (diag Z)♯[renyiDivergence α, (), ρ],
      H.leftMap = m ∧ H.rightMap = m :=
  (RDP_iff m Φ α ρ).trans (bound_iff_exists_hom _ _ _ m Φ)

theorem zCDP_iff_exists_hom (ξ ρ : ℝ≥0) :
    zCDP m Φ ξ ρ ↔ ∃ H : ofRel {p | Φ p.1 p.2} →ₛ (diag Z)♯[zcdpDivergence, .ofAdd ξ, ρ],
      H.leftMap = m ∧ H.rightMap = m :=
  (zCDP_iff m Φ ξ ρ).trans (bound_iff_exists_hom _ _ _ m Φ)

theorem tCDP_iff_exists_hom (ρ : ℝ≥0) (ω : ℝ) :
    tCDP m Φ ρ ω ↔ ∃ H : ofRel {p | Φ p.1 p.2} →ₛ (diag Z)♯[tcdpDivergence ω, (), ρ],
      H.leftMap = m ∧ H.rightMap = m :=
  (tCDP_iff m Φ ρ ω).trans (bound_iff_exists_hom _ _ _ m Φ)

end Notions

/-! ### DP is an `f`-divergence -/

/-- The DP divergence is the `f`-divergence of `t ↦ max 0 (t - e^ε)` (§2.2). -/
theorem dp_le_iff_fDiv_le {ε : ℝ≥0} {δ : ℝ≥0∞} {μ ν : Measure Ψ} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : dp (.ofAdd ε) μ ν ≤ δ ↔ fDiv (.dp ε) μ ν ≤ δ :=
  dp_le_iff.trans (fDiv_dp_le_iff _ _ _ _).symm

namespace Span.Hom

variable (s : Span X Y Ψ)

/-- The DP lifting is the lifting for the DP `f`-divergence. -/
noncomputable def dpToFDiv (ε : ℝ≥0) (δ : ℝ≥0∞) : dpLift s ε δ →ₛ s♯[fDivergence (.dp ε), (), δ] :=
  change s fun _ _ _ _ h ↦ EReal.toENNReal_le_iff_le_coe.2 (dp_le_iff_fDiv_le.1 h)

/-- The DP `f`-divergence lifting is the DP lifting. -/
noncomputable def fDivToDp (ε : ℝ≥0) (δ : ℝ≥0∞) : s♯[fDivergence (.dp ε), (), δ] →ₛ dpLift s ε δ :=
  change s fun _ _ _ _ h ↦ dp_le_iff_fDiv_le.2 (EReal.toENNReal_le_iff_le_coe.1 h)

/-! ### Conversions (Fig. 4) -/

/-- Pure DP gives zCDP ([D/z]). -/
noncomputable def dpToZcdp (ε : ℝ≥0) : dpLift s ε 0 →ₛ s♯[zcdpDivergence, .ofAdd ε, 0] :=
  change s fun _ _ _ _ h ↦ (zcdpDivergence.le_iff ε (ρ := 0)).2 fun _ hα ↦ by
    rw [NNReal.coe_zero, mul_zero, add_zero]
    exact renyiDiv_le_of_bound (dp_le_iff.1 h) hα

/-- zCDP gives RDP at every order `α > 1` (Def. 2.4). -/
noncomputable def zcdpToRdp (ξ ρ : ℝ≥0) {α : ℝ} (hα : 1 < α) :
    s♯[zcdpDivergence, .ofAdd ξ, ρ] →ₛ s♯[renyiDivergence α, (), .ofReal (ξ + α * ρ)] :=
  change s fun _ _ _ _ h ↦ renyiDivergence.le_coe_iff.2 <|
    ((zcdpDivergence.le_iff ξ).1 h α hα).trans_eq <| congrArg _
      (Real.coe_toNNReal _ (add_nonneg ξ.2 (mul_nonneg (by linarith) ρ.2))).symm

/-- tCDP gives RDP at every order `1 < α < ω` (Def. 2.5). -/
noncomputable def tcdpToRdp (ρ : ℝ≥0) (ω : ℝ) {α : ℝ} (hα : 1 < α) (hαω : α < ω) :
    s♯[tcdpDivergence ω, (), ρ] →ₛ s♯[renyiDivergence α, (), .ofReal (α * ρ)] :=
  change s fun _ _ _ _ h ↦ renyiDivergence.le_coe_iff.2 <|
    (tcdpDivergence.le_iff.1 h α hα hαω).trans_eq <| congrArg _
      (Real.coe_toNNReal _ (mul_nonneg (by linarith) ρ.2)).symm

/-- RDP gives DP at every slack `δ > 0` ([R/D]). -/
noncomputable def rdpToDp {α : ℝ} (hα : 1 < α) (ρ : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    s♯[renyiDivergence α, (), ρ] →ₛ
      dpLift s (ρ + log (1 / δ) / (α - 1)).toNNReal (ENNReal.ofReal δ) :=
  change s fun _ _ _ _ h ↦ dp_le_iff.2 <| (bound_of_renyiDiv_le hα hδ
    (renyiDivergence.le_coe_iff.1 h)).mono
    (ENNReal.ofReal_le_ofReal (exp_le_exp.2 (le_coe_toNNReal _))) le_rfl

/-- zCDP gives DP at every slack `0 < δ < 1` ([z/D]). -/
noncomputable def zcdpToDp (ξ ρ : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) :
    s♯[zcdpDivergence, .ofAdd ξ, ρ] →ₛ
      dpLift s (ξ + ρ + 2 * √(ρ * log (1 / δ))).toNNReal (ENNReal.ofReal δ) :=
  change s fun _ _ _ _ h ↦ dp_le_iff.2 <|
    (bound_of_zcdp ρ.2 hδ hδ₁ ((zcdpDivergence.le_iff ξ).1 h)).mono
      (ENNReal.ofReal_le_ofReal (exp_le_exp.2 (le_coe_toNNReal _))) le_rfl

/-- tCDP gives DP at every slack `0 < δ < 1` ([t/D]). -/
noncomputable def tcdpToDp {ρ : ℝ≥0} {ω : ℝ} (hρ : 0 < ρ) (hω : 1 < ω) {δ : ℝ} (hδ : 0 < δ)
    (hδ₁ : δ < 1) :
    s♯[tcdpDivergence ω, (), ρ] →ₛ
      dpLift s (ρ * min ω (1 + √(log (1 / δ) / ρ)) +
        log (1 / δ) / (min ω (1 + √(log (1 / δ) / ρ)) - 1)).toNNReal (ENNReal.ofReal δ) :=
  change s fun _ _ _ _ h ↦ dp_le_iff.2 <|
    (bound_of_tcdp (NNReal.coe_pos.2 hρ) hω hδ hδ₁ (tcdpDivergence.le_iff.1 h)).mono
      (ENNReal.ofReal_le_ofReal (exp_le_exp.2 (le_coe_toNNReal _))) le_rfl

end Span.Hom
