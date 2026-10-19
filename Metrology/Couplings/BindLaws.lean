module

public import Metrology.Couplings.Divergences.DpShapes
public import Metrology.Couplings.Divergences.RenyiAdaptive

/-! Bind laws beyond the canonical one: adaptive and choice DP composition, and escort-adaptive
Rényi composition (Rocq `instances_dp.v`). -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory GradedLifting GradedDivergence
open scoped ENNReal

namespace GradedLifting.BindLaw

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]

/-! ## DP, adaptive on the right outcome -/

/-- The head of right-keyed adaptive DP composition: a DP lifting of `S` within `(ε₁, δ₁)` whose
pairs continue at `(ε₂, D y)`, paid as `(ε₁ + ε₂, δ₁ + e^{ε₁} E_ν[D])` (Rocq `dp_rhs_head`). -/
def DpRhsHead (μ : Measure X) (ν : Measure Y) (R : X → Y → ℝ≥0∞ × ℝ≥0∞) (b : ℝ≥0∞ × ℝ≥0∞) :
    Prop :=
  ∃ (ε₁ ε₂ δ₁ : ℝ≥0∞) (D : Y → ℝ≥0∞) (S : X → Y → Prop), Measurable D ∧
    IsSubProbabilityMeasure μ ∧ IsSubProbabilityMeasure ν ∧ (codensity dp).Rel (ε₁, δ₁) S μ ν ∧
    (∀ x y, S x y → R x y = (ε₂, D y)) ∧ (ε₁ + ε₂, δ₁ + expBudget ε₁ * ∫⁻ y, D y ∂ν) ≤ b

/-- Right-keyed adaptive DP composition as a bind law (Rocq `GBL_DP_rhs`). -/
noncomputable def dpRhs : BindLaw (codensity dp.{u}) where
  head := DpRhsHead
  side _ _ _ _ _ := True
  sound := by
    classical
    rintro _ _ _ _ _ _ _ _ _ R _ μ ν f g _ _ ⟨ε₁, ε₂, δ₁, D, S, hD, hμ, hν, hS, hR, hb⟩ _ hk
    refine IsLawful.mono (L := codensity dp) ?_ hb le_rfl
    · exact HasBind.bind (codensity_dp_rhs hS hD) fun x y hxy ↦ by
        by_cases hxy' : S x y
        · simpa [hxy', hR x y hxy'] using hk x y (by simpa [hR x y hxy', hxy'] using hxy)
        · simp [hxy'] at hxy
  mono_out := fun ⟨ε₁, ε₂, δ₁, D, S, hD, hμ, hν, hS, hR, hb⟩ hb' ↦
    ⟨ε₁, ε₂, δ₁, D, S, hD, hμ, hν, hS, hR, hb.trans hb'⟩
  head_supp := by
    rintro _ _ _ _ _ _ _ _ A _ hA hμA ⟨ε₁, ε₂, δ₁, D, S, hD, hμ, hν, hS, hR, hb⟩
    refine ⟨ε₁, ε₂, δ₁, D, fun x y ↦ S x y ∧ x ∈ A, hD, hμ, hν, hS.restrict hA hμA,
      fun x y ⟨hxy, hx⟩ ↦ ?_, hb⟩
    simpa [Set.piecewise_eq_of_mem _ _ _ hx] using hR x y hxy
  side_supp _ := trivial

/-! ## DP, adaptive on the left outcome -/

/-- The head of left-keyed adaptive DP composition: a DP lifting of `S` within `(ε₁, δ₁)` whose
pairs continue at `(ε₂, D x)`, paid as `(ε₁ + ε₂, δ₁ + E_μ[D])` (Rocq `dp_lhs_head`). -/
def DpLhsHead (μ : Measure X) (ν : Measure Y) (R : X → Y → ℝ≥0∞ × ℝ≥0∞) (b : ℝ≥0∞ × ℝ≥0∞) :
    Prop :=
  ∃ (ε₁ ε₂ δ₁ : ℝ≥0∞) (D : X → ℝ≥0∞) (S : X → Y → Prop), Measurable D ∧
    IsSubProbabilityMeasure μ ∧ IsSubProbabilityMeasure ν ∧ (codensity dp).Rel (ε₁, δ₁) S μ ν ∧
    (∀ x y, S x y → R x y = (ε₂, D x)) ∧ (ε₁ + ε₂, δ₁ + ∫⁻ x, D x ∂μ) ≤ b

/-- Left-keyed adaptive DP composition as a bind law (Rocq `GBL_DP_lhs`). -/
noncomputable def dpLhs : BindLaw (codensity dp.{u}) where
  head := DpLhsHead
  side _ _ _ _ _ := True
  sound := by
    classical
    rintro _ _ _ _ _ _ _ _ _ R _ μ ν f g _ _ ⟨ε₁, ε₂, δ₁, D, S, hD, hμ, hν, hS, hR, hb⟩ _ hk
    refine IsLawful.mono (L := codensity dp) ?_ hb le_rfl
    · exact HasBind.bind (codensity_dp_lhs hS hD) fun x y hxy ↦ by
        by_cases hxy' : S x y
        · simpa [hxy', hR x y hxy'] using hk x y (by simpa [hR x y hxy', hxy'] using hxy)
        · simp [hxy'] at hxy
  mono_out := fun ⟨ε₁, ε₂, δ₁, D, S, hD, hμ, hν, hS, hR, hb⟩ hb' ↦
    ⟨ε₁, ε₂, δ₁, D, S, hD, hμ, hν, hS, hR, hb.trans hb'⟩
  head_supp := by
    rintro _ _ _ _ _ _ _ _ A _ hA hμA ⟨ε₁, ε₂, δ₁, D, S, hD, hμ, hν, hS, hR, hb⟩
    refine ⟨ε₁, ε₂, δ₁, D, fun x y ↦ S x y ∧ x ∈ A, hD, hμ, hν, hS.restrict hA hμA,
      fun x y ⟨hxy, hx⟩ ↦ ?_, hb⟩
    simpa [Set.piecewise_eq_of_mem _ _ _ hx] using hR x y hxy
  side_supp _ := trivial

/-! ## DP choice -/

/-- The head of the DP choice rule: two DP liftings of the same pair, chosen by a measurable left
predicate `P` whose sides they send to the sides of a measurable `T`, continuing at `(ε₂, δ₂)` on
`P` and `(ε₂', δ₂)` off it (Rocq `dp_choice_head`). -/
def DpChoiceHead (μ : Measure X) (ν : Measure Y) (R : X → Y → ℝ≥0∞ × ℝ≥0∞)
    (b : ℝ≥0∞ × ℝ≥0∞) : Prop :=
  ∃ (ε₁ δ₁ ε₁' δ₁' ε₂ ε₂' δ₂ : ℝ≥0∞) (S₁ S₂ : X → Y → Prop) (P : Set X) (T : Set Y),
    MeasurableSet P ∧ MeasurableSet T ∧ IsSubProbabilityMeasure μ ∧ IsSubProbabilityMeasure ν ∧
    (codensity dp).Rel (ε₁, δ₁) S₁ μ ν ∧ (codensity dp).Rel (ε₁', δ₁') S₂ μ ν ∧
    (∀ x y, x ∈ P → S₁ x y → y ∈ T) ∧ (∀ x y, x ∉ P → S₂ x y → y ∉ T) ∧
    (∀ x y, x ∈ P → S₁ x y → R x y = (ε₂, δ₂)) ∧ (∀ x y, x ∉ P → S₂ x y → R x y = (ε₂', δ₂)) ∧
    (max (ε₁ + ε₂) (ε₁' + ε₂'), δ₁ + δ₁' + δ₂) ≤ b

/-- The DP choice rule as a bind law (Rocq `GBL_DP_choice`). -/
noncomputable def dpChoice : BindLaw (codensity dp.{u}) where
  head := DpChoiceHead
  side _ _ _ _ _ := True
  sound := by
    classical
    rintro _ _ _ _ _ _ _ _ _ R _ μ ν f g _ _
      ⟨ε₁, δ₁, ε₁', δ₁', ε₂, ε₂', δ₂, S₁, S₂, P, T, hP, hT, hμ, hν, h₁, h₂, hPT₁, hPT₂, hR₁, hR₂,
        hb⟩ _ hk
    refine IsLawful.mono (L := codensity dp) ?_ hb le_rfl
    · refine HasBind.bind (codensity_dp_choice h₁ h₂ hP hT hPT₁ hPT₂) fun x y hxy ↦ ?_
      by_cases hx : x ∈ P
      · by_cases hxy' : S₁ x y
        · simpa [hx, hxy', hR₁ x y hx hxy'] using
            hk x y (by simpa [hR₁ x y hx hxy', hx, hxy'] using hxy)
        · simp [hx, hxy'] at hxy
      · by_cases hxy' : S₂ x y
        · simpa [hx, hxy', hR₂ x y hx hxy'] using
            hk x y (by simpa [hR₂ x y hx hxy', hx, hxy'] using hxy)
        · simp [hx, hxy'] at hxy
  mono_out := fun ⟨ε₁, δ₁, ε₁', δ₁', ε₂, ε₂', δ₂, S₁, S₂, P, T, hP, hT, hμ, hν, h₁, h₂, hPT₁, hPT₂,
      hR₁, hR₂, hb⟩ hb' ↦
    ⟨ε₁, δ₁, ε₁', δ₁', ε₂, ε₂', δ₂, S₁, S₂, P, T, hP, hT, hμ, hν, h₁, h₂, hPT₁, hPT₂, hR₁, hR₂,
      hb.trans hb'⟩
  head_supp := by
    rintro _ _ _ _ _ _ _ _ A _ hA hμA ⟨ε₁, δ₁, ε₁', δ₁', ε₂, ε₂', δ₂, S₁, S₂, P, T, hP, hT, hμ, hν,
      h₁, h₂, hPT₁, hPT₂, hR₁, hR₂, hb⟩
    refine ⟨ε₁, δ₁, ε₁', δ₁', ε₂, ε₂', δ₂, fun x y ↦ S₁ x y ∧ x ∈ A, fun x y ↦ S₂ x y ∧ x ∈ A,
      P, T, hP, hT, hμ, hν, h₁.restrict hA hμA, h₂.restrict hA hμA,
      fun x y hx h ↦ hPT₁ x y hx h.1, fun x y hx h ↦ hPT₂ x y hx h.1,
      fun x y hx ⟨h, hxA⟩ ↦ ?_, fun x y hx ⟨h, hxA⟩ ↦ ?_, hb⟩
    · simpa [Set.piecewise_eq_of_mem _ _ _ hxA] using hR₁ x y hx h
    · simpa [Set.piecewise_eq_of_mem _ _ _ hxA] using hR₂ x y hx h
  side_supp _ := trivial

/-! ## Escort-adaptive Rényi -/

/-- The head of escort-adaptive Rényi composition: an `S`-supported witness kernel `r` such that
`μ` is within `ρ` of `r ∘ ν` reweighted by `e^{-ρ₂}`, continuing at `ρ₂ x` on `S` over a set
carrying `μ` (`codensity_renyi_bind_escort`, Rocq `escort_adaptive`). -/
def EscortHead (α : ℝ) (μ : Measure X) (ν : Measure Y) (R : X → Y → ℝ≥0∞) (ρ : ℝ≥0∞) : Prop :=
  ∃ (S : X → Y → Prop) (ρ₂ : X → ℝ≥0∞) (r : Kernel Y X) (A : Set X), IsSubMarkovKernel r ∧
    Measurable ρ₂ ∧ MeasurableSet A ∧ μ Aᶜ = 0 ∧ IsSubProbabilityMeasure μ ∧
    IsSubProbabilityMeasure ν ∧ (∀ y, ∀ᵐ x ∂r y, S x y) ∧ (∀ x y, x ∈ A → S x y → R x y = ρ₂ x) ∧
    renyiDivergence α ρ μ ((r ∘ₘ ν).withDensity fun x ↦ (expBudget (ρ₂ x))⁻¹)

/-- Escort-adaptive Rényi composition as a bind law: the continuation budget depends on the left
outcome and is averaged under the escort, not under `μ` (Rocq `escort_adaptive`). -/
noncomputable def escort (α : ℝ) [Fact (1 < α)] : BindLaw (codensity (renyiDivergence.{u} α)) where
  head := EscortHead α
  side _ _ _ _ _ := True
  sound := by
    classical
    rintro _ _ _ _ _ _ _ _ _ R _ μ ν f g _ _ ⟨S, ρ₂, r, A, hr, hρ₂, hA, hμA, hμ, hν, hrS, hR, h⟩
      _ hk
    have hf : Kernel.piecewise hA f 0 ∘ₘ μ = f ∘ₘ μ := by
      rw [Measure.piecewise_zero_comp, restrict_eq_self_of_ae_mem (mem_ae_iff.2 hμA)]
    rw [← hf]
    refine codensity_renyi_bind_escort hρ₂ r hrS (fun x y hxy ↦ ?_) h
    by_cases hx : x ∈ A
    · simp only [Kernel.piecewise_apply, hx, ↓reduceIte]
      rcases lt_or_eq_of_le (le_top : ρ₂ x ≤ ⊤) with hlt | htop
      · simpa [hR x y hx hxy] using hk x y (by simpa [hR x y hx hxy] using hlt)
      · rw [htop]
        exact IsTopAbsorbing.top _ _ _
    · simp only [Kernel.piecewise_apply, hx, ↓reduceIte]
      exact IsZeroLeft.zero_left (L := codensity (renyiDivergence α)) _ _ _
  mono_out := fun ⟨S, ρ₂, r, A, hr, hρ₂, hA, hμA, hμ, hν, hrS, hR, h⟩ hb ↦
    ⟨S, ρ₂, r, A, hr, hρ₂, hA, hμA, hμ, hν, hrS, hR, IsGraded.mono hb h⟩
  head_supp := by
    rintro _ _ _ _ _ _ _ _ A' _ hA' hμA' ⟨S, ρ₂, r, A, hr, hρ₂, hA, hμA, hμ, hν, hrS, hR, h⟩
    refine ⟨S, ρ₂, r, A ∩ A', hr, hρ₂, hA.inter hA', ?_, hμ, hν, hrS,
      fun x y hx hxy ↦ ?_, h⟩
    · rw [Set.compl_inter]
      exact measure_union_null hμA hμA'
    · simpa [Set.piecewise_eq_of_mem _ _ _ hx.2] using hR x y hx.1 hxy
  side_supp _ := trivial

end GradedLifting.BindLaw
