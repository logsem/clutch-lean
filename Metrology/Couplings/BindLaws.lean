module

public import Metrology.Couplings.Divergences.DpShapes
public import Metrology.Couplings.Divergences.RenyiAdaptive
public import Metrology.Couplings.Divergences.RenyiFiber
public import Metrology.Couplings.Divergences.Power
public import Metrology.Couplings.Divergences.FillKl

/-! # Adaptive bind laws

Bind laws beyond `BindLaw.canonical`: adaptive DP (`dpRhs`, `dpLhs`), DP choice (`dpChoice`) and
escort-adaptive Rényi (`escort α`), each sound by a codensity lemma (Rocq `instances_dp.v`); the
escort law regraded to power and χ² liftings (`escortPower α`); and the KL chain rule for filled
KL (`fillKl`). -/

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

/-- Right-keyed adaptive DP composition as a bind law (Rocq `GBL_DP_rhs`). No `HeadShift`: adding
`c₂` to `D` would cost `e^{ε₁} c₂`, not `c₂`. -/
noncomputable def dpRhs : BindLaw (codensity dp.{u}) where
  head := DpRhsHead
  side _ _ _ _ _ := True
  sound := by
    classical
    rintro _ _ _ _ _ _ _ _ _ R _ μ ν f g _ _ ⟨ε₁, ε₂, δ₁, D, S, hD, hμ, hν, hS, hR, hb⟩ _ hk
    refine IsLawful.mono (L := codensity dp) ?_ hb le_rfl
    -- `codensity_dp_rhs` leaves `if S x y then (ε₂, D y) else ⊤`: on S this is `R x y`, off S
    -- nothing is owed
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

/-- The right-keyed DP law has no side condition. -/
instance sideFree_dpRhs : (dpRhs.{u}).SideFree :=
  ⟨fun _ _ _ _ _ ↦ trivial⟩

/-- Right-keyed DP heads are diagonal: the step against itself at `(0, 0)`, continuing at the
whole budget. -/
instance headDiag_dpRhs : (dpRhs.{u}).HeadDiag where
  diag μ _ b _ := ⟨0, b.1, 0, fun _ ↦ b.2, (· = ·), measurable_const, inferInstance,
    inferInstance, IsReflexive.refl (L := codensity dp) μ, fun x y h ↦ by subst h; simp,
    by simp [expBudget_zero]⟩
  side_diag _ _ _ _ := trivial

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
    -- as in `dpRhs`, with `D x` for `D y`
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

/-- The left-keyed head shifts: the extra slack `c₂` folds into `D` and costs at most `c₂`, since
`μ` has mass at most one (Rocq `gbl_head_shift`, not proved there for this law). -/
instance headShift_dpLhs : (dpLhs.{u}).HeadShift where
  shift := by
    rintro _ _ _ _ _ ⟨c₁, c₂⟩ _ μ _ _ ⟨ε₁, ε₂, δ₁, D, S, hD, hμ, hν, hS, hR, hb⟩
    refine ⟨ε₁, ε₂ + c₁, δ₁, fun x ↦ D x + c₂, S, hD.add_const _, hμ, hν, hS,
      fun x y h ↦ by simp [hR x y h], ?_⟩
    obtain ⟨hb₁, hb₂⟩ := Prod.mk_le_mk.1 hb
    refine Prod.mk_le_mk.2 ⟨by rw [← add_assoc]; gcongr, ?_⟩
    rw [lintegral_add_right _ measurable_const, lintegral_const, ← add_assoc]
    calc δ₁ + ∫⁻ x, D x ∂μ + c₂ * μ Set.univ ≤ δ₁ + ∫⁻ x, D x ∂μ + c₂ * 1 := by
          gcongr; exact hμ.measure_univ_le_one
      _ ≤ _ := by rw [mul_one]; gcongr

/-- The left-keyed DP law has no side condition. -/
instance sideFree_dpLhs : (dpLhs.{u}).SideFree :=
  ⟨fun _ _ _ _ _ ↦ trivial⟩

/-- Left-keyed DP heads are diagonal: the step against itself at `(0, 0)`, continuing at the
whole budget. -/
instance headDiag_dpLhs : (dpLhs.{u}).HeadDiag where
  diag μ _ b _ := ⟨0, b.1, 0, fun _ ↦ b.2, (· = ·), measurable_const, inferInstance,
    inferInstance, IsReflexive.refl (L := codensity dp) μ, fun x y h ↦ by subst h; simp,
    by simp⟩
  side_diag _ _ _ _ := trivial

/-! ## DP choice -/

/-- The head of the DP choice rule: two DP liftings of the same pair, chosen by a measurable left
predicate `P` that a measurable right set `T` reveals, so each branch pays only its own ε (Rocq
`dp_choice_head`). -/
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
    -- as in `dpRhs`, branch by branch
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

/-- The choice head survives adding a budget to every leftover and to the output (Rocq
`GBL_DP_choice_head_shift`). -/
instance headShift_dpChoice : (dpChoice.{u}).HeadShift where
  shift := by
    rintro _ _ _ _ _ ⟨c₁, c₂⟩ _ _ _ _ ⟨ε₁, δ₁, ε₁', δ₁', ε₂, ε₂', δ₂, S₁, S₂, P, T, hP, hT, hμ, hν,
      h₁, h₂, hPT₁, hPT₂, hR₁, hR₂, hb⟩
    refine ⟨ε₁, δ₁, ε₁', δ₁', ε₂ + c₁, ε₂' + c₁, δ₂ + c₂, S₁, S₂, P, T, hP, hT, hμ, hν, h₁, h₂,
      hPT₁, hPT₂, fun x y hx h ↦ by simp [hR₁ x y hx h], fun x y hx h ↦ by simp [hR₂ x y hx h],
      ?_⟩
    obtain ⟨hb₁, hb₂⟩ := Prod.mk_le_mk.1 hb
    refine Prod.mk_le_mk.2 ⟨?_, by rw [← add_assoc]; gcongr⟩
    rw [← add_assoc, ← add_assoc, max_add_add_right]
    gcongr

/-- The DP choice law has no side condition. -/
instance sideFree_dpChoice : (dpChoice.{u}).SideFree :=
  ⟨fun _ _ _ _ _ ↦ trivial⟩

/-- DP choice heads are diagonal: both branches are the step against itself at `(0, 0)`, with
`P` and `T` everything. -/
instance headDiag_dpChoice : (dpChoice.{u}).HeadDiag where
  diag μ _ b _ := ⟨0, 0, 0, 0, b.1, b.1, b.2, (· = ·), (· = ·), Set.univ, Set.univ,
    .univ, .univ, inferInstance, inferInstance, IsReflexive.refl (L := codensity dp) μ,
    IsReflexive.refl (L := codensity dp) μ, fun _ _ _ _ ↦ trivial, fun _ _ hx ↦ (hx trivial).elim,
    fun x y _ h ↦ by subst h; simp, fun x y _ h ↦ by subst h; simp, by simp⟩
  side_diag _ _ _ _ := trivial

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
    -- hR describes R only on A: zero the left kernel off A (μ Aᶜ = 0, so the bind is unchanged)
    -- and use IsZeroLeft there
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

/-- Escort heads shift: the escort continues at `ρ₂ + c` against the right measure reweighted by
another `e^{-c}`, which costs `c` more. -/
instance headShift_escort (α : ℝ) [hα : Fact (1 < α)] : (escort.{u} α).HeadShift where
  shift := by
    rintro _ _ _ _ _ c _ μ ν hc ⟨S, ρ₂, r, A, hr, hρ₂, hA, hμA, hμ, hν, hrS, hR, h⟩
    refine ⟨S, fun x ↦ ρ₂ x + c, r, A, hr, hρ₂.add_const c, hA, hμA, hμ, hν, hrS,
      fun x y hx hxy ↦ by simp only [hR x y hx hxy], ?_⟩
    have hw : (fun x ↦ (expBudget (ρ₂ x + c))⁻¹) =
        (expBudget c)⁻¹ • fun x ↦ (expBudget (ρ₂ x))⁻¹ := by
      ext x
      rw [expBudget_add, Pi.smul_apply, smul_eq_mul, mul_comm,
        ENNReal.mul_inv (.inl (zero_lt_one.trans_le (one_le_expBudget _)).ne')
        (.inr (zero_lt_one.trans_le (one_le_expBudget _)).ne')]
    rw [hw, withDensity_smul _ (f := fun x ↦ (expBudget (ρ₂ x))⁻¹) (by fun_prop)]
    exact renyiDivergence_smul_inv_expBudget hα.out hc.ne h

/-- The escort law has no side condition. -/
instance sideFree_escort (α : ℝ) [Fact (1 < α)] : (escort.{u} α).SideFree :=
  ⟨fun _ _ _ _ _ ↦ trivial⟩

/-- Escort heads are diagonal on spaces with measurable singletons: the identity witness against
the step reweighted by `e^{-b}`, which costs exactly `b`. Not a `HeadDiag` instance: on a space
whose σ-algebra does not separate points, no witness kernel is carried by the diagonal. -/
theorem escort_head_diag (α : ℝ) [hα : Fact (1 < α)] [MeasurableSingletonClass X]
    (μ : Measure X) [IsSubProbabilityMeasure μ] {b : ℝ≥0∞} (hb : b < ⊤) :
    (escort α).head μ μ (fun x y ↦ relCost (· = ·) x y + b) b := by
  refine ⟨(· = ·), fun _ ↦ b, Kernel.id, Set.univ, inferInstance, measurable_const, .univ,
    by simp, inferInstance, inferInstance, fun y ↦ by simp [Kernel.id_apply, ae_dirac_eq],
    fun x y _ h ↦ by subst h; simp, ?_⟩
  rw [Measure.id_comp, withDensity_const]
  simpa using renyiDivergence_smul_inv_expBudget hα.out hb.ne
    (GradedDivergence.IsReflexive.refl (D := renyiDivergence α) μ)

/-! ## Escort-adaptive power divergences -/

section Power

open PowerBudget

variable (α : ℝ) [hα : Fact (1 < α)]

/-- Escort-adaptive composition for power liftings (χ² at `α = 2`): the escort law read along
`c ↦ log (1 + c) / (α - 1)`. -/
noncomputable def escortPower : BindLaw (powerLifting.{u} α) :=
  (escort α).comap toRenyi_mono toRenyi_top

variable {α}

@[simp]
theorem head_escortPower {b : PowerBudget} {R : X → Y → PowerBudget} {μ : Measure X}
    {ν : Measure Y} : (escortPower α).head μ ν R b ↔
      EscortHead α μ ν (fun x y ↦ toRenyi α (R x y)) (toRenyi α b) :=
  Iff.rfl

variable (α)

/-- Escort power heads shift, since `toRenyi α` is additive. -/
instance headShift_escortPower : (escortPower.{u} α).HeadShift :=
  headShift_comap (law := escort α) (hφ := toRenyi_mono) (htop := toRenyi_top) toRenyi_add
    fun _ ↦ toRenyi_lt_top hα.out

/-- The escort power law has no side condition. -/
instance sideFree_escortPower : (escortPower.{u} α).SideFree :=
  sideFree_comap (law := escort α)

/-- Escort power heads are diagonal on spaces with measurable singletons, as escort heads are
(`escort_head_diag`). -/
theorem escortPower_head_diag [MeasurableSingletonClass X] (μ : Measure X)
    [IsSubProbabilityMeasure μ] {b : PowerBudget} (hb : b < ⊤) :
    (escortPower α).head μ μ (fun x y ↦ relCost (· = ·) x y + b) b := by
  have hrel (x y : X) : toRenyi α (relCost (B := PowerBudget) (· = ·) x y + b) =
      relCost (· = ·) x y + toRenyi α b := by
    rw [toRenyi_add]
    by_cases h : x = y <;> simp [h]
  rw [head_escortPower]
  simp only [hrel]
  exact escort_head_diag α μ (toRenyi_lt_top hα.out hb)

end Power

/-! ## Filled KL, adaptive on the left outcome -/

/-- The head of adaptive filled-KL composition: witnesses `π₁ π₂` on some `Z` with images `μ` and
`ν` along `u` and `v`, within filled KL `ε₁`, whose pairs continue at `D` of the left outcome on a
set `A` carrying `π₁`, paid as `ε₁ + E_μ[D]` (the KL chain rule). -/
def FillKlHead (μ : Measure X) (ν : Measure Y) (R : X → Y → ℝ≥0∞) (b : ℝ≥0∞) : Prop :=
  ∃ (Z : Type u) (_ : MeasurableSpace Z) (π₁ π₂ : Measure Z) (u : Z → X) (v : Z → Y)
    (A : Set Z) (ε₁ : ℝ≥0∞) (D : X → ℝ≥0∞), Measurable u ∧ Measurable v ∧ Measurable D ∧
    MeasurableSet A ∧ π₁ Aᶜ = 0 ∧ IsSubProbabilityMeasure π₁ ∧ IsSubProbabilityMeasure π₂ ∧
    π₁.map u = μ ∧ π₂.map v = ν ∧ fill klDivergence ε₁ π₁ π₂ ∧
    (∀ z ∈ A, R (u z) (v z) = D (u z)) ∧ ε₁ + ∫⁻ x, D x ∂μ ≤ b

/-- Adaptive filled-KL composition as a bind law: the continuation's cost depends on the left
outcome and is paid on average under the left measure, by the KL chain rule
`fill_kl_comp_lintegral`. -/
noncomputable def fillKl : BindLaw (codensity (fill klDivergence.{u})) where
  head := FillKlHead
  side _ _ _ _ _ := True
  sound := by
    classical
    rintro _ _ _ _ _ _ _ _ b R R' _ _ f g _ _ ⟨Z, _, π₁, π₂, u, v, A, ε₁, D, hu, hv, hD, hA, hπA,
      hπ₁, hπ₂, rfl, rfl, hkl, hR, hb⟩ _ hk
    intro I _ c _ k l _ _ hkl'
    -- read the test kernels through the witnesses, zeroing the left one off `A`
    have hK : Kernel.piecewise hA ((k ∘ₖ f).comap u hu) 0 ∘ₘ π₁ = k ∘ₘ (f ∘ₘ π₁.map u) := by
      rw [Measure.piecewise_zero_comp, restrict_eq_self_of_ae_mem (mem_ae_iff.2 hπA),
        Kernel.comap_comp_eq_comp_map, Measure.comp_assoc]
    have hL : (l ∘ₖ g).comap v hv ∘ₘ π₂ = l ∘ₘ (g ∘ₘ π₂.map v) := by
      rw [Kernel.comap_comp_eq_comp_map, Measure.comp_assoc]
    rw [← hK, ← hL]
    refine IsGraded.mono ?_ (fill_kl_comp_lintegral (c := fun z ↦ D (u z) + c) (by fun_prop) hkl
      fun z ↦ ?_)
    · calc ε₁ + ∫⁻ z, D (u z) + c ∂π₁ = ε₁ + (∫⁻ x, D x ∂(π₁.map u) + c * π₁ Set.univ) := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, lintegral_map hD hu]
        _ ≤ ε₁ + (∫⁻ x, D x ∂(π₁.map u) + c) := by
            gcongr
            exact mul_le_of_le_one_right' hπ₁.measure_univ_le_one
        _ ≤ b + c := by
            rw [← add_assoc]
            gcongr
    · by_cases hz : z ∈ A
      · simp only [Kernel.piecewise_apply, hz, ↓reduceIte, Kernel.comap_apply, Kernel.comp_apply]
        refine IsGraded.of_lt_top fun hDc ↦ ?_
        have hRz := hR z hz
        have := hk (u z) (v z) (by rw [hRz]; exact lt_of_le_of_lt le_self_add hDc)
          (by rwa [hRz]) hkl'
        rwa [hRz] at this
      · simp only [Kernel.piecewise_apply, hz, ↓reduceIte, zero_apply]
        exact GradedDivergence.IsZeroLeft.zero_left _ _
  mono_out := fun ⟨Z, mZ, π₁, π₂, u, v, A, ε₁, D, hu, hv, hD, hA, hπA, hπ₁, hπ₂, hμ, hν, hkl, hR,
      hb⟩ hb' ↦
    ⟨Z, mZ, π₁, π₂, u, v, A, ε₁, D, hu, hv, hD, hA, hπA, hπ₁, hπ₂, hμ, hν, hkl, hR, hb.trans hb'⟩
  head_supp := by
    rintro _ _ _ _ _ _ _ _ A' _ hA' hμA' ⟨Z, _, π₁, π₂, u, v, A, ε₁, D, hu, hv, hD, hA, hπA,
      hπ₁, hπ₂, hμ, hν, hkl, hR, hb⟩
    refine ⟨Z, _, π₁, π₂, u, v, A ∩ u ⁻¹' A', ε₁, D, hu, hv, hD, hA.inter (hu hA'), ?_, hπ₁, hπ₂,
      hμ, hν, hkl, fun z hz ↦ ?_, hb⟩
    · rw [Set.compl_inter]
      refine measure_union_null hπA ?_
      rw [← Set.preimage_compl, ← Measure.map_apply hu hA'.compl, hμ]
      exact hμA'
    · simpa [Set.piecewise_eq_of_mem _ _ _ (show u z ∈ A' from hz.2)] using hR z hz.1
  side_supp _ := trivial

/-- Filled-KL heads shift: the extra slack folds into `D` and costs at most itself, since `μ` has
mass at most one. -/
instance headShift_fillKl : (fillKl.{u}).HeadShift where
  shift := by
    rintro _ _ _ _ _ c' _ μ _ _ ⟨Z, _, π₁, π₂, u, v, A, ε₁, D, hu, hv, hD, hA, hπA, hπ₁, hπ₂, hμ,
      hν, hkl, hR, hb⟩
    refine ⟨Z, _, π₁, π₂, u, v, A, ε₁, fun x ↦ D x + c', hu, hv, hD.add_const _, hA, hπA, hπ₁,
      hπ₂, hμ, hν, hkl, fun z hz ↦ by simp [hR z hz], ?_⟩
    have hμ1 : μ Set.univ ≤ 1 := by
      rw [← hμ, Measure.map_apply hu .univ, Set.preimage_univ]
      exact hπ₁.measure_univ_le_one
    rw [lintegral_add_right _ measurable_const, lintegral_const, ← add_assoc]
    calc ε₁ + ∫⁻ x, D x ∂μ + c' * μ Set.univ ≤ ε₁ + ∫⁻ x, D x ∂μ + c' * 1 := by gcongr
      _ ≤ _ := by rw [mul_one]; gcongr

/-- Filled-KL heads are diagonal: the step against itself at `0`, continuing at the whole
budget. -/
instance headDiag_fillKl : (fillKl.{u}).HeadDiag where
  diag {X} _ μ _ b _ := ⟨X, inferInstance, μ, μ, id, id, Set.univ, 0, fun _ ↦ b, measurable_id,
    measurable_id, measurable_const, .univ, by simp, inferInstance, inferInstance, Measure.map_id,
    Measure.map_id, GradedDivergence.IsReflexive.refl _, fun z _ ↦ by simp, by simp⟩
  side_diag _ _ _ _ := trivial

/-- The filled-KL law has no side condition. -/
instance sideFree_fillKl : (fillKl.{u}).SideFree :=
  ⟨fun _ _ _ _ _ ↦ trivial⟩

end GradedLifting.BindLaw

/-! ## Escort heads from finite-output mechanisms -/

namespace GradedDivergence

variable {X Y Z : Type u} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [Fintype Z] [DiscreteMeasurableSpace Z] {f : X → Z} {g : Y → Z} {μ : Measure X}
  {ν : Measure Y} {α : ℝ} {ρ : ℝ≥0∞} [Fact (1 < α)] [IsSubProbabilityMeasure μ]
  [IsSubProbabilityMeasure ν]

/-- A Rényi bound between the images of `μ` and of `ν` reweighted by `e^{-ρ₂}` gives an escort
head relating equal images inside supports `A` and `T`, continuing at `ρ₂` of the image (used by
adaptive randomized response). -/
theorem escortHead_of_map (hf : Measurable f) (hg : Measurable g) {A : Set X} {T : Set Y}
    (hA : MeasurableSet A) (hT : MeasurableSet T) (hμA : μ Aᶜ = 0) (hνT : ν Tᶜ = 0)
    (ρ₂ : Z → ℝ≥0∞) {R : X → Y → ℝ≥0∞}
    (hR : ∀ x y, x ∈ A → y ∈ T → f x = g y → R x y = ρ₂ (f x))
    (h : renyiDivergence α ρ (μ.map f) ((ν.map g).withDensity fun z ↦ (expBudget (ρ₂ z))⁻¹)) :
    BindLaw.EscortHead α μ ν R ρ := by
  classical
  -- the witness kernel sends `y ∈ T` to `μ` conditioned on the fibre `f x = g y`
  refine ⟨fun x y ↦ y ∈ T ∧ f x = g y, fun x ↦ ρ₂ (f x),
    Kernel.piecewise hT ((fiberCond μ f).comap g hg) 0, A, inferInstance, by fun_prop, hA, hμA,
    inferInstance, inferInstance, fun y ↦ ?_, fun x y hx ⟨hy, hxy⟩ ↦ hR x y hx hy hxy, ?_⟩
  · by_cases hy : y ∈ T
    · simpa [Kernel.piecewise_apply, hy, fiberCond_apply] using
        ae_cond_mem (μ := μ) (hf (measurableSet_singleton (g y)))
    · simp [Kernel.piecewise_apply, hy]
  -- the witness applied to `ν` is the fibre conditional applied to the reweighted image of `ν`,
  -- so composing the image bound `h` with the fibre conditional gives the bound on `X`
  · rw [Measure.piecewise_zero_comp, restrict_eq_self_of_ae_mem (mem_ae_iff.2 hνT),
      Kernel.comap_comp_eq_comp_map _ hg,
      fiberCond_comp_withDensity hf (w := fun z ↦ (expBudget (ρ₂ z))⁻¹)]
    have := IsComposable.comp_self (fiberCond μ f) h
    rwa [fiberCond_comp_map hf] at this

/-- A filled-KL bound between the images of `μ` and `ν` gives a chain-rule head relating equal
images inside supports `A` and `T`, continuing at `ρ₂` of the image, when `μ` and `ν` charge the
same images (used by adaptive randomized response). -/
theorem fillKlHead_of_map (hf : Measurable f) (hg : Measurable g) {A : Set X} {T : Set Y}
    (hA : MeasurableSet A) (hT : MeasurableSet T) (hμA : μ Aᶜ = 0) (hνT : ν Tᶜ = 0)
    (hfib : ∀ z, μ (f ⁻¹' {z}) = 0 ↔ ν (g ⁻¹' {z}) = 0) (ρ₂ : Z → ℝ≥0∞) {R : X → Y → ℝ≥0∞}
    (hR : ∀ x y, x ∈ A → y ∈ T → f x = g y → R x y = ρ₂ (f x)) {ε b : ℝ≥0∞}
    (h : fill klDivergence ε (μ.map f) (ν.map g)) (hb : ε + ∫⁻ z, ρ₂ z ∂μ.map f ≤ b) :
    BindLaw.fillKl.head μ ν R b := by
  classical
  -- the witnesses recombine the products of the two fibers along each image
  let J : Kernel Z (X × Y) := ⟨fun z ↦ (fiberCond μ f z).prod (fiberCond ν g z), .of_discrete⟩
  have hJ (z : Z) : J z = (fiberCond μ f z).prod (fiberCond ν g z) := rfl
  have : IsSubMarkovKernel J := ⟨fun z ↦ by rw [hJ]; infer_instance⟩
  set S : Set (X × Y) := (A ×ˢ T) ∩ {p | f p.1 = g p.2}
  have hS : MeasurableSet S := (hA.prod hT).inter
    (measurableSet_eq_fun (hf.comp measurable_fst) (hg.comp measurable_snd))
  -- each product of fibers lies on equal images inside the supports
  have hJS (z : Z) : J z Sᶜ = 0 := by
    refine mem_ae_iff.1 ?_
    change ∀ᵐ p ∂(fiberCond μ f z).prod (fiberCond ν g z), p ∈ S
    rw [Measure.ae_prod_mem_iff_ae_ae_mem hS, fiberCond_apply, fiberCond_apply]
    filter_upwards [ae_cond_mem (hf (measurableSet_singleton z)),
      cond_absolutelyContinuous.ae_le (mem_ae_iff.2 hμA)] with x hx hxA
    filter_upwards [ae_cond_mem (hg (measurableSet_singleton z)),
      cond_absolutelyContinuous.ae_le (mem_ae_iff.2 hνT)] with y hy hyT
    exact ⟨⟨hxA, hyT⟩, (Set.mem_singleton_iff.1 hx).trans (Set.mem_singleton_iff.1 hy).symm⟩
  -- on images charged by both measures each fiber is a probability measure, so the marginals
  -- recombine to `μ` and `ν`
  have h₁ : (J ∘ₘ μ.map f).map Prod.fst = μ := by
    rw [Measure.map_comp _ _ measurable_fst]
    conv_rhs => rw [← fiberCond_comp_map hf (μ := μ)]
    refine Measure.comp_congr (ae_iff_of_countable.2 fun z hz ↦ ?_)
    have hν : ν (g ⁻¹' {z}) ≠ 0 := fun h0 ↦
      hz (by rw [map_apply hf (measurableSet_singleton z)]; exact (hfib z).2 h0)
    have := cond_isProbabilityMeasure hν
    rw [Kernel.map_apply _ measurable_fst, hJ, fiberCond_apply, fiberCond_apply,
      Measure.map_fst_prod, measure_univ, one_smul]
  have h₂ : (J ∘ₘ ν.map g).map Prod.snd = ν := by
    rw [Measure.map_comp _ _ measurable_snd]
    conv_rhs => rw [← fiberCond_comp_map hg (μ := ν)]
    refine Measure.comp_congr (ae_iff_of_countable.2 fun z hz ↦ ?_)
    have hμ : μ (f ⁻¹' {z}) ≠ 0 := fun h0 ↦
      hz (by rw [map_apply hg (measurableSet_singleton z)]; exact (hfib z).1 h0)
    have := cond_isProbabilityMeasure hμ
    rw [Kernel.map_apply _ measurable_snd, hJ, fiberCond_apply, fiberCond_apply,
      Measure.map_snd_prod, measure_univ, one_smul]
  refine ⟨X × Y, inferInstance, J ∘ₘ μ.map f, J ∘ₘ ν.map g, Prod.fst, Prod.snd, S, ε,
    fun x ↦ ρ₂ (f x), measurable_fst, measurable_snd, Measurable.of_discrete.comp hf, hS, ?_,
    inferInstance, inferInstance, h₁, h₂, IsComposable.comp_self J h,
    fun p hp ↦ hR p.1 p.2 hp.1.1 hp.1.2 hp.2, ?_⟩
  · rw [Measure.bind_apply hS.compl (Kernel.aemeasurable _)]
    simp [hJS]
  · rwa [lintegral_map .of_discrete hf] at hb

end GradedDivergence
