module

public import Metrology.Couplings.Divergences.RenyiCurve
public import Metrology.Couplings.LiftingHom

/-! # zCDP and tCDP

Rényi curves read along the lines `α ↦ ξ + α ρ`, giving `zcdpDivergence` and `tcdpDivergence`
(Approximate Span Liftings, §4), their liftings, and the homomorphisms to each Rényi order. -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory GradedLifting Set
open scoped ENNReal

namespace GradedDivergence

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]

/-! ## Lines -/

theorem ofReal_ioi_ne_zero (α : Ioi (1 : ℝ)) : ENNReal.ofReal α ≠ 0 :=
  (ENNReal.ofReal_pos.2 (zero_lt_one.trans α.2)).ne'

section Line

variable (A : Set ℝ)

open Classical in
/-- The line `α ↦ ξ + α ρ` on the orders in `A`, `⊤` off `A` (Rocq `zcdp_line`, `tcdp_line`). -/
noncomputable def concentratedLine (b : ℝ≥0∞ × ℝ≥0∞) : RenyiBudget :=
  fun α ↦ if (α : ℝ) ∈ A then b.1 + ENNReal.ofReal α * b.2 else ⊤

/-- Lines add (Rocq `zcdp_line_add`, `tcdp_line_add`). -/
theorem concentratedLine_add (b c : ℝ≥0∞ × ℝ≥0∞) :
    concentratedLine A (b + c) = concentratedLine A b + concentratedLine A c := by
  ext α
  by_cases hα : (α : ℝ) ∈ A <;> simp [concentratedLine, hα, mul_add, add_add_add_comm]

@[simp]
theorem concentratedLine_of_mem {b : ℝ≥0∞ × ℝ≥0∞} {α : Ioi (1 : ℝ)} (hα : (α : ℝ) ∈ A) :
    concentratedLine A b α = b.1 + ENNReal.ofReal α * b.2 := by
  simp [concentratedLine, hα]

@[simp]
theorem concentratedLine_of_notMem {b : ℝ≥0∞ × ℝ≥0∞} {α : Ioi (1 : ℝ)} (hα : (α : ℝ) ∉ A) :
    concentratedLine A b α = ⊤ := by
  simp [concentratedLine, hα]

theorem concentratedLine_mono : Monotone (concentratedLine A) := fun b c h α ↦ by
  by_cases hα : (α : ℝ) ∈ A
  · simpa [concentratedLine, hα] using add_le_add h.1 (mul_le_mul_right h.2 _)
  · simp [concentratedLine, hα]

theorem concentratedLine_fst_top (ρ : ℝ≥0∞) : concentratedLine A (⊤, ρ) = ⊤ := by
  ext α
  by_cases hα : (α : ℝ) ∈ A <;> simp [concentratedLine, hα]

theorem concentratedLine_snd_top (ξ : ℝ≥0∞) : concentratedLine A (ξ, ⊤) = ⊤ := by
  ext α
  simp [concentratedLine, ENNReal.mul_top (ofReal_ioi_ne_zero α)]

theorem concentratedLine_top : concentratedLine A ⊤ = ⊤ :=
  concentratedLine_snd_top A ⊤

/-- A zCDP line lies below the tCDP line of the summed budget (Rocq `zcdp_line_le_tcdp`). -/
theorem concentratedLine_ioi_le_ioo {ω : ℝ} (b : ℝ≥0∞ × ℝ≥0∞) :
    concentratedLine (Ioi 1) b ≤ concentratedLine (Ioo 1 ω) (0, b.1 + b.2) := fun α ↦ by
  by_cases hα : (α : ℝ) ∈ Ioo 1 ω
  · have h1 : 1 ≤ ENNReal.ofReal α := by simpa using α.2.le
    simp only [concentratedLine_of_mem _ hα, concentratedLine_of_mem _ α.2, zero_add, mul_add]
    exact add_le_add (le_mul_of_one_le_left zero_le h1) le_rfl
  · simp [hα]

end Line

/-! ## Concentrated divergences -/

/-- Rényi bounds `ξ + α ρ` at the orders `α ∈ A` (Eqs. 6 and 7). -/
noncomputable def concentratedDivergence (A : Set ℝ) : GradedDivergence.{u} (ℝ≥0∞ × ℝ≥0∞) :=
  renyiCurve.comap (concentratedLine A)

/-- `(ξ, ρ)`-zCDP: Rényi bounds `ξ + α ρ` at every order (Eq. 6). -/
noncomputable abbrev zcdpDivergence : GradedDivergence.{u} (ℝ≥0∞ × ℝ≥0∞) :=
  concentratedDivergence (Ioi 1)

/-- `(ρ, ω)`-tCDP: Rényi bounds `α ρ` at the orders `1 < α < ω` (Eq. 7). -/
-- a `def`: `Prod.mk 0` sends `⊤` to `(0, ⊤) ≠ ⊤`, so the generic `comap` instances do not fire; the
-- tCDP instances below use that the line at `(0, ⊤)` is still `⊤`.
noncomputable def tcdpDivergence (ω : ℝ) : GradedDivergence.{u} ℝ≥0∞ :=
  (concentratedDivergence (Ioo 1 ω)).comap (Prod.mk 0)

variable {A : Set ℝ} {b : ℝ≥0∞ × ℝ≥0∞} {ξ ρ : ℝ≥0∞} {ω : ℝ} {μ ν : Measure X}

/-- A Rényi bound at every order in `A` gives the concentrated bound. -/
theorem concentratedDivergence_of_forall
    (h : ∀ α : Ioi (1 : ℝ), (α : ℝ) ∈ A → renyiDivergence α (b.1 + ENNReal.ofReal α * b.2) μ ν) :
    concentratedDivergence A b μ ν := fun α ↦ by
  by_cases hα : (α : ℝ) ∈ A
  · simpa [concentratedLine, hα] using h α hα
  · simpa [concentratedLine, hα] using renyiDivergence_top α.2 μ ν

/-- The concentrated bound is a Rényi bound at every order in `A` (as a subtype of `(1, ∞)`). -/
theorem concentratedDivergence_iff :
    concentratedDivergence A b μ ν ↔
      ∀ α : Ioi (1 : ℝ), (α : ℝ) ∈ A → renyiDivergence α (b.1 + ENNReal.ofReal α * b.2) μ ν :=
  ⟨fun h α hα ↦ by simpa [hα] using h α, concentratedDivergence_of_forall⟩

/-- Same as `concentratedDivergence_iff` with real orders, when `A ⊆ (1, ∞)`. -/
theorem concentratedDivergence_iff' (hA : A ⊆ Ioi 1) :
    concentratedDivergence A (ξ, ρ) μ ν ↔
      ∀ α ∈ A, renyiDivergence α (ξ + ENNReal.ofReal α * ρ) μ ν :=
  concentratedDivergence_iff.trans ⟨fun h α hα ↦ h ⟨α, hA hα⟩ hα, fun h α hα ↦ h α hα⟩

/-- zCDP is a Rényi bound `ξ + α ρ` at every real order `α > 1`. -/
theorem zcdpDivergence_iff :
    zcdpDivergence (ξ, ρ) μ ν ↔ ∀ α, 1 < α → renyiDivergence α (ξ + ENNReal.ofReal α * ρ) μ ν :=
  concentratedDivergence_iff' subset_rfl

/-- tCDP is a Rényi bound `α ρ` at every real order `1 < α < ω`. -/
theorem tcdpDivergence_iff :
    tcdpDivergence ω ρ μ ν ↔ ∀ α, 1 < α → α < ω → renyiDivergence α (ENNReal.ofReal α * ρ) μ ν :=
  (concentratedDivergence_iff' Ioo_subset_Ioi_self).trans (by simp [and_imp])

/-! ## Divergence laws -/

variable (A ω)

/-- Concentrated divergences are graded, since lines are monotone and keep `⊤`. -/
instance isGraded_concentrated : (concentratedDivergence.{u} A).IsGraded :=
  isGraded_comap_of_map_top (concentratedLine_mono A) (concentratedLine_top A)

/-- Concentrated divergences are reflexive: every line is above `0`. -/
instance isReflexive_concentrated : (concentratedDivergence.{u} A).IsReflexive :=
  isReflexive_comap zero_le

/-- Concentrated budgets add, since lines do (Thms. 4.12 and 4.13). -/
instance isComposable_concentrated : (concentratedDivergence.{u} A).IsComposable :=
  isComposable_comap fun b c ↦ (concentratedLine_add A b c).ge

/-- The zero measure is within every concentrated budget of every measure. -/
instance isZeroLeft_concentrated : (concentratedDivergence.{u} A).IsZeroLeft :=
  GradedDivergence.isZeroLeft_comap

/-- Concentrated divergences are left continuous. -/
instance isLeftContinuous_concentrated : (concentratedDivergence.{u} A).IsLeftContinuous :=
  GradedDivergence.isLeftContinuous_comap

/-- Concentrated divergences are monotone in the right measure. -/
instance isRightMonotone_concentrated : (concentratedDivergence.{u} A).IsRightMonotone :=
  GradedDivergence.isRightMonotone_comap

/-- Concentrated divergences are antitone in the left measure. -/
instance isLeftAntitone_concentrated : (concentratedDivergence.{u} A).IsLeftAntitone :=
  GradedDivergence.isLeftAntitone_comap

/-- A bound at every larger budget is one at the budget: raise the shift `ξ`. -/
instance isBudgetClosed_concentrated : (concentratedDivergence.{u} A).IsBudgetClosed where
  of_forall_gt {b} := fun h ↦ concentratedDivergence_of_forall fun α hα ↦
    IsBudgetClosed.of_forall_gt fun t ht ↦ by
      obtain ⟨ξ', hξ', rfl⟩ := exists_lt_and_add_eq_of_add_lt ht
      simpa [hα] using h (ξ', b.2) (Prod.mk_lt_mk_iff_left.2 hξ') α

/-- tCDP divergences are graded: the line at `(0, ⊤)` is `⊤`. -/
instance isGraded_tcdp : (tcdpDivergence.{u} ω).IsGraded :=
  isGraded_comap (fun _ _ h ↦ Prod.mk_le_mk.2 ⟨le_rfl, h⟩) fun μ ν _ _ ↦ by
    simpa [tcdpDivergence, concentratedDivergence, comap_def, concentratedLine_snd_top] using
      IsGraded.top μ ν

/-- tCDP divergences are reflexive. -/
instance isReflexive_tcdp : (tcdpDivergence.{u} ω).IsReflexive :=
  isReflexive_comap le_rfl

/-- tCDP budgets add (Thm. 4.13). -/
instance isComposable_tcdp : (tcdpDivergence.{u} ω).IsComposable :=
  isComposable_comap fun _ _ ↦ by simp

/-- The zero measure is within every tCDP budget of every measure. -/
instance isZeroLeft_tcdp : (tcdpDivergence.{u} ω).IsZeroLeft :=
  GradedDivergence.isZeroLeft_comap

/-- tCDP divergences are left continuous. -/
instance isLeftContinuous_tcdp : (tcdpDivergence.{u} ω).IsLeftContinuous :=
  GradedDivergence.isLeftContinuous_comap

/-- tCDP divergences are monotone in the right measure. -/
instance isRightMonotone_tcdp : (tcdpDivergence.{u} ω).IsRightMonotone :=
  GradedDivergence.isRightMonotone_comap

/-- tCDP divergences are antitone in the left measure. -/
instance isLeftAntitone_tcdp : (tcdpDivergence.{u} ω).IsLeftAntitone :=
  GradedDivergence.isLeftAntitone_comap

/-- A value above `α ρ` is `α ρ'` for some `ρ' > ρ` (for budget closedness of tCDP). -/
theorem exists_lt_and_ofReal_mul_eq_of_mul_lt {α : Ioi (1 : ℝ)} {ρ t : ℝ≥0∞}
    (h : ENNReal.ofReal α * ρ < t) : ∃ ρ', ρ < ρ' ∧ ENNReal.ofReal α * ρ' = t := by
  have h0 := ofReal_ioi_ne_zero α
  refine ⟨t / ENNReal.ofReal α, ?_, ENNReal.mul_div_cancel h0 ENNReal.ofReal_ne_top⟩
  rwa [ENNReal.lt_div_iff_mul_lt (.inl h0) (.inl ENNReal.ofReal_ne_top), mul_comm]

/-- A bound at every larger budget is one at the budget: at order `α`, `ρ' = t / α`. -/
instance isBudgetClosed_tcdp : (tcdpDivergence.{u} ω).IsBudgetClosed where
  of_forall_gt {ρ} := fun h ↦ concentratedDivergence_of_forall fun α hα ↦
    IsBudgetClosed.of_forall_gt fun t ht ↦ by
      obtain ⟨ρ', hρ, rfl⟩ := exists_lt_and_ofReal_mul_eq_of_mul_lt (by simpa [hα] using ht)
      simpa [hα] using h ρ' hρ α

/-! ## Concentrated liftings -/

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- Both components of `relCost` are `0` or `⊤`, so a line through it is `relCost` again. -/
@[simp]
theorem relCost_fst_add_mul_snd {S : X → Y → Prop} {x : X} {y : Y} (c : ℝ≥0∞) :
    (relCost S x y : ℝ≥0∞ × ℝ≥0∞).1 + c * (relCost S x y : ℝ≥0∞ × ℝ≥0∞).2 = relCost S x y := by
  by_cases hS : S x y <;> simp [hS]

/-- The Rényi-curve lifting read along the lines, so that every order is a homomorphic image
(Rocq `GCF_zCDP`, `GCF_tCDP`). -/
noncomputable def concentratedLifting : GradedLifting.{u} (ℝ≥0∞ × ℝ≥0∞) :=
  (codensity renyiCurve).comap (concentratedLine A)

/-- The zCDP lifting: Rényi liftings along `ξ + α ρ` at every order. -/
noncomputable abbrev zcdpLifting : GradedLifting.{u} (ℝ≥0∞ × ℝ≥0∞) :=
  concentratedLifting (Ioi 1)

/-- The tCDP lifting: Rényi liftings along `α ρ` at the orders `1 < α < ω`. -/
noncomputable def tcdpLifting : GradedLifting.{u} ℝ≥0∞ :=
  (concentratedLifting (Ioo 1 ω)).comap (Prod.mk 0)

variable {A ω} {R : X → Y → ℝ≥0∞ × ℝ≥0∞} {S : X → Y → Prop} {ν : Measure Y}

/-- A concentrated lifting is a Rényi lifting along the line at every order of `A` (Rocq
`gcf_zCDP_iff`). -/
theorem concentratedLifting_iff :
    concentratedLifting A b R μ ν ↔ ∀ α : Ioi (1 : ℝ), (α : ℝ) ∈ A →
      (renyiDivergence α).codensity (b.1 + ENNReal.ofReal α * b.2)
        (fun x y ↦ (R x y).1 + ENNReal.ofReal α * (R x y).2) μ ν := by
  refine codensity_renyiCurve_iff.trans ⟨fun h α hα ↦ by simpa [hα] using h α, fun h α ↦ ?_⟩
  by_cases hα : (α : ℝ) ∈ A
  · simpa [hα] using h α hα
  · intro I _ c hc
    simp [hα] at hc

/-- A concentrated relational lifting is a Rényi one along the line at every order of `A` (Rocq
`gcf_zCDP_iff`). -/
theorem concentratedLifting_rel_iff :
    (concentratedLifting A).Rel b S μ ν ↔ ∀ α : Ioi (1 : ℝ), (α : ℝ) ∈ A →
      (codensity (renyiDivergence α)).Rel (b.1 + ENNReal.ofReal α * b.2) S μ ν := by
  simp only [GradedLifting.Rel, concentratedLifting_iff, relCost_fst_add_mul_snd]

/-- A tCDP lifting is a Rényi lifting along `α ρ` at every order below `ω` (Rocq
`gcf_tCDP_iff`). -/
theorem tcdpLifting_iff {R : X → Y → ℝ≥0∞} :
    tcdpLifting ω ρ R μ ν ↔ ∀ α : Ioi (1 : ℝ), (α : ℝ) < ω →
      (renyiDivergence α).codensity (ENNReal.ofReal α * ρ)
        (fun x y ↦ ENNReal.ofReal α * R x y) μ ν :=
  concentratedLifting_iff.trans <| forall_congr' fun α ↦ by simp [α.2.out]

/-- A tCDP relational lifting is a Rényi one along `α ρ` at every order below `ω` (Rocq
`gcf_tCDP_iff`). -/
theorem tcdpLifting_rel_iff :
    (tcdpLifting ω).Rel ρ S μ ν ↔ ∀ α : Ioi (1 : ℝ), (α : ℝ) < ω →
      (codensity (renyiDivergence α)).Rel (ENNReal.ofReal α * ρ) S μ ν := by
  refine tcdpLifting_iff.trans (forall₂_congr fun α _ ↦ ?_)
  have : (fun x y ↦ ENNReal.ofReal α * relCost S x y) = relCost S := by
    ext x y
    by_cases hS : S x y <;> simp [hS, ENNReal.mul_top (ofReal_ioi_ne_zero α)]
  rw [this, GradedLifting.Rel]

/-- A tCDP lifting is a codensity lifting of the tCDP divergence. -/
theorem codensity_tcdp_of_tcdpLifting [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    {R : X → Y → ℝ≥0∞} (h : tcdpLifting ω ρ R μ ν) : (tcdpDivergence ω).codensity ρ R μ ν :=
  comap_codensity_le (φ := fun c ↦ concentratedLine (Ioo 1 ω) (0, c))
    (fun _ _ ↦ by rw [← concentratedLine_add]; simp) h

variable (A ω)

/-- Concentrated liftings are lawful; `(⊤, 0) < ⊤` has line `⊤`, so `isLawful_comap` does not
apply and top-absorption of codensity is used instead. -/
instance isLawful_concentratedLifting : (concentratedLifting.{u} A).IsLawful :=
  isLawful_comap_codensity (concentratedLine_mono A) (concentratedLine_add A)

/-- Concentrated liftings bind, since lines keep `⊤`. -/
instance hasBind_concentratedLifting : (concentratedLifting.{u} A).HasBind :=
  hasBind_comap (concentratedLine_top A)

/-- Concentrated liftings are reflexive: off `A` every order is at `⊤`, on `A` the line at `0`
is `0`. -/
instance isReflexive_concentratedLifting : (concentratedLifting.{u} A).IsReflexive where
  refl μ _ := concentratedLifting_rel_iff.2 fun α _ ↦ by
    simpa using GradedLifting.IsReflexive.refl μ

/-- The zero measure on the left lifts against everything. -/
instance isZeroLeft_concentratedLifting : (concentratedLifting.{u} A).IsZeroLeft :=
  GradedLifting.isZeroLeft_comap

/-- Concentrated liftings are left continuous. -/
instance isLeftContinuous_concentratedLifting : (concentratedLifting.{u} A).IsLeftContinuous :=
  GradedLifting.isLeftContinuous_comap

/-- Concentrated liftings are support local, since lines keep `⊤`. -/
instance isSupportLocal_concentratedLifting : (concentratedLifting.{u} A).IsSupportLocal :=
  isSupportLocal_comap (concentratedLine_top A)

/-- Concentrated liftings relate everything at `⊤`. -/
instance isTopAbsorbing_concentratedLifting : (concentratedLifting.{u} A).IsTopAbsorbing :=
  isTopAbsorbing_comap (concentratedLine_top A)

/-- A concentrated lifting of equality gives the concentrated divergence. -/
instance isSound_concentratedLifting :
    (concentratedLifting.{u} A).IsSound (concentratedDivergence A) where
  sound h := codensity_sound (comap_codensity_le (concentratedLine_add A) h)

/-- The concentrated divergence gives a concentrated lifting of equality, order by order. -/
instance isComplete_concentratedLifting :
    (concentratedLifting.{u} A).IsComplete (concentratedDivergence A) where
  complete h := concentratedLifting_rel_iff.2 fun α hα ↦
    codensity_complete (concentratedDivergence_iff.1 h α hα)

/-- A lifting at every larger budget is one at the budget: raise the shift `ξ`. -/
instance isBudgetClosed_concentratedLifting : (concentratedLifting.{u} A).IsBudgetClosed where
  of_forall_gt {_ _} _ _ b := fun h ↦ concentratedLifting_iff.2 fun α hα ↦
    GradedLifting.IsBudgetClosed.of_forall_gt fun t ht ↦ by
      obtain ⟨ξ', hξ', rfl⟩ := exists_lt_and_add_eq_of_add_lt ht
      exact concentratedLifting_iff.1 (h (ξ', b.2) (Prod.mk_lt_mk_iff_left.2 hξ')) α hα

/-- A budget with an infinite shift is absorbing: its line is `⊤`. -/
theorem absorbing_concentratedLifting_fst_top (ρ : ℝ≥0∞) :
    (concentratedLifting.{u} A).Absorbing (⊤, ρ) :=
  absorbing_comap (concentratedLine_fst_top A ρ)

/-- tCDP liftings are lawful although `(0, ⊤)` is below `⊤`. -/
instance isLawful_tcdpLifting : (tcdpLifting.{u} ω).IsLawful :=
  isLawful_comap_of_top (fun _ _ ↦ Prod.mk_le_mk_iff_right.2) fun _ _ ↦ by simp

/-- tCDP liftings bind, since the line at `(0, ⊤)` is `⊤`. -/
instance hasBind_tcdpLifting : (tcdpLifting.{u} ω).HasBind :=
  hasBind_comap (L := codensity renyiCurve) (concentratedLine_snd_top _ 0)

/-- tCDP liftings are reflexive: frame by the finite budget `(0, 0)`. -/
instance isReflexive_tcdpLifting : (tcdpLifting.{u} ω).IsReflexive :=
  isReflexive_comap_of_lt_top bot_lt_top

/-- The zero measure on the left lifts against everything. -/
instance isZeroLeft_tcdpLifting : (tcdpLifting.{u} ω).IsZeroLeft :=
  GradedLifting.isZeroLeft_comap

/-- tCDP liftings are left continuous. -/
instance isLeftContinuous_tcdpLifting : (tcdpLifting.{u} ω).IsLeftContinuous :=
  GradedLifting.isLeftContinuous_comap

/-- tCDP liftings are support local, since the line at `(0, ⊤)` is `⊤`. -/
instance isSupportLocal_tcdpLifting : (tcdpLifting.{u} ω).IsSupportLocal :=
  isSupportLocal_comap (L := codensity renyiCurve) (concentratedLine_snd_top _ 0)

/-- tCDP liftings relate everything at `⊤`. -/
instance isTopAbsorbing_tcdpLifting : (tcdpLifting.{u} ω).IsTopAbsorbing :=
  isTopAbsorbing_comap (L := codensity renyiCurve) (concentratedLine_snd_top _ 0)

/-- A tCDP lifting of equality gives the tCDP divergence. -/
instance isSound_tcdpLifting : (tcdpLifting.{u} ω).IsSound (tcdpDivergence ω) where
  sound h := codensity_sound (codensity_tcdp_of_tcdpLifting h)

/-- The tCDP divergence gives a tCDP lifting of equality, order by order. -/
instance isComplete_tcdpLifting : (tcdpLifting.{u} ω).IsComplete (tcdpDivergence ω) where
  complete h := tcdpLifting_rel_iff.2 fun α hα ↦
    codensity_complete (tcdpDivergence_iff.1 h α α.2 hα)

/-- A lifting at every larger budget is one at the budget: at order `α`, `ρ' = t / α`. -/
instance isBudgetClosed_tcdpLifting : (tcdpLifting.{u} ω).IsBudgetClosed where
  of_forall_gt {_ _} _ _ ρ := fun h ↦ tcdpLifting_iff.2 fun α hα ↦
    GradedLifting.IsBudgetClosed.of_forall_gt fun t ht ↦ by
      obtain ⟨ρ', hρ, rfl⟩ := exists_lt_and_ofReal_mul_eq_of_mul_lt ht
      exact tcdpLifting_iff.1 (h ρ' hρ) α hα

variable {A ω}

/-- A concentrated lifting of equality gives the concentrated divergence. -/
theorem concentratedLifting_sound {μ ν : Measure X} [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] (h : (concentratedLifting A).Rel b (· = ·) μ ν) :
    concentratedDivergence A b μ ν :=
  IsSound.sound (D := concentratedDivergence A) h

/-- The concentrated divergence gives a concentrated lifting of equality. -/
theorem concentratedLifting_complete {μ ν : Measure X} [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] (h : concentratedDivergence A b μ ν) :
    (concentratedLifting A).Rel b (· = ·) μ ν :=
  IsComplete.complete h

/-- A tCDP lifting of equality gives the tCDP divergence. -/
theorem tcdpLifting_sound {μ ν : Measure X} [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] (h : (tcdpLifting ω).Rel ρ (· = ·) μ ν) :
    tcdpDivergence ω ρ μ ν :=
  IsSound.sound (D := tcdpDivergence ω) h

/-- The tCDP divergence gives a tCDP lifting of equality. -/
theorem tcdpLifting_complete {μ ν : Measure X} [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] (h : tcdpDivergence ω ρ μ ν) :
    (tcdpLifting ω).Rel ρ (· = ·) μ ν :=
  IsComplete.complete h

/-! ## Codensity of the concentrated divergence -/

/-- Rényi liftings along the line at every order of `A` give a codensity lifting of the divergence
(Rocq `gcf_zCDP_iff`, `gcf_tCDP_iff`, one direction). -/
theorem codensity_concentrated_of_forall [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    (h : ∀ α ∈ A, (renyiDivergence α).codensity (b.1 + ENNReal.ofReal α * b.2)
      (fun x y ↦ (R x y).1 + ENNReal.ofReal α * (R x y).2) μ ν) :
    (concentratedDivergence A).codensity b R μ ν :=
  comap_codensity_le (concentratedLine_add A) (concentratedLifting_iff.2 fun α hα ↦ h α hα)

/-- A relational concentrated bound follows from a codensity Rényi bound at every order in `A`. -/
theorem codensity_concentrated_rel_of_forall [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν]
    (h : ∀ α ∈ A, (codensity (renyiDivergence α)).Rel (ξ + ENNReal.ofReal α * ρ) S μ ν) :
    (codensity (concentratedDivergence A)).Rel (ξ, ρ) S μ ν :=
  codensity_concentrated_of_forall fun α hα ↦ by
    simp only [relCost_fst_add_mul_snd]
    exact h α hα

end GradedDivergence

/-! ## Homomorphisms out of concentrated liftings -/

open GradedDivergence

namespace LiftingHom

variable (A : Set ℝ) (ω : ℝ)

/-- A Rényi-curve lifting is a Rényi lifting at each order. -/
noncomputable def renyiCurveToRenyi (α : Ioi (1 : ℝ)) :
    LiftingHom (codensity renyiCurve.{u}) (codensity (renyiDivergence.{u} α)) where
  map ρ := ρ α
  mono _ _ h := h α
  map_lift h := codensity_renyiCurve_iff.1 h α

/-- A concentrated lifting is a Rényi-curve lifting along the line (Rocq `CM_zCDP_curve`). -/
noncomputable def concentratedToRenyiCurve :
    LiftingHom (concentratedLifting.{u} A) (codensity renyiCurve.{u}) :=
  comapHom (concentratedLine_mono A)

/-- A tCDP lifting is a Rényi-curve lifting along the line (Rocq `CM_tCDP_curve`). -/
noncomputable def tcdpToRenyiCurve : LiftingHom (tcdpLifting.{u} ω) (codensity renyiCurve.{u}) :=
  (concentratedToRenyiCurve _).comp (comapHom fun _ _ ↦ Prod.mk_le_mk_iff_right.2)

/-- A concentrated lifting is a Rényi lifting at each order (Rocq `CM_zCDP_RDP`). -/
noncomputable def concentratedToRenyi (α : Ioi (1 : ℝ)) :
    LiftingHom (concentratedLifting.{u} A) (codensity (renyiDivergence.{u} α)) :=
  (renyiCurveToRenyi α).comp (concentratedToRenyiCurve A)

/-- A tCDP lifting is a Rényi lifting at each order, along `α ρ` below `ω` and `⊤` above
(Rocq `CM_tCDP_RDP`). -/
noncomputable def tcdpToRenyi (α : Ioi (1 : ℝ)) :
    LiftingHom (tcdpLifting.{u} ω) (codensity (renyiDivergence.{u} α)) :=
  (renyiCurveToRenyi α).comp (tcdpToRenyiCurve ω)

/-- A concentrated lifting is a codensity lifting of the concentrated divergence. -/
noncomputable def concentratedToCodensity :
    LiftingHom (concentratedLifting.{u} A) (codensity (concentratedDivergence.{u} A)) where
  map b := b
  mono := monotone_id
  map_lift := comap_codensity_le (concentratedLine_add A)

@[simp]
theorem concentratedToCodensity_map (b : ℝ≥0∞ × ℝ≥0∞) :
    (concentratedToCodensity.{u} A).map b = b :=
  rfl

/-- A tCDP lifting is a codensity lifting of the tCDP divergence. -/
noncomputable def tcdpToCodensity :
    LiftingHom (tcdpLifting.{u} ω) (codensity (tcdpDivergence.{u} ω)) where
  map b := b
  mono := monotone_id
  map_lift := codensity_tcdp_of_tcdpLifting

@[simp]
theorem tcdpToCodensity_map (ρ : ℝ≥0∞) : (tcdpToCodensity.{u} ω).map ρ = ρ :=
  rfl

end LiftingHom

namespace LiftingRelHom

/-- A zCDP relational lifting at `(ξ, ρ)` is a tCDP one at `ξ + ρ`, for every `ω`
(Rocq `CM_zCDP_tCDP`). -/
noncomputable def zcdpToTcdp (ω : ℝ) : LiftingRelHom zcdpLifting.{u} (tcdpLifting.{u} ω) where
  map b := b.1 + b.2
  mono _ _ h := add_le_add h.1 h.2
  map_rel {_ _} _ _ b := fun h ↦ tcdpLifting_rel_iff.2 fun α hα ↦
    (concentratedLifting_rel_iff.1 h α α.2).mono
      (by simpa [α.2.out, hα] using concentratedLine_ioi_le_ioo (ω := ω) b α) fun _ _ h ↦ h

@[simp]
theorem zcdpToTcdp_map (ω : ℝ) (b : ℝ≥0∞ × ℝ≥0∞) : (zcdpToTcdp.{u} ω).map b = b.1 + b.2 :=
  rfl

end LiftingRelHom
