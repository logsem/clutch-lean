module

public import Metrology.Iris.CappedCredits
public import Metrology.Couplings.Divergences.Tv
public import Metrology.Couplings.Divergences.Concentrated
import Metrology.Iris.LocalBI

/-! # Absorbing budgets and DP capped credits

Which budgets are absorbing for dp, tv and Rényi, and that the others cancel, so capped credits
can always be spent (Rocq `gccredit_top_False`). -/

@[expose] public section

universe u

open scoped ENNReal

namespace GradedLifting

open MeasureTheory

/-! ## Absorbing budgets of any lifting -/

variable {B : Type*} {L : GradedLifting.{u} B}

/-- Absorbing budgets form an upper set. -/
theorem isUpperSet_absorbing [Add B] [Preorder B] [Top B] [L.IsLawful] :
    IsUpperSet {b | L.Absorbing b} :=
  fun _ _ hb h ↦ Absorbing.mono h hb

/-- Absorbing budgets form an upper set, as a `Fact`. -/
instance fact_isUpperSet_absorbing [Add B] [Preorder B] [Top B] [L.IsLawful] :
    Fact (IsUpperSet {b | L.Absorbing b}) :=
  ⟨isUpperSet_absorbing⟩

/-- A budget at which the divergence fails for some pair of measures is not absorbing for a sound
lifting. -/
theorem not_absorbing_of_not_divergence [Zero B] [Top B] {D : GradedDivergence.{u} B} [L.IsSound D]
    {X : Type u} [MeasurableSpace X] {b : B} {μ ν : Measure X} [IsSubProbabilityMeasure μ]
    [IsSubProbabilityMeasure ν] (h : ¬D b μ ν) : ¬L.Absorbing b :=
  fun hb ↦ h (IsSound.sound (hb _ μ ν))

end GradedLifting

namespace GradedDivergence

open GradedLifting IsTopAbsorbing
open Prod (mk_le_mk isAddLeftRegular_mk)
open IsAddRegular (of_ne_top)
open Function (update)

/-! ## Which budgets are absorbing for dp, tv and Rényi -/

/-- A DP budget is absorbing exactly when its multiplier is `⊤` or its slack is at least `1`. -/
theorem absorbing_codensity_dp_iff {ε δ : ℝ≥0∞} :
    (codensity dp.{u}).Absorbing (ε, δ) ↔ ε = (⊤ : ℝ≥0∞) ∨ 1 ≤ δ := by
  refine ⟨fun h ↦ or_iff_not_imp_left.2 fun hε ↦ ?_, ?_⟩
  · exact (codensity_dp_rel_false_iff hε).1 (h _ _ _)
  · rintro (rfl | hδ)
    · exact absorbing_codensity_dp_top_left
    · exact absorbing_codensity_dp.mono (mk_le_mk.2 ⟨zero_le, hδ⟩)

variable {δ : ℝ≥0∞}

/-- A total variation budget is absorbing exactly from `1` on. -/
theorem absorbing_codensity_tv_iff : (codensity tv.{u}).Absorbing δ ↔ 1 ≤ δ :=
  ⟨fun h ↦ codensity_tv_rel_false_iff.1 (h _ _ _), absorbing_codensity_tv_one.mono⟩

variable {α : ℝ} {ρ : ℝ≥0∞}

/-- A Rényi budget is absorbing exactly at `⊤`. -/
theorem absorbing_codensity_renyi_iff (hα : 1 < α) :
    (codensity (renyiDivergence.{u} α)).Absorbing ρ ↔ ρ = (⊤ : ℝ≥0∞) :=
  ⟨fun h ↦ by_contra fun hρ ↦ not_absorbing_codensity_renyi hα (lt_top_iff_ne_top.2 hρ) h,
    fun h ↦ h ▸ absorbing_top⟩

/-- The zero DP budget is not absorbing. -/
instance fact_not_absorbing_codensity_dp_zero :
    Fact ((0 : ℝ≥0∞ × ℝ≥0∞) ∉ {b | (codensity dp.{u}).Absorbing b}) :=
  ⟨fun h ↦ by simpa using absorbing_codensity_dp_iff.1 h⟩

/-- The zero total variation budget is not absorbing. -/
instance fact_not_absorbing_codensity_tv_zero :
    Fact ((0 : ℝ≥0∞) ∉ {b | (codensity tv.{u}).Absorbing b}) :=
  ⟨fun h ↦ by simpa using absorbing_codensity_tv_iff.1 h⟩

/-- The zero Rényi budget is not absorbing. -/
instance fact_not_absorbing_codensity_renyi_zero [hα : Fact (1 < α)] :
    Fact ((0 : ℝ≥0∞) ∉ {b | (codensity (renyiDivergence.{u} α)).Absorbing b}) :=
  ⟨fun h ↦ by simpa using (absorbing_codensity_renyi_iff hα.out).1 h⟩

/-! ## Valid budgets cancel -/

/-- A DP budget that is not absorbing cancels: both coordinates are finite. -/
theorem isAddLeftRegular_of_not_absorbing_codensity_dp {b : ℝ≥0∞ × ℝ≥0∞}
    (h : ¬(codensity dp.{u}).Absorbing b) : IsAddLeftRegular b := by
  obtain ⟨ε, δ⟩ := b
  obtain ⟨hε, hδ⟩ := not_or.1 (absorbing_codensity_dp_iff.not.1 h)
  exact isAddLeftRegular_mk.2 ⟨(of_ne_top hε).1, (of_ne_top (not_le.1 hδ).ne_top).1⟩

/-- A total variation budget that is not absorbing cancels. -/
theorem isAddLeftRegular_of_not_absorbing_codensity_tv
    (h : ¬(codensity tv.{u}).Absorbing δ) : IsAddLeftRegular δ :=
  (of_ne_top fun hδ ↦ h (absorbing_codensity_tv_iff.2 (hδ ▸ le_top))).1

/-- A Rényi budget that is not absorbing cancels. -/
theorem isAddLeftRegular_of_not_absorbing_codensity_renyi
    (h : ¬(codensity (renyiDivergence.{u} α)).Absorbing ρ) : IsAddLeftRegular ρ :=
  (of_ne_top fun hρ ↦ h (by rw [hρ]; exact absorbing_top)).1

/-- Some Rényi curve is valid but does not cancel: `⊤` at order `2` and `0` elsewhere. -/
theorem exists_not_absorbing_not_isAddLeftRegular_renyiCurve :
    ∃ ρ : RenyiBudget, ¬(codensity renyiCurve.{u}).Absorbing ρ ∧ ¬IsAddLeftRegular ρ := by
  -- Absorbing means `⊤` at every order, which fails at `three`; adding `1` at `two` is
  -- invisible because the curve is `⊤` there.
  let two : Set.Ioi (1 : ℝ) := ⟨2, by norm_num⟩
  let three : Set.Ioi (1 : ℝ) := ⟨3, by norm_num⟩
  refine ⟨update 0 two ⊤, fun h ↦ ?_, fun h ↦ ?_⟩
  · have := congrFun (absorbing_codensity_renyiCurve_iff.1 h) three
    simp [two, three] at this
  · have := congrFun (h (a₁ := update 0 two 1) (a₂ := 0) <| funext fun α ↦ by
      by_cases hα : α = two <;> simp [hα]) two
    simp at this

end GradedDivergence

/-! ## DP capped credits

Specializes `CappedCredit` to the DP codensity, whose bad budgets are the absorbing ones. -/

namespace CappedCredit

open Iris GradedDivergence

variable {GF : BundledGFunctors}
  [CappedCreditGS (ℝ≥0∞ × ℝ≥0∞) {b | (codensity dp.{u}).Absorbing b} GF]
local bi IProp GF

/-- Spending a DP credit takes it out of the supply. -/
theorem dp_supply_decrease {s c : ℝ≥0∞ × ℝ≥0∞} :
    ⊢ ●↯c s -∗ ↯c c -∗ |==> ∃ r, ⌜s = c + r⌝ ∗ ●↯c r :=
  supply_decrease_of_valid fun _ ↦
    isAddLeftRegular_of_not_absorbing_codensity_dp

/-- A DP credit with slack at least `1` is contradictory. -/
theorem dp_contradict_of_one_le {ε δ : ℝ≥0∞} (hδ : 1 ≤ δ) : ↯c (ε, δ) ⊢ False :=
  contradict (absorbing_codensity_dp_iff.2 (.inr hδ))

end CappedCredit
