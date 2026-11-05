module

public import Metrology.ProbLang.Syntax.Syntax
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Function.Floor

/-! # The real-number model `LawfulProbLangℝ ℝ`

The instance takes `unifUnit` to be Lebesgue measure on `[0,1]`; `x ↦ frac (m + x)` preserves it. -/

namespace ProbLang

open MeasureTheory Set
open MeasureTheory.Measure (map_apply restrict_apply restrict_apply' restrict_apply_univ)
open Int (fract fract_add_floor fract_eq_self fract_lt_one fract_nonneg fract_sub_intCast
  fract_sub_one)
open Function (uncurry)
open ProbLangℝ (realAdd realFrac realNeg realOfInt realOfRat)
open LawfulProbLangℝ (unifUnit unifUnitSupport)

/-! ## The instance -/

/-- The reals as a `LawfulProbLangℝ` model, with `unifUnit` Lebesgue measure on `[0,1]`. -/
public noncomputable instance instLawfulProbLangℝReal : LawfulProbLangℝ ℝ where
  beq a b := decide (a = b)
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl
  measurableSet_diagonal := isClosed_diagonal.measurableSet
  instDecidableEq := inferInstance
  unifUnit := volume.restrict (Icc 0 1)
  unifUnit_isProbabilityMeasure := by
    constructor
    rw [restrict_apply_univ, Real.volume_Icc]
    simp
  -- The open interval: the endpoints are null, and callers get the strict range `0 < r < 1`.
  unifUnitSupport := Ioo 0 1
  unifUnitSupportMeasurable := measurableSet_Ioo
  unifUnitIsConcentrated := by
    rw [restrict_apply' measurableSet_Icc]
    refine measure_mono_null (t := {0, 1}) ?_ ?_
    · rintro x ⟨hx, h0, h1⟩
      simp only [mem_compl_iff, mem_Ioo, not_and, not_lt] at hx
      simp only [mem_insert_iff, mem_singleton_iff]
      rcases eq_or_lt_of_le h0 with h | h
      · exact .inl h.symm
      · exact .inr (le_antisymm h1 (hx h))
    · exact ((finite_singleton 1).insert 0).countable.measure_zero volume
  realLt a b := decide (a < b)
  realLe a b := decide (a ≤ b)
  measurable_realLt := by
    apply measurable_to_bool
    have h : (uncurry (fun a b => decide (a < b)) ⁻¹' {true}) = {p : ℝ × ℝ | p.1 < p.2} := by
      ext p; simp [uncurry, decide_eq_true_eq]
    rw [h]; exact measurableSet_lt measurable_fst measurable_snd
  measurable_realLe := by
    apply measurable_to_bool
    have h : (uncurry (fun a b => decide (a ≤ b)) ⁻¹' {true}) = {p : ℝ × ℝ | p.1 ≤ p.2} := by
      ext p; simp [uncurry, decide_eq_true_eq]
    rw [h]; exact measurableSet_le measurable_fst measurable_snd
  realAdd a b := a + b
  realNeg a := -a
  realOfInt z := z
  realOfRat q := q
  realFrac r := fract r
  measurable_realAdd := measurable_add
  measurable_realNeg := measurable_neg
  measurable_realFrac := measurable_fract

/-! ## Reduction lemmas

At `rT = ℝ` the `ProbLangℝ` operations are Lean's own; these let `twp_pures` normalise them. -/

/-- At `ℝ`, `realAdd` is ordinary addition. -/
@[simp] public theorem realAdd_real (a b : ℝ) : realAdd a b = a + b := rfl

/-- At `ℝ`, `realNeg` is ordinary negation. -/
@[simp] public theorem realNeg_real (a : ℝ) : realNeg a = -a := rfl

/-- At `ℝ`, `realOfInt` is the integer cast. -/
@[simp] public theorem realOfInt_real (z : ℤ) : realOfInt z = (z : ℝ) := rfl

/-- At `ℝ`, `realOfRat` is the rational cast. -/
@[simp] public theorem realOfRat_real (q : ℚ) : realOfRat q = (q : ℝ) := rfl

/-- At `ℝ`, `realFrac` is the fractional part. -/
@[simp] public theorem realFrac_real (r : ℝ) : realFrac r = fract r := rfl

/-- Membership in the support of `unifUnit` at `ℝ` means lying in the open interval `(0, 1)`. -/
public theorem mem_unifUnitSupport_real {r : ℝ} : r ∈ unifUnitSupport ↔ 0 < r ∧ r < 1 := mem_Ioo

/-! ## Rotation invariance of `Uniform[0,1]`

`x ↦ frac (m + x)` swaps the blocks `[0, 1-m)` and `[1-m, 1)` by translation, so it preserves
`Uniform[0,1]`. -/

/-- Adding `m ∈ [0, 1)` modulo 1 preserves `Uniform[0,1]`. -/
theorem measurePreserving_fracAdd_aux {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m < 1) :
    MeasurePreserving (fun r => realFrac (realAdd m r)) unifUnit unifUnit := by
  show MeasurePreserving (fun r => fract (m + r)) (volume.restrict (Icc 0 1))
    (volume.restrict (Icc 0 1))
  have hmeas : Measurable (fun r => fract (m + r)) := measurable_fract.comp (measurable_const_add m)
  refine ⟨hmeas, ?_⟩
  refine Measure.ext fun S hS => ?_
  rw [map_apply hmeas hS, restrict_apply (hmeas hS), restrict_apply hS]
  -- `Icc 0 1` and `Ico 0 1` differ by the null set `{1}`.
  have hIcc : ∀ A : Set ℝ, volume (A ∩ Icc 0 1) = volume (A ∩ Ico 0 1) := by
    intro A
    have hsplit : A ∩ Icc 0 1 = (A ∩ Ico 0 1) ∪ (A ∩ {1}) := by
      rw [← inter_union_distrib_left, Ico_union_right zero_le_one]
    have hnull : volume (A ∩ {1}) = 0 := measure_mono_null inter_subset_right (measure_singleton 1)
    rw [hsplit]
    refine le_antisymm ?_ (measure_mono subset_union_left)
    exact (measure_union_le _ _).trans (by rw [hnull, add_zero])
  rw [hIcc, hIcc]
  have hlo : 0 ≤ 1 - m := by linarith
  have hhi : 1 - m ≤ 1 := by linarith
  -- Block `[0, 1-m)`: `frac (m + r) = m + r`, a shift onto `[m, 1)`.
  have hA : (fun r => fract (m + r)) ⁻¹' S ∩ Ico 0 (1 - m) =
      (fun r => m + r) ⁻¹' (S ∩ Ico m 1) := by
    ext r
    simp only [mem_inter_iff, mem_preimage, mem_Ico]
    have hfr : 0 ≤ r → r < 1 - m → fract (m + r) = m + r :=
      fun h0 h1 => fract_eq_self.mpr ⟨by linarith, by linarith⟩
    constructor
    · rintro ⟨hSr, hr0, hr1⟩
      exact ⟨by rwa [hfr hr0 hr1] at hSr, by linarith, by linarith⟩
    · rintro ⟨hSr, hge, hlt⟩
      exact ⟨by rwa [hfr (by linarith) (by linarith)], by linarith, by linarith⟩
  -- Block `[1-m, 1)`: `frac (m + r) = m + r - 1`, a shift onto `[0, m)`.
  have hB : (fun r => fract (m + r)) ⁻¹' S ∩ Ico (1 - m) 1 =
      (fun r => (m - 1) + r) ⁻¹' (S ∩ Ico 0 m) := by
    ext r
    simp only [mem_inter_iff, mem_preimage, mem_Ico]
    have hshift : fract (m + r) = fract (m + r - 1) := (fract_sub_one (m + r)).symm
    have hfr : 1 - m ≤ r → r < 1 → fract (m + r - 1) = m + r - 1 :=
      fun h0 h1 => fract_eq_self.mpr ⟨by linarith, by linarith⟩
    constructor
    · rintro ⟨hSr, hr0, hr1⟩
      rw [hshift, hfr hr0 hr1] at hSr
      exact ⟨by convert hSr using 1; ring, by linarith, by linarith⟩
    · rintro ⟨hSr, hge, hlt⟩
      refine ⟨?_, by linarith, by linarith⟩
      rw [hshift, hfr (by linarith) (by linarith)]
      convert hSr using 1; ring
  have hunion1 : Ico 0 (1 - m) ∪ Ico (1 - m) 1 = Ico 0 1 := Ico_union_Ico_eq_Ico hlo hhi
  have hunion2 : Ico 0 m ∪ Ico m 1 = Ico 0 1 := Ico_union_Ico_eq_Ico hm0 hm1.le
  -- Split both sides along the blocks; translations preserve volume.
  have hL : volume ((fun r => fract (m + r)) ⁻¹' S ∩ Ico 0 1) =
      volume ((fun r => fract (m + r)) ⁻¹' S ∩ Ico 0 (1 - m)) +
        volume ((fun r => fract (m + r)) ⁻¹' S ∩ Ico (1 - m) 1) := by
    rw [← hunion1, inter_union_distrib_left]
    exact measure_union (Ico_disjoint_Ico_same.mono inter_subset_right inter_subset_right)
      ((hmeas hS).inter measurableSet_Ico)
  have hR : volume (S ∩ Ico 0 1) = volume (S ∩ Ico 0 m) + volume (S ∩ Ico m 1) := by
    rw [← hunion2, inter_union_distrib_left]
    exact measure_union (Ico_disjoint_Ico_same.mono inter_subset_right inter_subset_right)
      (hS.inter measurableSet_Ico)
  rw [hL, hR, hA, hB, measure_preimage_add, measure_preimage_add]
  exact add_comm _ _

/-- Adding any real `m` modulo 1 preserves `Uniform[0,1]`. -/
public theorem measurePreserving_fracAdd (m : ℝ) :
    MeasurePreserving (fun r => realFrac (realAdd m r)) unifUnit unifUnit := by
  have hper : (fun r => fract (m + r)) = fun r => fract (fract m + r) :=
    funext fun r => by rw [add_comm (fract m) r, Int.fract_add_fract, add_comm]
  show MeasurePreserving (fun r => fract (m + r)) _ _
  rw [hper]
  exact measurePreserving_fracAdd_aux (fract_nonneg m) (fract_lt_one m)

end ProbLang
