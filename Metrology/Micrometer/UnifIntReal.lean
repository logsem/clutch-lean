module

public import Metrology.Micrometer.UnifInt
public import Metrology.ProbLang.Reals
import Metrology.ProbLang.Syntax.Notation

/-! # The floor map at the reals

At `ℝ`, `u ↦ ⌊N u⌋` pushes `unifUnit` to the uniform integer measure `unifInt N`. -/

@[expose] public section

open MeasureTheory (Measure MeasurePreserving)

namespace ProbLang

open LawfulProbLangℝ
open Set Real
open MeasureTheory.Measure (ext_of_singleton map_apply uniformOfFinset_apply_singleton)
open _root_.Int (cast_pos measurable_floor floor_eq_iff card_Ico toNat_of_nonneg lt_or_le)
open ENNReal (ofReal_div_of_pos ofReal_one ofReal_natCast)

/-- At `ℝ`, `u ↦ ⌊N u⌋` pushes the uniform measure on `[0, 1]` to the uniform measure on
`{0, …, N-1}`. -/
theorem measurePreserving_floor_mul (N : Int) (HN : 0 < N) :
    MeasurePreserving (fun u : ℝ => ⌊(N : ℝ) * u⌋) unifUnit (unifInt N HN) := by
  have hNr : (0 : ℝ) < N := cast_pos.mpr HN
  have hmeas : Measurable (fun u : ℝ => ⌊(N : ℝ) * u⌋) :=
    measurable_floor.comp (measurable_const_mul _)
  refine ⟨hmeas, ext_of_singleton fun k => ?_⟩
  have hpre : (fun u : ℝ => ⌊(N : ℝ) * u⌋) ⁻¹' {k} = Ico ((k : ℝ) / N) ((k + 1) / N) := by
    ext u
    simp only [mem_preimage, mem_singleton_iff, floor_eq_iff, mem_Ico,
      div_le_iff₀ hNr, lt_div_iff₀ hNr]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [map_apply hmeas (measurableSet_singleton k), hpre, unifInt,
    uniformOfFinset_apply_singleton]
  show (MeasureTheory.volume.restrict (Icc (0 : ℝ) 1)) _ = _
  rw [Measure.restrict_apply measurableSet_Ico]
  split_ifs with hk
  · obtain ⟨hk0, hkN⟩ := Finset.mem_Ico.mp hk
    have hk0' : (0 : ℝ) ≤ k := by exact_mod_cast hk0
    have hkN' : (k : ℝ) + 1 ≤ N := by exact_mod_cast (show k + 1 ≤ N by omega)
    have hsub : Ico ((k : ℝ) / N) ((k + 1) / N) ⊆ Icc 0 1 := fun u ⟨h1, h2⟩ =>
      ⟨(div_nonneg hk0' hNr.le).trans h1, h2.le.trans ((div_le_one hNr).mpr hkN')⟩
    rw [inter_eq_left.mpr hsub, volume_Ico, card_Ico, sub_zero, ← sub_div,
      add_sub_cancel_left, ofReal_div_of_pos hNr, ofReal_one, one_div]
    congr 1
    rw [← ofReal_natCast]
    congr 1
    exact_mod_cast (toNat_of_nonneg HN.le).symm
  · refine MeasureTheory.measure_mono_null (t := {(1 : ℝ)}) ?_ (volume_singleton)
    rintro u ⟨⟨h1, h2⟩, h3, h4⟩
    rw [div_le_iff₀ hNr] at h1
    rw [lt_div_iff₀ hNr] at h2
    simp only [Finset.mem_Ico] at hk
    rcases lt_or_le k 0 with hk' | hk'
    · have : (k : ℝ) + 1 ≤ 0 := by exact_mod_cast (show k + 1 ≤ 0 by omega)
      nlinarith
    · have : (N : ℝ) ≤ k := by exact_mod_cast (show N ≤ k by omega)
      exact le_antisymm h4 (by nlinarith)

end ProbLang
