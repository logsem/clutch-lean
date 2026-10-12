module

public import Iris
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.MeasureTheory.Measure.Sub
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Iris.Algebra.View
public import Iris.Instances.IProp.Instance
public import Iris.Algebra.Auth
public import Iris.Algebra.Numbers

@[expose] public section

open Std Iris COFE ProbabilityTheory MeasureTheory

noncomputable section

instance authMeasureOFE [MeasurableSpace α] : OFE (Measure α) where
  Dist _ x y := x = y
  dist_eqv := ⟨fun _ => rfl, (Eq.symm ·), (Eq.trans · ·)⟩
  eq_dist' := .symm <| forall_const _
  dist_lt H _ := H

instance [MeasurableSpace α] : CMRA (Measure α) where
  pcore _ := .some 0
  op μ₁ μ₂ := μ₁ + μ₂
  Valid μ := μ .univ ≤ 1
  ValidN _ μ := μ .univ ≤ 1
  op_ne.ne {_ _ _} H := by rw [H]
  pcore_ne := by simp
  validN_ne := (· ▸ ·)
  valid_iff_validN := ⟨fun H _ => H, fun H => H 0⟩
  validN_succ := (·)
  validN_op_left := (le_of_add_le_of_nonneg_left · <| zero_le)
  assoc := by simp [add_assoc]
  comm := by simp [add_comm]
  pcore_op_left := by simp
  pcore_idem := by simp
  pcore_op_mono {_ _} := by
    rintro ⟨rfl⟩ _
    exact ⟨0, Option.some_inj.mpr (zero_add 0).symm⟩
  extend {_ _ y1 y2} _ := (⟨y1, y2, ·, rfl, rfl⟩)

instance [MeasurableSpace α] : UCMRA (Measure α) where
  unit := 0
  unit_valid := by simp [CMRA.Valid]
  unit_left_id := zero_add _
  pcore_unit := by simp [CMRA.pcore]

end
