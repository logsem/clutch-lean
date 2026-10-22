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

/-! # Measures as a camera

`Measure α` is a unital camera: composition is `+`, valid when the total mass is at most `1`. -/

@[expose] public section

open Std Iris COFE ProbabilityTheory MeasureTheory

noncomputable section

/-- Measures form a discrete OFE: distance is equality at every step. -/
instance [MeasurableSpace α] : OFE (Measure α) where
  Dist _ x y := x = y
  dist_eqv := ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩
  eq_dist' := .symm <| forall_const _
  dist_lt H _ := H

/-- Measures compose by `+` and are valid when their total mass is at most `1`; the core is `0`. -/
instance [MeasurableSpace α] : CMRA (Measure α) where
  pcore _ := .some 0
  op μ₁ μ₂ := μ₁ + μ₂
  Valid μ := μ .univ ≤ 1
  ValidN _ μ := μ .univ ≤ 1
  op_ne.ne {_ _ _} H := by rw [H]
  pcore_ne := by simp
  validN_ne := (· ▸ ·)
  valid_iff_validN := ⟨fun H _ ↦ H, fun H ↦ H 0⟩
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

/-- The discrete OFE on measures is discrete. -/
instance [MeasurableSpace α] : OFE.Discrete (Measure α) := ⟨id⟩

/-- The zero measure is the unit. -/
instance [MeasurableSpace α] : UCMRA (Measure α) where
  unit := 0
  unit_valid := by simp [CMRA.Valid]
  unit_left_id := zero_add _
  pcore_unit := by simp [CMRA.pcore]

end
