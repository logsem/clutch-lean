module

public import Metrology.ProbLang.CtxStep
public import Metrology.ProbLang.Reals
import Metrology.ProbLang.Syntax.Notation

/-! # Sampling from a named distribution family -/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory ENNReal

namespace ProbLang.Test.Sample

/-- A fair coin on boolean values. -/
def coin : Measure (Val ℝ) :=
  (2⁻¹ : ℝ≥0∞) • (dirac (.bool true) + dirac (.bool false))

instance : IsProbabilityMeasure coin := by
  constructor
  simp [coin, ← two_mul, ENNReal.mul_inv_cancel two_ne_zero ofNat_ne_top]

/-- A coin showing `true` with probability `p`. -/
def bern (p : ℝ≥0∞) : Measure (Val ℝ) :=
  p • dirac (.bool true) + (1 - p) • dirac (.bool false)

theorem bern_isProbabilityMeasure {p : ℝ≥0∞} (hp : p ≤ 1) : IsProbabilityMeasure (bern p) := by
  constructor
  simp [bern, add_tsub_cancel_of_le hp]

/-- Swaps `true` and `false`; every other value goes to `true`. -/
def flip (w : Val ℝ) : Val ℝ := by
  classical
  exact if w = .bool true then .bool false else .bool true

theorem measurable_flip : Measurable flip := by
  classical
  exact Measurable.ite (measurableSet_singleton _) measurable_const measurable_const

/-- Flipping a `p`-coin gives a `(1 - p)`-coin. -/
theorem bern_map_flip {p : ℝ≥0∞} (hp : p ≤ 1) : (bern p).map flip = bern (1 - p) := by
  have htrue : flip (.bool true) = .bool false := by simp [flip]
  have hfalse : flip (.bool false) = .bool true := by simp [flip]
  rw [bern, bern, Measure.map_add _ _ measurable_flip, Measure.map_smul, Measure.map_smul,
    map_dirac' measurable_flip, map_dirac' measurable_flip, htrue, hfalse,
    ENNReal.sub_sub_cancel one_ne_top hp, add_comm]
  all_goals exact measurable_flip.aemeasurable

/-- Families `2`, `4` and `5` flip coins with bias `1/2`, `1/3` and `2/3`; the other families
return their argument. -/
def coinKernel : ℕ → Kernel (Val ℝ) (Val ℝ)
  | 2 => Kernel.const _ coin
  | 4 => Kernel.const _ (bern 3⁻¹)
  | 5 => Kernel.const _ (bern (1 - 3⁻¹))
  | _ => Kernel.deterministic id measurable_id

/-- Every measure produced by `coinKernel` is a probability measure. -/
theorem coinKernel_isZeroOrProbabilityMeasure (n : ℕ) (v : Val ℝ) :
    IsZeroOrProbabilityMeasure (coinKernel n v) := by
  match n with
  | 2 =>
    change IsZeroOrProbabilityMeasure coin
    infer_instance
  | 4 =>
    have := bern_isProbabilityMeasure (ENNReal.inv_le_one.mpr (by norm_num : (1 : ℝ≥0∞) ≤ 3))
    change IsZeroOrProbabilityMeasure (bern 3⁻¹)
    infer_instance
  | 5 =>
    have := bern_isProbabilityMeasure (tsub_le_self : 1 - (3 : ℝ≥0∞)⁻¹ ≤ 1)
    change IsZeroOrProbabilityMeasure (bern (1 - 3⁻¹))
    infer_instance
  | 0 | 1 | 3 | _ + 6 =>
    change IsZeroOrProbabilityMeasure (dirac v)
    infer_instance

/-- The ProbLang distribution interpretation containing the fair-coin family. -/
@[instance_reducible]
def coinProbLangDist : ProbLangDist ℝ where
  dist := coinKernel
  isZeroOrProbabilityMeasure_dist := coinKernel_isZeroOrProbabilityMeasure

/-- Every observation returns zero, for examples that do not use random variables. -/
@[instance_reducible]
def zeroObs : ProbLangObs ℝ where
  obs _ _ := 0
  measurable_obs _ := measurable_const

local instance : ProbLangDist ℝ := coinProbLangDist
local instance : ProbLangFFI ℝ := ProbLangFFI.stuck
local instance : ProbLangObs ℝ := zeroObs

@[simp]
theorem dist_two (v : Val ℝ) : ProbLangDist.dist 2 v = coin :=
  rfl

@[simp]
theorem dist_four (v : Val ℝ) : ProbLangDist.dist 4 v = bern 3⁻¹ :=
  rfl

@[simp]
theorem dist_five (v : Val ℝ) : ProbLangDist.dist 5 v = bern (1 - 3⁻¹) :=
  rfl

variable (σ : State ℝ)

/-- A fresh sample from family `2` takes one fair-coin head step. -/
example : headStep ⟨(pl(sample(2, #(), #())) : Exp ℝ), σ⟩ =
    (2⁻¹ : ℝ≥0∞) • (dirac ⟨.lit (.bool true), σ⟩ + dirac ⟨.lit (.bool false), σ⟩) := by
  have hm : Measurable fun v : Val ℝ => (⟨Exp.ofVal v, σ⟩ : Cfg ℝ) := by fun_prop
  rw [headStep_sample rfl]
  change coin.map (fun v : Val ℝ => (⟨Exp.ofVal v, σ⟩ : Cfg ℝ)) = _
  rw [coin, Measure.map_smul,
    Measure.map_add _ _ hm, map_dirac' hm, map_dirac' hm]
  · rfl
  · exact hm.aemeasurable

/-- Family `3` returns its argument in one fresh-sample head step. -/
example : headStep ⟨(pl(sample(3, #5, #())) : Exp ℝ), σ⟩ = dirac ⟨.lit (.int 5), σ⟩ := by
  have hm : Measurable fun v : Val ℝ => (⟨Exp.ofVal v, σ⟩ : Cfg ℝ) := by fun_prop
  rw [headStep_sample rfl]
  change (dirac (Val.int 5)).map (fun v : Val ℝ => (⟨Exp.ofVal v, σ⟩ : Cfg ℝ)) = _
  rw [map_dirac' hm]
  rfl

end ProbLang.Test.Sample
