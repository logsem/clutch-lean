module

public import Metrology.Couplings.Divergences.RenyiAdaptive

/-! A worked example of adaptive Rényi composition through the escort rule: randomized response,
followed by a second randomized response only when the first report is `true` (Rocq
`escort_adaptive`). -/

@[expose] public section

open MeasureTheory Measure ProbabilityTheory GradedLifting GradedDivergence
open scoped ENNReal

namespace AdaptiveRenyi

/-! ## The mechanism -/

/-- Randomized response: report the input bit with probability `2 / 3`. -/
noncomputable def randResp (d : Bool) : Measure Bool :=
  (2 / 3 : ℝ≥0∞) • dirac d + (1 / 3 : ℝ≥0∞) • dirac (!d)

instance isProbabilityMeasure_randResp (d : Bool) : IsProbabilityMeasure (randResp d) := ⟨by
  simp [randResp]
  rw [div_eq_mul_inv, ← add_one_mul, two_add_one_eq_three,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]⟩

/-- The second stage: after a reported `true`, run randomized response again; after `false`,
release nothing new. It outputs both reports. -/
noncomputable def stageTwo (d : Bool) : Kernel Bool (Bool × Bool) :=
  ⟨fun b ↦ cond b ((randResp d).map (Prod.mk true)) (dirac (false, false)), .of_discrete⟩

instance isMarkovKernel_stageTwo (d : Bool) : IsMarkovKernel (stageTwo d) := ⟨by
  rintro (_ | _)
  · exact inferInstanceAs (IsProbabilityMeasure (dirac _))
  · exact inferInstanceAs (IsProbabilityMeasure (map _ _))⟩

/-- The Rényi cost of the second stage after each first report. -/
noncomputable def stageTwoCost (b : Bool) : ℝ≥0∞ :=
  cond b (ENNReal.ofReal (Real.log (3 / 2))) 0

/-- The two-stage adaptive mechanism on input `d`. -/
noncomputable def adaptive (d : Bool) : Measure (Bool × Bool) :=
  stageTwo d ∘ₘ randResp d

instance isProbabilityMeasure_adaptive (d : Bool) : IsProbabilityMeasure (adaptive d) := by
  unfold adaptive
  infer_instance

/-! ## The budget -/

/-- The multiplier of the expensive branch is `3 / 2`. -/
theorem expBudget_log_three_halves :
    expBudget (ENNReal.ofReal (Real.log (3 / 2))) = 3 / 2 := by
  rw [expBudget_ofReal (Real.log_nonneg (by norm_num)), Real.exp_log (by norm_num),
    ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

/-- Randomized response on adjacent inputs is within Rényi budget `log (3 / 2)` at order `2`. -/
theorem renyiDivergence_randResp :
    renyiDivergence 2 (ENNReal.ofReal (Real.log (3 / 2))) (randResp false) (randResp true) := by
  rw [renyiDivergence_iff_of_ne_top one_le_two ENNReal.ofReal_ne_top,
    fDiv_eq_sum (convexOn_rpow one_le_two) (continuousWithinAt_rpow_zero two_pos)]
  simp [randResp]
  rw [persp_of_ne_zero (by norm_num), persp_of_ne_zero (by norm_num), ← EReal.coe_add,
    ENNReal.toReal_ofReal (Real.log_nonneg (by norm_num)), EReal.coe_le_coe_iff]
  norm_num [Real.exp_log]

/-- The escort head premise, with witness kernel `Kernel.id`: the first stage is within Rényi
budget `log (19 / 12)` of its neighbour reweighted by `e^{-ρ₂}`. -/
theorem renyiDivergence_randResp_escort :
    renyiDivergence 2 (ENNReal.ofReal (Real.log (19 / 12))) (randResp false)
      (((Kernel.id : Kernel Bool Bool) ∘ₘ randResp true).withDensity
        fun b ↦ (expBudget (stageTwoCost b))⁻¹) := by
  rw [renyiDivergence_iff_of_ne_top one_le_two ENNReal.ofReal_ne_top,
    fDiv_eq_sum (convexOn_rpow one_le_two) (continuousWithinAt_rpow_zero two_pos)]
  simp [randResp, stageTwoCost, withDensity_apply _ (measurableSet_singleton _),
    expBudget_log_three_halves]
  rw [persp_of_ne_zero (by norm_num), persp_of_ne_zero (by norm_num), ← EReal.coe_add,
    ENNReal.toReal_ofReal (Real.log_nonneg (by norm_num)), EReal.coe_le_coe_iff]
  norm_num [Real.exp_log]

/-- The adaptive mechanism on adjacent inputs is within Rényi budget `log (19 / 12)` at order
`2` (Rocq `escort_adaptive`). Uses `codensity_renyi_bind_escort`, the lemma behind
`BindLaw.escort`. -/
theorem renyiDivergence_adaptive :
    renyiDivergence 2 (ENNReal.ofReal (Real.log (19 / 12))) (adaptive false) (adaptive true) := by
  have : Fact (1 < (2 : ℝ)) := ⟨one_lt_two⟩
  refine codensity_sound (codensity_renyi_bind_escort (S := (· = ·)) .of_discrete Kernel.id
      (fun _ ↦ by simp [Kernel.id_apply, ae_dirac_eq]) (fun x y hxy ↦ ?_)
      renyiDivergence_randResp_escort)
  subst hxy
  cases x
  -- first report false: nothing new released, budget 0
  · change (codensity (renyiDivergence 2)).Rel 0 (· = ·) (dirac (false, false))
      (dirac (false, false))
    exact codensity_complete (IsReflexive.refl _)
  -- first report true: a second randomized response at log (3/2)
  · change (codensity (renyiDivergence 2)).Rel (ENNReal.ofReal (Real.log (3 / 2))) (· = ·)
      ((randResp false).map (Prod.mk true)) ((randResp true).map (Prod.mk true))
    exact (codensity_complete renyiDivergence_randResp).map fun _ _ h ↦ h ▸ rfl

/-- The adaptive budget is strictly below the worst-case non-adaptive budget: the first stage's
`log (3 / 2)` plus the largest second-stage cost. -/
theorem log_nineteen_twelfths_lt :
    ENNReal.ofReal (Real.log (19 / 12)) <
      ENNReal.ofReal (Real.log (3 / 2)) + ⨆ b, stageTwoCost b := by
  have hlog : 0 ≤ Real.log (3 / 2) := Real.log_nonneg (by norm_num)
  rw [show ⨆ b, stageTwoCost b = ENNReal.ofReal (Real.log (3 / 2)) by simp [iSup_bool_eq,
      stageTwoCost], ← ENNReal.ofReal_add hlog hlog,
    ENNReal.ofReal_lt_ofReal_iff (by positivity), ← Real.log_mul (by norm_num) (by norm_num)]
  exact Real.log_lt_log (by norm_num) (by norm_num)

end AdaptiveRenyi
