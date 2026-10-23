module

public import Metrology.Couplings.Examples.AdaptiveRenyi
public import Metrology.Couplings.BindLaws

/-! # Adaptive filled-KL example: two-stage randomized response

Two-stage randomized response in filled KL: the chain-rule law `BindLaw.fillKl` gives budget
`(4/9) log 2` (`fill_kl_adaptive`), below the non-adaptive `(2/3) log 2`. -/

@[expose] public section

open MeasureTheory Measure ProbabilityTheory GradedLifting GradedDivergence InformationTheory
  ENNReal Real
open scoped ENNReal

namespace AdaptiveFillKl

open AdaptiveRenyi BindLaw

/-! ## The budget of each stage -/

/-- Randomized response puts `2/3` on its input and `1/3` on the other bit. -/
theorem randResp_singleton (d c : Bool) :
    randResp d {c} = if c = d then 2 / 3 else 1 / 3 := by
  cases d <;> cases c <;> simp [randResp]

/-- Randomized response on adjacent inputs is within KL `(log 2) / 3`. -/
theorem klDivergence_randResp :
    klDivergence (ENNReal.ofReal (Real.log 2 / 3)) (randResp false) (randResp true) := by
  have hl : Real.log (1 / 2) = - Real.log 2 := by rw [one_div, Real.log_inv]
  rw [klDivergence_iff_fDiv, fDiv_klFun_eq_sum _ _ fun c ↦ by
      rw [randResp_singleton, randResp_singleton]; split_ifs <;> norm_num,
    EReal.coe_ennreal_ofReal, max_eq_left (by positivity), EReal.coe_le_coe_iff,
    Fintype.sum_bool, randResp_singleton, randResp_singleton, randResp_singleton,
    randResp_singleton]
  norm_num [klTerm, hl]
  linarith

/-- The filled-KL cost of the second stage after each first report. -/
noncomputable def stageTwoCostKl (b : Bool) : ℝ≥0∞ :=
  cond b (ENNReal.ofReal (Real.log 2 / 3)) 0

/-- The adaptive budget is `(log 2) / 3 + (1 / 3) · (log 2) / 3 = (4 / 9) log 2`. -/
theorem budget_adaptive :
    ENNReal.ofReal (Real.log 2 / 3) + ∫⁻ b, stageTwoCostKl b ∂randResp false =
      ENNReal.ofReal (4 * Real.log 2 / 9) := by
  have h3 : (1 / 3 : ℝ≥0∞) = ENNReal.ofReal (1 / 3) := by
    rw [ofReal_div_of_pos (by norm_num)]
    simp
  have hlog : 0 ≤ Real.log 2 / 3 := by positivity
  rw [lintegral_fintype, Fintype.sum_bool, randResp_singleton, randResp_singleton]
  simp only [stageTwoCostKl, Bool.cond_true, Bool.cond_false, Bool.true_eq_false, ↓reduceIte,
    zero_mul, add_zero]
  rw [h3, ← ofReal_mul hlog, ← ofReal_add hlog (by positivity)]
  congr 1
  ring

/-! ## The adaptive bound -/

/-- The chain-rule head of the two-stage mechanism, at budget `(4 / 9) log 2`. -/
theorem fillKlHead_randResp :
    fillKl.head (randResp false) (randResp true)
      (fun x y ↦ if x = y then stageTwoCostKl x else ⊤) (ENNReal.ofReal (4 * Real.log 2 / 9)) :=
  ⟨Bool, inferInstance, randResp false, randResp true, id, id, Set.univ,
    ENNReal.ofReal (Real.log 2 / 3), stageTwoCostKl, measurable_id, measurable_id, .of_discrete,
    .univ, by rw [Set.compl_univ, measure_empty], inferInstance, inferInstance, map_id,
    map_id, fill_kl_iff_of_isProbabilityMeasure.2 klDivergence_randResp, fun z _ ↦ by simp,
    budget_adaptive.le⟩

/-- The adaptive mechanism on adjacent inputs is within filled KL `(4/9) log 2`. -/
theorem fill_kl_adaptive :
    fill klDivergence (ENNReal.ofReal (4 * Real.log 2 / 9)) (adaptive false) (adaptive true) := by
  refine codensity_sound (fillKl.sound fillKlHead_randResp trivial fun x y hxy ↦ ?_)
  obtain rfl : x = y := by_contra fun h ↦ by simp [h] at hxy
  cases x
  -- first report false: nothing new released, budget 0
  · change (codensity (fill klDivergence)).Rel (if false = false then stageTwoCostKl false else ⊤)
      (· = ·) (dirac (false, false)) (dirac (false, false))
    simpa [stageTwoCostKl] using codensity_complete (IsReflexive.refl _)
  -- first report true: a second randomized response at (log 2) / 3
  · change (codensity (fill klDivergence)).Rel (if true = true then stageTwoCostKl true else ⊤)
      (· = ·) ((randResp false).map (Prod.mk true)) ((randResp true).map (Prod.mk true))
    simpa [stageTwoCostKl] using (codensity_complete
      (fill_kl_iff_of_isProbabilityMeasure.2 klDivergence_randResp)).map fun _ _ h ↦ h ▸ rfl

/-- The adaptive mechanism on adjacent inputs is within KL `(4/9) log 2`. -/
theorem klDiv_adaptive_le :
    klDiv (adaptive false) (adaptive true) ≤ ENNReal.ofReal (4 * Real.log 2 / 9) :=
  klDiv_le_of_fill fill_kl_adaptive

/-! ## Adaptivity helps -/

/-- The adaptive budget is strictly below the non-adaptive one. -/
theorem fill_kl_adaptive_budget_lt_nonadaptive :
    ENNReal.ofReal (4 * Real.log 2 / 9) <
      ENNReal.ofReal (Real.log 2 / 3) + ⨆ b, stageTwoCostKl b := by
  have hlog : 0 < Real.log 2 := log_pos one_lt_two
  rw [show ⨆ b, stageTwoCostKl b = ENNReal.ofReal (Real.log 2 / 3) by
      simp [iSup_bool_eq, stageTwoCostKl], ← ofReal_add (by positivity) (by positivity),
    ofReal_lt_ofReal_iff (by positivity)]
  linarith

end AdaptiveFillKl
