module

public import Metrology.Micrometer.Examples.RandomizedResponse.Adaptive
public import Metrology.Couplings.Examples.AdaptiveFillKl
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Adaptive randomized response in filled KL, with the chain-rule law

`rrAdaptive_fillKl`: adaptive randomized response is within filled KL `(4/9) log 2`, by the
chain-rule law `fillKl`. -/

open MeasureTheory ProbabilityTheory GradedLifting GradedDivergence AdaptiveRenyi AdaptiveFillKl
open scoped ENNReal

namespace ProbLang.RandomizedResponse

open MeasureTheory.Measure (map_apply map_map)
open Set (Ico finite_Ico)
open ENNReal (ofReal isAddLeftRegular_ofReal)
open Real (log)
open BindLaw (fillKl)
open Cfg (drawCost drawCost_apply)

/-! ## The second round: one `rr3` draw at `(log 2) / 3` -/

/-- A draw from `[0, 3)` read by `h` charges each report. -/
theorem map_unifInt_three_ne_zero {h : Int → Bool} {d : Bool} (h0 : h 0 = d) (h1 : h 1 = d)
    (h2 : h 2 = !d) (c : Bool) : (unifInt 3 (by norm_num)).map h {c} ≠ 0 := by
  rw [map_unifInt_three h0 h1 h2, randResp_singleton]
  split_ifs <;> norm_num

/-- The second round couples along equal reports at filled KL `(log 2) / 3`. -/
theorem rr3_coupling_fillKl :
    (codensity klDivergence.fill).Rel (ofReal (log 2 / 3))
      (fun r r' ↦ rr3Out false r = rr3Out true r') (unifInt 3 (by norm_num))
      (unifInt 3 (by norm_num)) := by
  refine codensity_rel_of_map .of_discrete .of_discrete (fun c h ↦ absurd h ?_) ?_
  · rw [← map_apply .of_discrete (measurableSet_singleton c)]
    exact map_unifInt_three_ne_zero rfl rfl rfl c
  · rw [map_unifInt_three rfl rfl rfl, map_unifInt_three rfl rfl rfl,
      fill_kl_iff_of_isProbabilityMeasure]
    exact klDivergence_randResp

/-! ## The first round: the chain-rule head at `(4/9) log 2` -/

/-- The budget handed to the continuation after first draws `n`, `m`: the second round's cost
`stageTwoCostKl` of their common report, or `⊤` if the reports differ. -/
noncomputable def adaptiveCostKl (n m : Int) : ℝ≥0∞ :=
  if rr3Out false n = rr3Out true m then stageTwoCostKl (rr3Out false n) else ⊤

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

/-- The first draws, as configurations, form a chain-rule head at `(4/9) log 2` with continuation
cost `adaptiveCostKl`. -/
theorem fillKlHead_rr3 (K : Ectx rT) (σ σ' : State rT) :
    fillKl.head ((unifInt 3 (by norm_num)).map fun n ↦ (⟨pl(#int n), σ⟩ : Cfg rT))
      ((unifInt 3 (by norm_num)).map fun m ↦ (⟨K.fill pl(#int m), σ'⟩ : Cfg rT))
      (drawCost σ σ' K adaptiveCostKl) (ofReal (4 * log 2 / 9)) := by
  classical
  have hK (a b) : K.fill a = K.fill b ↔ a = b := (Ectx.fill_injective K).eq_iff
  have hμf := map_reportL σ
  have hνg := map_reportR K σ'
  refine fillKlHead_of_map (ε := ofReal (log 2 / 3)) (measurable_reportL σ)
    (measurable_reportR K σ') ((finite_Ico 0 3).image _).measurableSet
    ((finite_Ico 0 3).image _).measurableSet (map_unifInt_three_compl_image _)
    (map_unifInt_three_compl_image _) (fun c ↦ ?_) stageTwoCostKl ?_ ?_ ?_
  · rw [← map_apply (measurable_reportL σ) (measurableSet_singleton c),
      ← map_apply (measurable_reportR K σ') (measurableSet_singleton c), hμf, hνg,
      randResp_singleton, randResp_singleton]
    split_ifs <;> norm_num
  · rintro _ _ ⟨n, ⟨hn0, hn3⟩, rfl⟩ ⟨m, ⟨hm0, hm3⟩, rfl⟩ hfg
    rw [drawCost_apply]
    interval_cases n <;> interval_cases m <;> simp_all [adaptiveCostKl, rr3Out]
  · rw [hμf, hνg, fill_kl_iff_of_isProbabilityMeasure]
    exact klDivergence_randResp
  · rw [hμf, budget_adaptive]

/-! ## The relational proof -/

open Iris Iris.BI Iris.ProofMode

variable {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF] [BudgetCreditGS ℝ≥0∞ GF]
local bi IProp GF

/-- The adaptive program on `false` refines it on `true` at equal pairs of reports, spending
filled KL `(4/9) log 2`: the chain-rule law at the first draw, the canonical law at the second. -/
theorem rrAdaptive_refines_fillKl :
    ⊢ ↯b (ofReal (4 * log 2 / 9)) -∗
      REL[codensity klDivergence.fill] (rrAdaptive (rT := rT) false) << (rrAdaptive true) :
        lrel_prod lrel_bool lrel_bool := by
  iintro Hb
  rel_couple_UU_law fillKl adaptiveCostKl (ofReal (4 * log 2 / 9))
    (isAddLeftRegular_ofReal _) fillKlHead_rr3
  iframe Hb
  iintro %n %m %hR Hb
  rel_pures
  by_cases hn : n < 2 <;> by_cases hm : m < 2 <;>
    simp only [adaptiveCostKl, rr3Out, hn, hm, ↓reduceIte, decide_true, decide_false,
      Bool.not_false, Bool.not_true, stageTwoCostKl, Bool.cond_true, Bool.cond_false] at hR ⊢ <;>
    (try simp at hR) <;> rel_pures
  -- mismatched reports close by `hR`; first goal: report `false`, no second round; second goal:
  -- report `true`, spend the remaining `(log 2) / 3` on the second draw
  · rel_values
  · rel_couple_UU_spend (fun r r' ↦ rr3Out false r = rr3Out true r') _
      (isAddLeftRegular_ofReal _) rr3_coupling_fillKl
    iframe Hb
    iintro %r %r' %hr
    rel_pures
    by_cases hd : r < 2 <;> by_cases hd' : r' < 2 <;>
      simp only [rr3Out, hd, hd', ↓reduceIte, decide_true, decide_false, Bool.not_false,
        Bool.not_true] at hr ⊢ <;> (try simp at hr) <;> rel_pures <;> rel_values

/-! ## Adequacy -/

/-- The adaptive program on `false` and on `true` is within filled KL `(4/9) log 2`, as
`fill_kl_adaptive` computes for the measures. -/
theorem rrAdaptive_fillKl (σ σ' : State rT) :
    klDivergence.fill (ofReal (4 * log 2 / 9))
      (limExecV ⟨rrAdaptive false, σ⟩) (limExecV ⟨rrAdaptive true, σ'⟩) :=
  approximates_div (GF := MicrometerFunctor rT ℝ≥0∞) (fun _ _ ↦ lrel_prod lrel_bool lrel_bool)
    _ _ σ σ' _ (fun _ _ ↦ lrel_prod_car_eq lrel_bool_car_eq lrel_bool_car_eq)
    fun _ _ ↦ rrAdaptive_refines_fillKl

end ProbLang.RandomizedResponse
