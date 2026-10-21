module

public import Metrology.Micrometer.Examples.RandomizedResponse.Adaptive
public import Metrology.Couplings.Examples.AdaptiveFillKl
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Adaptive randomized response in filled KL, with the chain-rule law

`rrAdaptive_fillKl`: adaptive randomized response is within filled KL `(4/9) log 2`, not
`(2/3) log 2`, as the chain-rule law `BindLaw.fillKl` pays the second round's cost on average
under the first round's left outcome (`AdaptiveFillKl`). -/

open MeasureTheory ProbabilityTheory GradedLifting GradedDivergence AdaptiveRenyi AdaptiveFillKl
open scoped ENNReal

namespace ProbLang
namespace RandomizedResponse

/-! ## The second round: one `rr3` draw at `(log 2) / 3` -/

/-- A draw from `[0, 3)` read by `h` charges each report. -/
theorem map_unifInt_three_ne_zero {h : Int → Bool} {d : Bool} (h0 : h 0 = d) (h1 : h 1 = d)
    (h2 : h 2 = !d) (c : Bool) : (unifInt 3 (by norm_num)).map h {c} ≠ 0 := by
  rw [map_unifInt_three h0 h1 h2, randResp_singleton]
  split_ifs <;> norm_num

/-- The second round couples along equal reports at filled KL `(log 2) / 3`. -/
theorem rr3_coupling_fillKl :
    (codensity klDivergence.fill).Rel (ENNReal.ofReal (Real.log 2 / 3))
      (fun r r' ↦ rr3Out false r = rr3Out true r') (unifInt 3 (by norm_num))
      (unifInt 3 (by norm_num)) := by
  refine codensity_rel_of_map .of_discrete .of_discrete (fun c h ↦ absurd h ?_) ?_
  · rw [← Measure.map_apply .of_discrete (measurableSet_singleton c)]
    exact map_unifInt_three_ne_zero (d := true) rfl rfl rfl c
  · rw [map_unifInt_three (d := false) rfl rfl rfl, map_unifInt_three (d := true) rfl rfl rfl,
      fill_kl_iff_of_isProbabilityMeasure]
    exact klDivergence_randResp

/-! ## The first round: the chain-rule head at `(4/9) log 2` -/

/-- The budget handed to the continuation after first draws `n`, `m`: the second round's cost
`stageTwoCostKl` of their common report, or `⊤` if the reports differ. -/
noncomputable def adaptiveCostKl (n m : Int) : ℝ≥0∞ :=
  if rr3Out false n = rr3Out true m then stageTwoCostKl (rr3Out false n) else ⊤

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

/-- The first draws, as configurations, form a chain-rule head at `(4/9) log 2` with continuation
cost `adaptiveCostKl`: map the draws to reports and use `klDivergence_randResp`. -/
theorem fillKlHead_rr3 (K : Ectx rT) (σ σ' : State rT) :
    BindLaw.fillKl.head
      ((unifInt 3 (by norm_num)).map fun n ↦ (⟨pl(#int n), σ⟩ : Cfg rT))
      ((unifInt 3 (by norm_num)).map fun m ↦ (⟨K.fill pl(#int m), σ'⟩ : Cfg rT))
      (Cfg.drawCost σ σ' K adaptiveCostKl) (ENNReal.ofReal (4 * Real.log 2 / 9)) := by
  classical
  have hK (a b : Exp rT) : K.fill a = K.fill b ↔ a = b := (Ectx.fill_injective K).eq_iff
  -- `hf`, `hg`: the left and right reports, read off the configurations (left reports `true` only
  -- at draw `2`, right reports `true` at draws `0, 1`)
  have hf : Measurable fun (ρ : Cfg rT) ↦ decide (ρ = ⟨pl(#2), σ⟩) :=
    measurable_to_bool <| by
      convert measurableSet_singleton (⟨pl(#2), σ⟩ : Cfg rT)
      ext
      simp
  have hg : Measurable fun (ρ : Cfg rT) ↦
      decide (ρ = ⟨K.fill pl(#0), σ'⟩ ∨ ρ = ⟨K.fill pl(#1), σ'⟩) :=
    measurable_to_bool <| by
      convert (measurableSet_singleton (⟨K.fill pl(#1), σ'⟩ : Cfg rT)).insert
        (⟨K.fill pl(#0), σ'⟩ : Cfg rT)
      ext
      simp
  have hsupp {x : Int → Cfg rT} : (unifInt 3 (by norm_num)).map x (x '' Set.Ico 0 3)ᶜ = 0 := by
    rw [Measure.map_apply .of_discrete ((Set.finite_Ico 0 3).image x).measurableSet.compl]
    exact measure_mono_null (fun n hn h ↦ hn ⟨n, h, rfl⟩) (unifInt_compl_Ico _)
  have hμf : ((unifInt 3 (by norm_num)).map fun n ↦ (⟨pl(#int n), σ⟩ : Cfg rT)).map
      (fun ρ ↦ decide (ρ = ⟨pl(#2), σ⟩)) = randResp false := by
    rw [Measure.map_map hf .of_discrete]
    exact map_unifInt_three (by simp) (by simp) (by simp)
  have hνg : ((unifInt 3 (by norm_num)).map fun m ↦ (⟨K.fill pl(#int m), σ'⟩ : Cfg rT)).map
      (fun ρ ↦ decide (ρ = ⟨K.fill pl(#0), σ'⟩ ∨ ρ = ⟨K.fill pl(#1), σ'⟩)) =
      randResp true := by
    rw [Measure.map_map hg .of_discrete]
    exact map_unifInt_three (by simp [hK]) (by simp [hK]) (by simp [hK])
  refine fillKlHead_of_map (ε := ENNReal.ofReal (Real.log 2 / 3)) hf hg
    ((Set.finite_Ico 0 3).image _).measurableSet ((Set.finite_Ico 0 3).image _).measurableSet
    hsupp hsupp (fun c ↦ ?_) stageTwoCostKl ?_ ?_ ?_
  · rw [← Measure.map_apply hf (measurableSet_singleton c),
      ← Measure.map_apply hg (measurableSet_singleton c), hμf, hνg, randResp_singleton,
      randResp_singleton]
    split_ifs <;> norm_num
  · rintro _ _ ⟨n, ⟨hn0, hn3⟩, rfl⟩ ⟨m, ⟨hm0, hm3⟩, rfl⟩ hfg
    rw [Cfg.drawCost_apply]
    interval_cases n <;> interval_cases m <;> simp_all [adaptiveCostKl, rr3Out]
  · rw [hμf, hνg, fill_kl_iff_of_isProbabilityMeasure]
    exact klDivergence_randResp
  · rw [hμf, budget_adaptive]

/-! ## The relational proof -/

section Logic

open Iris Iris.BI Iris.ProofMode

variable {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF] [BudgetCreditGS ℝ≥0∞ GF]
local bi IProp GF

/-- The adaptive program on `false` refines it on `true` at equal pairs of reports, spending
filled KL `(4/9) log 2`: the chain-rule law at the first draw, the canonical law at the second. -/
theorem rrAdaptive_refines_fillKl :
    ⊢ ↯b (ENNReal.ofReal (4 * Real.log 2 / 9)) -∗
      REL[codensity klDivergence.fill] (rrAdaptive (rT := rT) false) << (rrAdaptive true) :
        lrel_prod lrel_bool lrel_bool := by
  iintro Hb
  rel_couple_UU_law BindLaw.fillKl adaptiveCostKl (ENNReal.ofReal (4 * Real.log 2 / 9))
    (ENNReal.isAddLeftRegular_ofReal _) fillKlHead_rr3
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
      (ENNReal.isAddLeftRegular_ofReal _) rr3_coupling_fillKl
    iframe Hb
    iintro %r %r' %hr
    rel_pures
    by_cases hd : r < 2 <;> by_cases hd' : r' < 2 <;>
      simp only [rr3Out, hd, hd', ↓reduceIte, decide_true, decide_false, Bool.not_false,
        Bool.not_true] at hr ⊢ <;> (try simp at hr) <;> rel_pures <;> rel_values

end Logic

/-! ## Adequacy -/

/-- The adaptive program on `false` and on `true` is within filled KL `(4/9) log 2`, as
`AdaptiveFillKl.fill_kl_adaptive` computes for the measures. -/
theorem rrAdaptive_fillKl (σ σ' : State rT) :
    klDivergence.fill (ENNReal.ofReal (4 * Real.log 2 / 9))
      (limExecV ⟨rrAdaptive false, σ⟩) (limExecV ⟨rrAdaptive true, σ'⟩) :=
  approximates_div (GF := MicrometerFunctor rT ℝ≥0∞) (fun _ _ ↦ lrel_prod lrel_bool lrel_bool)
    _ _ σ σ' _ (fun _ _ ↦ lrel_prod_car_eq lrel_bool_car_eq lrel_bool_car_eq)
    fun _ _ ↦ rrAdaptive_refines_fillKl

end RandomizedResponse
end ProbLang
