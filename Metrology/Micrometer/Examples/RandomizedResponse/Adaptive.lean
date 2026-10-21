module

public import Metrology.Micrometer.CouplingRulesLaw
public import Metrology.Micrometer.AdequacyRel
public import Metrology.Code.RandomizedResponseAdaptive
public import Metrology.Couplings.Examples.AdaptiveRenyi
public import Metrology.Couplings.BindLaws
public import Metrology.Couplings.Divergences.Power
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Adaptive randomized response, with the escort law

`rrAdaptive_renyi`: adaptive randomized response is within Rényi-2 budget `log (19/12)`, not
`log (9/4)`, as the escort law pays the second round's cost on average (`AdaptiveRenyi`). -/

open MeasureTheory ProbabilityTheory GradedLifting GradedDivergence AdaptiveRenyi
open scoped ENNReal

namespace ProbLang
namespace RandomizedResponse

/-! ## The second round: one `rr3` draw at `log (3/2)` -/

/-- The report of `rr3 b` as a function of its draw. -/
def rr3Out (b : Bool) (r : Int) : Bool := if r < 2 then b else !b

/-- A draw from `[0, 3)` read by `h`, which takes the value `d` at two of the three draws, is
randomized response on `d`. -/
theorem map_unifInt_three {h : Int → Bool} {d : Bool} (h0 : h 0 = d) (h1 : h 1 = d)
    (h2 : h 2 = !d) : (unifInt 3 (by norm_num)).map h = randResp d := by
  refine Measure.ext_iff_singleton.2 fun c ↦ ?_
  rw [Measure.map_apply .of_discrete (measurableSet_singleton c), unifInt_apply,
    show Finset.Ico (0 : Int) 3 = {0, 1, 2} by decide]
  cases d <;> cases c <;> simp_all [randResp, Set.indicator, Finset.filter_insert,
    Finset.filter_singleton, ENNReal.div_eq_inv_mul, mul_comm]

/-- The second round couples along equal reports at `log (3/2)`. -/
theorem rr3_coupling :
    (codensity (renyiDivergence 2)).Rel (ENNReal.ofReal (Real.log (3 / 2)))
      (fun r r' ↦ rr3Out false r = rr3Out true r') (unifInt 3 (by norm_num))
      (unifInt 3 (by norm_num)) :=
  codensity_renyi_rel_of_map .of_discrete .of_discrete <| by
    rw [map_unifInt_three (d := false) rfl rfl rfl, map_unifInt_three (d := true) rfl rfl rfl]
    exact renyiDivergence_randResp

/-! ## The first round: the escort head at `log (19/12)` -/

/-- The budget handed to the continuation after first draws `n`, `m`: the second round's cost
`stageTwoCost` of their common report, or `⊤` if the reports differ. -/
noncomputable def adaptiveCost (n m : Int) : ℝ≥0∞ :=
  if rr3Out false n = rr3Out true m then stageTwoCost (rr3Out false n) else ⊤

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

/-- The first draws, as configurations, form an escort head at `log (19/12)` with continuation
cost `adaptiveCost`: map the draws to reports and use `renyiDivergence_randResp_escort`. -/
theorem escortHead_rr3 (K : Ectx rT) (σ σ' : State rT) :
    (BindLaw.escort 2).head ((unifInt 3 (by norm_num)).map fun n ↦ (⟨pl(#int n), σ⟩ : Cfg rT))
      ((unifInt 3 (by norm_num)).map fun m ↦ (⟨K.fill pl(#int m), σ'⟩ : Cfg rT))
      (Cfg.drawCost σ σ' K adaptiveCost) (ENNReal.ofReal (Real.log (19 / 12))) := by
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
  refine escortHead_of_map hf hg ((Set.finite_Ico 0 3).image _).measurableSet
    ((Set.finite_Ico 0 3).image _).measurableSet hsupp hsupp stageTwoCost ?_ ?_
  · rintro _ _ ⟨n, ⟨hn0, hn3⟩, rfl⟩ ⟨m, ⟨hm0, hm3⟩, rfl⟩ hfg
    rw [Cfg.drawCost_apply]
    interval_cases n <;> interval_cases m <;> simp_all [adaptiveCost, rr3Out]
  · rw [Measure.map_map hf .of_discrete, Measure.map_map hg .of_discrete,
      map_unifInt_three (d := false) (by simp) (by simp) (by simp),
      map_unifInt_three (d := true) (by simp [hK]) (by simp [hK]) (by simp [hK])]
    simpa [Measure.id_comp] using renyiDivergence_randResp_escort

/-! ## The relational proof -/

section Logic

open Iris Iris.BI Iris.ProofMode

/-- The adaptive program on `false` refines it on `true` at equal pairs of reports, spending
`log (19/12)`: the escort law at the first draw, the canonical law at the second. -/
theorem rrAdaptive_refines {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF]
    [BudgetCreditGS ℝ≥0∞ GF] :
    ⊢@{IProp GF} ↯b (ENNReal.ofReal (Real.log (19 / 12))) -∗
      REL[codensity (renyiDivergence 2)] (rrAdaptive (rT := rT) false) << (rrAdaptive true) :
        lrel_prod lrel_bool lrel_bool := by
  iintro Hb
  rel_couple_UU_law (BindLaw.escort 2) adaptiveCost (ENNReal.ofReal (Real.log (19 / 12)))
    (ENNReal.isAddLeftRegular_ofReal _) escortHead_rr3
  iframe Hb
  iintro %n %m %hR Hb
  rel_pures
  by_cases hn : n < 2 <;> by_cases hm : m < 2 <;>
    simp only [adaptiveCost, rr3Out, hn, hm, ↓reduceIte, decide_true, decide_false,
      Bool.not_false, Bool.not_true, stageTwoCost, Bool.cond_true, Bool.cond_false] at hR ⊢ <;>
    simp at hR <;> rel_pures
  -- mismatched reports close by `hR`; first goal: report `false`, no second round; second goal:
  -- report `true`, spend the remaining `log (3/2)` on the second draw
  · rel_values
  · rel_couple_UU_spend (fun r r' ↦ rr3Out false r = rr3Out true r') _
      (ENNReal.isAddLeftRegular_ofReal _) rr3_coupling
    iframe Hb
    iintro %r %r' %hr
    rel_pures
    by_cases hd : r < 2 <;> by_cases hd' : r' < 2 <;>
      simp only [rr3Out, hd, hd', ↓reduceIte, decide_true, decide_false, Bool.not_false,
        Bool.not_true] at hr ⊢ <;> (try simp at hr) <;> rel_pures <;> rel_values

end Logic

/-! ## Adequacy -/

/-- The adaptive program on `false` and on `true` is within Rényi budget `log (19/12)` at
order `2`, as `AdaptiveRenyi.renyiDivergence_adaptive` computes for the measures. -/
theorem rrAdaptive_renyi (σ σ' : State rT) :
    renyiDivergence 2 (ENNReal.ofReal (Real.log (19 / 12)))
      (limExecV ⟨rrAdaptive false, σ⟩) (limExecV ⟨rrAdaptive true, σ'⟩) :=
  approximates_div (GF := MicrometerFunctor rT ℝ≥0∞) (fun _ _ ↦ lrel_prod lrel_bool lrel_bool)
    _ _ σ σ' _ (fun _ _ ↦ lrel_prod_car_eq lrel_bool_car_eq lrel_bool_car_eq)
    fun _ _ ↦ rrAdaptive_refines

end RandomizedResponse
end ProbLang
