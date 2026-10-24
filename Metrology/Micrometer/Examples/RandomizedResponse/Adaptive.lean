module

public import Metrology.Micrometer.CouplingRulesLaw
public import Metrology.Micrometer.AdequacyRel
public import Metrology.Code.RandomizedResponseAdaptive
public import Metrology.Couplings.Examples.AdaptiveRenyi
public import Metrology.Couplings.BindLaws
public import Metrology.Couplings.Divergences.Power
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Adaptive randomized response, with the escort law

`rrAdaptive_renyi`: adaptive randomized response is within Rényi-2 budget `log (19/12)`, by the
escort law. -/

open MeasureTheory ProbabilityTheory GradedLifting GradedDivergence AdaptiveRenyi
open scoped ENNReal

namespace ProbLang.RandomizedResponse

open MeasureTheory.Measure (ext_iff_singleton map_apply map_map id_comp)
open Set (Ico indicator finite_Ico)
open Finset (filter_insert filter_singleton)
open ENNReal (ofReal div_eq_inv_mul isAddLeftRegular_ofReal)
open Real (log)
open BindLaw (escort)
open Cfg (drawCost drawCost_apply)

/-! ## The second round: one `rr3` draw at `log (3/2)` -/

/-- The report of `rr3 b` as a function of its draw on `[0, 3)`: `b` on `0, 1` and `!b` on `2`. -/
def rr3Out (b : Bool) (r : Int) : Bool := if r < 2 then b else !b

/-- A draw from `[0, 3)` read by `h`, which takes the value `d` at two of the three draws, is
randomized response on `d`. -/
theorem map_unifInt_three {h : Int → Bool} {d : Bool} (h0 : h 0 = d) (h1 : h 1 = d)
    (h2 : h 2 = !d) : (unifInt 3 (by norm_num)).map h = randResp d := by
  refine ext_iff_singleton.2 fun c ↦ ?_
  rw [map_apply .of_discrete (measurableSet_singleton c), unifInt_apply,
    show Finset.Ico (0 : Int) 3 = {0, 1, 2} by decide]
  cases d <;> cases c <;> simp_all [randResp, indicator, filter_insert,
    filter_singleton, div_eq_inv_mul, mul_comm]

/-- The second round couples along equal reports at `log (3/2)`. -/
theorem rr3_coupling :
    (codensity (renyiDivergence 2)).Rel (ofReal (log (3 / 2)))
      (fun r r' ↦ rr3Out false r = rr3Out true r') (unifInt 3 (by norm_num))
      (unifInt 3 (by norm_num)) :=
  codensity_renyi_rel_of_map .of_discrete .of_discrete <| by
    rw [map_unifInt_three rfl rfl rfl, map_unifInt_three rfl rfl rfl]
    exact renyiDivergence_randResp

/-! ## The first round: the escort head at `log (19/12)` -/

/-- The budget handed to the continuation after first draws `n`, `m`: the second round's cost
`stageTwoCost` of their common report, or `⊤` if the reports differ. -/
noncomputable def adaptiveCost (n m : Int) : ℝ≥0∞ :=
  if rr3Out false n = rr3Out true m then stageTwoCost (rr3Out false n) else ⊤

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

open scoped Classical in
/-- The left report of the first draws, read off the configuration: `true` only at draw `2`. -/
theorem measurable_reportL (σ : State rT) :
    Measurable fun (ρ : Cfg rT) ↦ decide (ρ = ⟨pl(#2), σ⟩) :=
  measurable_to_bool <| by
    convert measurableSet_singleton (⟨pl(#2), σ⟩ : Cfg rT)
    ext
    simp

open scoped Classical in
/-- The right report of the first draws, read off the configuration: `true` at draws `0, 1`. -/
theorem measurable_reportR (K : Ectx rT) (σ' : State rT) :
    Measurable fun (ρ : Cfg rT) ↦
      decide (ρ = ⟨K.fill pl(#0), σ'⟩ ∨ ρ = ⟨K.fill pl(#1), σ'⟩) :=
  measurable_to_bool <| by
    convert (measurableSet_singleton (⟨K.fill pl(#1), σ'⟩ : Cfg rT)).insert
      (⟨K.fill pl(#0), σ'⟩ : Cfg rT)
    ext
    simp

/-- The first draws, mapped into configurations by `x`, are supported on the image of `[0, 3)`. -/
theorem map_unifInt_three_compl_image (x : Int → Cfg rT) :
    (unifInt 3 (by norm_num)).map x (x '' Ico 0 3)ᶜ = 0 := by
  rw [map_apply .of_discrete ((finite_Ico 0 3).image x).measurableSet.compl]
  exact measure_mono_null (fun n hn h ↦ hn ⟨n, h, rfl⟩) (unifInt_compl_Ico _)

open scoped Classical in
/-- The left report of the first draws is randomized response on `false`. -/
theorem map_reportL (σ : State rT) :
    ((unifInt 3 (by norm_num)).map fun n ↦ (⟨pl(#int n), σ⟩ : Cfg rT)).map
      (fun ρ ↦ decide (ρ = ⟨pl(#2), σ⟩)) = randResp false := by
  rw [map_map (measurable_reportL σ) .of_discrete]
  exact map_unifInt_three (by simp) (by simp) (by simp)

open scoped Classical in
/-- The right report of the first draws is randomized response on `true`. -/
theorem map_reportR (K : Ectx rT) (σ' : State rT) :
    ((unifInt 3 (by norm_num)).map fun m ↦ (⟨K.fill pl(#int m), σ'⟩ : Cfg rT)).map
      (fun ρ ↦ decide (ρ = ⟨K.fill pl(#0), σ'⟩ ∨ ρ = ⟨K.fill pl(#1), σ'⟩)) = randResp true := by
  have hK (a b) : K.fill a = K.fill b ↔ a = b := (Ectx.fill_injective K).eq_iff
  rw [map_map (measurable_reportR K σ') .of_discrete]
  exact map_unifInt_three (by simp [hK]) (by simp [hK]) (by simp [hK])

/-- The first draws, as configurations, form an escort head at `log (19/12)` with continuation
cost `adaptiveCost`. -/
theorem escortHead_rr3 (K : Ectx rT) (σ σ' : State rT) :
    (escort 2).head ((unifInt 3 (by norm_num)).map fun n ↦ (⟨pl(#int n), σ⟩ : Cfg rT))
      ((unifInt 3 (by norm_num)).map fun m ↦ (⟨K.fill pl(#int m), σ'⟩ : Cfg rT))
      (drawCost σ σ' K adaptiveCost) (ofReal (log (19 / 12))) := by
  classical
  have hK (a b) : K.fill a = K.fill b ↔ a = b := (Ectx.fill_injective K).eq_iff
  refine escortHead_of_map (measurable_reportL σ) (measurable_reportR K σ')
    ((finite_Ico 0 3).image _).measurableSet ((finite_Ico 0 3).image _).measurableSet
    (map_unifInt_three_compl_image _) (map_unifInt_three_compl_image _) stageTwoCost ?_ ?_
  · rintro _ _ ⟨n, ⟨hn0, hn3⟩, rfl⟩ ⟨m, ⟨hm0, hm3⟩, rfl⟩ hfg
    rw [drawCost_apply]
    interval_cases n <;> interval_cases m <;> simp_all [adaptiveCost, rr3Out]
  · rw [map_reportL, map_reportR]
    simpa [id_comp] using renyiDivergence_randResp_escort

/-! ## The relational proof -/

open Iris Iris.BI Iris.ProofMode

variable {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF] [BudgetCreditGS ℝ≥0∞ GF]
local bi IProp GF

/-- The adaptive program on `false` refines it on `true` at equal pairs of reports, spending
`log (19/12)`: the escort law at the first draw, the canonical law at the second. -/
theorem rrAdaptive_refines :
    ⊢ ↯b (ofReal (log (19 / 12))) -∗
      REL[codensity (renyiDivergence 2)] (rrAdaptive (rT := rT) false) << (rrAdaptive true) :
        lrel_prod lrel_bool lrel_bool := by
  iintro Hb
  rel_couple_UU_law (escort 2) adaptiveCost (ofReal (log (19 / 12)))
    (isAddLeftRegular_ofReal _) escortHead_rr3
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
      (isAddLeftRegular_ofReal _) rr3_coupling
    iframe Hb
    iintro %r %r' %hr
    rel_pures
    by_cases hd : r < 2 <;> by_cases hd' : r' < 2 <;>
      simp only [rr3Out, hd, hd', ↓reduceIte, decide_true, decide_false, Bool.not_false,
        Bool.not_true] at hr ⊢ <;> (try simp at hr) <;> rel_pures <;> rel_values

/-! ## Adequacy -/

/-- The adaptive program on `false` and on `true` is within Rényi budget `log (19/12)` at
order `2`, as `renyiDivergence_adaptive` computes for the measures. -/
theorem rrAdaptive_renyi (σ σ' : State rT) :
    renyiDivergence 2 (ofReal (log (19 / 12)))
      (limExecV ⟨rrAdaptive false, σ⟩) (limExecV ⟨rrAdaptive true, σ'⟩) :=
  approximates_div (GF := MicrometerFunctor rT ℝ≥0∞) (fun _ _ ↦ lrel_prod lrel_bool lrel_bool)
    _ _ σ σ' _ (fun _ _ ↦ lrel_prod_car_eq lrel_bool_car_eq lrel_bool_car_eq)
    fun _ _ ↦ rrAdaptive_refines

end ProbLang.RandomizedResponse
