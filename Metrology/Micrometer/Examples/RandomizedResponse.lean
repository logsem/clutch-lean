module

public import Metrology.Micrometer.Adequacy
public import Metrology.Micrometer.AdequacyRel
public import Metrology.Micrometer.CouplingRules
public import Metrology.Micrometer.WpTactics
public import Metrology.Code.RandomizedResponse
public import Metrology.Couplings.Divergences.Dp
public import Metrology.Couplings.Divergences.Mechanism
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Randomized response is `ln 3`-differentially private

Port of clutch-dp's `examples/randomized_response.v`. -/

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting
open GradedDivergence (dp codensity expBudget)
open scoped ENNReal NNReal

namespace ProbLang
namespace RandomizedResponse

/-! ## The coupling of the two draws -/

section Coupling

open MeasureTheory

/-- The reported bit as a function of the draw. -/
def rrOut (b : Bool) (r : Int) : Bool := if r < 3 then b else !b

theorem unifInt_four_singleton {k : Int} (h0 : 0 ≤ k) (h4 : k < 4) :
    unifInt 4 (by norm_num) {k} = 4⁻¹ := by
  rw [unifInt, PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    PMF.uniformOfFinset_apply_of_mem _ (Finset.mem_Ico.2 ⟨h0, h4⟩)]
  rfl

/-- Draws `0` and `3` report different bits, so each report is hit by one and missed by the
other. -/
theorem rrOut_zero_three (b c : Bool) :
    rrOut b 0 = c ∧ rrOut b 3 ≠ c ∨ rrOut b 3 = c ∧ rrOut b 0 ≠ c := by
  revert b c
  decide

/-- One fiber of the reported bit misses a draw, so it has mass at most `3/4`. -/
theorem rrOut_fiber_le (b c : Bool) : unifInt 4 (by norm_num) (rrOut b ⁻¹' {c}) ≤ 1 - 4⁻¹ := by
  obtain ⟨k, hk0, hk4, hk⟩ : ∃ k, 0 ≤ k ∧ k < 4 ∧ rrOut b k ≠ c := by
    rcases rrOut_zero_three b c with ⟨-, h⟩ | ⟨-, h⟩
    · exact ⟨3, by norm_num, by norm_num, h⟩
    · exact ⟨0, by norm_num, by norm_num, h⟩
  calc _ ≤ unifInt 4 (by norm_num) {k}ᶜ := measure_mono fun r hr hrk ↦ hk (hrk ▸ hr)
    _ = 1 - 4⁻¹ := by
        rw [prob_compl_eq_one_sub (measurableSet_singleton k), unifInt_four_singleton hk0 hk4]

/-- Every fiber of the reported bit contains a draw, so it has mass at least `1/4`. -/
theorem rrOut_fiber_ge (b c : Bool) : 4⁻¹ ≤ unifInt 4 (by norm_num) (rrOut b ⁻¹' {c}) := by
  obtain ⟨k, hk0, hk4, hk⟩ : ∃ k, 0 ≤ k ∧ k < 4 ∧ rrOut b k = c := by
    rcases rrOut_zero_three b c with ⟨h, -⟩ | ⟨h, -⟩
    · exact ⟨0, by norm_num, by norm_num, h⟩
    · exact ⟨3, by norm_num, by norm_num, h⟩
  rw [← unifInt_four_singleton hk0 hk4]
  exact measure_mono (Set.singleton_subset_iff.2 hk)

theorem one_sub_quarter_le : (1 - 4⁻¹ : ℝ≥0∞) ≤ 3 * 4⁻¹ := by
  rw [tsub_le_iff_right, ← add_one_mul, show (3 + 1 : ℝ≥0∞) = 4 by norm_num,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

theorem expBudget_log_three : expBudget (ENNReal.ofReal (Real.log 3)) = 3 := by
  rw [GradedDivergence.expBudget_of_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (Real.log_nonneg (by norm_num)), Real.exp_log (by norm_num)]
  norm_num

/-- The privacy budget `(ln 3, 0)`. -/
noncomputable abbrev budget : ℝ≥0∞ × ℝ≥0∞ := (ENNReal.ofReal (Real.log 3), 0)

/-- The budget `(ln 3, 0)` is finite, so it can be spent. -/
theorem isAddLeftRegular_budget : IsAddLeftRegular budget := fun x y h ↦
  Prod.ext (ENNReal.isAddLeftRegular_of_ne_top ENNReal.ofReal_ne_top (congrArg Prod.fst h))
    (by simpa using congrArg Prod.snd h)

/-- The two draws couple along equal reports at privacy budget `(ln 3, 0)`. -/
theorem rr_coupling (b b' : Bool) :
    (codensity dp).Rel budget (fun r r' ↦ rrOut b r = rrOut b' r')
      (unifInt 4 (by norm_num)) (unifInt 4 (by norm_num)) := by
  refine GradedDivergence.codensity_dp_of_fiber .of_discrete .of_discrete fun c ↦ ?_
  rw [expBudget_log_three]
  calc _ ≤ 1 - 4⁻¹ := rrOut_fiber_le b c
    _ ≤ 3 * 4⁻¹ := one_sub_quarter_le
    _ ≤ _ := by gcongr; exact rrOut_fiber_ge b' c

end Coupling

/-! ## The program logic proof -/

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

section Tail

variable {GF : BundledGFunctors} [MicrometerGS rT .hasNoLC GF]
  [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF]

/-- The program reports `bif d then b else !b`. -/
theorem wp_report (d b : Bool) (Φ : Val rT → IProp GF) :
    Φ (.bool (bif d then b else !b)) ⊢
      wp (codensity dp) ⊤
        pl(if #(.bool d) then #(.bool b) else ~#(.bool b)) Φ := by
  cases d
  all_goals cases b
  all_goals
    simp only [Bool.cond_false, Bool.cond_true, Bool.not_false, Bool.not_true]
    iintro H
    wp_pures
    wp_value
    imodintro
    iexact H

/-- The spec reports `bif d then b else !b`, under any evaluation context. -/
theorem tp_report_fill (K : Ectx rT) (d b : Bool) (e : Exp rT) (Φ : Val rT → IProp GF) :
    ⤇ K.fill pl(if #(.bool d) then #(.bool b) else ~#(.bool b)) ∗
      (⤇ K.fill pl(#(.bool (bif d then b else !b))) -∗
        wp (codensity dp) ⊤ e Φ) ⊢
      wp (codensity dp) ⊤ e Φ := by
  cases d
  all_goals cases b
  all_goals
    simp only [Bool.cond_false, Bool.cond_true, Bool.not_false, Bool.not_true]
    iintro ⟨Hj, H⟩
    tp_pures
    iapply H
    iexact Hj

/-- The spec reports `bif d then b else !b`. -/
theorem tp_report (d b : Bool) (e : Exp rT) (Φ : Val rT → IProp GF) :
    ⤇ pl(if #(.bool d) then #(.bool b) else ~#(.bool b)) ∗
      (⤇ pl(#(.bool (bif d then b else !b))) -∗ wp (codensity dp) ⊤ e Φ) ⊢
      wp (codensity dp) ⊤ e Φ :=
  tp_report_fill [] d b e Φ

end Tail

theorem wp_rr {GF : BundledGFunctors} [MicrometerGS rT .hasNoLC GF]
    [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF] (b b' : Bool) :
    ⊢@{IProp GF} ⤇ rr (rT := rT) b' -∗ ↯b budget -∗
      wp (codensity dp) ⊤ (rr b)
        (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜v = v'⌝)) := by
  iintro Hj Hb
  simp only [rr, Exp.close, Exp.closeRec, ↓reduceIte]
  wp_bind (pl% rand(#4, #.unit))
  tp_bind (pl% rand(#4, #.unit))
  iapply wp_couple_rand_rand_spend 4 (by norm_num) (fun r r' ↦ rrOut b r = rrOut b' r') budget
    isAddLeftRegular_budget (rr_coupling b b')
  iframe Hj Hb
  iintro %r %r' %hR Hj
  wp_pures
  tp_pures
  iapply tp_report
  iframe Hj
  iintro Hj
  iapply wp_report
  iexists .bool (bif decide (r' < 3) then b' else !b')
  ihave Hj := specProgFrag_reshape (e₁ := pl(#(.bool _))) (e₂ := Exp.ofVal (.bool _)) rfl $$ Hj
  iframe Hj
  ipureintro
  exact congrArg Val.bool (by simpa [rrOut] using hR)

/-! ## The relational proof -/

/-- Randomized response refines itself at equal reports, spending the budget `(ln 3, 0)`. -/
theorem rr_refines {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF]
    [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF] (b b' : Bool) :
    ⊢@{IProp GF} ↯b budget -∗
      REL[codensity dp] (rr (rT := rT) b) << (rr b') : lrel_bool := by
  iintro Hb
  iunfold refines
  iintro %K %ε Hj Hna Herr %Hpos
  simp only [rr, Exp.close, Exp.closeRec, ↓reduceIte]
  wp_bind (pl% rand(#4, #.unit))
  tp_bind (pl% rand(#4, #.unit))
  iapply wp_couple_rand_rand_spend 4 (by norm_num) (fun r r' ↦ rrOut b r = rrOut b' r') budget
    isAddLeftRegular_budget (rr_coupling b b')
  iframe Hj Hb
  iintro %r %r' %hR Hj
  wp_pures
  tp_pures
  iapply tp_report_fill
  iframe Hj
  iintro Hj
  iapply wp_report
  iexists .bool (bif decide (r' < 3) then b' else !b'), ε
  iframe Hj Hna Herr %Hpos
  iunfold lrel_bool
  iexists _
  ipureintro
  exact ⟨congrArg Val.bool (by simpa [rrOut] using hR), rfl⟩

/-! ## Adequacy: exit the logic -/

theorem rr_dp_of (GF : BundledGFunctors) [AppPreGS rT GF] [SpecPreGS rT GF]
    [BudgetCreditPreGS (ℝ≥0∞ × ℝ≥0∞) GF] [InvGpreS GF] (b b' : Bool) (σ σ' : State rT) :
    dp budget (limExecV ⟨rr b, σ⟩) (limExecV ⟨rr b', σ'⟩) :=
  wp_adequacy_div (GF := GF) (L := codensity dp) _ _ σ σ' budget
    fun _ _ ↦ wp_rr b b'

/-- `rr_dp_of`, through the refinement `rr_refines`. -/
theorem rr_dp_of_refines (GF : BundledGFunctors) [RefinesPreGS rT (ℝ≥0∞ × ℝ≥0∞) GF]
    (b b' : Bool) (σ σ' : State rT) :
    dp budget (limExecV ⟨rr b, σ⟩) (limExecV ⟨rr b', σ'⟩) := by
  refine approximates_div (GF := GF) (L := codensity dp)
    (fun _ _ ↦ lrel_bool) _ _ σ σ' budget ?_ ?_
  · intro _ _ v v'
    iunfold lrel_bool
    iintro ⟨%c, %⟨rfl, rfl⟩⟩
    ipureintro
    rfl
  · intro _ _
    iintro Hb
    iapply rr_refines b b' $$ Hb

/-- Randomized response is `ln 3`-differentially private, for any two private bits
(clutch-dp's `randomized_response.v`). -/
theorem rr_dp (b b' : Bool) (σ σ' : State rT) :
    dp budget (limExecV ⟨rr b, σ⟩) (limExecV ⟨rr b', σ'⟩) :=
  rr_dp_of (MicrometerFunctor rT (ℝ≥0∞ × ℝ≥0∞)) b b' σ σ'

/-- Every event is at most three times as likely under one private bit as under the other. -/
theorem rr_event_le (b b' : Bool) (σ σ' : State rT) (S : Set (Exp rT)) (hS : MeasurableSet S) :
    limExecV ⟨rr b, σ⟩ S ≤ 3 * limExecV ⟨rr b', σ'⟩ S := by
  have h := (GradedDivergence.dp_iff ENNReal.ofReal_ne_top).1 (rr_dp b b' σ σ') S hS
  rwa [expBudget_log_three, add_zero] at h

/-- Randomized response as a mechanism on private bits, started from state `σ`. -/
noncomputable def rrMech (σ : State rT) : Mechanism Bool (Exp rT) :=
  ⟨fun b ↦ limExecV ⟨rr b, σ⟩, .of_discrete⟩

/-- Randomized response is `(ln 3, 0)`-differentially private for any two bits (Def. 2.1). -/
theorem rr_DP (σ : State rT) : (rrMech σ).DP ⊤ (ENNReal.ofReal (Real.log 3)) 0 :=
  fun b b' _ ↦ rr_dp b b' σ σ

end RandomizedResponse
end ProbLang
