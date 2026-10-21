module

public import Metrology.Micrometer.AdequacyRel
public import Metrology.Micrometer.Mechanism
public import Metrology.Micrometer.CouplingRules
public import Metrology.Micrometer.WpTactics
public import Metrology.Micrometer.RelTactics
public import Metrology.Code.RandomizedResponseLoop
public import Metrology.Couplings.Divergences.Dp
public import Metrology.Couplings.Divergences.FDivFinite
public import Metrology.Couplings.Divergences.Renyi
import Metrology.ProbLang.Syntax.Notation
import Mathlib.Algebra.Regular.Prod
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Randomized response in any lifting

Given `RRCoupling L c`, one round and the `k`-round loop refine themselves in any graded lifting,
so the loop is `k • c`-private in every divergence `L` is sound for (`rrCount_isPrivate`). -/

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting
open GradedDivergence (expBudget expBudget_of_ne_top)
open scoped ENNReal

namespace ProbLang.RandomizedResponse

/-! ## The reported bit and its arithmetic

The facts the divergence files feed into `RRCoupling`: the fiber bound `rrOut_fiber_le_three`
and the moment `fDiv_rrOut`. -/

section Distribution

open MeasureTheory ProbabilityTheory

/-- The reported bit as a function of the draw. -/
def rrOut (b : Bool) (r : Int) : Bool := if r < 3 then b else !b

/-- The draw of one round, uniform on `{0, 1, 2, 3}`. -/
noncomputable abbrev draw : Measure Int :=
  unifInt 4 (by norm_num)

/-- Each of the four draws has mass `1/4`. -/
theorem draw_singleton {k : Int} (h0 : 0 ≤ k) (h4 : k < 4) : draw {k} = 4⁻¹ := by
  rw [draw, unifInt, PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    PMF.uniformOfFinset_apply_of_mem _ (Finset.mem_Ico.2 ⟨h0, h4⟩)]
  rfl

/-- One round reports its bit with probability `3/4`. -/
theorem map_rrOut_singleton (b c : Bool) :
    draw.map (rrOut b) {c} = if b = c then 3 / 4 else 1 / 4 := by
  rw [Measure.map_apply .of_discrete (measurableSet_singleton c), unifInt_apply,
    show Finset.Ico (0 : Int) 4 = {0, 1, 2, 3} by decide]
  cases b <;> cases c <;> norm_num [rrOut, Set.indicator, Finset.filter_insert,
    Finset.filter_singleton, ENNReal.div_eq_inv_mul, mul_comm]

/-- Draws `0` and `3` report different bits, so each report is hit by one and missed by the
other. -/
theorem rrOut_zero_three (b c : Bool) :
    rrOut b 0 = c ∧ rrOut b 3 ≠ c ∨ rrOut b 3 = c ∧ rrOut b 0 ≠ c := by
  decide +revert

/-- One fiber of the reported bit misses a draw, so it has mass at most `3/4`. -/
theorem rrOut_fiber_le (b c : Bool) : draw (rrOut b ⁻¹' {c}) ≤ 1 - 4⁻¹ := by
  obtain ⟨k, hk0, hk4, hk⟩ : ∃ k, 0 ≤ k ∧ k < 4 ∧ rrOut b k ≠ c := by
    rcases rrOut_zero_three b c with ⟨-, h⟩ | ⟨-, h⟩
    · exact ⟨3, by norm_num, by norm_num, h⟩
    · exact ⟨0, by norm_num, by norm_num, h⟩
  calc _ ≤ draw {k}ᶜ := measure_mono fun r hr hrk ↦ hk (hrk ▸ hr)
    _ = 1 - 4⁻¹ := by
        rw [prob_compl_eq_one_sub (measurableSet_singleton k), draw_singleton hk0 hk4]

/-- Every fiber of the reported bit contains a draw, so it has mass at least `1/4`. -/
theorem rrOut_fiber_ge (b c : Bool) : 4⁻¹ ≤ draw (rrOut b ⁻¹' {c}) := by
  obtain ⟨k, hk0, hk4, hk⟩ : ∃ k, 0 ≤ k ∧ k < 4 ∧ rrOut b k = c := by
    rcases rrOut_zero_three b c with ⟨h, -⟩ | ⟨h, -⟩
    · exact ⟨0, by norm_num, by norm_num, h⟩
    · exact ⟨3, by norm_num, by norm_num, h⟩
  rw [← draw_singleton hk0 hk4]
  exact measure_mono (Set.singleton_subset_iff.2 hk)

/-- Each fiber's mass under one bit is at most three times its mass under the other. -/
theorem rrOut_fiber_le_three (b b' c : Bool) :
    draw (rrOut b ⁻¹' {c}) ≤ 3 * draw (rrOut b' ⁻¹' {c}) :=
  calc _ ≤ 1 - 4⁻¹ := rrOut_fiber_le b c
    _ ≤ 3 * 4⁻¹ := by
        rw [tsub_le_iff_right, ← add_one_mul, show (3 + 1 : ℝ≥0∞) = 4 by norm_num,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
    _ ≤ _ := by gcongr; exact rrOut_fiber_ge b' c

/-- The `α`-th moment between rounds on different bits is `(3^α + 3^{1-α}) / 4`. -/
theorem fDiv_rrOut {α : ℝ} (hα : 1 < α) (b : Bool) :
    fDiv (· ^ α) (draw.map (rrOut b)) (draw.map (rrOut !b)) = ((3 ^ α + 3 ^ (1 - α)) / 4 : ℝ) := by
  rw [fDiv_eq_sum (convexOn_rpow hα.le) (continuousWithinAt_rpow_zero (by linarith)),
    Fintype.sum_bool, map_rrOut_singleton, map_rrOut_singleton, map_rrOut_singleton,
    map_rrOut_singleton, Real.rpow_sub (by norm_num), Real.rpow_one]
  -- the two perspectives are `(3/4)^α (1/4)^{1-α}` and `(1/4)^α (3/4)^{1-α}`; move to ℝ and
  -- clear denominators
  cases b
  all_goals
    norm_num [persp_rpow_of_pos, Real.div_rpow]
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff]
    field_simp
  ring

end Distribution

/-! ## One round, in any lifting -/

/-- `L` couples the draws of rounds on any two bits along equal reports at budget `c`.
This is the one fact each divergence file proves. -/
def RRCoupling {B : Type} [Zero B] [Top B] (L : GradedLifting.{0} B) (c : B) : Prop :=
  ∀ b b', L.Rel c (fun r r' ↦ rrOut b r = rrOut b' r') draw draw

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
  {B : Type} [AddCommMonoid B] [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B}
  [L.IsLawful] [L.IsTopAbsorbing]

section Rel

variable {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF] [BudgetCreditGS B GF]
local bi IProp GF

/-- One round refines itself at equal reports, spending `↯b c`, given a coupling of the two draws
at `c`. -/
theorem rr_refines_of [CanonicallyOrderedAdd B] [L.IsSupportLocal] [L.HasBind] (c : B)
    (hc : IsAddLeftRegular c)
    (hcpl : RRCoupling L c) (b b' : Bool) :
    ⊢ ↯b c -∗ REL[L] (rr (rT := rT) b) << (rr b') : lrel_bool := by
  iintro Hb
  rel_couple_UU_spend (fun r r' ↦ rrOut b r = rrOut b' r') c hc (hcpl b b')
  iframe Hb
  iintro %r %r' %hR
  rel_pures
  -- four branch combinations; in each, hR equates the two returned bits
  by_cases hd : r < 3 <;> by_cases hd' : r' < 3 <;>
    simp only [rrOut, hd, hd', ↓reduceIte, decide_true, decide_false] at hR ⊢ <;>
    rel_pures <;> rw [hR] <;> rel_values

end Rel

/-! ## The same round, against a spec -/

section Wp

variable {GF : BundledGFunctors} [MicrometerGS rT .hasNoLC GF] [BudgetCreditGS B GF]

/-- The program reports `bif d then b else !b`. -/
theorem wp_report (d b : Bool) (Φ : Val rT → IProp GF) :
    Φ (.bool (bif d then b else !b)) ⊢
      wp L ⊤ pl(if #bool d then #b else ~#b) Φ := by
  cases d <;> cases b <;>
    simp only [Bool.cond_false, Bool.cond_true, Bool.not_false, Bool.not_true] <;>
    iintro H <;> wp_pures <;> wp_value <;> imodintro <;> iexact H

/-- The spec reports `bif d then b else !b`, under any evaluation context. -/
theorem tp_report (K : Ectx rT) (d b : Bool) (e : Exp rT) (Φ : Val rT → IProp GF) :
    ⤇ K.fill pl(if #bool d then #b else ~#b) ∗
      (⤇ K.fill pl(#bool (bif d then b else !b)) -∗ wp L ⊤ e Φ) ⊢ wp L ⊤ e Φ := by
  cases d <;> cases b <;>
    simp only [Bool.cond_false, Bool.cond_true, Bool.not_false, Bool.not_true] <;>
    iintro ⟨Hj, H⟩ <;> tp_pures <;> iapply H <;> iexact Hj

/-- One round against the spec in context `K`, spending `↯b c` given a coupling of the two
draws at `c`: both sides report the same bit. -/
theorem wp_rr_of [CanonicallyOrderedAdd B] [L.IsSupportLocal] [L.HasBind] (c : B)
    (hc : IsAddLeftRegular c)
    (hcpl : RRCoupling L c)
    (K : Ectx rT) (b b' : Bool) (Φ : Val rT → IProp GF) :
    ⤇ K.fill (rr b') ∗ ↯b c ∗ (∀ d, ⤇ K.fill pl(#bool d) -∗ Φ (.bool d)) ⊢
      wp L ⊤ (rr b) Φ := by
  iintro ⟨Hj, Hb, H⟩
  -- unfold rr's let binder so wp_bind/tp_bind can focus the draw
  simp only [rr, Exp.close, Exp.closeRec, ↓reduceIte]
  wp_bind (pl% rand(#4, #()))
  tp_bind (pl% rand(#4, #()))
  iapply wp_couple_rand_rand_spend 4 (by norm_num) _ c hc (hcpl b b')
  iframe Hj Hb
  iintro %r %r' %hR Hj
  wp_pures
  tp_pures
  iapply tp_report
  iframe Hj
  iintro Hj
  iapply wp_report
  rw [show (bif decide (r < 3) then b else !b) = bif decide (r' < 3) then b' else !b' by
    simpa [rrOut] using hR]
  iapply H $$ Hj

end Wp

/-! ## The loop, in any lifting -/

section Loop

variable {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF] [BudgetCreditGS B GF]
local bi IProp GF

/-- The loop refines itself at equal counts, spending `↯b c` per round, given a refinement of one
round at `c`. -/
theorem rrCount_refines_of (c : B)
    (hrr : ∀ b b', ⊢ ↯b c -∗ REL[L] (rr (rT := rT) b) << (rr b') : lrel_bool)
    (b b' : Bool) (k : ℕ) :
    ⊢ ↯b (k • c) -∗ REL[L] (rrCount (rT := rT) b k) << (rrCount b' k) : lrel_int := by
  induction k with
  | zero =>
    iintro -
    simp only [rrCount]
    rel_pures
    rel_values
  | succ k ih =>
    rw [succ_nsmul]
    iintro Hb
    icases BudgetCredit.split $$ Hb with ⟨Hk, H1⟩
    simp only [rrCount]
    -- unfold `rec` into its else branch
    rel_pure_l 5
    rel_pure_r 5
    rw [show ((k + 1 : ℕ) : ℤ) - 1 = k by omega]
    -- `+` evaluates its right operand first: the recursive call, then the round
    rel_bind (rrCount b k) (rrCount b' k)
    isplitl [Hk]
    · iapply ih $$ Hk
    iintro %v %v' Hv
    iunfold lrel_int at Hv
    icases Hv with ⟨%n, %⟨rfl, rfl⟩⟩
    rel_bind (rr b) (rr b')
    isplitl [H1]
    · iapply hrr $$ H1
    iintro %w %w' Hw
    iunfold lrel_bool at Hw
    icases Hw with ⟨%d, %⟨rfl, rfl⟩⟩
    cases d <;> rel_pures <;> rel_values

end Loop

/-! ## Adequacy, in any lifting -/

section Adequacy

/-- Randomized response in a loop of `k` rounds on private bits, started from state `σ`. -/
noncomputable abbrev rrCountMech (k : ℕ) (σ : State rT) : Mechanism Bool (Exp rT) :=
  progMech (rrCount · k) σ

variable [CanonicallyOrderedAdd B] [Nontrivial B] [L.IsSupportLocal] [L.HasBind] [L.IsZeroLeft]
  [L.IsLeftContinuous] [L.IsBudgetClosed] (c : B) (hc : IsAddLeftRegular c)
  (hcpl : RRCoupling L c)
include hc hcpl

/-- `k` rounds couple equal outputs at `k • c`, given a coupling of one round's draws at `c`. -/
theorem rrCount_rel (b b' : Bool) (k : ℕ) (σ σ' : State rT) :
    L.Rel (k • c) (· = ·) (limExecV ⟨rrCount b k, σ⟩) (limExecV ⟨rrCount b' k, σ'⟩) :=
  -- relational adequacy at `lrel_int`, whose carrier forces equal outputs
  (approximates_coupling (GF := MicrometerFunctor rT B) (fun _ _ ↦ lrel_int) _ _ _ σ σ' _
    (fun _ _ ↦ lrel_int_car_eq) fun _ _ ↦
      rrCount_refines_of c (rr_refines_of c hc hcpl) b b' k).mono le_rfl adequacyRel_eq_subset

/-- `k` rounds are within `k • c` in every divergence `L` is sound for. -/
theorem rrCount_div {D : GradedDivergence.{0} B} [L.IsSound D] (b b' : Bool) (k : ℕ)
    (σ σ' : State rT) :
    D (k • c) (limExecV ⟨rrCount b k, σ⟩) (limExecV ⟨rrCount b' k, σ'⟩) :=
  IsSound.sound (rrCount_rel c hc hcpl b b' k σ σ')

/-- The loop as a mechanism is `k • c`-private in every divergence `L` is sound for. -/
theorem rrCount_isPrivate {D : GradedDivergence.{0} B} [L.IsSound D] (k : ℕ) (σ : State rT) :
    (rrCountMech k σ).IsPrivate D ⊤ (k • c) :=
  fun b b' _ ↦ rrCount_div c hc hcpl b b' k σ σ

end Adequacy

/-! ## The budget `(ln 3, 0)` of the DP and zCDP files -/

/-- The DP factor of budget `ln 3` is `3`. -/
theorem expBudget_log_three : expBudget (ENNReal.ofReal (Real.log 3)) = 3 := by
  rw [expBudget_of_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (Real.log_nonneg (by norm_num)), Real.exp_log (by norm_num)]
  norm_num

/-- The privacy budget `(ln 3, 0)`, shared by the dp and zCDP liftings. -/
noncomputable abbrev budget : ℝ≥0∞ × ℝ≥0∞ := (ENNReal.ofReal (Real.log 3), 0)

/-- The budget `(ln 3, 0)` is finite, so it can be spent. -/
theorem isAddLeftRegular_budget : IsAddLeftRegular budget := by simp

end ProbLang.RandomizedResponse
