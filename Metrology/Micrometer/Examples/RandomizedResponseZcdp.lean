module

public import Metrology.Micrometer.Examples.RandomizedResponse
public import Metrology.Code.RandomizedResponseTwice
public import Metrology.Couplings.Divergences.RenyiFiber
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Randomized response on two bits is zCDP

Each bit is randomized as in `RandomizedResponse`, but the proof runs in the zCDP lifting: each
draw spends a `(ln 3, 0)` credit, adequacy gives `(ln 9, 0)`-zCDP, and `zcdpToDp` turns the
lifting into `(ln 9, δ)`-DP for every `δ > 0`. -/

open scoped ENNReal

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting
open GradedDivergence (dp zcdpDivergence zcdpLifting expBudget)

namespace ProbLang
namespace RandomizedResponse

/-! ## The coupling of one draw -/

/-- The two draws couple along equal reports in the zCDP lifting at budget `(ln 3, 0)`. -/
theorem rr_zcdp_coupling (b b' : Bool) :
    zcdpLifting.Rel budget (fun r r' ↦ rrOut b r = rrOut b' r')
      (unifInt 4 (by norm_num)) (unifInt 4 (by norm_num)) := by
  refine GradedDivergence.zcdpLifting_rel_of_fiber .of_discrete .of_discrete fun c ↦ ?_
  rw [expBudget_log_three]
  calc _ ≤ 1 - 4⁻¹ := rrOut_fiber_le b c
    _ ≤ 3 * 4⁻¹ := one_sub_quarter_le
    _ ≤ _ := by gcongr; exact rrOut_fiber_ge b' c

/-! ## The program logic proof -/

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

section Logic

variable {GF : BundledGFunctors} [MicrometerGS rT .hasNoLC GF]
  [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF]

/-- One round of randomized response against the spec in context `K`, spending `(ln 3, 0)`:
both sides report the same bit. -/
theorem wp_rr_step (K : Ectx rT) (b b' : Bool) (Φ : Val rT → IProp GF) :
    ⤇ K.fill (rr b') ∗ ↯b budget ∗ (∀ c, ⤇ K.fill pl(#(.bool c)) -∗ Φ (.bool c)) ⊢
      wp zcdpLifting ⊤ (rr b) Φ :=
  wp_rr_of budget isAddLeftRegular_budget rr_zcdp_coupling K b b' Φ

/-- The two-bit program against the spec in context `K`, spending `(ln 3, 0)` per bit: both
sides report the same pair. -/
theorem wp_rr2_fill (K : Ectx rT) (b₁ b₂ b₁' b₂' : Bool) (Φ : Val rT → IProp GF) :
    ⤇ K.fill (rr2 b₁' b₂') ∗ ↯b (budget + budget) ∗
      (∀ c₁ c₂, ⤇ K.fill (Exp.ofVal (.pair (.bool c₁) (.bool c₂))) -∗
        Φ (.pair (.bool c₁) (.bool c₂))) ⊢
      wp zcdpLifting ⊤ (rr2 b₁ b₂) Φ := by
  iintro ⟨Hj, Hb, H⟩
  icases BudgetCredit.split $$ Hb with ⟨Hb₁, Hb₂⟩
  simp only [rr2, Exp.close, Exp.closeRec, ↓reduceIte]
  wp_bind (rr b₁)
  tp_bind (rr b₁')
  iapply wp_rr_step
  iframe Hj Hb₁
  iintro %c₁ Hj
  wp_pures
  tp_pures
  wp_bind (rr b₂)
  tp_bind (rr b₂')
  iapply wp_rr_step
  iframe Hj Hb₂
  iintro %c₂ Hj
  wp_pures
  tp_pures
  wp_value
  imodintro
  iapply H
  iapply specProgFrag_reshape (e₁ := K.fill pl((#(.bool c₁), #(.bool c₂))))
    (e₂ := K.fill (Exp.ofVal (.pair (.bool c₁) (.bool c₂)))) rfl $$ Hj

/-- The two-bit program against itself, spending `(ln 3, 0)` per bit. -/
theorem wp_rr2 (b₁ b₂ b₁' b₂' : Bool) :
    ⊢@{IProp GF} ⤇ rr2 (rT := rT) b₁' b₂' -∗ ↯b (budget + budget) -∗
      wp zcdpLifting ⊤ (rr2 b₁ b₂) (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜v = v'⌝)) := by
  rw [spec_eq_fill_nil]
  iintro Hj Hb
  iapply wp_rr2_fill []
  iframe Hj Hb
  iintro %c₁ %c₂ Hj
  rw [Exp.ofVal]
  iapply spec_fill_nil_exists _ $$ Hj

end Logic

/-! ## The relational proof -/

/-- The two-bit program refines itself at equal pairs of reports, spending `(ln 3, 0)` per
bit. -/
theorem rr2_refines {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF]
    [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF] (b₁ b₂ b₁' b₂' : Bool) :
    ⊢@{IProp GF} ↯b (budget + budget) -∗
      REL[zcdpLifting] (rr2 (rT := rT) b₁ b₂) << (rr2 b₁' b₂') :
        lrel_prod lrel_bool lrel_bool := by
  iintro Hb
  icases BudgetCredit.split $$ Hb with ⟨Hb₁, Hb₂⟩
  simp only [rr2]
  rel_bind (rr b₁) (rr b₁')
  isplitl [Hb₁]
  · iapply rr_refines_of _ isAddLeftRegular_budget rr_zcdp_coupling b₁ b₁' $$ Hb₁
  iintro %v %v' Hv
  iunfold lrel_bool at Hv
  icases Hv with ⟨%c₁, %⟨rfl, rfl⟩⟩
  rel_pures
  rel_bind (rr b₂) (rr b₂')
  isplitl [Hb₂]
  · iapply rr_refines_of _ isAddLeftRegular_budget rr_zcdp_coupling b₂ b₂' $$ Hb₂
  iintro %w %w' Hw
  iunfold lrel_bool at Hw
  icases Hw with ⟨%c₂, %⟨rfl, rfl⟩⟩
  rel_pures
  rel_values

/-! ## Adequacy: exit the logic -/

/-- The budget `(ln 9, 0)` of two rounds. -/
noncomputable abbrev budget2 : ℝ≥0∞ × ℝ≥0∞ := (ENNReal.ofReal (Real.log 9), 0)

/-- Two rounds at `(ln 3, 0)` cost `(ln 9, 0)`. -/
theorem budget_add_budget : budget + budget = budget2 := by
  have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  rw [Prod.mk_add_mk, add_zero, ← ENNReal.ofReal_add h3 h3, ← Real.log_mul (by norm_num)
    (by norm_num)]
  norm_num

/-- Equal pairs of reports from `↯b (ln 9, 0)` couple the two runs in the zCDP lifting. -/
theorem rr2_coupling_of (GF : BundledGFunctors) [AppPreGS rT GF] [SpecPreGS rT GF]
    [BudgetCreditPreGS (ℝ≥0∞ × ℝ≥0∞) GF] [InvGpreS GF] (b₁ b₂ b₁' b₂' : Bool)
    (σ σ' : State rT) :
    zcdpLifting.Rel budget2 (· = ·) (limExecV ⟨rr2 b₁ b₂, σ⟩) (limExecV ⟨rr2 b₁' b₂', σ'⟩) :=
  (wp_adequacy (GF := GF) _ _ σ σ' budget2 (· = ·) fun _ _ ↦
    budget_add_budget ▸ wp_rr2 b₁ b₂ b₁' b₂').mono le_rfl adequacyRel_eq_subset

/-- The two-bit program is `(ln 9, 0)`-zCDP, through `wp_rr2`. -/
theorem rr2_zcdp_of (GF : BundledGFunctors) [AppPreGS rT GF] [SpecPreGS rT GF]
    [BudgetCreditPreGS (ℝ≥0∞ × ℝ≥0∞) GF] [InvGpreS GF] (b₁ b₂ b₁' b₂' : Bool)
    (σ σ' : State rT) :
    zcdpDivergence budget2 (limExecV ⟨rr2 b₁ b₂, σ⟩) (limExecV ⟨rr2 b₁' b₂', σ'⟩) :=
  wp_adequacy_div (GF := GF) (L := zcdpLifting) _ _ σ σ' budget2 fun _ _ ↦
    budget_add_budget ▸ wp_rr2 b₁ b₂ b₁' b₂'

/-- `rr2_zcdp_of`, through the refinement `rr2_refines`. -/
theorem rr2_zcdp_of_refines (GF : BundledGFunctors) [RefinesPreGS rT (ℝ≥0∞ × ℝ≥0∞) GF]
    (b₁ b₂ b₁' b₂' : Bool) (σ σ' : State rT) :
    zcdpDivergence budget2 (limExecV ⟨rr2 b₁ b₂, σ⟩) (limExecV ⟨rr2 b₁' b₂', σ'⟩) :=
  approximates_div (GF := GF) (L := zcdpLifting) (fun _ _ ↦ lrel_prod lrel_bool lrel_bool) _ _
    σ σ' budget2 (fun _ _ ↦ lrel_prod_car_eq lrel_bool_car_eq lrel_bool_car_eq) fun _ _ ↦
      budget_add_budget ▸ rr2_refines b₁ b₂ b₁' b₂'

/-- Randomized response on two bits is `(ln 9, 0)`-zCDP, for any two pairs of private bits. -/
theorem rr2_zcdp (b₁ b₂ b₁' b₂' : Bool) (σ σ' : State rT) :
    zcdpDivergence budget2 (limExecV ⟨rr2 b₁ b₂, σ⟩) (limExecV ⟨rr2 b₁' b₂', σ'⟩) :=
  rr2_zcdp_of (MicrometerFunctor rT (ℝ≥0∞ × ℝ≥0∞)) b₁ b₂ b₁' b₂' σ σ'

/-! ## From zCDP to DP -/

/-- Without the quadratic term, the best Rényi conversion of `(ξ, 0)` costs nothing over `ξ`:
send the order to infinity. -/
theorem iInf_conversion_le (ξ : ℝ≥0∞) {δ : ℝ} :
    ⨅ α ∈ Set.Ioi (1 : ℝ), ξ + ENNReal.ofReal α * 0 +
      ENNReal.ofReal (Real.log (1 / δ) / (α - 1)) ≤ ξ := by
  refine ENNReal.le_of_forall_pos_le_add fun t ht _ ↦ ?_
  set l := Real.log (1 / δ)
  have hl : 0 < |l| + 1 := by positivity
  have ht' : (0 : ℝ) < t := ht
  refine (iInf₂_le (1 + (|l| + 1) / t) (lt_add_of_pos_right _ (div_pos hl ht'))).trans ?_
  rw [mul_zero, add_zero, add_sub_cancel_left]
  gcongr
  refine ENNReal.ofReal_le_of_le_toReal ?_
  rw [ENNReal.coe_toReal, div_div_eq_mul_div, div_le_iff₀ hl]
  nlinarith [le_abs_self l]

/-- The two-bit program is `(ln 9, δ)`-DP for every `δ > 0`, converting the zCDP coupling with
`zcdpToDp`. -/
theorem rr2_dp (b₁ b₂ b₁' b₂' : Bool) (σ σ' : State rT) {δ : ℝ} (hδ : 0 < δ) :
    dp (ENNReal.ofReal (Real.log 9), ENNReal.ofReal δ)
      (limExecV ⟨rr2 b₁ b₂, σ⟩) (limExecV ⟨rr2 b₁' b₂', σ'⟩) := by
  have h := GradedDivergence.codensity_sound <| (LiftingRelHom.zcdpToDp hδ).map_rel
    (rr2_coupling_of (MicrometerFunctor rT (ℝ≥0∞ × ℝ≥0∞)) b₁ b₂ b₁' b₂' σ σ')
  simp only [LiftingRelHom.zcdpToDp_map] at h
  exact GradedDivergence.IsGraded.mono (Prod.mk_le_mk.2 ⟨iInf_conversion_le _, le_rfl⟩) h

/-- Randomized response on pairs of private bits, started from state `σ`. -/
noncomputable abbrev rr2Mech (σ : State rT) : Mechanism (Bool × Bool) (Exp rT) :=
  progMech (fun b ↦ rr2 b.1 b.2) σ

/-- `rr2_refines` packaged for the mechanism rule, on any two pairs of bits. -/
theorem rr2_refines_mech {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF]
    [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF] (b b' : Bool × Bool) :
    ⊢@{IProp GF} ↯b budget2 -∗
      REL[zcdpLifting] (rr2 (rT := rT) b.1 b.2) << (rr2 b'.1 b'.2) :
        lrel_prod lrel_bool lrel_bool :=
  budget_add_budget ▸ rr2_refines b.1 b.2 b'.1 b'.2

/-- Randomized response on two bits is `(ln 9, 0)`-zCDP for any two pairs of bits (Def. 2.4). -/
theorem rr2_zCDP (σ : State rT) : (rr2Mech σ).zCDP ⊤ (ENNReal.ofReal (Real.log 9)) 0 :=
  progMech_isPrivate (MicrometerFunctor rT (ℝ≥0∞ × ℝ≥0∞)) (L := zcdpLifting) _ σ budget2
    (fun _ _ ↦ lrel_prod lrel_bool lrel_bool)
    (fun _ _ ↦ lrel_prod_car_eq lrel_bool_car_eq lrel_bool_car_eq)
    fun b b' _ _ _ ↦ rr2_refines_mech b b'

/-- Randomized response on two bits is `(ln 9, δ)`-DP for any two pairs of bits and every
`δ > 0` (Def. 2.1). -/
theorem rr2_DP (σ : State rT) {δ : ℝ} (hδ : 0 < δ) :
    (rr2Mech σ).DP ⊤ (ENNReal.ofReal (Real.log 9)) (ENNReal.ofReal δ) :=
  fun b b' _ ↦ rr2_dp b.1 b.2 b'.1 b'.2 σ σ hδ

end RandomizedResponse
end ProbLang
