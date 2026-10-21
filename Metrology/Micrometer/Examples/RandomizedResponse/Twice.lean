module

public import Metrology.Micrometer.Examples.RandomizedResponse.Zcdp
public import Metrology.Code.RandomizedResponseTwice
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Randomized response on two bits is zCDP

Each draw spends `(ln 3, 0)` in the zCDP lifting, so the pair is `(ln 9, 0)`-zCDP, and `zcdpToDp`
gives `(ln 9, δ)`-DP for every `δ > 0`. -/

open scoped ENNReal

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting
open GradedDivergence (dp zcdpDivergence zcdpLifting)

namespace ProbLang.RandomizedResponse

/-! ## The program logic proof -/

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

section Logic

variable {GF : BundledGFunctors} [MicrometerGS rT .hasNoLC GF]
  [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF]
local bi IProp GF

/-- `wp_rr_of` at the zCDP coupling `rrCoupling_zcdp`: one round against the spec in context `K`,
spending `(ln 3, 0)`. -/
theorem wp_rr_step (K : Ectx rT) (b b' : Bool) (Φ : Val rT → IProp GF) :
    ⤇ K.fill (rr b') ∗ ↯b budget ∗ (∀ c, ⤇ K.fill pl(#(.bool c)) -∗ Φ (.bool c)) ⊢
      wp zcdpLifting ⊤ (rr b) Φ :=
  wp_rr_of budget isAddLeftRegular_budget rrCoupling_zcdp K b b' Φ

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
  -- the spec holds the pair expression; restate it as Exp.ofVal of the pair value
  iapply specProgFrag_reshape (e₁ := K.fill pl((#(.bool c₁), #(.bool c₂))))
    (e₂ := K.fill (Exp.ofVal (.pair (.bool c₁) (.bool c₂)))) rfl $$ Hj

/-- The two-bit program against itself, spending `(ln 3, 0)` per bit. -/
theorem wp_rr2 (b₁ b₂ b₁' b₂' : Bool) :
    ⊢ ⤇ rr2 (rT := rT) b₁' b₂' -∗ ↯b (budget + budget) -∗
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
  · iapply rr_refines_of _ isAddLeftRegular_budget rrCoupling_zcdp b₁ b₁' $$ Hb₁
  iintro %v %v' Hv
  iunfold lrel_bool at Hv
  icases Hv with ⟨%c₁, %⟨rfl, rfl⟩⟩
  rel_pures
  rel_bind (rr b₂) (rr b₂')
  isplitl [Hb₂]
  · iapply rr_refines_of _ isAddLeftRegular_budget rrCoupling_zcdp b₂ b₂' $$ Hb₂
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
theorem rr2_coupling (b₁ b₂ b₁' b₂' : Bool) (σ σ' : State rT) :
    zcdpLifting.Rel budget2 (· = ·) (limExecV ⟨rr2 b₁ b₂, σ⟩) (limExecV ⟨rr2 b₁' b₂', σ'⟩) :=
  (wp_adequacy (GF := MicrometerFunctor rT (ℝ≥0∞ × ℝ≥0∞)) _ _ σ σ' budget2 (· = ·) fun _ _ ↦
    budget_add_budget ▸ wp_rr2 b₁ b₂ b₁' b₂').mono le_rfl adequacyRel_eq_subset

/-- Randomized response on two bits is `(ln 9, 0)`-zCDP, for any two pairs of private bits. -/
theorem rr2_zcdp (b₁ b₂ b₁' b₂' : Bool) (σ σ' : State rT) :
    zcdpDivergence budget2 (limExecV ⟨rr2 b₁ b₂, σ⟩) (limExecV ⟨rr2 b₁' b₂', σ'⟩) :=
  GradedLifting.IsSound.sound (rr2_coupling b₁ b₂ b₁' b₂' σ σ')

/-! ## From zCDP to DP -/

/-- The two-bit program is `(ln 9, δ)`-DP for every `δ > 0`, converting the zCDP coupling with
`zcdpToDp`. -/
theorem rr2_dp (b₁ b₂ b₁' b₂' : Bool) (σ σ' : State rT) {δ : ℝ} (hδ : 0 < δ) :
    dp (ENNReal.ofReal (Real.log 9), ENNReal.ofReal δ)
      (limExecV ⟨rr2 b₁ b₂, σ⟩) (limExecV ⟨rr2 b₁' b₂', σ'⟩) := by
  have h := GradedDivergence.codensity_sound <| (LiftingRelHom.zcdpToDp hδ).map_rel
    (rr2_coupling b₁ b₂ b₁' b₂' σ σ')
  simp only [LiftingRelHom.zcdpToDp_map] at h
  exact GradedDivergence.IsGraded.mono
    (Prod.mk_le_mk.2 ⟨LiftingRelHom.zcdpToDp_budget_le_of_rho_zero _, le_rfl⟩) h

/-! ## The mechanism form -/

/-- Randomized response on pairs of private bits, started from state `σ`. -/
noncomputable abbrev rr2Mech (σ : State rT) : Mechanism (Bool × Bool) (Exp rT) :=
  progMech (fun b ↦ rr2 b.1 b.2) σ

/-- `rr2_refines` at the single budget `budget2`, for `progMech_isPrivate`. -/
theorem rr2_refines_mech {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF]
    [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF] (b b' : Bool × Bool) :
    ⊢@{IProp GF} ↯b budget2 -∗
      REL[zcdpLifting] (rr2 (rT := rT) b.1 b.2) << (rr2 b'.1 b'.2) :
        lrel_prod lrel_bool lrel_bool :=
  budget_add_budget ▸ rr2_refines b.1 b.2 b'.1 b'.2

/-- Randomized response on two bits is `(ln 9, 0)`-zCDP as a mechanism (Def. 2.4). -/
theorem rr2_zCDP (σ : State rT) : (rr2Mech σ).zCDP ⊤ (ENNReal.ofReal (Real.log 9)) 0 :=
  progMech_isPrivate (MicrometerFunctor rT (ℝ≥0∞ × ℝ≥0∞)) (L := zcdpLifting) _ σ budget2
    (fun _ _ ↦ lrel_prod lrel_bool lrel_bool)
    (fun _ _ ↦ lrel_prod_car_eq lrel_bool_car_eq lrel_bool_car_eq)
    fun b b' _ _ _ ↦ rr2_refines_mech b b'

/-- Randomized response on two bits is `(ln 9, δ)`-DP as a mechanism, for every `δ > 0`
(Def. 2.1). -/
theorem rr2_DP (σ : State rT) {δ : ℝ} (hδ : 0 < δ) :
    (rr2Mech σ).DP ⊤ (ENNReal.ofReal (Real.log 9)) (ENNReal.ofReal δ) :=
  fun b b' _ ↦ rr2_dp b.1 b.2 b'.1 b'.2 σ σ hδ

end ProbLang.RandomizedResponse
