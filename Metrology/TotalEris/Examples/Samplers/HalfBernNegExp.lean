module

public import Metrology.TotalEris
import Metrology.ProbLang.Syntax.Notation
public import Metrology.ProbLang.Reals
public import Metrology.TotalEris.Examples.Samplers.RealDecrTrial
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Bernoulli with base-½ negative-exponential bias -/

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS
open scoped ENNReal NNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
local bi IProp GF

section program

def LeHalfSpec (r : ℝ) : Bool := decide (r ≤ 1 / 2)

end program

section distribution

def BNEHalfPMF (b : Bool) : ℝ≥0∞ :=
  if b then .ofReal (Real.exp (-1 / 2)) else .ofReal (1 - Real.exp (-1 / 2))

end distribution

section creditExpectation

def BNEHalfCreditV (F : Bool → ℝ≥0∞) : ℝ≥0∞ :=
  F true * BNEHalfPMF true + F false * BNEHalfPMF false

end creditExpectation

section creditKernel

def LiftParity (F : Bool → ℝ≥0∞) : ℕ → ℝ≥0∞ := fun n => F (n % 2 = 1)

theorem LiftParity_eq_ite (F : Bool → ℝ≥0∞) (n : ℕ) :
    LiftParity F n = if n % 2 = 0 then F false else F true := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [LiftParity, h]

def BNEHalfCredit (F : Bool → ℝ≥0∞) : ℝ → ℝ≥0∞ := fun r =>
  (if r ≤ 1 / 2 then RealDecrTrialCreditV (LiftParity F) 0 r else 0) +
  (if ¬ r ≤ 1 / 2 then F true else 0)

end creditKernel

section measurability

theorem measurable_bneHalfCredit (F : Bool → ℝ≥0∞) : Measurable (BNEHalfCredit F) := by
  unfold BNEHalfCredit
  exact (Measurable.ite measurableSet_Iic (measurable_realDecrTrialCreditV (LiftParity F) 0)
      measurable_const).add
    (Measurable.ite measurableSet_Iic.compl measurable_const measurable_const)

end measurability

section lintegral

open MeasureTheory in
theorem lintegral_indicator_restrict {s t : Set ℝ} (hs : MeasurableSet s) (f : ℝ → ℝ≥0∞) :
    ∫⁻ r, s.indicator f r ∂(volume.restrict t) = ∫⁻ r in s ∩ t, f r ∂volume := by
  rw [lintegral_indicator hs, Measure.restrict_restrict hs]

private theorem Iic_half_inter_unit : Set.Iic (1 / 2 : ℝ) ∩ Set.Icc 0 1 = Set.Icc 0 (1 / 2) := by
  ext r; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
  exact ⟨fun ⟨h2, h1, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, by linarith⟩⟩

private theorem Ioi_half_inter_unit : Set.Ioi (1 / 2 : ℝ) ∩ Set.Icc 0 1 = Set.Ioc (1 / 2) 1 := by
  ext r; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
  exact ⟨fun ⟨h2, _, h1⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨h2, by linarith, h1⟩⟩

end lintegral

section conservation

open MeasureTheory in
theorem BNEHalfCredit_lintegral {F : Bool → ℝ≥0∞} :
    ∫⁻ r, BNEHalfCredit F r ∂(LawfulProbLangℝ.unifUnit) = BNEHalfCreditV F := by
  have hlift : LiftParity F = fun n => if n % 2 = 0 then F false else F true :=
    funext (LiftParity_eq_ite F)
  have hexphalf : ∫ r in (0 : ℝ)..(1 / 2), Real.exp (-r) = 1 - Real.exp (-1 / 2) := by
    rw [intervalIntegral.integral_comp_neg fun x => Real.exp x, neg_zero,
        integral_exp, Real.exp_zero]
    norm_num
  show ∫⁻ r, BNEHalfCredit F r ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = _
  simp only [BNEHalfCredit]
  rw [lintegral_add_left (Measurable.ite measurableSet_Iic
        (measurable_realDecrTrialCreditV (LiftParity F) 0) measurable_const)]
  have hB : (∫⁻ r, (if ¬ r ≤ 1 / 2 then F true else 0) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      = ENNReal.ofReal (1 / 2) * F true := by
    have hind : (fun r => if ¬ r ≤ 1 / 2 then F true else 0)
        = (Set.Ioi (1 / 2 : ℝ)).indicator (fun _ => F true) := by
      ext r; simp only [Set.indicator_apply, Set.mem_Ioi, not_le]
    rw [hind, lintegral_indicator_restrict measurableSet_Ioi (fun _ => F true), Ioi_half_inter_unit,
        setLIntegral_const, Real.volume_Ioc, mul_comm]
    norm_num
  have hA : (∫⁻ r, (if r ≤ 1 / 2 then RealDecrTrialCreditV (LiftParity F) 0 r else 0)
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      = ENNReal.ofReal (1 - Real.exp (-1 / 2)) * F false
        + ENNReal.ofReal (Real.exp (-1 / 2) - 1 / 2) * F true := by
    rw [← indicator_Iic_eq,
        lintegral_indicator_restrict measurableSet_Iic (RealDecrTrialCreditV (LiftParity F) 0),
        Iic_half_inter_unit,
        setLIntegral_congr_fun (g := fun x => ENNReal.ofReal (Real.exp (-x)) * F false
          + ENNReal.ofReal (1 - Real.exp (-x)) * F true) measurableSet_Icc fun r hr => by
        rw [hlift]
        exact RealDecrTrialCreditV_parity (F false) (F true) hr.1 (hr.2.trans (by norm_num))]
    have hmexp : Measurable (fun r : ℝ => ENNReal.ofReal (Real.exp (-r))) :=
      ENNReal.measurable_ofReal.comp (by fun_prop)
    have hmexp' : Measurable (fun r : ℝ => ENNReal.ofReal (1 - Real.exp (-r))) :=
      ENNReal.measurable_ofReal.comp (by fun_prop)
    have hintsub : ∫ r in (0 : ℝ)..(1 / 2), (1 - Real.exp (-r)) = Real.exp (-1 / 2) - 1 / 2 := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const
            (Continuous.intervalIntegrable (by fun_prop) _ _),
          intervalIntegral.integral_const, hexphalf]
      simp only [smul_eq_mul, mul_one, sub_zero]
      ring
    rw [lintegral_add_left (hmexp.mul_const _), lintegral_mul_const _ hmexp,
        lintegral_mul_const _ hmexp',
        lintegral_ofReal_Icc (by norm_num) (by fun_prop) fun r _ => (Real.exp_pos _).le,
        hexphalf,
        lintegral_ofReal_Icc (by norm_num) (by fun_prop) fun r hr =>
          sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr.1)),
        hintsub]
  rw [hA, hB]
  have hexp_ge : (0 : ℝ) ≤ Real.exp (-1 / 2) - 1 / 2 := by
    linarith [Real.add_one_le_exp (-1 / 2 : ℝ)]
  have ht : BNEHalfPMF true = ENNReal.ofReal (Real.exp (-1 / 2)) := rfl
  have hf : BNEHalfPMF false = ENNReal.ofReal (1 - Real.exp (-1 / 2)) := rfl
  rw [BNEHalfCreditV, ht, hf, add_assoc, ← add_mul,
      ← ENNReal.ofReal_add hexp_ge (by norm_num)]
  ring_nf

end conservation

section specification

theorem twp_LeHalf (E : CoPset) (r : ℝ) :
    ⊢ tglWp E pl(&LeHalf #real r)
      (fun v : Val ℝ => iprop(⌜v.1 = .lit (.bool (LeHalfSpec r))⌝)) := by
  twp_pures
  twp_value
  imodintro
  ipureintro
  -- `LeHalf`'s constant is `realOfRat (1 / 2)`: at `ℝ`, the cast of the rational `1 / 2`.
  simp only [LeHalfSpec, realOfRat_real, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  rfl

theorem twp_BNEHalf (E : CoPset) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (BNEHalfCreditV F) -∗
      tglWp E pl(&BNEHalf #())
        (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v.1 = .lit (.bool b)⌝ ∗ ↯ (F b))) := by
  iintro Hε
  twp_pure
  twp_bind pl(urand)
  iapply (twp_urand_exp (measurable_bneHalfCredit F) ?hint) $$ Hε
  case hint => rw [BNEHalfCredit_lintegral]
  iintro %r ⟨%Hrm, Hcr⟩
  have Hr := mem_unifUnitSupport_real_le Hrm
  twp_pure
  twp_bind pl(&LeHalf #real r)
  iapply tglWp_wand
  isplitl []
  · iapply twp_LeHalf
  iintro %⟨w, _⟩ %hv
  dsimp only at hv
  generalize hbdef : LeHalfSpec r = b at hv
  subst hv
  obtain _ | _ := b
  · have hle : ¬ r ≤ 1 / 2 := of_decide_eq_false hbdef
    twp_pures
    twp_value
    imodintro
    iexists true
    isimp only [BNEHalfCredit, ite_eq_right hle, ite_eq_left hle, zero_add] at Hcr
    iframe Hcr
    itrivial
  · have hle : r ≤ 1 / 2 := of_decide_eq_true hbdef
    isimp only [BNEHalfCredit, ite_eq_left hle, ite_eq_right (not_not_intro hle), add_zero] at Hcr
    twp_pure
    twp_bind pl(&DecrTrial #int (0 : ℤ) #real r)
    iapply tglWp_wand
    isplitl [Hcr]
    · iapply (twp_DecrTrial E (LiftParity F) 0 r Hr) $$ Hcr
    iintro %⟨w', _⟩ ⟨%n, %rfl, Hcrn⟩
    twp_pures
    obtain hpar | hpar := Nat.mod_two_eq_zero_or_one n
    · rw [intOfNat_emod_two_eq_zero hpar]
      twp_value
      imodintro
      iexists false
      isimp only [LiftParity_eq_ite, ite_eq_left hpar] at Hcrn
      iframe Hcrn
      itrivial
    · rw [intOfNat_emod_two_eq_one hpar]
      twp_value
      imodintro
      iexists true
      isimp only [LiftParity_eq_ite, ite_eq_right (show ¬ n % 2 = 0 by omega)] at Hcrn
      iframe Hcrn
      itrivial

/-! ## Fair coin

`LeHalf` applied to a `urand` sample is an unbiased coin: `urand ≤ ½` has
probability exactly ½. `FairCoinCredit` is the pointwise credit fed to
`twp_urand_exp`, and `FairCoinCreditV` its expectation. -/

section fairCoin

def FairCoinCredit (F : Bool → ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  fun r => if r ≤ 1 / 2 then F true else F false

def FairCoinCreditV (F : Bool → ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / 2) * F true + ENNReal.ofReal (1 / 2) * F false

theorem measurable_fairCoinCredit (F : Bool → ℝ≥0∞) : Measurable (FairCoinCredit F) :=
  Measurable.ite measurableSet_Iic measurable_const measurable_const

open MeasureTheory in
theorem FairCoinCredit_lintegral (F : Bool → ℝ≥0∞) :
    ∫⁻ r, FairCoinCredit F r ∂(LawfulProbLangℝ.unifUnit) = FairCoinCreditV F := by
  have hsplit : FairCoinCredit F
      = fun r => (Set.Iic (1 / 2 : ℝ)).indicator (fun _ => F true) r
          + (Set.Ioi (1 / 2 : ℝ)).indicator (fun _ => F false) r := by
    funext r
    simp only [FairCoinCredit, Set.indicator_apply, Set.mem_Iic, Set.mem_Ioi]
    by_cases hr : r ≤ 1 / 2
    · rw [ite_eq_left hr, ite_eq_left hr, ite_eq_right (not_lt.mpr hr), add_zero]
    · rw [ite_eq_right hr, ite_eq_right hr, ite_eq_left (not_le.mp hr), zero_add]
  show ∫⁻ r, FairCoinCredit F r ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = _
  rw [hsplit, lintegral_add_left (measurable_const.indicator measurableSet_Iic),
    lintegral_indicator_restrict measurableSet_Iic (fun _ => F true),
    lintegral_indicator_restrict measurableSet_Ioi (fun _ => F false),
    Iic_half_inter_unit, Ioi_half_inter_unit, setLIntegral_const, setLIntegral_const,
    Real.volume_Icc, Real.volume_Ioc]
  norm_num [FairCoinCreditV, mul_comm]

/-! `FairCoin` is a closed constant, so it survives being carried under the
binders of an enclosing program: these two rewrites strip the `openRec`/`closeRec`
wrapper that stepping leaves behind, letting `twp_bind` see the constant. -/

theorem FairCoin_lc : (FairCoin : Exp ℝ).IsLocallyClosed := by is_lc

theorem FairCoin_fv : (FairCoin : Exp ℝ).fv = ∅ := by
  simp [FairCoin, LeHalf, Exp.fv]

@[simp] theorem FairCoin_openRec (k : ℕ) (t : Exp ℝ) :
    Exp.openRec k t FairCoin = FairCoin := (Exp.open_lc k t FairCoin FairCoin_lc).symm

@[simp] theorem FairCoin_closeRec (k : ℕ) (x : Var) :
    Exp.closeRec k x (FairCoin : Exp ℝ) = FairCoin :=
  Exp.closeRec_fresh x FairCoin k (by simp [FairCoin_fv])

theorem twp_FairCoin (E : CoPset) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (FairCoinCreditV F) -∗
      tglWp E pl(&FairCoin #())
        (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v.1 = .lit (.bool b)⌝ ∗ ↯ (F b))) := by
  iintro Hε
  twp_pure
  twp_bind pl(urand)
  iapply (twp_urand_exp (measurable_fairCoinCredit F) ?hint) $$ Hε
  case hint => rw [FairCoinCredit_lintegral]
  iintro %r ⟨%Hrm, Hcr⟩
  twp_pure
  twp_bind pl(&LeHalf #real r)
  iapply tglWp_wand
  isplitl []
  · iapply twp_LeHalf
  iintro %⟨w, _⟩ %hv
  dsimp only at hv
  generalize hbdef : LeHalfSpec r = b at hv
  subst hv
  twp_value
  imodintro
  obtain _ | _ := b
  · iexists false
    isimp only [FairCoinCredit, ite_eq_right (of_decide_eq_false hbdef)] at Hcr
    iframe Hcr
    ipureintro
    rfl
  · iexists true
    isimp only [FairCoinCredit, ite_eq_left (of_decide_eq_true hbdef)] at Hcr
    iframe Hcr
    ipureintro
    rfl

end fairCoin

end specification

end
end Examples
end TotalEris
end ProbLang
