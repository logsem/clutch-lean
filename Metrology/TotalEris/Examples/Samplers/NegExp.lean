module

public import Metrology.TotalEris
import Metrology.ProbLang.Syntax.Notation
public import Metrology.ProbLang.Reals
public import Metrology.TotalEris.Examples.Samplers.RealDecrTrial
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Negative-exponential sampler -/

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS
open scoped ENNReal NNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
local bi IProp GF

section distribution

def NegExppdf₀ (k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  if 0 ≤ x ∧ x ≤ 1 then .ofReal (Real.exp (-(x + k))) else 0

def NegExppdf (L k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  if L ≤ k then NegExppdf₀ (k - L) x else 0

theorem NegExppdf₀_zero {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    NegExppdf₀ 0 x = ENNReal.ofReal (Real.exp (-x)) := by
  unfold NegExppdf₀
  rw [ite_eq_left ⟨hx0, hx1⟩, Nat.cast_zero, add_zero]

theorem NegExppdf₀_succ {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (j : ℕ) :
    NegExppdf₀ (j + 1) x = ENNReal.ofReal (Real.exp (-1)) * NegExppdf₀ j x := by
  unfold NegExppdf₀
  rw [ite_eq_left ⟨hx0, hx1⟩, ite_eq_left ⟨hx0, hx1⟩, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add]
  congr 2
  push_cast
  ring

def NegExpRejectProb : ℝ≥0∞ := .ofReal (Real.exp (-1))

def NegExpFactor : ℝ≥0 := ⟨Real.exp 1, (Real.exp_pos 1).le⟩

theorem one_lt_NegExpFactor : 1 < NegExpFactor := by
  rw [← NNReal.coe_lt_coe, NNReal.coe_one]
  show (1 : ℝ) < Real.exp 1
  linarith [Real.add_one_le_exp (1 : ℝ)]

theorem NegExpRejectProb_mul_NegExpFactor :
    NegExpRejectProb * (NegExpFactor : ℝ≥0∞) = 1 := by
  rw [NegExpRejectProb, ← ENNReal.ofReal_coe_nnreal (p := NegExpFactor),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  show ENNReal.ofReal (Real.exp (-1) * Real.exp 1) = 1
  rw [← Real.exp_add]
  norm_num

open MeasureTheory in
theorem NegExpReject_lintegral :
    ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-x)) ∂(LawfulProbLangℝ.unifUnit (T := ℝ))
      = ENNReal.ofReal (Real.exp (-1)) := by
  have h_exp : ∫ x in (0 : ℝ)..1, Real.exp (-x) = 1 - Real.exp (-1) := by
    rw [intervalIntegral.integral_comp_neg fun t => Real.exp t, integral_exp]
    simp only [neg_zero, Real.exp_zero]
  show ∫⁻ x in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (1 - Real.exp (-x)) ∂volume = _
  rw [lintegral_ofReal_Icc (by norm_num) (by fun_prop) (fun x hx => by
        have : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hx.1]); linarith)]
  congr 1
  rw [intervalIntegral.integral_sub intervalIntegrable_const
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const, h_exp]
  simp only [smul_eq_mul, mul_one, sub_zero]
  ring

end distribution

section creditExpectation

open MeasureTheory in
def NegExpCreditV (F : ℕ → ℝ → ℝ≥0∞) (L : ℕ) : ℝ≥0∞ :=
  ∑' k : ℕ, ∫⁻ x, NegExppdf L k x * F k x ∂(LawfulProbLangℝ.unifUnit (T := ℝ))

open MeasureTheory in
theorem NegExpCreditV_reindex (F : ℕ → ℝ → ℝ≥0∞) (L : ℕ) :
    NegExpCreditV F L
      = ∑' j : ℕ, ∫⁻ x, NegExppdf₀ j x * F (L + j) x ∂(LawfulProbLangℝ.unifUnit (T := ℝ)) := by
  unfold NegExpCreditV
  rw [← (add_right_injective L).tsum_eq
        (f := fun k => ∫⁻ x, NegExppdf L k x * F k x ∂(LawfulProbLangℝ.unifUnit (T := ℝ))) ?supp]
  · exact tsum_congr fun j => lintegral_congr fun x => by
      simp only [NegExppdf, ite_eq_left (Nat.le_add_right L j), Nat.add_sub_cancel_left]
  · intro k hk
    refine ⟨k - L, Nat.add_sub_of_le ?_⟩
    by_contra h
    exact hk (by simp only [NegExppdf, ite_eq_right h, zero_mul, lintegral_zero])

open MeasureTheory in
theorem NegExpCreditV_recurrence (F : ℕ → ℝ → ℝ≥0∞) (L : ℕ) :
    NegExpCreditV F L
      = (∫⁻ x, ENNReal.ofReal (Real.exp (-x)) * F L x ∂(LawfulProbLangℝ.unifUnit (T := ℝ)))
        + ENNReal.ofReal (Real.exp (-1)) * NegExpCreditV F (L + 1) := by
  rw [NegExpCreditV_reindex F L,
    tsum_eq_zero_add'
      (f := fun j => ∫⁻ x, NegExppdf₀ j x * F (L + j) x ∂(LawfulProbLangℝ.unifUnit (T := ℝ)))
      ENNReal.summable]
  congr 1
  · rw [Nat.add_zero]
    exact setLIntegral_congr_fun measurableSet_Icc
      (fun x hx => by rw [NegExppdf₀_zero hx.1 hx.2])
  · rw [NegExpCreditV_reindex F (L + 1), ← ENNReal.tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Icc (fun x hx => ?_)
    have hidx : L + (j + 1) = L + 1 + j := by omega
    rw [NegExppdf₀_succ hx.1 hx.2, hidx, mul_assoc]

end creditExpectation

section creditKernel

def NegExpContAmp (F : ℕ → ℝ → ℝ≥0∞) (x : ℝ) (L : ℕ) (c : ℝ≥0∞) : ℕ → ℝ≥0∞ := fun z =>
  if z % 2 = 0 then F L x else NegExpCreditV F (L + 1) + c

end creditKernel

section measurability

open MeasureTheory in
theorem measurable_negExpContAmp (F : ℕ → ℝ → ℝ≥0∞) (hF : ∀ a, Measurable (F a))
    (L : ℕ) (c : ℝ≥0∞) :
    Measurable (fun x => RealDecrTrialCreditV (NegExpContAmp F x L c) 0 x) := by
  unfold RealDecrTrialCreditV NegExpContAmp
  refine Measurable.tsum fun n => (measurable_realDecrTrialPMF 0 n).mul ?_
  split
  exacts [hF L, measurable_const]

end measurability

section conservation

open MeasureTheory in
theorem NegExpCredit_recurrence (F : ℕ → ℝ → ℝ≥0∞) (L : ℕ) (c : ℝ≥0∞) :
    ∫⁻ x, RealDecrTrialCreditV (NegExpContAmp F x L c) 0 x ∂(LawfulProbLangℝ.unifUnit (T := ℝ))
      = NegExpCreditV F L + NegExpRejectProb * c := by
  have key : ∫⁻ x, RealDecrTrialCreditV (NegExpContAmp F x L c) 0 x
        ∂(LawfulProbLangℝ.unifUnit (T := ℝ))
      = ∫⁻ x, (ENNReal.ofReal (Real.exp (-x)) * F L x
          + ENNReal.ofReal (1 - Real.exp (-x)) * (NegExpCreditV F (L + 1) + c))
          ∂(LawfulProbLangℝ.unifUnit (T := ℝ)) :=
    setLIntegral_congr_fun measurableSet_Icc fun x hx =>
      RealDecrTrialCreditV_parity (F L x) (NegExpCreditV F (L + 1) + c) hx.1 hx.2
  have hmof : Measurable (fun x : ℝ => ENNReal.ofReal (1 - Real.exp (-x))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [key, lintegral_add_right _ (hmof.mul_const _), lintegral_mul_const _ hmof,
      NegExpReject_lintegral, NegExpCreditV_recurrence F L, NegExpRejectProb]
  ring

end conservation

section specification

theorem twp_NegExp (E : CoPset) (F : ℕ → ℝ → ℝ≥0∞) (hFm : ∀ a, Measurable (F a)) (L : ℕ) :
    ⊢ ↯ (NegExpCreditV F L) -∗
      tglWp E pl(&NegExp #(.int (L : ℤ)))
        (fun p : Val ℝ => iprop(∃ (vz : ℕ) (vr : ℝ),
          ⌜p.1 = .pair (pl(#(.int (Int.ofNat vz)))) pl(#(.real vr))⌝ ∗
          ⌜0 ≤ vr ∧ vr < 1⌝ ∗ ↯ (F vz vr))) := by
  iintro Hε_spec
  iapply twp_err_pos solve_not_value
  iintro %ε_term %Hε_term_pos Hε_term
  irevert! %L
  iapply ErrorCredit.Induction.simple (k := NegExpFactor) Hε_term_pos one_lt_NegExpFactor
    $$ [] Hε_term
  iintro !> ⟨IH, Hε_term⟩ %L Hε_spec
  set c : ℝ≥0∞ := (NegExpFactor : ℝ≥0∞) * ε_term with hc_def
  twp_pure
  twp_pure
  twp_bind pl(urand)
  icombine Hε_spec Hε_term as Hε
  iapply (twp_urand_exp'
    (ε₂ := fun x => RealDecrTrialCreditV (NegExpContAmp F x L c) 0 x)
    (measurable_negExpContAmp F hFm L _) ?hint) $$ Hε
  case hint =>
    rw [NegExpCredit_recurrence, hc_def, ← mul_assoc, NegExpRejectProb_mul_NegExpFactor,
      one_mul]
  iintro %x ⟨%Hxm, Hcx⟩
  obtain ⟨Hx0, Hx1⟩ := mem_unifUnitSupport_real.mp Hxm
  have Hxr := mem_unifUnitSupport_real_le Hxm
  twp_pure
  twp_bind pl(&DecrTrial #(.int (0 : ℤ)) #(.real x))
  iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ n : ℕ,
    ⌜v.1 = pl(#(.int (Int.ofNat n)))⌝ ∗ ↯ (NegExpContAmp F x L c n))))
  isplitl [Hcx]
  · iapply (twp_DecrTrial E (NegExpContAmp F x L c) 0 x Hxr) $$ Hcx
  iintro %⟨w, _⟩ ⟨%n, %rfl, Hcn⟩
  twp_pures
  obtain hpar | hpar := Nat.mod_two_eq_zero_or_one n
  · isimp only [NegExpContAmp, ite_eq_left hpar] at Hcn
    rw [intOfNat_emod_two_eq_zero hpar]
    twp_pures
    twp_value
    imodintro
    iexists L, x
    iframe Hcn
    ipureintro
    exact ⟨rfl, Hx0.le, Hx1⟩
  · rw [intOfNat_emod_two_eq_one hpar]
    isimp only [NegExpContAmp, ite_eq_right (show ¬ n % 2 = 0 by omega)] at Hcn
    ihave ⟨Hexp, Hterm⟩ := ErrorCredit.split $$ Hcn
    twp_pure
    twp_pure
    rw [← Nat.cast_add_one]
    twp_bind pl(&NegExp #(.int ((L + 1 : ℕ) : ℤ)))
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply IH $$ Hterm Hexp

end specification

end
end Examples
end TotalEris
end ProbLang
