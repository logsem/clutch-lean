module

public import Metrology.Code.ContinuousOTP
public import Metrology.Couplings.Divergences.Tv
public import Metrology.Micrometer.AdequacyRel
public import Metrology.Micrometer.ContinuousSampler
public import Metrology.Micrometer.RelTactics
public import Metrology.Micrometer.Soundness
public import Metrology.ProbLang.Advantage
public import Metrology.ProbLang.Reals
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

/-! # A continuous one-time pad, adding a uniform key modulo one

The encryption and `urand` have equal distributions, so no distinguisher has advantage. -/

@[expose] public section

open scoped ENNReal

namespace ProbLang
open Iris Iris.BI Iris.ProofMode MicrometerWpGS MeasureTheory GradedLifting
  GradedDivergence
open _root_.Int (fract fract_add_fract fract_eq_self)
open Set (univ Ioo)
open Cfg (uniformReal uniformReal_isProbabilityMeasure measurable_expr)
open Measure (bind_apply map_apply)
open Tctx (empty)
open Ctx (BindersFresh binderAtoms payloadFv)
open Exp (ofVal_of_toVal_some decompItem_none_of_lc_headReducible)

namespace ContinuousOTP

variable {rT : Type} {hlc : HasLC} {GF : BundledGFunctors}
local bi IProp GF

section Abstract

variable [MeasurableSpace rT] [LawfulProbLangℝ rT]

variable [MicrometerRGS rT hlc GF] [BudgetCreditGS ℝ≥0∞ GF]

open ProbLangℝ LawfulProbLangℝ

variable (m : rT)

/-- The encrypted sample refines the ideal sample, given a measure-preserving rotation. -/
theorem otp_refines
    (hmp : MeasurePreserving (fun r => realFrac (realAdd m r)) unifUnit unifUnit) :
    ⊢ REL[codensity tv] (otpEnc m) << otpIdeal : lrel_real := by
  rel_couple_urands _ hmp
  iintro %r %_
  rel_pures
  rel_values

/-! ### The reverse direction

The ideal sample is coupled with the key through the inverse rotation `g`, so that the
encryption sends `g r` back to `r`. -/

/-- The ideal sample refines the encrypted sample, given the inverse rotation `g`. -/
theorem otp_refines_rev (g : rT → rT)
    (hmp : MeasurePreserving g unifUnit unifUnit)
    (hinv : ∀ r ∈ unifUnitSupport, realFrac (realAdd m (g r)) = r) :
    ⊢ REL[codensity tv] otpIdeal << otpEnc m : lrel_real := by
  rel_couple_urands _ hmp
  iintro %r %hr
  rel_pures
  rw [hinv r hr]
  rel_values

end Abstract

/-! ### At `rT = ℝ`

The measure-preservation hypothesis holds by rotation invariance of `Uniform[0,1]`. -/

section Real

variable [MicrometerRGS ℝ hlc GF] [BudgetCreditGS ℝ≥0∞ GF]

variable (m : ℝ)

/-- At `ℝ`, the encrypted sample refines the ideal sample. -/
theorem otp_refines_real : ⊢ REL[codensity tv] (otpEnc m) << otpIdeal : lrel_real :=
  otp_refines m (measurePreserving_fracAdd m)

/-- At `ℝ`, the ideal sample refines the encrypted sample. -/
theorem otp_refines_rev_real : ⊢ REL[codensity tv] otpIdeal << otpEnc m : lrel_real :=
  otp_refines_rev m (fun r => fract (-m + r)) (measurePreserving_fracAdd (-m)) fun r hr => by
    -- on `(0, 1)`, `fract (m + fract (-m + r)) = fract r = r`
    obtain ⟨hr0, hr1⟩ : r ∈ Ioo 0 1 := hr
    show fract (m + fract (-m + r)) = r
    rw [fract_add_fract, show m + (-m + r) = r by ring]
    exact fract_eq_self.mpr ⟨hr0.le, hr1⟩

end Real

/-! ## Adequacy: exiting the logic

`refines_coupling` turns each refinement into a statement about the limiting
execution distributions, with no Iris in sight. -/

/-- The two programs return the same real. -/
def otpφ (v v' : Val rT) : Prop :=
  ∃ r : rT, v = .real r ∧ v' = .real r

/-- Related values of `adequacyRel otpφ` force equal programs. -/
theorem adequacyRel_otpφ_subset_eq (e₁ e₂ : Exp rT) : adequacyRel otpφ e₁ e₂ → e₁ = e₂ := by
  rintro ⟨v, v', hv, hv', r, rfl, rfl⟩
  exact (ofVal_of_toVal_some hv).symm.trans (ofVal_of_toVal_some hv')

/-- Related real values satisfy `otpφ`. -/
theorem lrel_real_to_otpφ [MeasurableSpace rT] [LawfulProbLangℝ rT] [MicrometerRGS rT hlc GF]
    (v v' : Val rT) :
    ⊢ lrel_real.car v v' -∗ ⌜otpφ v v'⌝ := by
  iunfold lrel_real
  iintro ⟨%r, %hv, %hv'⟩
  ipureintro
  exact ⟨r, hv, hv'⟩

/-- The limit distributions of the encryption and the ideal sample are coupled at budget `0`. -/
theorem otp_adequate_real [RefinesPreGS ℝ ℝ≥0∞ GF] (m : ℝ) (σ σ' : State ℝ) :
    (codensity tv).Rel 0 (adequacyRel otpφ) (limExecV ⟨otpEnc m, σ⟩) (limExecV ⟨otpIdeal, σ'⟩) :=
  refines_coupling (GF := GF) (fun _ _ => lrel_real) otpφ _ _ σ σ' (fun _ _ => lrel_real_to_otpφ)
    fun _ _ => otp_refines_real m

/-- The reverse coupling of the limit distributions at budget `0`. -/
theorem otp_adequate_rev_real [RefinesPreGS ℝ ℝ≥0∞ GF] (m : ℝ) (σ σ' : State ℝ) :
    (codensity tv).Rel 0 (adequacyRel otpφ) (limExecV ⟨otpIdeal, σ⟩) (limExecV ⟨otpEnc m, σ'⟩) :=
  refines_coupling (GF := GF) (fun _ _ => lrel_real) otpφ _ _ σ σ' (fun _ _ => lrel_real_to_otpφ)
    fun _ _ => otp_refines_rev_real m

/-! ## Closed statement

At the concrete model `MicrometerFunctor ℝ` every ghost-state hypothesis is
discharged, leaving a self-contained theorem about `ℝ`-valued programs. -/

section Closed

variable (m : ℝ) (σ : State ℝ)

/-- The encrypted and ideal samples have the same distribution. -/
theorem otp_distribution_eq (σ' : State ℝ) : limExecV ⟨otpEnc m, σ⟩ = limExecV ⟨otpIdeal, σ'⟩ :=
  tv_eq_of_rel ((otp_adequate_real (GF := MicrometerFunctor ℝ ℝ≥0∞) m σ σ').mono le_rfl
      adequacyRel_otpφ_subset_eq)
    ((otp_adequate_rev_real (GF := MicrometerFunctor ℝ ℝ≥0∞) m σ' σ).mono le_rfl
      adequacyRel_otpφ_subset_eq)

/-- No distinguisher has positive advantage. -/
theorem otp_advantage_zero : advantage (otpEnc m) otpIdeal = 0 :=
  advantage_eq_zero_of_limExecV_eq fun σ => otp_distribution_eq m σ σ

/-! ### Non-vacuity

An equality of measures says nothing if both sides are zero, so the mass must be pinned down.
`urand` reaches a value in one step (`Atomic.urand`), hence `execN 2` carries all of it. -/

/-- The ideal sample has total mass one. -/
theorem otp_ideal_mass : limExecV ⟨otpIdeal, σ⟩ univ = 1 := by
  have hnv : ¬ (pl(urand) : Exp ℝ).isValue := fun ⟨w⟩ => nomatch w
  have hprim : primStep ⟨pl(urand), σ⟩ = uniformReal σ :=
    primStep_eq_headStep (decompItem_none_of_lc_headReducible (by is_lc)
      (show uniformReal σ ≠ 0 from IsProbabilityMeasure.ne_zero _))
  have hstep : execN 2 ⟨otpIdeal, σ⟩ univ = 1 := by
    show execN 2 ⟨pl(urand), σ⟩ univ = 1
    have hae : ∀ᵐ ρ' ∂(primStep ⟨pl(urand), σ⟩), execN 1 ρ' univ = 1 := by
      rw [ae_iff]
      refine measure_mono_null ?_ (Atomic.urand σ)
      intro ρ' hρ' hv
      exact hρ' (by rw [execN_succ_isValue hv]; simp)
    rw [execN_succ_not_isValue hnv,
      bind_apply .univ (execN_measurable 1).aemeasurable,
      lintegral_congr_ae hae, lintegral_const, one_mul, hprim]
    exact uniformReal_isProbabilityMeasure.measure_univ
  show asExpr (limExec _) univ = 1
  rw [asExpr, map_apply measurable_expr .univ, limExec_term hstep]
  simpa using hstep

/-- The encrypted sample has total mass one. -/
theorem otp_enc_mass : limExecV ⟨otpEnc m, σ⟩ univ = 1 := by
  rw [otp_distribution_eq m σ σ, otp_ideal_mass]

end Closed

/-! ## Contextual equivalence

Both programs are typed `real`, so `refines_sound_fresh` turns the refinements into inequalities
for every well-typed boolean context. -/

section Typing

/-- The ideal sample is typed `real`. -/
theorem otp_ideal_typed : Typed (rT := rT) empty otpIdeal .real := .urand

variable (m : rT)

/-- The body of `otpEnc m` as a lambda, which `otpEnc m` applies to `urand`. -/
abbrev otpLam : Exp rT := pl% fun k, frac(#m + k)

/-- The body of the encryption is typed `real → real`. -/
theorem otpLam_typed : Typed empty (otpLam m) (.arrow .real .real) :=
  Typed.lam ∅ fun _ _ => .unop_real (.binop_real .lit_real (.fvar (by simp [Tctx.insert])) rfl) rfl

/-- The encryption is typed `real`. -/
theorem otp_enc_typed : Typed empty (otpEnc m) .real := .app (otpLam_typed m) .urand

end Typing

section Contextual

/-! `GF'` is explicit, as `Σ` in Rocq's `refines_sound`: any ghost-state bundle hosting the
Micrometer resources works. -/

variable (GF' : BundledGFunctors) [RefinesPreGS ℝ ℝ≥0∞ GF'] (m : ℝ)

include GF'

/-- Every well-typed boolean context gives the encryption at most the ideal sample's probability
of each outcome. -/
theorem otp_ctx_refines_real (K : Ctx ℝ) (σ₀ : State ℝ) (b : Bool)
    (hK : TypedCtx K empty .real empty .bool) (hbf : BindersFresh K ∅)
    (hfresh : ∀ x ∈ binderAtoms K, x ∉ (otpEnc m).fv ∧ x ∉ (otpIdeal (rT := ℝ)).fv ∧
      x ∉ payloadFv K) :
    limExec ⟨K.fill (otpEnc m), σ₀⟩ (finalBool b) ≤
    limExec ⟨K.fill otpIdeal, σ₀⟩ (finalBool b) :=
  refines_sound_fresh (GF := GF') (.id ℝ≥0∞) _ _ .real (otp_enc_typed m) otp_ideal_typed
    (fun _ _ _ => otp_refines_real m) K σ₀ b hK hbf hfresh

/-- The converse inequality: the ideal sample is at most the encryption. -/
theorem otp_ctx_refines_rev_real (K : Ctx ℝ) (σ₀ : State ℝ) (b : Bool)
    (hK : TypedCtx K empty .real empty .bool) (hbf : BindersFresh K ∅)
    (hfresh : ∀ x ∈ binderAtoms K, x ∉ (otpIdeal (rT := ℝ)).fv ∧ x ∉ (otpEnc m).fv ∧
      x ∉ payloadFv K) :
    limExec ⟨K.fill otpIdeal, σ₀⟩ (finalBool b) ≤
    limExec ⟨K.fill (otpEnc m), σ₀⟩ (finalBool b) :=
  refines_sound_fresh (GF := GF') (.id ℝ≥0∞) _ _ .real otp_ideal_typed (otp_enc_typed m)
    (fun _ _ _ => otp_refines_rev_real m) K σ₀ b hK hbf hfresh

/-- Every well-typed boolean context sees the same distribution on both programs. -/
theorem otp_ctx_equiv_real
    (K : Ctx ℝ) (σ₀ : State ℝ) (b : Bool) (hK : TypedCtx K empty .real empty .bool)
    (hbf : BindersFresh K ∅) (hfresh : ∀ x ∈ binderAtoms K, x ∉ (otpEnc m).fv ∧
      x ∉ (otpIdeal (rT := ℝ)).fv ∧ x ∉ payloadFv K) :
    limExec ⟨K.fill (otpEnc m), σ₀⟩ (finalBool b) =
    limExec ⟨K.fill otpIdeal, σ₀⟩ (finalBool b) :=
  le_antisymm (otp_ctx_refines_real GF' m K σ₀ b hK hbf hfresh) <|
    otp_ctx_refines_rev_real GF' m K σ₀ b hK hbf fun x hx => and_left_comm.1 (hfresh x hx)

end Contextual

end ContinuousOTP
end ProbLang
