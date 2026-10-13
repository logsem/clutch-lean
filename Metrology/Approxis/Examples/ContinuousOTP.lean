module

public import Metrology.Approxis.ContinuousSampler
public import Metrology.Approxis.Soundness
public import Metrology.ProbLang.Advantage
import Metrology.ProbLang.Syntax.Notation
public import Metrology.ProbLang.Reals
public import Metrology.Approxis.AdequacyRel
public import Metrology.Code.ContinuousOTP
public import Metrology.Couplings.CodensityTV

@[expose] public section

/-! # A continuous one-time pad -/

namespace ProbLang
open Iris Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS MeasureTheory

namespace ContinuousOTP

variable {rT : Type} [LawfulProbLangℝ rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [IR : ApproxisRGS rT hlc TVDiv.tv GF]

abbrev otpLam (m : rT) : Exp rT := pl% fun k, frac(#(.real m) + k)

def otpKLam (m : rT) : Ectx rT := [EctxItem.appR (otpLam m)]

private theorem refines_lit_real (r : rT) :
    ⊢@{IProp GF} refines ⊤ (pl(#(.real r)) : Exp rT) pl(#(.real r)) lrel_real := by
  iapply refines_ret (v1 := .real r) (v2 := .real r) rfl rfl
  imodintro
  iapply lrel_real_lit

theorem otp_refines (m : rT)
    (hmp : MeasurePreserving (fun r => ProbLangℝ.realFrac (ProbLangℝ.realAdd m r))
      LawfulProbLangℝ.unifUnit LawfulProbLangℝ.unifUnit) :
    ⊢@{IProp GF} refines ⊤ (otp_enc m) otp_ideal lrel_real := by
  simp only [otp_enc, otp_ideal, Exp.close, Exp.closeRec, ↓reduceIte]
  show ⊢@{IProp GF} refines ⊤
    ((otpKLam m).fill pl(urand))
    (Ectx.fill ([] : Ectx rT) pl(urand)) lrel_real
  iapply refines_couple_urands_lr _ hmp
  iintro %r %_
  show ⊢@{IProp GF} refines ⊤ (Ectx.fill ([] : Ectx rT) pl({otpLam m} #(.real r))) _ lrel_real
  iapply refines_pure_l (Hex := pureExec_app_lam) ⟨IsVal.lit.toIsValue, by is_lc⟩
  inext
  let Kfrac : Ectx rT := [EctxItem.unop .frac]
  show ⊢@{IProp GF} refines ⊤ (Kfrac.fill pl(#(.real m) + #(.real r))) _ lrel_real
  iapply refines_pure_l ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, rfl⟩
  inext
  show ⊢@{IProp GF} refines ⊤
    (Ectx.fill ([] : Ectx rT) pl(frac(#(.real (ProbLangℝ.realAdd m r))))) _ lrel_real
  iapply refines_pure_l ⟨IsVal.lit.toIsValue, rfl⟩
  inext
  exact refines_lit_real _

/-! ### The reverse direction

Couple the ideal sample against the encryption's key using the *inverse* rotation
`g`, so that the encryption's combiner sends `g r` back to `r`. -/

theorem otp_refines_rev (m : rT) (g : rT → rT)
    (hmp : MeasurePreserving g LawfulProbLangℝ.unifUnit LawfulProbLangℝ.unifUnit)
    (hinv : ∀ r ∈ LawfulProbLangℝ.unifUnitSupport,
      ProbLangℝ.realFrac (ProbLangℝ.realAdd m (g r)) = r) :
    ⊢@{IProp GF} refines ⊤ otp_ideal (otp_enc m) lrel_real := by
  simp only [otp_enc, otp_ideal, Exp.close, Exp.closeRec, ↓reduceIte]
  show ⊢@{IProp GF} refines ⊤
    (Ectx.fill ([] : Ectx rT) pl(urand))
    ((otpKLam m).fill pl(urand)) lrel_real
  iapply refines_couple_urands_lr _ hmp
  iintro %r %hr
  show ⊢@{IProp GF} refines ⊤ _
    (Ectx.fill ([] : Ectx rT) pl({otpLam m} #(.real (g r)))) lrel_real
  iapply refines_pure_r (Hex := pureExec_app_lam) ⟨IsVal.lit.toIsValue, by is_lc⟩
  let Kfrac : Ectx rT := [EctxItem.unop .frac]
  show ⊢@{IProp GF} refines ⊤ _ (Kfrac.fill pl(#(.real m) + #(.real (g r)))) lrel_real
  iapply refines_pure_r ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, rfl⟩
  show ⊢@{IProp GF} refines ⊤ _
    (Ectx.fill ([] : Ectx rT) pl(frac(#(.real (ProbLangℝ.realAdd m (g r)))))) lrel_real
  iapply refines_pure_r ⟨IsVal.lit.toIsValue, rfl⟩
  rw [hinv r hr]
  exact refines_lit_real r

/-! ### At `rT = ℝ`

The abstract hypothesis is discharged by rotation invariance of `Uniform[0,1]`,
so the refinement holds outright for the genuinely continuous instance. -/

theorem otp_refines_real (m : ℝ) {hlc : HasLC} {GF : BundledGFunctors}
    [ApproxisRGS ℝ hlc TVDiv.tv GF] :
    ⊢@{IProp GF} refines ⊤ (otp_enc m) otp_ideal lrel_real :=
  otp_refines m (measurePreserving_fracAdd m)

noncomputable def invRot (m : ℝ) : ℝ → ℝ := fun r => Int.fract (-m + r)

theorem otp_refines_rev_real (m : ℝ) {hlc : HasLC} {GF : BundledGFunctors}
    [ApproxisRGS ℝ hlc TVDiv.tv GF] :
    ⊢@{IProp GF} refines ⊤ otp_ideal (otp_enc m) lrel_real :=
  otp_refines_rev m (invRot m) (measurePreserving_fracAdd (-m)) fun r hr => by
    obtain ⟨hr0, hr1⟩ : r ∈ Set.Ioo 0 1 := hr
    show Int.fract (m + Int.fract (-m + r)) = r
    rw [fract_add_fract_right, show m + (-m + r) = r by ring]
    exact Int.fract_eq_self.mpr ⟨hr0.le, hr1⟩

/-! ## Adequacy: exiting the logic

`refines_coupling` turns each refinement into a statement about the limiting
execution distributions, with no Iris in sight. -/

def otpφ (v v' : Val rT) : Prop :=
  ∃ r : rT, v = .real r ∧ v' = .real r

theorem lrel_real_to_otpφ {GF : BundledGFunctors} [ApproxisRGS rT hlc TVDiv.tv GF] (v v' : Val rT) :
    ⊢@{IProp GF} lrel_real.car v v' -∗ ⌜otpφ v v'⌝ := by
  iintro Hr
  iunfold lrel_real at Hr
  icases Hr with ⟨%r, %hv, %hv'⟩
  ipureintro; exact ⟨r, hv, hv'⟩

section Adequacy
variable {GF : BundledGFunctors}

theorem otp_adequate_real [RefinesPreGS ℝ GF] (m : ℝ) (σ σ' : State ℝ) :
    TVDiv.tv.{0}.Codensity 1 0 (adequacyRel otpφ) (limExecV ⟨otp_enc m, σ⟩)
      (limExecV ⟨otp_ideal, σ'⟩) :=
  refines_coupling (GF := GF) (fun _ => lrel_real) otpφ _ _ σ σ' (fun _ => lrel_real_to_otpφ)
    fun _ => otp_refines_real m

theorem otp_adequate_rev_real [RefinesPreGS ℝ GF] (m : ℝ) (σ σ' : State ℝ) :
    TVDiv.tv.{0}.Codensity 1 0 (adequacyRel otpφ) (limExecV ⟨otp_ideal, σ⟩)
      (limExecV ⟨otp_enc m, σ'⟩) :=
  refines_coupling (GF := GF) (fun _ => lrel_real) otpφ _ _ σ σ' (fun _ => lrel_real_to_otpφ)
    fun _ => otp_refines_rev_real m

end Adequacy

/-! ## Closed statement

At the concrete model `ApproxisFunctor ℝ` every ghost-state hypothesis is
discharged, leaving a self-contained theorem about `ℝ`-valued programs. -/

omit [LawfulProbLangℝ rT] in
theorem adequacyRel_otpφ_subset_eq : adequacyRel otpφ ⊆ {p : Exp rT × Exp rT | p.1 = p.2} := by
  rintro ⟨e₁, e₂⟩ ⟨v, v', hv, hv', r, rfl, rfl⟩
  exact (Exp.ofVal_of_toVal_some hv).symm.trans (Exp.ofVal_of_toVal_some hv')

theorem otp_distribution_eq (m : ℝ) (σ σ' : State ℝ) :
    limExecV ⟨otp_enc m, σ⟩ = limExecV ⟨otp_ideal, σ'⟩ :=
  GradedDivergence.Codensity.tv_eq_of_diag
    ((otp_adequate_real (GF := ApproxisFunctor ℝ) m σ σ').mono_rel adequacyRel_otpφ_subset_eq)
    ((otp_adequate_rev_real (GF := ApproxisFunctor ℝ) m σ' σ).mono_rel adequacyRel_otpφ_subset_eq)

/-! ### Non-vacuity

An equality of measures says nothing if both sides are the zero measure, so we
pin down the mass. `urand` reaches a value in one step, hence `execN 2` already
carries the whole mass; the a.e. step "every successor is a value" is exactly
`Atomic.urand'`. -/

theorem otp_ideal_mass (σ : State ℝ) : limExecV ⟨otp_ideal, σ⟩ Set.univ = 1 := by
  have hnv : ¬ (pl(urand) : Exp ℝ).isValue := fun ⟨w⟩ => nomatch w
  have hstep : execN 2 ⟨otp_ideal, σ⟩ Set.univ = 1 := by
    show execN 2 ⟨pl(urand), σ⟩ Set.univ = 1
    rw [execN_succ_not_isValue hnv,
        Measure.bind_apply MeasurableSet.univ (execN_measurable 1).aemeasurable]
    have hae : ∀ᵐ ρ' ∂(primStep ⟨pl(urand), σ⟩), execN 1 ρ' Set.univ = 1 := by
      rw [ae_iff]
      refine measure_mono_null ?_ (Atomic.urand' σ)
      intro ρ' hρ' hv
      exact hρ' (by rw [execN_succ_isValue hv]; simp)
    rw [lintegral_congr_ae hae, lintegral_const, one_mul,
        show primStep ⟨pl(urand), σ⟩ = Cfg.uniformReal σ from primStep_eq_headStep
          (Exp.decompItem_none_of_lc_headReducible (by is_lc)
            (show Cfg.uniformReal σ ≠ 0 from IsProbabilityMeasure.ne_zero _))]
    exact Cfg.uniformReal_isProbabilityMeasure.measure_univ
  show asExpr (limExec _) Set.univ = 1
  rw [asExpr, Measure.map_apply Cfg.measurable_expr MeasurableSet.univ,
      limExec_term hstep]
  simpa using hstep

theorem otp_enc_mass (m : ℝ) (σ : State ℝ) : limExecV ⟨otp_enc m, σ⟩ Set.univ = 1 := by
  rw [otp_distribution_eq m σ σ, otp_ideal_mass]

/-! ## Contextual equivalence

`GF` is a parameter in the Rocq sense (`refines_sound Σ`): the statement holds for any
ghost-state bundle able to host the Approxis resources. -/

section Typing

omit [LawfulProbLangℝ rT] in
theorem otp_ideal_typed : Typed (rT := rT) Tctx.empty otp_ideal .real := .urand

omit [LawfulProbLangℝ rT] in
theorem otpLam_typed (m : rT) : Typed Tctx.empty (otpLam m) (.arrow .real .real) :=
  Typed.lam ∅ fun _ _ => .unop_real (.binop_real .lit_real (.fvar (by simp [Tctx.insert])) rfl) rfl

omit [LawfulProbLangℝ rT] in
theorem otp_enc_typed (m : rT) : Typed Tctx.empty (otp_enc m) .real := .app (otpLam_typed m) .urand

end Typing

theorem otp_ctx_refines_real (GF : BundledGFunctors) [RefinesPreGS ℝ GF] (m : ℝ) :
    ∀ (K : Ctx ℝ) (σ₀ : State ℝ) (b : Bool),
      TypedCtx K Tctx.empty .real Tctx.empty .bool → Ctx.BindersFresh K ∅ →
      (∀ x ∈ Ctx.binderAtoms K, x ∉ (otp_enc m).fv ∧ x ∉ (otp_ideal (rT := ℝ)).fv ∧
        x ∉ Ctx.payloadFv K) →
      limExec ⟨K.fill (otp_enc m), σ₀⟩ (finalBool b) ≤
      limExec ⟨K.fill otp_ideal, σ₀⟩ (finalBool b) :=
  refines_sound_fresh (GF := GF) _ _ .real (otp_enc_typed m) otp_ideal_typed
    fun _ _ => otp_refines_real m

theorem otp_ctx_refines_rev_real (GF : BundledGFunctors) [RefinesPreGS ℝ GF] (m : ℝ) :
    ∀ (K : Ctx ℝ) (σ₀ : State ℝ) (b : Bool),
      TypedCtx K Tctx.empty .real Tctx.empty .bool → Ctx.BindersFresh K ∅ →
      (∀ x ∈ Ctx.binderAtoms K, x ∉ (otp_ideal (rT := ℝ)).fv ∧ x ∉ (otp_enc m).fv ∧
        x ∉ Ctx.payloadFv K) →
      limExec ⟨K.fill otp_ideal, σ₀⟩ (finalBool b) ≤
      limExec ⟨K.fill (otp_enc m), σ₀⟩ (finalBool b) :=
  refines_sound_fresh (GF := GF) _ _ .real otp_ideal_typed (otp_enc_typed m)
    fun _ _ => otp_refines_rev_real m

theorem otp_ctx_equiv_real (GF : BundledGFunctors) [RefinesPreGS ℝ GF] (m : ℝ)
    (K : Ctx ℝ) (σ₀ : State ℝ) (b : Bool) (hK : TypedCtx K Tctx.empty .real Tctx.empty .bool)
    (hbf : Ctx.BindersFresh K ∅) (hfresh : ∀ x ∈ Ctx.binderAtoms K, x ∉ (otp_enc m).fv ∧
      x ∉ (otp_ideal (rT := ℝ)).fv ∧ x ∉ Ctx.payloadFv K) :
    limExec ⟨K.fill (otp_enc m), σ₀⟩ (finalBool b) =
    limExec ⟨K.fill otp_ideal, σ₀⟩ (finalBool b) :=
  le_antisymm (otp_ctx_refines_real GF m K σ₀ b hK hbf hfresh) <|
    otp_ctx_refines_rev_real GF m K σ₀ b hK hbf fun x hx =>
      have ⟨henc, hideal, hpayload⟩ := hfresh x hx
      ⟨hideal, henc, hpayload⟩

theorem otp_advantage_zero (m : ℝ) : advantage (otp_enc m) otp_ideal = 0 :=
  advantage_eq_zero_of_limExecV_eq fun σ => otp_distribution_eq m σ σ

end ContinuousOTP
end ProbLang
