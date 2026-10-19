module

public import Metrology.Micrometer.AdequacyRel
public import Metrology.Micrometer.BinLogRelatedCtx
import Metrology.ProbLang.Syntax.Notation
public import Metrology.ProbLang.ContextualRefinement
public import Metrology.Couplings.Divergences.Dp

/-! Soundness of the logical relation for contextual refinement. -/

@[expose] public section

namespace ProbLang

open GradedLifting ProbLang.Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang
open ProbLang.MicrometerWpGS

section RefinesSound
open MeasureTheory
variable {rT : Type} {GF : BundledGFunctors}

/-- Two values are the same boolean. -/
def boolEqVal (v v' : Val rT) : Prop :=
  ∃ b : Bool, v = .bool b ∧ v' = .bool b

theorem lrel_bool_to_boolEqVal [LawfulProbLangℝ rT] [MicrometerRGS rT .hasNoLC GF] (v v' : Val rT) :
    ⊢@{IProp GF} lrel_bool.car v v' -∗ ⌜boolEqVal v v'⌝ := by
  iunfold lrel_bool
  iintro ⟨%b, %h⟩
  exact pure_intro ⟨b, h⟩

/-- Results related along equal booleans end in `b` together. -/
theorem adequacyRel_boolEqVal_mem {b : Bool} (a a' : Exp rT) (h : adequacyRel boolEqVal a a')
    (ha : a ∈ ({pl(#(.bool b))} : Set (Exp rT))) : a' ∈ ({pl(#(.bool b))} : Set (Exp rT)) := by
  obtain ⟨v, v', hv, hv', b'', hvb1, hvb2⟩ := h
  have hv1 : v.1 = pl(#(.bool b'')) := congrArg Val.fst hvb1
  rw [show v.1 = pl(#(.bool b)) from (Exp.ofVal_of_toVal_some hv).trans ha] at hv1
  obtain rfl : b'' = b := by simpa using hv1.symm
  exact (Exp.ofVal_of_toVal_some hv').symm.trans (congrArg Val.fst hvb2)

/-- Results related along equal booleans are equal. -/
theorem adequacyRel_boolEqVal_eq (a a' : Exp rT) (h : adequacyRel boolEqVal a a') : a = a' :=
  let ⟨v, v', hv, hv', _, h1, h2⟩ := h
  adequacyRel_eq_subset a a' ⟨v, v', hv, hv', h1.trans h2.symm⟩

section Budget
variable [LawfulProbLangℝ rT] {B : Type} [AddCommMonoid B] [PartialOrder B]
  [CanonicallyOrderedAdd B] [OrderTop B] [Nontrivial B] {L : GradedLifting.{0} B} [L.IsLawful]
  [L.IsZeroLeft] [L.IsLeftContinuous] [L.IsBudgetClosed] [RefinesPreGS rT B GF]

/-- The runs of `ρ` that end in the boolean `b` are the mass of its results at `b`. -/
theorem limExec_finalBool (ρ : Cfg rT) (b : Bool) :
    limExec ρ (finalBool b) = limExecV ρ {pl(#(.bool b))} := by
  unfold limExecV asExpr
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.singleton _)]
  rfl

/-! ### Contextual soundness under budget credits -/

variable (L) in
/-- A closed refinement at `bool` from `↯b β` couples the two runs at `β` along equal booleans. -/
theorem refines_bool_coupling (β : B) (E E' : Exp rT) (σ σ' : State rT)
    (Hlog : ∀ (_IR : MicrometerRGS rT .hasNoLC GF) (_IBC : BudgetCreditGS B GF),
      ⊢@{IProp GF} ↯b β -∗ refines L ⊤ E E' (lrel_bool)) :
    L.Rel β (adequacyRel boolEqVal) (limExecV ⟨E, σ⟩) (limExecV ⟨E', σ'⟩) :=
  approximates_coupling (fun _ _ => lrel_bool) boolEqVal E E' σ σ' β
    (fun _ _ v v' => lrel_bool_to_boolEqVal v v') Hlog

section Bind
variable [L.HasBind] [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing]

variable (L) in
theorem refines_sound_open_fresh (s : ENNReal →+o B) [L.IsMassDetecting s] (Γtc : Tctx)
    (e e' : Exp rT) (τ : Ty) (Hty_e : Typed Γtc e τ) (Hty_e' : Typed Γtc e' τ)
    (Hlog : ∀ (_IR : MicrometerRGS rT .hasNoLC GF) (_IBC : BudgetCreditGS B GF)
      (Δ : TyEnv rT GF) (Γrc : RelCtx rT GF), TctxRelated L Δ Γtc Γrc →
        ⊢@{IProp GF} bin_log_related_ty L (hlc := .hasNoLC) ⊤ Δ Γrc e e' τ) :
    ∀ (K : Ctx rT) (σ₀ : State rT) (b : Bool), TypedCtx K Γtc τ Tctx.empty .bool →
      Ctx.BindersFresh K ∅ → (∀ x ∈ Ctx.binderAtoms K, x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ Ctx.payloadFv K) →
      limExec ⟨K.fill e, σ₀⟩ (finalBool b) ≤ limExec ⟨K.fill e', σ₀⟩ (finalBool b) := by
  intro K σ₀ b Htyped HfreshK Hbinders
  rw [limExec_finalBool, limExec_finalBool]
  have hCpl : L.Rel 0 (adequacyRel boolEqVal) (limExecV ⟨K.fill e, σ₀⟩)
      (limExecV ⟨K.fill e', σ₀⟩) := by
    apply refines_coupling (GF := GF)
    · exact fun _ _ v v' => lrel_bool_to_boolEqVal v v'
    · intro IR IBC
      have HrelClosed : ⊢@{IProp GF}
          bin_log_related_ty L ⊤ (default : TyEnv rT GF) [] (K.fill e) (K.fill e') .bool :=
        bin_log_related_under_typed_ctx Htyped Hty_e Hty_e' Hbinders (Hlog IR IBC) _ _
          TctxRelated.empty_nil HfreshK
      unfold bin_log_related_ty bin_log_related at HrelClosed
      show ⊢@{IProp GF} refines L ⊤
        (Exp.substMap (ValSubstMap.fst ([] : ValSubstMap rT)) (K.fill e))
        (Exp.substMap (ValSubstMap.snd ([] : ValSubstMap rT)) (K.fill e'))
        (interp L Ty.bool (default : TyEnv rT GF))
      iapply HrelClosed $$ %([] : ValSubstMap rT)
      iapply env_ltyped2_empty
  exact IsMassDetecting.measure_le (s := s) (.singleton _) (.singleton _) hCpl
    adequacyRel_boolEqVal_mem

theorem refines_sound_fresh (s : ENNReal →+o B) [L.IsMassDetecting s] (e e' : Exp rT) (τ : Ty)
    (Hty_e : Typed Tctx.empty e τ) (Hty_e' : Typed Tctx.empty e' τ)
    (Hlog : ∀ (_IR : MicrometerRGS rT .hasNoLC GF) (_IBC : BudgetCreditGS B GF)
      (Δ : TyEnv rT GF), ⊢@{IProp GF} refines L (hlc := .hasNoLC) ⊤ e e' (interp L τ Δ)) :
    ∀ (K : Ctx rT) (σ₀ : State rT) (b : Bool), TypedCtx K Tctx.empty τ Tctx.empty .bool →
      Ctx.BindersFresh K ∅ → (∀ x ∈ Ctx.binderAtoms K, x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ Ctx.payloadFv K) →
      limExec ⟨K.fill e, σ₀⟩ (finalBool b) ≤ limExec ⟨K.fill e', σ₀⟩ (finalBool b) := by
  apply refines_sound_open_fresh L s (GF := GF) Tctx.empty e e' τ Hty_e Hty_e'
  intro IR IBC Δ Γrc HCtx
  obtain rfl := HCtx.eq_nil_of_empty
  unfold bin_log_related_ty bin_log_related
  iintro %vs Hvs
  ihave ⟨%hvs_nil⟩ := env_ltyped2_empty_inv vs $$ Hvs
  rw [hvs_nil]
  iclear Hvs
  show ⊢@{IProp GF} refines L ⊤ e e' (interp L τ Δ)
  exact Hlog IR IBC Δ

variable (L) in
/-- A refinement from `↯b β` couples the runs of every linear boolean context at `β` along equal
booleans: the credits are a frame, and the context's own steps are budget-free. -/
theorem refines_ctx_coupling (β : B) (e e' : Exp rT) (τ : Ty)
    (Hlog : ∀ (_IR : MicrometerRGS rT .hasNoLC GF) (_IBC : BudgetCreditGS B GF)
      (Δ : TyEnv rT GF), ⊢@{IProp GF} ↯b β -∗ refines L ⊤ e e' (interp L τ Δ))
    (K : Ctx rT) (σ σ' : State rT) (HK : TypedCtx K Tctx.empty τ Tctx.empty .bool)
    (Hlin : K.IsLinear) :
    L.Rel β (adequacyRel boolEqVal) (limExecV ⟨K.fill e, σ⟩) (limExecV ⟨K.fill e', σ'⟩) := by
  refine refines_bool_coupling L (GF := GF) β _ _ σ σ' fun IR IBC => ?_
  have Hrel : ∀ (Δ : TyEnv rT GF) (Γrc : RelCtx rT GF), TctxRelated L Δ Tctx.empty Γrc →
      ⊢@{IProp GF} ↯b β -∗ bin_log_related_ty L ⊤ Δ Γrc e e' τ := by
    intro Δ Γrc HCtx
    obtain rfl := HCtx.eq_nil_of_empty
    unfold bin_log_related_ty bin_log_related
    iintro Hb %vs Hvs
    ihave ⟨%hvs_nil⟩ := env_ltyped2_empty_inv vs $$ Hvs
    subst hvs_nil
    iapply (show ⊢@{IProp GF} ↯b β -∗ refines L ⊤ (Exp.substMap (ValSubstMap.fst []) e)
      (Exp.substMap (ValSubstMap.snd []) e') (interp L τ Δ) from Hlog IR IBC Δ) $$ Hb
  have H := bin_log_related_under_linear_ctx HK Hlin Hrel (default : TyEnv rT GF) []
    TctxRelated.empty_nil
  unfold bin_log_related_ty bin_log_related at H
  show ⊢@{IProp GF} ↯b β -∗ refines L ⊤
    (Exp.substMap (ValSubstMap.fst ([] : ValSubstMap rT)) (K.fill e))
    (Exp.substMap (ValSubstMap.snd ([] : ValSubstMap rT)) (K.fill e'))
    (interp L Ty.bool (default : TyEnv rT GF))
  iintro Hb
  iapply H $$ Hb %([] : ValSubstMap rT)
  iapply env_ltyped2_empty

/-- A refinement from `↯b β` bounds the divergence of every linear boolean context's outputs by
`β`, for a divergence `D` the lifting is sound for. -/
theorem refines_ctx_div {D : GradedDivergence.{0} B} [L.IsSound D] (β : B) (e e' : Exp rT)
    (τ : Ty) (Hlog : ∀ (_IR : MicrometerRGS rT .hasNoLC GF) (_IBC : BudgetCreditGS B GF)
      (Δ : TyEnv rT GF), ⊢@{IProp GF} ↯b β -∗ refines L ⊤ e e' (interp L τ Δ))
    (K : Ctx rT) (σ σ' : State rT) (HK : TypedCtx K Tctx.empty τ Tctx.empty .bool)
    (Hlin : K.IsLinear) :
    D β (limExecV ⟨K.fill e, σ⟩) (limExecV ⟨K.fill e', σ'⟩) :=
  IsSound.sound ((refines_ctx_coupling L β e e' τ Hlog K σ σ' HK Hlin).mono le_rfl
    adequacyRel_boolEqVal_eq)

/-- A refinement from `↯b (s δ)` bounds the chance that a linear boolean context returns `b`
by that of the other side plus `δ`. -/
theorem refines_ctx_mass (s : ENNReal →+o B) [L.IsMassDetecting s] (δ : ENNReal)
    (e e' : Exp rT) (τ : Ty)
    (Hlog : ∀ (_IR : MicrometerRGS rT .hasNoLC GF) (_IBC : BudgetCreditGS B GF)
      (Δ : TyEnv rT GF), ⊢@{IProp GF} ↯b (s δ) -∗ refines L ⊤ e e' (interp L τ Δ))
    (K : Ctx rT) (σ σ' : State rT) (b : Bool) (HK : TypedCtx K Tctx.empty τ Tctx.empty .bool)
    (Hlin : K.IsLinear) :
    limExec ⟨K.fill e, σ⟩ (finalBool b) ≤ limExec ⟨K.fill e', σ'⟩ (finalBool b) + δ := by
  rw [limExec_finalBool, limExec_finalBool]
  exact IsMassDetecting.measure_le_add (.singleton _) (.singleton _)
    (refines_ctx_coupling L (s δ) e e' τ Hlog K σ σ' HK Hlin) adequacyRel_boolEqVal_mem

end Bind

end Budget

end RefinesSound

section RefinesSoundDp
open MeasureTheory GradedDivergence
open scoped _root_.ENNReal
variable {rT : Type} [LawfulProbLangℝ rT] {GF : BundledGFunctors}
  [RefinesPreGS rT (ℝ≥0∞ × ℝ≥0∞) GF]

/-- An `(ε, δ)`-DP refinement makes every linear boolean context `(ε, δ)`-DP:
`P[K[e] = b] ≤ e^ε P[K[e'] = b] + δ`. -/
theorem refines_ctx_dp {ε δ : ℝ≥0∞} (hε : ε ≠ ∞) (e e' : Exp rT) (τ : Ty)
    (Hlog : ∀ (_IR : MicrometerRGS rT .hasNoLC GF) (_IBC : BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF)
      (Δ : TyEnv rT GF),
        ⊢@{IProp GF} ↯b (ε, δ) -∗ refines (codensity dp) ⊤ e e' (interp (codensity dp) τ Δ))
    (K : Ctx rT) (σ σ' : State rT) (b : Bool) (HK : TypedCtx K Tctx.empty τ Tctx.empty .bool)
    (Hlin : K.IsLinear) :
    limExec ⟨K.fill e, σ⟩ (finalBool b) ≤
      expBudget ε * limExec ⟨K.fill e', σ'⟩ (finalBool b) + δ := by
  rw [limExec_finalBool, limExec_finalBool]
  exact dp_measure_le_add hε (refines_ctx_coupling _ (ε, δ) e e' τ Hlog K σ σ' HK Hlin)
    (.singleton _) (.singleton _) adequacyRel_boolEqVal_mem

end RefinesSoundDp

end ProbLang
