module

public import Metrology.Micrometer.AdequacyRel
public import Metrology.Micrometer.BinLogRelatedCtx
import Metrology.Iris.LocalBI
import Metrology.ProbLang.Syntax.Notation
public import Metrology.ProbLang.ContextualRefinement
public import Metrology.Couplings.Divergences.Dp

/-! # Contextual soundness

`↯b β -∗ REL[L] e << e' : interp L τ Δ` bounds every linear boolean context by `β` (divergence,
mass, DP: `refines_ctx_div`/`_mass`/`_dp`); without credits, `refines_sound_open_fresh`. -/

@[expose] public section

namespace ProbLang

open GradedLifting Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE
open ProbLang.MicrometerWpGS
open Val (fst)
open Exp (ofVal_of_toVal_some)
open Tctx (empty)
open TctxRelated (empty_nil)
open IsMassDetecting (measure_le measure_le_add)
open Ctx (BindersFresh binderAtoms payloadFv)

section RefinesSound
open MeasureTheory
variable {rT : Type} {GF : BundledGFunctors}
local bi IProp GF

/-! ## Pure facts: equal booleans and boolean results -/

variable (v v' : Val rT)

/-- Two values are the same boolean. -/
def boolEqVal : Prop :=
  ∃ b : Bool, v = .bool b ∧ v' = .bool b

/-- Related booleans are the same boolean. -/
theorem lrel_bool_to_boolEqVal [LawfulProbLangℝ rT] [MicrometerRGS rT .hasNoLC GF] :
    ⊢ lrel_bool.car v v' -∗ ⌜boolEqVal v v'⌝ := by
  iunfold lrel_bool
  iintro ⟨%b, %h⟩
  exact pure_intro ⟨b, h⟩

/-- Results related along equal booleans end in `b` together. -/
theorem adequacyRel_boolEqVal_mem {b : Bool} (a a' : Exp rT) (h : adequacyRel boolEqVal a a')
    (ha : a ∈ ({pl(#b)} : Set _)) : a' ∈ ({pl(#b)} : Set _) := by
  obtain ⟨v, v', hv, hv', b'', hvb1, hvb2⟩ := h
  have hv1 : v.1 = pl(#b'') := congrArg fst hvb1
  rw [show v.1 = pl(#b) from (ofVal_of_toVal_some hv).trans ha] at hv1
  obtain rfl : b'' = b := by simpa using hv1.symm
  exact (ofVal_of_toVal_some hv').symm.trans (congrArg fst hvb2)

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
    limExec ρ (finalBool b) = limExecV ρ {pl(#b)} := by
  unfold limExecV asExpr
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.singleton _)]
  rfl

/-! ## Closed programs at `bool` -/

variable (L) in
/-- A closed refinement at `bool` from `↯b β` couples the two runs at `β` along equal booleans. -/
theorem refines_bool_coupling (β : B) (e e' : Exp rT) (σ σ' : State rT)
    (Hlog : ∀ (_IR : MicrometerRGS rT .hasNoLC GF) (_IBC : BudgetCreditGS B GF),
      ⊢ ↯b β -∗ refines L ⊤ e e' (lrel_bool)) :
    L.Rel β (adequacyRel boolEqVal) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  approximates_coupling (fun _ _ => lrel_bool) boolEqVal e e' σ σ' β
    (fun _ _ v v' => lrel_bool_to_boolEqVal v v') Hlog

section Bind
variable [L.HasBind] [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing]

/-! ## Linear contexts under budget credits -/

variable (L) in
/-- A refinement from `↯b β` couples the runs of every linear boolean context at `β` along equal
booleans. -/
theorem refines_ctx_coupling (β : B) (e e' : Exp rT) (τ : Ty)
    (Hlog : ∀ (_IR : MicrometerRGS rT .hasNoLC GF) (_IBC : BudgetCreditGS B GF)
      Δ, ⊢ ↯b β -∗ refines L ⊤ e e' (interp L τ Δ))
    (K : Ctx rT) (σ σ' : State rT) (HK : TypedCtx K empty τ empty .bool)
    (Hlin : K.IsLinear) :
    L.Rel β (adequacyRel boolEqVal) (limExecV ⟨K.fill e, σ⟩) (limExecV ⟨K.fill e', σ'⟩) := by
  -- Adequacy at `lrel_bool` leaves a closed refinement of the filled programs.
  refine refines_bool_coupling L (GF := GF) β _ _ σ σ' fun IR IBC => ?_
  -- The closed refinement `Hlog` is an open one at the empty context.
  have Hrel : ∀ (Δ : TyEnv rT GF) (Γrc : RelCtx rT GF), TctxRelated L Δ empty Γrc →
      ⊢ ↯b β -∗ bin_log_related_ty L ⊤ Δ Γrc e e' τ := by
    intro Δ Γrc HCtx
    obtain rfl := HCtx.eq_nil_of_empty
    iintro Hb
    iapply bin_log_related_nil_intro
    iapply Hlog IR IBC Δ $$ Hb
  -- The credit passes through the linear context as a frame.
  have H := bin_log_related_under_linear_ctx HK Hlin Hrel (default : TyEnv rT GF) [] empty_nil
  -- `interp L .bool _` is `lrel_bool` by `rfl`.
  show ⊢ ↯b β -∗ refines L ⊤ (K.fill e) (K.fill e') (interp L .bool default)
  iintro Hb
  iapply bin_log_related_nil_elim
  iapply H $$ Hb

/-- A refinement from `↯b β` bounds the divergence of every linear boolean context's outputs by
`β`, for a divergence `D` the lifting is sound for. -/
theorem refines_ctx_div {D : GradedDivergence.{0} B} [L.IsSound D] (β : B) (e e' : Exp rT)
    (τ : Ty) (Hlog : ∀ (_IR : MicrometerRGS rT .hasNoLC GF) (_IBC : BudgetCreditGS B GF)
      Δ, ⊢ ↯b β -∗ refines L ⊤ e e' (interp L τ Δ))
    (K : Ctx rT) (σ σ' : State rT) (HK : TypedCtx K empty τ empty .bool)
    (Hlin : K.IsLinear) :
    D β (limExecV ⟨K.fill e, σ⟩) (limExecV ⟨K.fill e', σ'⟩) :=
  IsSound.sound ((refines_ctx_coupling L β e e' τ Hlog K σ σ' HK Hlin).mono le_rfl
    adequacyRel_boolEqVal_eq)

section
variable (s : ENNReal →+o B) [L.IsMassDetecting s]
include s

/-- A refinement from `↯b (s δ)` bounds the chance that a linear boolean context returns `b`
by that of the other side plus `δ`. -/
theorem refines_ctx_mass (δ : ENNReal) (e e' : Exp rT) (τ : Ty)
    (Hlog : ∀ (_IR : MicrometerRGS rT .hasNoLC GF) (_IBC : BudgetCreditGS B GF)
      Δ, ⊢ ↯b (s δ) -∗ refines L ⊤ e e' (interp L τ Δ))
    (K : Ctx rT) (σ σ' : State rT) (b : Bool) (HK : TypedCtx K empty τ empty .bool)
    (Hlin : K.IsLinear) :
    limExec ⟨K.fill e, σ⟩ (finalBool b) ≤ limExec ⟨K.fill e', σ'⟩ (finalBool b) + δ := by
  rw [limExec_finalBool, limExec_finalBool]
  exact measure_le_add (.singleton _) (.singleton _)
    (refines_ctx_coupling L (s δ) e e' τ Hlog K σ σ' HK Hlin) adequacyRel_boolEqVal_mem

/-! ## Without credits -/

variable (L) in
/-- A budget-free refinement makes each typed boolean context with fresh binders return `b` on the
left no more often than on the right, from the same state (the inequality inside `CtxRefines`). -/
theorem refines_sound_open_fresh (Γtc : Tctx) (e e' : Exp rT) (τ : Ty) (Hty_e : Typed Γtc e τ)
    (Hty_e' : Typed Γtc e' τ)
    (Hlog : ∀ (_IR : MicrometerRGS rT .hasNoLC GF) (_IBC : BudgetCreditGS B GF) Δ Γrc,
      TctxRelated L Δ Γtc Γrc → ⊢ bin_log_related_ty L ⊤ Δ Γrc e e' τ) :
    ∀ (K : Ctx rT) (σ₀ : State rT) (b : Bool), TypedCtx K Γtc τ empty .bool →
      BindersFresh K ∅ → (∀ x ∈ binderAtoms K, x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ payloadFv K) →
      limExec ⟨K.fill e, σ₀⟩ (finalBool b) ≤ limExec ⟨K.fill e', σ₀⟩ (finalBool b) := by
  intro K σ₀ b Htyped HfreshK Hbinders
  -- A budget-0 coupling through the unrestricted context lemma, then mass detection at `δ = 0`.
  rw [limExec_finalBool, limExec_finalBool]
  have hCpl : L.Rel 0 (adequacyRel boolEqVal) (limExecV ⟨K.fill e, σ₀⟩)
      (limExecV ⟨K.fill e', σ₀⟩) := by
    apply refines_coupling (GF := GF)
    · exact fun _ _ v v' => lrel_bool_to_boolEqVal v v'
    · intro IR IBC
      have HrelClosed : ⊢
          bin_log_related_ty L ⊤ (default : TyEnv rT GF) [] (K.fill e) (K.fill e') .bool :=
        bin_log_related_under_typed_ctx Htyped Hty_e Hty_e' Hbinders (Hlog IR IBC) _ _
          empty_nil HfreshK
      exact HrelClosed.trans bin_log_related_nil_elim
  exact measure_le (s := s) (.singleton _) (.singleton _) hCpl adequacyRel_boolEqVal_mem

/-- `refines_sound_open_fresh` for closed programs. -/
theorem refines_sound_fresh (e e' : Exp rT) (τ : Ty) (Hty_e : Typed empty e τ)
    (Hty_e' : Typed empty e' τ)
    (Hlog : ∀ (_IR : MicrometerRGS rT .hasNoLC GF) (_IBC : BudgetCreditGS B GF)
      Δ, ⊢ refines L ⊤ e e' (interp L τ Δ)) :
    ∀ (K : Ctx rT) (σ₀ : State rT) (b : Bool), TypedCtx K empty τ empty .bool →
      BindersFresh K ∅ → (∀ x ∈ binderAtoms K, x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ payloadFv K) →
      limExec ⟨K.fill e, σ₀⟩ (finalBool b) ≤ limExec ⟨K.fill e', σ₀⟩ (finalBool b) := by
  apply refines_sound_open_fresh L s (GF := GF) empty e e' τ Hty_e Hty_e'
  intro IR IBC Δ Γrc HCtx
  obtain rfl := HCtx.eq_nil_of_empty
  iapply bin_log_related_nil_intro
  iapply Hlog IR IBC Δ

end

end Bind

end Budget

end RefinesSound

/-! ## Differential privacy -/

section RefinesSoundDp
open MeasureTheory GradedDivergence
open scoped _root_.ENNReal
variable {rT : Type} [LawfulProbLangℝ rT] {GF : BundledGFunctors}
  [RefinesPreGS rT (ℝ≥0∞ × ℝ≥0∞) GF]
local bi IProp GF

/-- An `(ε, δ)`-DP refinement makes every linear boolean context `(ε, δ)`-DP:
`P[K[e] = b] ≤ e^ε P[K[e'] = b] + δ`. -/
theorem refines_ctx_dp {ε δ : ℝ≥0∞} (hε : ε ≠ ∞) (e e' : Exp rT) (τ : Ty)
    (Hlog : ∀ (_IR : MicrometerRGS rT .hasNoLC GF) (_IBC : BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF)
      Δ, ⊢ ↯b (ε, δ) -∗ refines (codensity dp) ⊤ e e' (interp (codensity dp) τ Δ))
    (K : Ctx rT) (σ σ' : State rT) (b : Bool) (HK : TypedCtx K empty τ empty .bool)
    (Hlin : K.IsLinear) :
    limExec ⟨K.fill e, σ⟩ (finalBool b) ≤
      expBudget ε * limExec ⟨K.fill e', σ'⟩ (finalBool b) + δ := by
  rw [limExec_finalBool, limExec_finalBool]
  exact dp_measure_le_add hε (refines_ctx_coupling _ (ε, δ) e e' τ Hlog K σ σ' HK Hlin)
    (.singleton _) (.singleton _) adequacyRel_boolEqVal_mem

end RefinesSoundDp

end ProbLang
