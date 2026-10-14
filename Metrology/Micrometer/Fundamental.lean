module

public import Metrology.Micrometer.PrimitiveLaws
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Micrometer.Model
public import Metrology.Micrometer.Compatibility
public import Metrology.Micrometer.AppRelRules
public import Metrology.Micrometer.ContinuousSampler
public import Metrology.Micrometer.RelTactics
public import Metrology.Micrometer.Interp

@[expose] public section

/-! # Fundamental Theorem -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS

namespace ProbLang

open Cslib Exp

section Fundamental
variable {rT : Type} [LawfulProbLangℝ rT]
variable {hlc : HasLC} {ι : Type} [Monoid ι] {D : GradedDivergence.{0} ι}
  {GF : BundledGFunctors} [IR : MicrometerRGS rT hlc GF]
  [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft]

/-! ## Tctx → RelCtx lifting -/

variable (D) in
def TctxRelated (Δ : TyEnv rT GF) (Γtc : Tctx) (Γrc : RelCtx rT GF) : Prop :=
  ∀ x, (Γtc x).map (fun τ => interp D τ Δ) = Γrc.lookup x

/-! ## Compatibility lemmas -/

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
theorem bin_log_related_var (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (x : Var) (τ : Ty)
    (hΓ : Γ.lookup x = some (interp D τ Δ)) :
    ⊢@{IProp GF} bin_log_related_ty D ⊤ Δ Γ (.fvar x) (.fvar x) τ := by
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  icases env_ltyped2_lookup Γ vs x (interp D τ Δ) hΓ $$ Hvs with ⟨%v1, %v2, %hvs_eq, HA⟩
  ihave %hfst_closed := env_ltyped2_fst_allClosed Γ vs $$ Hvs
  ihave %hsnd_closed := env_ltyped2_snd_allClosed Γ vs $$ Hvs
  have hfst_lookup : SubstMap.lookup vs.fst x = some v1.1 := by
    rw [ValSubstMap.fst_lookup, hvs_eq]; rfl
  have hsnd_lookup : SubstMap.lookup vs.snd x = some v2.1 := by
    rw [ValSubstMap.snd_lookup, hvs_eq]; rfl
  rw [substMap_fvar_lookup_some _ _ hfst_closed hfst_lookup,
    substMap_fvar_lookup_some _ _ hsnd_closed hsnd_lookup]
  iapply refines_ret rfl rfl
  imodintro
  iexact HA

private theorem substMap_open_fresh_pair {vs vs' : ValSubstMap rT} {x : Var} {v v' : Val rT}
    {e e' : Exp rT} (hvs' : vs' = (x, (v, v')) :: vs)
    (hfst : SubstMap.AllClosed vs.fst) (hsnd : SubstMap.AllClosed vs.snd)
    (hxe : x ∉ e.fv) (hxe' : x ∉ e'.fv) (hxdom : x ∉ (vs.map (·.1)).toFinset)
    (hv : v.1.isClosedEmpty) (hv' : v'.1.isClosedEmpty) :
    substMap vs'.fst (open' e (.fvar x)) = open' (substMap vs.fst e) v.1 ∧
    substMap vs'.snd (open' e' (.fvar x)) = open' (substMap vs.snd e') v'.1 := by
  subst hvs'
  exact ⟨substMap_open_fresh hfst hxe (ValSubstMap.fst_lookup_eq_none_of_not_mem hxdom) hv.1,
    substMap_open_fresh hsnd hxe' (ValSubstMap.snd_lookup_eq_none_of_not_mem hxdom) hv'.1⟩

private theorem fv_subset_substMap_dom {Γ : RelCtx rT GF} {vs : ValSubstMap rT} {e e' : Exp rT}
    (hdom : (Γ.map (·.1)).toFinset ⊆ (vs.map (·.1)).toFinset)
    (he : e.fv ⊆ (Γ.map (·.1)).toFinset) (he' : e'.fv ⊆ (Γ.map (·.1)).toFinset) :
    e.fv ⊆ (vs.fst.map (·.1)).toFinset ∧ e'.fv ⊆ (vs.snd.map (·.1)).toFinset := by
  rw [ValSubstMap.fst_dom, ValSubstMap.snd_dom]
  exact ⟨he.trans hdom, he'.trans hdom⟩

/-! ### Lifting `refines` compatibility to `bin_log_related`

`bin_log_related_lift{1,2,3}` push `substMap` through a constructor `f` and apply a
`refines` rule for `f`. -/

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
private theorem bin_log_related_lift1 {Γ : RelCtx rT GF} {e e' : Exp rT} {A B : lrel rT GF}
    {f : Exp rT → Exp rT} (hf : ∀ σ t, substMap σ (f t) = f (substMap σ t))
    (H : ∀ t t', refines D ⊤ t t' A ⊢ refines D ⊤ (f t) (f t') B) :
    bin_log_related D ⊤ Γ e e' A ⊢ bin_log_related D ⊤ Γ (f e) (f e') B := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [hf, hf]
  iapply H _ _ $$ IH'

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
private theorem bin_log_related_lift2 {Γ : RelCtx rT GF} {e1 e2 e1' e2' : Exp rT}
    {A1 A2 B : lrel rT GF} {f : Exp rT → Exp rT → Exp rT}
    (hf : ∀ σ t1 t2, substMap σ (f t1 t2) = f (substMap σ t1) (substMap σ t2))
    (H : ∀ t1 t2 t1' t2', iprop%
      refines D ⊤ t1 t1' A1 ⊢ refines D ⊤ t2 t2' A2 -∗ refines D ⊤ (f t1 t2) (f t1' t2') B) : iprop%
    bin_log_related D ⊤ Γ e1 e1' A1 ⊢
    bin_log_related D ⊤ Γ e2 e2' A2 -∗ bin_log_related D ⊤ Γ (f e1 e2) (f e1' e2') B := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  ihave IH1' := IH1 $$ %vs Hvs
  ihave IH2' := IH2 $$ %vs Hvs
  rw [hf, hf]
  iapply H _ _ _ _ $$ IH1' IH2'

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
private theorem bin_log_related_lift3 {Γ : RelCtx rT GF} {e0 e1 e2 e0' e1' e2' : Exp rT}
    {A0 A1 A2 B : lrel rT GF} {f : Exp rT → Exp rT → Exp rT → Exp rT}
    (hf : ∀ σ t0 t1 t2,
      substMap σ (f t0 t1 t2) = f (substMap σ t0) (substMap σ t1) (substMap σ t2))
    (H : ∀ t0 t1 t2 t0' t1' t2', iprop%
      refines D ⊤ t0 t0' A0 ⊢ refines D ⊤ t1 t1' A1 -∗ refines D ⊤ t2 t2' A2 -∗
      refines D ⊤ (f t0 t1 t2) (f t0' t1' t2') B) : iprop%
    bin_log_related D ⊤ Γ e0 e0' A0 ⊢
    bin_log_related D ⊤ Γ e1 e1' A1 -∗ bin_log_related D ⊤ Γ e2 e2' A2 -∗
    bin_log_related D ⊤ Γ (f e0 e1 e2) (f e0' e1' e2') B := by
  unfold bin_log_related
  iintro IH0 IH1 IH2 %vs #Hvs
  ihave IH0' := IH0 $$ %vs Hvs
  ihave IH1' := IH1 $$ %vs Hvs
  ihave IH2' := IH2 $$ %vs Hvs
  rw [hf, hf]
  iapply H _ _ _ _ _ _ $$ IH0' IH1' IH2'

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
private theorem bin_log_related_lit (Γ : RelCtx rT GF) (l : BaseLit rT) {A : lrel rT GF}
    (HA : ⊢@{IProp GF} A.car (.ofBaseLit l) (.ofBaseLit l)) :
    ⊢@{IProp GF} bin_log_related D ⊤ Γ (.lit l) (.lit l) A := by
  unfold bin_log_related
  iintro %vs -
  rw [substMap_lit, substMap_lit, show lit l = (Val.ofBaseLit l).1 from rfl]
  iapply refines_ret rfl rfl
  imodintro
  iapply HA

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
theorem bin_log_related_pair (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e1 e2 e1' e2' : Exp rT}
    {τ1 τ2 : Ty} : iprop%
    bin_log_related_ty D ⊤ Δ Γ e1 e1' τ1 ⊢
    bin_log_related_ty D ⊤ Δ Γ e2 e2' τ2 -∗
    bin_log_related_ty D ⊤ Δ Γ (.pair e1 e2) (.pair e1' e2') (.prod τ1 τ2) :=
  bin_log_related_lift2 substMap_pair fun _ _ _ _ => refines_pair

theorem bin_log_related_fst (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ1 τ2 : Ty} :
    bin_log_related_ty D ⊤ Δ Γ e e' (.prod τ1 τ2) ⊢
    bin_log_related_ty D ⊤ Δ Γ (.fst e) (.fst e') τ1 :=
  bin_log_related_lift1 substMap_fst fun _ _ => refines_fst

theorem bin_log_related_snd (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ1 τ2 : Ty} :
    bin_log_related_ty D ⊤ Δ Γ e e' (.prod τ1 τ2) ⊢
    bin_log_related_ty D ⊤ Δ Γ (.snd e) (.snd e') τ2 :=
  bin_log_related_lift1 substMap_snd fun _ _ => refines_snd

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
theorem bin_log_related_injl (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ1 τ2 : Ty} :
    bin_log_related_ty D ⊤ Δ Γ e e' τ1 ⊢
    bin_log_related_ty D ⊤ Δ Γ (.inl e) (.inl e') (.sum τ1 τ2) :=
  bin_log_related_lift1 substMap_inl fun _ _ => refines_injl

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
theorem bin_log_related_injr (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ1 τ2 : Ty} :
    bin_log_related_ty D ⊤ Δ Γ e e' τ2 ⊢
    bin_log_related_ty D ⊤ Δ Γ (.inr e) (.inr e') (.sum τ1 τ2) :=
  bin_log_related_lift1 substMap_inr fun _ _ => refines_injr

theorem bin_log_related_case (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e0 e1 e2 e0' e1' e2' : Exp rT} {τ1 τ2 τ3 : Ty} : iprop%
    bin_log_related_ty D ⊤ Δ Γ e0 e0' (.sum τ1 τ2) ⊢
    bin_log_related_ty D ⊤ Δ Γ e1 e1' (.arrow τ1 τ3) -∗
    bin_log_related_ty D ⊤ Δ Γ e2 e2' (.arrow τ2 τ3) -∗
    bin_log_related_ty D ⊤ Δ Γ (.case e0 e1 e2) (.case e0' e1' e2') τ3 :=
  bin_log_related_lift3 substMap_case fun _ _ _ _ _ _ => refines_case

theorem bin_log_related_if (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e0 e1 e2 e0' e1' e2' : Exp rT} {τ : Ty} : iprop%
    bin_log_related_ty D ⊤ Δ Γ e0 e0' .bool ⊢
    bin_log_related_ty D ⊤ Δ Γ e1 e1' τ -∗
    bin_log_related_ty D ⊤ Δ Γ e2 e2' τ -∗
    bin_log_related_ty D ⊤ Δ Γ (.cond e0 e1 e2) (.cond e0' e1' e2') τ :=
  bin_log_related_lift3 substMap_cond fun _ _ _ _ _ _ => refines_if

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
theorem bin_log_related_app (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e1 e2 e1' e2' : Exp rT}
    {τ1 τ2 : Ty} : iprop%
    bin_log_related_ty D ⊤ Δ Γ e1 e1' (.arrow τ1 τ2) ⊢
    bin_log_related_ty D ⊤ Δ Γ e2 e2' τ1 -∗
    bin_log_related_ty D ⊤ Δ Γ (.app e1 e2) (.app e1' e2') τ2 :=
  bin_log_related_lift2 substMap_app fun _ _ _ _ => refines_app

theorem bin_log_related_lam (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ1 τ2 : Ty}
    (L : Finset Var) (he_lc : ∀ x ∉ L, (open' e (.fvar x)).IsLocallyClosed)
    (he'_lc : ∀ x ∉ L, (open' e' (.fvar x)).IsLocallyClosed)
    (he_fv : e.fv ⊆ (Γ.map (·.1)).toFinset) (he'_fv : e'.fv ⊆ (Γ.map (·.1)).toFinset)
    (Hbody : ∀ x ∉ L, ⊢@{IProp GF} bin_log_related_ty D ⊤ Δ ((x, interp D τ1 Δ) :: Γ)
      (open' e (.fvar x)) (open' e' (.fvar x)) τ2) :
    ⊢@{IProp GF} bin_log_related_ty D ⊤ Δ Γ (.lam e) (.lam e') (.arrow τ1 τ2) := by
  unfold bin_log_related_ty bin_log_related at Hbody ⊢
  iintro %vs #Hvs
  rw [substMap_lam, substMap_lam, interp_arrow]
  ihave %hvsfst_closed := env_ltyped2_fst_allClosed Γ vs $$ Hvs
  ihave %hvssnd_closed := env_ltyped2_snd_allClosed Γ vs $$ Hvs
  have hlam_lc : (Exp.lam (substMap vs.fst e)).IsLocallyClosed :=
    lam_substMap_isLocallyClosed hvsfst_closed
      (fun _ hy => ValSubstMap.fst_lookup_eq_none_of_not_mem hy) he_lc
  have hlam'_lc : (Exp.lam (substMap vs.snd e')).IsLocallyClosed :=
    lam_substMap_isLocallyClosed hvssnd_closed
      (fun _ hy => ValSubstMap.snd_lookup_eq_none_of_not_mem hy) he'_lc
  ihave %hΓdomVs := env_ltyped2_domSubset Γ vs $$ Hvs
  obtain ⟨he_dom_fst, he_dom_snd⟩ := fv_subset_substMap_dom hΓdomVs he_fv he'_fv
  have hlam_closed : (Exp.lam (substMap vs.fst e)).isClosedEmpty ∧
      (Exp.lam (substMap vs.snd e')).isClosedEmpty :=
    ⟨⟨hlam_lc, substMap_fv_eq_empty hvsfst_closed he_dom_fst⟩,
      ⟨hlam'_lc, substMap_fv_eq_empty hvssnd_closed he_dom_snd⟩⟩
  iapply refines_arrow_val (v := ⟨.lam (substMap vs.fst e), IsVal.lam (by is_lc), by is_lc⟩)
    (v' := ⟨.lam (substMap vs.snd e'), IsVal.lam (by is_lc), by is_lc⟩) hlam_closed
  iintro !> %v1 %v2 #HA
  ihave %hv1v2_closed := interp_closed τ1 v1 v2 $$ HA
  obtain ⟨x, hx⟩ := HasFresh.fresh_exists (L ∪ e.fv ∪ e'.fv ∪ (vs.map (·.1)).toFinset)
  simp only [Finset.mem_union, not_or] at hx
  obtain ⟨⟨⟨hxL, hxFvE⟩, hxFvE'⟩, hxNotDom⟩ := hx
  let vs' : ValSubstMap rT := (x, (v1, v2)) :: vs
  ihave Hvs' : iprop(env_ltyped2 ((x, interp D τ1 Δ) :: Γ) vs') $$ [HA]
  · iapply env_ltyped2_insert Γ vs x (interp D τ1 Δ) v1 v2
      hv1v2_closed.1.toFvSubsetEmpty hv1v2_closed.2.toFvSubsetEmpty
    iframe HA Hvs
  ihave HbodyApplied := Hbody x hxL $$ Hvs'
  obtain ⟨hbridge_fst, hbridge_snd⟩ := substMap_open_fresh_pair (vs' := vs') rfl
    hvsfst_closed hvssnd_closed hxFvE hxFvE' hxNotDom hv1v2_closed.1 hv1v2_closed.2
  isimp only [hbridge_fst, hbridge_snd] at HbodyApplied
  rw [Ectx.eq_fill_nil (.app (.lam (substMap vs.fst e)) v1.1),
    Ectx.eq_fill_nil (.app (.lam (substMap vs.snd e')) v2.1)]
  iapply refines_pure_l (e' := open' (substMap vs.fst e) v1.1) (Hex := pureExec_app_lam)
    ⟨v1.2.toIsValue, by is_lc⟩
  inext
  iapply refines_pure_r (e' := open' (substMap vs.snd e') v2.1) (Hex := pureExec_app_lam)
    ⟨v2.2.toIsValue, by is_lc⟩
  simp only [Ectx.fill_nil]
  iexact HbodyApplied

theorem bin_log_related_fix (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ1 τ2 : Ty}
    (L : Finset Var) (he_lc : ∀ f ∉ L, (open' e (.fvar f)).IsLocallyClosed)
    (he'_lc : ∀ f ∉ L, (open' e' (.fvar f)).IsLocallyClosed)
    (he_fv : e.fv ⊆ (Γ.map (·.1)).toFinset) (he'_fv : e'.fv ⊆ (Γ.map (·.1)).toFinset)
    (Hbody : ∀ f ∉ L, ⊢@{IProp GF} bin_log_related_ty D ⊤ Δ ((f, interp D (.arrow τ1 τ2) Δ) :: Γ)
      (open' e (.fvar f)) (open' e' (.fvar f)) (.arrow τ1 τ2)) :
    ⊢@{IProp GF} bin_log_related_ty D ⊤ Δ Γ (.fix e) (.fix e') (.arrow τ1 τ2) := by
  unfold bin_log_related_ty bin_log_related at Hbody ⊢
  iintro %vs #Hvs
  rw [substMap_fix, substMap_fix, interp_arrow]
  ihave %hvsfst_closed := env_ltyped2_fst_allClosed Γ vs $$ Hvs
  ihave %hvssnd_closed := env_ltyped2_snd_allClosed Γ vs $$ Hvs
  have hfix_lc : (Exp.fix (substMap vs.fst e)).IsLocallyClosed :=
    fix_substMap_isLocallyClosed hvsfst_closed
      (fun _ hy => ValSubstMap.fst_lookup_eq_none_of_not_mem hy) he_lc
  have hfix'_lc : (Exp.fix (substMap vs.snd e')).IsLocallyClosed :=
    fix_substMap_isLocallyClosed hvssnd_closed
      (fun _ hy => ValSubstMap.snd_lookup_eq_none_of_not_mem hy) he'_lc
  ihave %hΓdomVs := env_ltyped2_domSubset Γ vs $$ Hvs
  obtain ⟨he_dom_fst, he_dom_snd⟩ := fv_subset_substMap_dom hΓdomVs he_fv he'_fv
  have hfix_closed : (Exp.fix (substMap vs.fst e)).isClosedEmpty ∧
      (Exp.fix (substMap vs.snd e')).isClosedEmpty :=
    ⟨⟨hfix_lc, substMap_fv_eq_empty hvsfst_closed he_dom_fst⟩,
      ⟨hfix'_lc, substMap_fv_eq_empty hvssnd_closed he_dom_snd⟩⟩
  obtain ⟨f, hf⟩ := HasFresh.fresh_exists (L ∪ e.fv ∪ e'.fv ∪ (vs.map (·.1)).toFinset)
  simp only [Finset.mem_union, not_or] at hf
  obtain ⟨⟨⟨hfL, hfFvE⟩, hfFvE'⟩, hfNotDom⟩ := hf
  iapply refines_ret (e1 := .fix (substMap vs.fst e)) (e2 := .fix (substMap vs.snd e'))
    (v1 := ⟨_, IsVal.fix (by is_lc), by is_lc⟩) (v2 := ⟨_, IsVal.fix (by is_lc), by is_lc⟩) rfl rfl
  imodintro
  iapply loeb_wand (P := (lrel_arr D (interp D τ1 Δ) (interp D τ2 Δ)).car
    ⟨.fix (substMap vs.fst e), IsVal.fix (by is_lc), by is_lc⟩
    ⟨.fix (substMap vs.snd e'), IsVal.fix (by is_lc), by is_lc⟩)
  iintro !> #IH
  unfold lrel_arr
  isplitr; · ipureintro; exact hfix_closed
  iintro !> %v1 %v2 #HA
  rw [Ectx.eq_fill_nil (.app (.fix (substMap vs.fst e)) v1.1),
    Ectx.eq_fill_nil (.app (.fix (substMap vs.snd e')) v2.1)]
  iapply refines_pure_l (e' := .app (open' (substMap vs.fst e) (.fix (substMap vs.fst e))) v1.1)
    (Hex := pureExec_app_fix) ⟨v1.2.toIsValue, by is_lc⟩
  inext
  iapply refines_pure_r (e' := .app (open' (substMap vs.snd e') (.fix (substMap vs.snd e'))) v2.1)
    (Hex := pureExec_app_fix) ⟨v2.2.toIsValue, by is_lc⟩
  let fixv : Val rT := ⟨.fix (substMap vs.fst e), IsVal.fix (by is_lc), by is_lc⟩
  let fixv' : Val rT := ⟨.fix (substMap vs.snd e'), IsVal.fix (by is_lc), by is_lc⟩
  let vs' : ValSubstMap rT := (f, (fixv, fixv')) :: vs
  ihave Hvs' : iprop(env_ltyped2 ((f, interp D (.arrow τ1 τ2) Δ) :: Γ) vs') $$ [IH]
  · rw [interp_arrow]
    iapply env_ltyped2_insert Γ vs f (lrel_arr D (interp D τ1 Δ) (interp D τ2 Δ))
      fixv fixv' hfix_closed.1.toFvSubsetEmpty hfix_closed.2.toFvSubsetEmpty
    isplitr [IH]
    · iunfold lrel_arr
      iexact IH
    iexact Hvs
  ihave HbodyApplied := Hbody f hfL $$ Hvs'
  obtain ⟨hbridge_fst, hbridge_snd⟩ := substMap_open_fresh_pair (vs' := vs') rfl
    hvsfst_closed hvssnd_closed hfFvE hfFvE' hfNotDom hfix_closed.1 hfix_closed.2
  isimp only [hbridge_fst, hbridge_snd, interp_arrow] at HbodyApplied
  ihave HArgs : iprop(refines D ⊤ v1.1 v2.1 (interp D τ1 Δ)) $$ [HA]
  · iapply refines_ret rfl rfl
    imodintro
    iexact HA
  simp only [Ectx.fill_nil]
  iapply refines_app $$ HbodyApplied HArgs

/-! ### Heap and tape cases -/

section Discrete

theorem bin_log_related_alloc (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ : Ty} :
    bin_log_related_ty D ⊤ Δ Γ e e' τ ⊢
    bin_log_related_ty D ⊤ Δ Γ (.alloc e) (.alloc e') (.ref τ) :=
  bin_log_related_lift1 substMap_alloc fun _ _ => refines_alloc

theorem bin_log_related_load (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ : Ty} :
    bin_log_related_ty D ⊤ Δ Γ e e' (.ref τ) ⊢ bin_log_related_ty D ⊤ Δ Γ (.load e) (.load e') τ :=
  bin_log_related_lift1 substMap_load fun _ _ => refines_load

theorem bin_log_related_store (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e1 e2 e1' e2' : Exp rT}
    {τ : Ty} : iprop%
    bin_log_related_ty D ⊤ Δ Γ e1 e1' (.ref τ) ⊢
    bin_log_related_ty D ⊤ Δ Γ e2 e2' τ -∗
    bin_log_related_ty D ⊤ Δ Γ (.store e1 e2) (.store e1' e2') .unit :=
  bin_log_related_lift2 substMap_store fun _ _ _ _ => refines_store

theorem bin_log_related_alloctape (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} :
    bin_log_related_ty D ⊤ Δ Γ e e' .int ⊢ bin_log_related_ty D ⊤ Δ Γ (.tape e) (.tape e') .tape :=
  bin_log_related_lift1 substMap_tape fun _ _ => refines_alloctape

theorem bin_log_related_rand_tape (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e1 e1' e2 e2' : Exp rT} : iprop%
    bin_log_related_ty D ⊤ Δ Γ e1 e1' .int ⊢
    bin_log_related_ty D ⊤ Δ Γ e2 e2' .tape -∗
    bin_log_related_ty D ⊤ Δ Γ (.rand e1 e2) (.rand e1' e2') .int :=
  bin_log_related_lift2 substMap_rand fun _ _ _ _ => refines_rand_tape_int

theorem bin_log_related_rand_unit (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e1 e1' e2 e2' : Exp rT} : iprop%
    bin_log_related_ty D ⊤ Δ Γ e1 e1' .int ⊢
    bin_log_related_ty D ⊤ Δ Γ e2 e2' .unit -∗
    bin_log_related_ty D ⊤ Δ Γ (.rand e1 e2) (.rand e1' e2') .int :=
  bin_log_related_lift2 substMap_rand fun t1 t2 t1' _ => by
    rw [interp_int, interp_unit]
    iintro IH1 IH2
    rw [← Ectx.fill_randR t1, ← Ectx.fill_randR t1']
    iapply refines_bind [EctxItem.randR t1] [EctxItem.randR t1'] $$ IH2
    iintro %v2 %v2' Hu
    iunfold lrel_unit at Hu
    icases Hu with ⟨%hv2, %hv2'⟩
    rw [hv2, hv2',
      show Ectx.fill [EctxItem.randR t1] pl(#(.unit)) = Ectx.fill [EctxItem.randL .unit] t1
        from rfl,
      show Ectx.fill [EctxItem.randR t1'] pl(#(.unit)) = Ectx.fill [EctxItem.randL .unit] t1'
        from rfl]
    iapply refines_rand_unit_int $$ IH1

end Discrete

/-! ### Polymorphic / recursive type compatibility -/

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
theorem refines_proper_entails (E : CoPset) (e e' : Exp rT) {A B : lrel rT GF} (h : A = B) :
    refines D E e e' A ⊢ refines D E e e' B :=
  (BI.equiv_iff.mp (refines_proper h)).1

theorem bin_log_related_tlam (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ : Ty}
    (he_lc : e.IsLocallyClosed) (he'_lc : e'.IsLocallyClosed)
    (he_fv : e.fv ⊆ (Γ.map (·.1)).toFinset) (he'_fv : e'.fv ⊆ (Γ.map (·.1)).toFinset)
    (Hbody : ∀ A, ⊢@{IProp GF} □ (bin_log_related_ty D ⊤ (TyEnv.cons A Δ) Γ e e' τ)) :
    ⊢@{IProp GF} bin_log_related_ty D ⊤ Δ Γ (.lam e) (.lam e') (.forall' τ) := by
  unfold bin_log_related_ty bin_log_related at Hbody ⊢
  iintro %vs #Hvs
  rw [substMap_lam, substMap_lam]
  ihave %hvsfst_closed := env_ltyped2_fst_allClosed Γ vs $$ Hvs
  ihave %hvssnd_closed := env_ltyped2_snd_allClosed Γ vs $$ Hvs
  ihave %hΓdomVs := env_ltyped2_domSubset Γ vs $$ Hvs
  obtain ⟨he_dom_fst, he_dom_snd⟩ := fv_subset_substMap_dom hΓdomVs he_fv he'_fv
  rw [show interp D (.forall' τ) Δ = lrel_forall D fun A => interp D τ (TyEnv.cons A Δ) from rfl]
  iapply refines_forall (substMap_lc hvsfst_closed he_lc) (substMap_lc hvssnd_closed he'_lc)
    (substMap_fv_eq_empty hvsfst_closed he_dom_fst) (substMap_fv_eq_empty hvssnd_closed he_dom_snd)
  iintro !> %A
  iapply Hbody A $$ Hvs

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
theorem bin_log_related_tapp (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ τ' : Ty} :
    bin_log_related_ty D ⊤ Δ Γ e e' (.forall' τ) ⊢
    bin_log_related_ty D ⊤ Δ Γ (.app e pl(#(.unit))) (.app e' pl(#(.unit))) (τ.single τ') := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [substMap_app, substMap_app, substMap_lit, substMap_lit,
    show app (substMap vs.fst e) pl(#(.unit)) =
      Ectx.fill [EctxItem.appL .unit] (substMap vs.fst e) from rfl,
    show app (substMap vs.snd e') pl(#(.unit)) =
      Ectx.fill [EctxItem.appL .unit] (substMap vs.snd e') from rfl]
  iapply refines_bind [EctxItem.appL .unit] [EctxItem.appL .unit] $$ IH'
  iintro %v %v' Hv
  isimp only [show (interp D (.forall' τ) Δ).car v v' =
    (lrel_forall D fun A => interp D τ (TyEnv.cons A Δ)).car v v' from rfl] at Hv
  iunfold lrel_forall at Hv
  ihave HvSpec := Hv $$ %(interp D τ' Δ)
  ihave HvArr := lrel_arr_unfold_wand lrel_unit (interp D τ (TyEnv.cons (interp D τ' Δ) Δ)) v v'
    $$ HvSpec
  ihave HvArr2 := HvArr $$ %(.unit : Val rT) %(.unit : Val rT)
  ihave HvApp : iprop(refines D ⊤ (app v.1 pl(#(.unit))) (app v'.1 pl(#(.unit)))
      (interp D τ (TyEnv.cons (interp D τ' Δ) Δ))) $$ [HvArr2]
  · iapply HvArr2
    iapply lrel_unit_lit
  rw [interp_subst τ' τ Δ,
    show Ectx.fill [EctxItem.appL .unit] v.1 = app v.1 pl(#(.unit)) from rfl,
    show Ectx.fill [EctxItem.appL .unit] v'.1 = app v'.1 pl(#(.unit)) from rfl]
  iexact HvApp

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
private theorem interp_rec_car (Δ : TyEnv rT GF) (τ : Ty) (v v' : Val rT) :
    (interp D (.rec' τ) Δ).car v v' = iprop(⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝ ∗
      ▷ (interp D τ (TyEnv.cons (interp D (.rec' τ) Δ) Δ)).car v v') :=
  congrArg (fun A => A.car v v') (lrel_rec_unfold
    { f := fun X => interp D τ (TyEnv.cons X Δ)
      ne := ⟨fun {_ _ _} hXY => (interpNE D τ).ne (TyEnv.cons_ne_head hXY)⟩ })

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
private theorem interp_exists_car (Δ : TyEnv rT GF) (τ : Ty) (v v' : Val rT) :
    (interp D (.exists' τ) Δ).car v v' = iprop(⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝ ∗
      ∃ A, (interp D τ (TyEnv.cons A Δ)).car v v') :=
  rfl

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
theorem bin_log_related_fold (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ : Ty} :
    bin_log_related_ty D ⊤ Δ Γ e e' (τ.single (.rec' τ)) ⊢
    bin_log_related_ty D ⊤ Δ Γ e e' (.rec' τ) := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  isimp only [interp_subst (.rec' τ) τ Δ] at IH'
  iapply refines_wand $$ IH'
  iintro %v %v' #Hv !>
  rw [interp_rec_car Δ τ v v']
  isplitr
  · iapply interp_closed τ v v' $$ Hv
  imodintro
  iexact Hv

theorem bin_log_related_unfold (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ : Ty} :
    bin_log_related_ty D ⊤ Δ Γ e e' (.rec' τ) ⊢
    bin_log_related_ty D ⊤ Δ Γ (.app recUnfold e) (.app recUnfold e') (τ.single (.rec' τ)) := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  have hru : ∀ σ : SubstMap rT, substMap σ recUnfold = recUnfold := fun σ => by
    show substMap σ (.lam (.bvar 0)) = _
    simp [substMap_lam, substMap_bvar, recUnfold]
  rw [substMap_app, substMap_app, hru, hru, ← Ectx.fill_appR recUnfold,
    ← Ectx.fill_appR recUnfold]
  iapply refines_bind [EctxItem.appR recUnfold] [EctxItem.appR recUnfold] $$ IH'
  iintro %v %v' Hv
  isimp only [interp_rec_car Δ τ v v'] at Hv
  icases Hv with ⟨-, HvL⟩
  rw [show Ectx.fill [EctxItem.appR recUnfold] v.1 = Ectx.fill [] (.app (.lam (.bvar 0)) v.1)
      from rfl,
    show Ectx.fill [EctxItem.appR recUnfold] v'.1 = Ectx.fill [] (.app (.lam (.bvar 0)) v'.1)
      from rfl]
  have hopenL : open' (.bvar 0) v.1 = v.1 := by simp [open', openRec]
  have hopenR : open' (.bvar 0) v'.1 = v'.1 := by simp [open', openRec]
  iapply refines_pure_l (e' := open' (.bvar 0) v.1) (Hex := pureExec_app_lam)
    ⟨v.2.toIsValue, by is_lc⟩
  inext
  rw [hopenL]
  iapply refines_pure_r (e' := open' (.bvar 0) v'.1) (Hex := pureExec_app_lam)
    ⟨v'.2.toIsValue, by is_lc⟩
  rw [hopenR]
  iapply refines_ret (e1 := Ectx.fill [] v.1) (e2 := Ectx.fill [] v'.1) (v1 := v) (v2 := v') rfl rfl
  imodintro
  rw [interp_subst (.rec' τ) τ Δ]
  iexact HvL

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
theorem bin_log_related_pack (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ τ' : Ty} :
    bin_log_related_ty D ⊤ Δ Γ e e' (τ.single τ') ⊢
    bin_log_related_ty D ⊤ Δ Γ e e' (.exists' τ) := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  isimp only [interp_subst τ' τ Δ] at IH'
  iapply refines_wand $$ IH'
  iintro %v %v' #Hv !>
  ihave %Hclosed := interp_closed τ v v' $$ Hv
  rw [interp_exists_car Δ τ v v']
  iframe %Hclosed
  iexists interp D τ' Δ
  iexact Hv

theorem bin_log_related_unpack (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (L : Finset Var)
    {e1 e1' e2 e2' : Exp rT} {τ τ2 : Ty}
    (HIH1 : ⊢@{IProp GF} bin_log_related_ty D ⊤ Δ Γ e1 e1' (.exists' τ))
    (he2_lc : ∀ x ∉ L, (open' e2 (.fvar x)).IsLocallyClosed)
    (he2'_lc : ∀ x ∉ L, (open' e2' (.fvar x)).IsLocallyClosed)
    (HIH2 : ∀ A : lrel rT GF, ∀ x ∉ L, ⊢@{IProp GF} bin_log_related_ty D ⊤ (TyEnv.cons A Δ)
      ((x, interp D τ (TyEnv.cons A Δ)) :: Γ) (open' e2 (.fvar x)) (open' e2' (.fvar x)) τ2.shift) :
    ⊢@{IProp GF} bin_log_related_ty D ⊤ Δ Γ (.app (.lam e2) e1) (.app (.lam e2') e1') τ2 := by
  unfold bin_log_related_ty bin_log_related at HIH1 HIH2 ⊢
  iintro %vs #Hvs
  ihave HIH1' := HIH1 $$ %vs Hvs
  rw [substMap_app, substMap_app, substMap_lam, substMap_lam]
  ihave %hvsfst_closed := env_ltyped2_fst_allClosed Γ vs $$ Hvs
  ihave %hvssnd_closed := env_ltyped2_snd_allClosed Γ vs $$ Hvs
  have hlam2_lc : (Exp.lam (substMap vs.fst e2)).IsLocallyClosed :=
    lam_substMap_isLocallyClosed hvsfst_closed
      (fun _ hy => ValSubstMap.fst_lookup_eq_none_of_not_mem hy) he2_lc
  have hlam2'_lc : (Exp.lam (substMap vs.snd e2')).IsLocallyClosed :=
    lam_substMap_isLocallyClosed hvssnd_closed
      (fun _ hy => ValSubstMap.snd_lookup_eq_none_of_not_mem hy) he2'_lc
  rw [← Ectx.fill_appR (.lam (substMap vs.fst e2)), ← Ectx.fill_appR (.lam (substMap vs.snd e2'))]
  iapply refines_bind [EctxItem.appR (.lam (substMap vs.fst e2))]
    [EctxItem.appR (.lam (substMap vs.snd e2'))] $$ HIH1'
  iintro %v %v' #Hv
  isimp only [interp_exists_car Δ τ v v'] at Hv
  icases Hv with ⟨%hvc, %A, #HvA⟩
  obtain ⟨x, hx⟩ := HasFresh.fresh_exists (L ∪ e2.fv ∪ e2'.fv ∪ (vs.map (·.1)).toFinset)
  simp only [Finset.mem_union, not_or] at hx
  obtain ⟨⟨⟨hxL, hxFvE2⟩, hxFvE2'⟩, hxNotDom⟩ := hx
  rw [Ectx.fill_appR, Ectx.eq_fill_nil (.app (.lam (substMap vs.fst e2)) v.1), Ectx.fill_appR,
    Ectx.eq_fill_nil (.app (.lam (substMap vs.snd e2')) v'.1)]
  iapply refines_pure_l (e' := open' (substMap vs.fst e2) v.1) (Hex := pureExec_app_lam)
    ⟨v.2.toIsValue, by is_lc⟩
  inext
  iapply refines_pure_r (e' := open' (substMap vs.snd e2') v'.1) (Hex := pureExec_app_lam)
    ⟨v'.2.toIsValue, by is_lc⟩
  let vs' : ValSubstMap rT := (x, (v, v')) :: vs
  ihave Hvs' : iprop(env_ltyped2 ((x, interp D τ (TyEnv.cons A Δ)) :: Γ) vs') $$ [HvA]
  · iapply env_ltyped2_insert Γ vs x (interp D τ (TyEnv.cons A Δ)) v v'
      hvc.1.toFvSubsetEmpty hvc.2.toFvSubsetEmpty
    iframe HvA Hvs
  ihave HBody_shift := HIH2 A x hxL $$ Hvs'
  ihave HBody := refines_proper_entails ⊤ (substMap vs'.fst (open' e2 (.fvar x)))
    (substMap vs'.snd (open' e2' (.fvar x))) (interp_ren τ2 A Δ) $$ HBody_shift
  obtain ⟨hbridge_fst, hbridge_snd⟩ := substMap_open_fresh_pair (vs' := vs') rfl
    hvsfst_closed hvssnd_closed hxFvE2 hxFvE2' hxNotDom hvc.1 hvc.2
  isimp only [hbridge_fst, hbridge_snd] at HBody
  simp only [Ectx.fill_nil]
  iexact HBody

/-! ### Operator / scrut compatibility

`lrel_int`, `lrel_bool` and `lrel_real` relate exactly equal literals, so each operator
lemma binds the operands (`refines_{un,bin}op_bind`) and takes one pure step. -/

private theorem refines_binop_val (op : BinOp) (w1 w2 : Val rT) {l : BaseLit rT}
    {A : lrel rT GF} (heval : op.eval w1.1 w2.1 = some (.lit l))
    (HA : ⊢@{IProp GF} A.car (.ofBaseLit l) (.ofBaseLit l)) :
    ⊢@{IProp GF} refines D ⊤ (.binop op w1.1 w2.1) (.binop op w1.1 w2.1) A :=
  refines_binop_pure op _ _ _ w1.2 w2.2 IsVal.lit heval HA

private theorem refines_unop_val (op : UnOp) (w : Val rT) {l : BaseLit rT} {A : lrel rT GF}
    (heval : op.eval w.1 = some (.lit l)) (HA : ⊢@{IProp GF} A.car (.ofBaseLit l) (.ofBaseLit l)) :
    ⊢@{IProp GF} refines D ⊤ (.unop op w.1) (.unop op w.1) A :=
  refines_unop_pure op _ _ w.2 IsVal.lit heval HA

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
private theorem refines_binop_bind (op : BinOp) {ι : Type _} (V : ι → Val rT) {A B : lrel rT GF}
    {e1 e2 e1' e2' : Exp rT} (hA : ∀ v v', A.car v v' ⊢ ∃ i, ⌜v = V i ∧ v' = V i⌝) : iprop%
    refines D ⊤ e1 e1' A ⊢
    refines D ⊤ e2 e2' A -∗
    (∀ i1 i2, refines D ⊤ (.binop op (V i1).1 (V i2).1) (.binop op (V i1).1 (V i2).1) B) -∗
    refines D ⊤ (.binop op e1 e2) (.binop op e1' e2') B := by
  iintro IH1 IH2 Hcont
  rw [show binop op e1 e2 = Ectx.fill [EctxItem.binopR op e1] e2 from rfl,
    show binop op e1' e2' = Ectx.fill [EctxItem.binopR op e1'] e2' from rfl]
  iapply refines_bind [EctxItem.binopR op e1] [EctxItem.binopR op e1'] $$ IH2
  iintro %v2 %v2' Hv2
  icases hA v2 v2' $$ Hv2 with ⟨%i2, %hv2, %hv2'⟩
  rw [show Ectx.fill [EctxItem.binopR op e1] v2.1 = binop op e1 v2.1 from rfl,
    show Ectx.fill [EctxItem.binopR op e1'] v2'.1 = binop op e1' v2'.1 from rfl, hv2, hv2',
    show binop op e1 (V i2).1 = Ectx.fill [EctxItem.binopL op (V i2)] e1 from rfl,
    show binop op e1' (V i2).1 = Ectx.fill [EctxItem.binopL op (V i2)] e1' from rfl]
  iapply refines_bind [EctxItem.binopL op (V i2)] [EctxItem.binopL op (V i2)] $$ IH1
  iintro %v1 %v1' Hv1
  icases hA v1 v1' $$ Hv1 with ⟨%i1, %hv1, %hv1'⟩
  rw [show Ectx.fill [EctxItem.binopL op (V i2)] v1.1 = binop op v1.1 (V i2).1 from rfl,
    show Ectx.fill [EctxItem.binopL op (V i2)] v1'.1 = binop op v1'.1 (V i2).1 from rfl, hv1, hv1']
  iapply Hcont $$ %i1 %i2

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
private theorem refines_unop_bind (op : UnOp) {ι : Type _} (V : ι → Val rT) {A B : lrel rT GF}
    {e e' : Exp rT} (hA : ∀ v v', A.car v v' ⊢ ∃ i, ⌜v = V i ∧ v' = V i⌝) : iprop%
    refines D ⊤ e e' A ⊢
    (∀ i, refines D ⊤ (.unop op (V i).1) (.unop op (V i).1) B) -∗
    refines D ⊤ (.unop op e) (.unop op e') B := by
  iintro IH Hcont
  rw [show unop op e = Ectx.fill [EctxItem.unop op] e from rfl,
    show unop op e' = Ectx.fill [EctxItem.unop op] e' from rfl]
  iapply refines_bind [EctxItem.unop op] [EctxItem.unop op] $$ IH
  iintro %v %v' Hv
  icases hA v v' $$ Hv with ⟨%i, %hv, %hv'⟩
  rw [show Ectx.fill [EctxItem.unop op] v.1 = unop op v.1 from rfl,
    show Ectx.fill [EctxItem.unop op] v'.1 = unop op v'.1 from rfl, hv, hv']
  iapply Hcont $$ %i

theorem bin_log_related_int_binop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (op : BinOp)
    {e1 e2 e1' e2' : Exp rT} {τ : Ty} (Hres : op.intResTy = some τ) : iprop%
    bin_log_related_ty D ⊤ Δ Γ e1 e1' .int ⊢
    bin_log_related_ty D ⊤ Δ Γ e2 e2' .int -∗
    bin_log_related_ty D ⊤ Δ Γ (.binop op e1 e2) (.binop op e1' e2') τ :=
  bin_log_related_lift2 (fun σ => substMap_binop σ op) fun _ _ _ _ => by
    rw [interp_int]
    iintro IH1 IH2
    iapply refines_binop_bind op Val.int (fun _ _ => .rfl) $$ IH1 IH2
    iintro %n1 %n2
    cases op <;> simp [BinOp.intResTy] at Hres <;> subst Hres
    all_goals first
      | (rw [interp_int]; iapply refines_binop_val _ _ _ rfl (lrel_int_lit _))
      | (rw [interp_bool]; iapply refines_binop_val _ _ _ rfl (lrel_bool_lit _))

theorem bin_log_related_bool_binop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (op : BinOp)
    {e1 e2 e1' e2' : Exp rT} {τ : Ty} (Hres : op.boolResTy = some τ) : iprop%
    bin_log_related_ty D ⊤ Δ Γ e1 e1' .bool ⊢
    bin_log_related_ty D ⊤ Δ Γ e2 e2' .bool -∗
    bin_log_related_ty D ⊤ Δ Γ (.binop op e1 e2) (.binop op e1' e2') τ :=
  bin_log_related_lift2 (fun σ => substMap_binop σ op) fun _ _ _ _ => by
    rw [interp_bool]
    iintro IH1 IH2
    iapply refines_binop_bind op Val.bool (fun _ _ => .rfl) $$ IH1 IH2
    iintro %b1 %b2
    cases op <;> simp [BinOp.boolResTy] at Hres <;> subst Hres
    all_goals (rw [interp_bool]; iapply refines_binop_val _ _ _ rfl (lrel_bool_lit _))

theorem bin_log_related_int_unop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (op : UnOp)
    {e e' : Exp rT} {τ : Ty} (Hres : op.intResTy = some τ) :
    bin_log_related_ty D ⊤ Δ Γ e e' .int ⊢
    bin_log_related_ty D ⊤ Δ Γ (.unop op e) (.unop op e') τ :=
  bin_log_related_lift1 (fun σ => substMap_unop σ op) fun _ _ => by
    rw [interp_int]
    iintro IH
    iapply refines_unop_bind op Val.int (fun _ _ => .rfl) $$ IH
    iintro %n
    cases op <;> simp [UnOp.intResTy] at Hres <;> subst Hres
    all_goals first
      | (rw [interp_int]; iapply refines_unop_val _ _ rfl (lrel_int_lit _))
      | (rw [interp_real]; iapply refines_unop_val _ _ rfl (lrel_real_lit _))

/-! ### The real fragment -/

theorem bin_log_related_real_unop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (op : UnOp)
    {e e' : Exp rT} {τ : Ty} (Hres : op.realResTy = some τ) :
    bin_log_related_ty D ⊤ Δ Γ e e' .real ⊢
    bin_log_related_ty D ⊤ Δ Γ (.unop op e) (.unop op e') τ :=
  bin_log_related_lift1 (fun σ => substMap_unop σ op) fun _ _ => by
    rw [interp_real]
    iintro IH
    iapply refines_unop_bind op Val.real (fun _ _ => .rfl) $$ IH
    iintro %r
    cases op <;> simp [UnOp.realResTy] at Hres <;> subst Hres
    all_goals (rw [interp_real]; iapply refines_unop_val _ _ rfl (lrel_real_lit _))

theorem bin_log_related_real_binop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (op : BinOp)
    {e1 e2 e1' e2' : Exp rT} {τ : Ty} (Hres : op.realResTy = some τ) : iprop%
    bin_log_related_ty D ⊤ Δ Γ e1 e1' .real ⊢
    bin_log_related_ty D ⊤ Δ Γ e2 e2' .real -∗
    bin_log_related_ty D ⊤ Δ Γ (.binop op e1 e2) (.binop op e1' e2') τ :=
  bin_log_related_lift2 (fun σ => substMap_binop σ op) fun _ _ _ _ => by
    rw [interp_real]
    iintro IH1 IH2
    iapply refines_binop_bind op Val.real (fun _ _ => .rfl) $$ IH1 IH2
    iintro %r1 %r2
    cases op <;> simp [BinOp.realResTy] at Hres <;> subst Hres
    all_goals first
      | (rw [interp_real]; iapply refines_binop_val _ _ _ rfl (lrel_real_lit _))
      | (rw [interp_bool]; iapply refines_binop_val _ _ _ rfl (lrel_bool_lit _))

theorem bin_log_related_urand (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) :
    ⊢@{IProp GF} bin_log_related_ty D ⊤ Δ Γ .urand .urand .real := by
  unfold bin_log_related_ty bin_log_related
  iintro %vs -
  rw [substMap_urand, substMap_urand, interp_real,
    show (Exp.urand : Exp rT) = Ectx.fill [] Exp.urand from rfl]
  iapply refines_couple_urands_lr id (MeasureTheory.MeasurePreserving.id _)
  iintro %r -
  simp only [id_eq]
  iapply refines_ret (e1 := Ectx.fill [] pl(#(.real r))) (e2 := Ectx.fill [] pl(#(.real r)))
    (v1 := .real r) (v2 := .real r) rfl rfl
  imodintro
  iapply lrel_real_lit r

theorem bin_log_related_bool_unop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (op : UnOp)
    {e e' : Exp rT} {τ : Ty} (Hres : op.boolResTy = some τ) :
    bin_log_related_ty D ⊤ Δ Γ e e' .bool ⊢
    bin_log_related_ty D ⊤ Δ Γ (.unop op e) (.unop op e') τ :=
  bin_log_related_lift1 (fun σ => substMap_unop σ op) fun _ _ => by
    rw [interp_bool]
    iintro IH
    iapply refines_unop_bind op Val.bool (fun _ _ => .rfl) $$ IH
    iintro %b
    cases op <;> simp [UnOp.boolResTy] at Hres
    subst Hres
    rw [interp_bool]
    iapply refines_unop_val _ _ rfl (lrel_bool_lit _)

theorem bin_log_related_unboxed_eq (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e1 e2 e1' e2' : Exp rT}
    {τ : Ty} (HUnboxed : UnboxedType τ) : iprop%
    bin_log_related_ty D ⊤ Δ Γ e1 e1' τ ⊢
    bin_log_related_ty D ⊤ Δ Γ e2 e2' τ -∗
    bin_log_related_ty D ⊤ Δ Γ (.binop .eq e1 e2) (.binop .eq e1' e2') .bool := by
  iintro IH1 IH2
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH1' := IH1 $$ %vs Hvs
  ihave IH2' := IH2 $$ %vs Hvs
  rw [substMap_binop, substMap_binop, ← Ectx.fill_binopR .eq (substMap vs.fst e1),
    ← Ectx.fill_binopR .eq (substMap vs.snd e1')]
  iapply refines_bind [EctxItem.binopR .eq (substMap vs.fst e1)]
    [EctxItem.binopR .eq (substMap vs.snd e1')] $$ IH2'
  iintro %v2 %v2' #Hv2
  rw [show Ectx.fill [EctxItem.binopR .eq (substMap vs.fst e1)] v2.1 =
      Ectx.fill [EctxItem.binopL .eq v2] (substMap vs.fst e1) from rfl,
    show Ectx.fill [EctxItem.binopR .eq (substMap vs.snd e1')] v2'.1 =
      Ectx.fill [EctxItem.binopL .eq v2'] (substMap vs.snd e1') from rfl]
  iapply refines_bind [EctxItem.binopL .eq v2] [EctxItem.binopL .eq v2'] $$ IH1'
  iintro %v1 %v1' #Hv1
  ihave Heq : iprop(|={⊤}=> ⌜v1 = v2 ↔ v1' = v2'⌝) $$ [Hv1 Hv2]
  · iapply unboxed_type_eq HUnboxed $$ Hv1 Hv2
  icases unboxed_type_lit_shape HUnboxed $$ Hv1 with ⟨%l1, %l1', %hv1eq, %hv1'eq⟩
  icases unboxed_type_lit_shape HUnboxed $$ Hv2 with ⟨%l2, %l2', %hv2eq, %hv2'eq⟩
  rw [show Ectx.fill [EctxItem.binopL .eq v2] v1.1 = .binop .eq v1.1 v2.1 from rfl,
    show Ectx.fill [EctxItem.binopL .eq v2'] v1'.1 = .binop .eq v1'.1 v2'.1 from rfl,
    hv1eq, hv2eq, hv1'eq, hv2'eq]
  imod Heq with %heqIff
  have hval : ∀ {w w' : Val rT} {m m' : BaseLit rT}, w.1 = .lit m → w'.1 = .lit m' →
      (w = w' ↔ m = m') := by
    refine fun hw hw' => ⟨fun h => ?_, fun h => Val.ext (by rw [hw, hw', h])⟩
    have hp := congrArg Val.fst h
    rw [hw, hw'] at hp
    exact lit.inj hp
  have hdec : decide (l1 = l2) = decide (l1' = l2') :=
    decide_eq_decide.mpr ((hval hv1eq hv2eq).symm.trans (heqIff.trans (hval hv1'eq hv2'eq)))
  have hφ_l : (Exp.lit l1).isValue ∧ (Exp.lit l2).isValue ∧
      BinOp.eval .eq (.lit l1) (.lit l2) = some pl(#(.bool (decide (l1 = l2)))) :=
    ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, by rw [← Bool.beq_eq_decide_eq]; rfl⟩
  have hφ_r : (Exp.lit l1').isValue ∧ (Exp.lit l2').isValue ∧
      BinOp.eval .eq (.lit l1') (.lit l2') = some pl(#(.bool (decide (l1' = l2')))) :=
    ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, by rw [← Bool.beq_eq_decide_eq]; rfl⟩
  rw [Ectx.eq_fill_nil (.binop .eq (.lit l1) (.lit l2)),
    Ectx.eq_fill_nil (.binop .eq (.lit l1') (.lit l2'))]
  iapply refines_pure_l hφ_l
  inext
  iapply refines_pure_r hφ_r
  iapply refines_ret (e1 := Ectx.fill [] pl(#(.bool (decide (l1 = l2)))))
    (e2 := Ectx.fill [] pl(#(.bool (decide (l1' = l2'))))) (v1 := .bool (decide (l1 = l2)))
    (v2 := .bool (decide (l1' = l2'))) rfl rfl
  imodintro
  rw [interp_bool, hdec]
  iapply lrel_bool_lit _

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
private theorem pat_match_lit {Δ : TyEnv rT GF} {l l' : BaseLit rT} {v v' : Val rT}
    (hv : v = .ofBaseLit l') (hv' : v' = .ofBaseLit l') (hll : l = l' ∨ ¬ (l == l') = true) :
    ⊢@{IProp GF} (∃ (b b' : Val rT), ⌜Pat.tryMatch (.lit l) v.1 = some b.1 ∧
      Pat.tryMatch (.lit l) v'.1 = some b'.1⌝ ∗ (interp D Ty.unit Δ).car b b') ∨
      ⌜Pat.tryMatch (.lit l) v.1 = none ∧ Pat.tryMatch (.lit l) v'.1 = none⌝ := by
  subst hv hv'
  rcases hll with rfl | hne
  · ileft
    iexists (.unit : Val _), (.unit : Val _)
    isplitr
    · ipureintro; exact ⟨Pat.tryMatch_lit_eq l, Pat.tryMatch_lit_eq l⟩
    rw [interp_unit]
    iapply lrel_unit_lit
  · iright
    ipureintro
    exact ⟨Pat.tryMatch_lit_ne hne, Pat.tryMatch_lit_ne hne⟩

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
theorem pat_match_related {Δ : TyEnv rT GF} {τs τb : Ty} {p : Pat rT}
    (Hpat : PatTyped τs p τb) (v v' : Val rT) :
    (interp D τs Δ).car v v' ⊢@{IProp GF}
      (∃ (b b' : Val rT), ⌜Pat.tryMatch p v.1 = some b.1 ∧ Pat.tryMatch p v'.1 = some b'.1⌝ ∗
        (interp D τb Δ).car b b') ∨
      ⌜Pat.tryMatch p v.1 = none ∧ Pat.tryMatch p v'.1 = none⌝ := by
  induction Hpat generalizing v v' with
  | @wildcard τ =>
    iintro Hvv
    ileft
    iexists v, v'
    isplitr
    · ipureintro; simp [Pat.tryMatch]
    iexact Hvv
  | @lit_int z =>
    rw [interp_int]
    iintro Hv
    iunfold lrel_int at Hv
    icases Hv with ⟨%n, %h⟩
    have hll : (BaseLit.int z : BaseLit rT) = .int n ∨
        ¬ ((BaseLit.int z : BaseLit rT) == .int n) = true :=
      if hzn : z = n then .inl (by rw [hzn]) else
        .inr (show ¬ (Int.decEq z n).decide = true from fun hd => hzn (of_decide_eq_true hd))
    iapply pat_match_lit h.1 h.2 hll
  | @lit_bool b =>
    rw [interp_bool]
    iintro Hv
    iunfold lrel_bool at Hv
    icases Hv with ⟨%b', %h⟩
    have hll : (BaseLit.bool b : BaseLit rT) = .bool b' ∨
        ¬ ((BaseLit.bool b : BaseLit rT) == .bool b') = true :=
      if hbb : b = b' then .inl (by rw [hbb]) else
        .inr (show ¬ (Bool.decEq b b').decide = true from fun hd => hbb (of_decide_eq_true hd))
    iapply pat_match_lit h.1 h.2 hll
  | lit_unit =>
    show iprop(⌜v = .unit ∧ v' = .unit⌝) ⊢ _
    iintro %h
    iapply pat_match_lit (l := .unit) h.1 h.2 (.inl rfl)
  | @pair τ1 τ2 p1 p2 b1 b2 Hpat1 Hpat2 ih1 ih2 =>
    rw [interp_prod]
    iintro Hv
    iunfold lrel_prod at Hv
    icases Hv with ⟨%a1, %a2, %c1, %c2, %hv1, %hv2, HA, HC⟩
    icases ih1 a1 a2 $$ HA with (⟨%ba, %ba', %hra, HBa⟩ | %hna)
    · icases ih2 c1 c2 $$ HC with (⟨%bb, %bb', %hrb, HBb⟩ | %hnb)
      · ileft
        iexists ⟨.pair ba.1 bb.1, IsVal.pair ba.2 bb.2, (IsVal.pair ba.2 bb.2).lc⟩,
          ⟨.pair ba'.1 bb'.1, IsVal.pair ba'.2 bb'.2, (IsVal.pair ba'.2 bb'.2).lc⟩
        isplitr
        · ipureintro; simp [Pat.tryMatch, hv1, hv2, hra.1, hra.2, hrb.1, hrb.2]
        rw [interp_prod]
        unfold lrel_prod
        iexists ba, ba', bb, bb'
        isplitr; · ipureintro; rfl
        isplitr; · ipureintro; rfl
        iframe HBa HBb
      · iright
        ipureintro
        simp [Pat.tryMatch, hv1, hv2, hra.1, hra.2, hnb.1, hnb.2]
    · iright
      ipureintro
      simp [Pat.tryMatch, hv1, hv2, hna.1, hna.2]
  | @inl τ1 τ2 p b Hpat' ih =>
    rw [interp_sum]
    iintro Hv
    iunfold lrel_sum at Hv
    icases Hv with ⟨%w1, %w2, Hcase⟩
    icases Hcase with (⟨%hv1, %hv2, HA⟩ | ⟨%hv1, %hv2, HB⟩)
    · icases ih w1 w2 $$ HA with (⟨%bb, %bb', %hr, Hbnd⟩ | %hn)
      · ileft
        iexists bb, bb'
        isplitr
        · ipureintro; simp [Pat.tryMatch, hv1, hv2, hr.1, hr.2]
        iexact Hbnd
      · iright
        ipureintro
        simp [Pat.tryMatch, hv1, hv2, hn.1, hn.2]
    · iright
      ipureintro
      simp [Pat.tryMatch, hv1, hv2]
  | @inr τ1 τ2 p b Hpat' ih =>
    rw [interp_sum]
    iintro Hv
    iunfold lrel_sum at Hv
    icases Hv with ⟨%w1, %w2, Hcase⟩
    icases Hcase with (⟨%hv1, %hv2, HA⟩ | ⟨%hv1, %hv2, HB⟩)
    · iright
      ipureintro
      simp [Pat.tryMatch, hv1, hv2]
    · icases ih w1 w2 $$ HB with (⟨%bb, %bb', %hr, Hbnd⟩ | %hn)
      · ileft
        iexists bb, bb'
        isplitr
        · ipureintro; simp [Pat.tryMatch, hv1, hv2, hr.1, hr.2]
        iexact Hbnd
      · iright
        ipureintro
        simp [Pat.tryMatch, hv1, hv2, hn.1, hn.2]

theorem bin_log_related_scrut (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT}
    {p : Pat rT} {τs τb : Ty} (Hpat : PatTyped τs p τb) :
    bin_log_related_ty D ⊤ Δ Γ e e' τs ⊢
    bin_log_related_ty D ⊤ Δ Γ (.scrut e p) (.scrut e' p) (.sum τb .unit) := by
  iintro IH
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  rw [substMap_scrut, substMap_scrut, ← Ectx.fill_scrut p, ← Ectx.fill_scrut p]
  iapply refines_bind [EctxItem.scrut p] [EctxItem.scrut p] $$ IH'
  iintro %v %v' #Hv
  ihave Hmatch := pat_match_related Hpat v v' $$ Hv
  rw [show Ectx.fill [EctxItem.scrut p] v.1 = Ectx.fill [] (.scrut v.1 p) from rfl,
    show Ectx.fill [EctxItem.scrut p] v'.1 = Ectx.fill [] (.scrut v'.1 p) from rfl]
  icases Hmatch with (⟨%bb, %bb', %hr, Hbnd⟩ | %hn)
  · iapply refines_pure_l (Hex := pureExec_scrut_some) ⟨v.2.toIsValue, hr.1⟩
    inext
    iapply refines_pure_r (Hex := pureExec_scrut_some) ⟨v'.2.toIsValue, hr.2⟩
    iapply refines_ret (e1 := Ectx.fill [] (.inl bb.1)) (e2 := Ectx.fill [] (.inl bb'.1))
      (v1 := ⟨.inl bb.1, IsVal.inl bb.2, (IsVal.inl bb.2).lc⟩)
      (v2 := ⟨.inl bb'.1, IsVal.inl bb'.2, (IsVal.inl bb'.2).lc⟩) rfl rfl
    imodintro
    rw [interp_sum, interp_unit]
    unfold lrel_sum
    iexists bb, bb'
    ileft
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; rfl
    iexact Hbnd
  · iapply refines_pure_l (Hex := pureExec_scrut_none) ⟨v.2.toIsValue, hn.1⟩
    inext
    iapply refines_pure_r (Hex := pureExec_scrut_none) ⟨v'.2.toIsValue, hn.2⟩
    iapply refines_ret (e1 := Ectx.fill [] (.inr pl(#(.unit))))
      (e2 := Ectx.fill [] (.inr pl(#(.unit))))
      (v1 := ⟨.inr pl(#(.unit)), IsVal.inr IsVal.lit, (IsVal.inr IsVal.lit).lc⟩)
      (v2 := ⟨.inr pl(#(.unit)), IsVal.inr IsVal.lit, (IsVal.inr IsVal.lit).lc⟩) rfl rfl
    imodintro
    rw [interp_sum, interp_unit]
    unfold lrel_sum
    iexists (.unit : Val _), (.unit : Val _)
    iright
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; rfl
    iapply lrel_unit_lit

/-! ## The fundamental theorem

Every well-typed expression is logically related to itself. -/

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
theorem TctxRelated.lookup_isSome {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated D Δ Γtc Γrc) {x : Var} (hx : (Γtc x).isSome) : (Γrc.lookup x).isSome := by
  rw [← HCtx x]
  simpa using hx

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
theorem TctxRelated.lookup_some {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated D Δ Γtc Γrc) {x : Var} {τ : Ty} (hx : Γtc x = some τ) :
    Γrc.lookup x = some (interp D τ Δ) := by
  rw [← HCtx x, hx]
  rfl

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
theorem TctxRelated.shift {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated D Δ Γtc Γrc) (A : lrel rT GF) :
    TctxRelated D (TyEnv.cons A Δ) Γtc.shift Γrc := by
  intro x
  have heq := HCtx x
  unfold Tctx.shift
  cases hΓ : Γtc x with
  | none => rw [hΓ] at heq; rw [← heq]; rfl
  | some τ =>
    rw [hΓ] at heq
    simp [interp_ren τ A Δ]; exact heq

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
theorem TctxRelated.insert {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated D Δ Γtc Γrc) (x : Var) (τ : Ty) (hfresh : Γrc.lookup x = none) :
    TctxRelated D Δ (Γtc.insert x τ) ((x, interp D τ Δ) :: Γrc) := by
  intro y
  unfold Tctx.insert RelCtx.lookup
  have heq := HCtx y
  by_cases hxy : y = x
  · subst hxy
    simp [hfresh]
  · rw [ite_eq_right hxy]
    cases hRc : Γrc.lookup y with
    | none =>
      rw [hRc] at heq
      cases hΓy : Γtc y with
      | none => simp [ite_eq_right hxy]
      | some τ' => rw [hΓy] at heq; simp at heq
    | some A =>
      rw [hRc] at heq
      cases hΓy : Γtc y with
      | none => rw [hΓy] at heq; simp at heq
      | some τ' =>
        rw [hΓy] at heq; simp at heq
        show some (interp D τ' Δ) = some A
        rw [heq]

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
theorem fv_subset_relCtxDom {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated D Δ Γtc Γrc) {e : Exp rT} {τ : Ty} (Hty : Typed Γtc e τ) :
    e.fv ⊆ (Γrc.map (·.1)).toFinset :=
  fun x hx => RelCtx.mem_of_lookup_isSome (HCtx.lookup_isSome (Hty.fvSubset x hx))

omit [D.IsReflexive] [D.IsComposable] [D.IsZeroLeft] in
private theorem fv_subset_of_cofinite {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated D Δ Γtc Γrc) {L : Finset Var} {e : Exp rT} {τ1 τ2 : Ty}
    (Hbody : ∀ x ∉ L, Typed (Γtc.insert x τ1) (open' e (.fvar x)) τ2) :
    e.fv ⊆ (Γrc.map (·.1)).toFinset := by
  intro z hz
  obtain ⟨y, hy⟩ := HasFresh.fresh_exists (L ∪ (Γrc.map (·.1)).toFinset ∪ {z})
  have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hyRc : y ∉ (Γrc.map (·.1)).toFinset := fun h =>
    hy (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hzy : z ≠ y := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h.symm))
  have hzdom := fv_subset_relCtxDom (HCtx.insert y τ1 (RelCtx.lookup_eq_none_of_not_mem hyRc))
    (Hbody y hyL) (fv_subset_open e y hz)
  simp only [List.mem_toFinset, List.mem_map] at hzdom ⊢
  obtain ⟨p, hpmem, hpeq⟩ := hzdom
  rcases List.mem_cons.mp hpmem with rfl | hmem
  · exact (hzy hpeq.symm).elim
  · exact ⟨p, hmem, hpeq⟩

omit [LawfulProbLangℝ rT] in
private theorem not_mem_union_dom {L : Finset Var} {Γrc : RelCtx rT GF} {x : Var}
    (hx : x ∉ L ∪ (Γrc.map (·.1)).toFinset) : x ∉ L ∧ Γrc.lookup x = none := by
  simp only [Finset.mem_union, not_or] at hx
  exact ⟨hx.1, RelCtx.lookup_eq_none_of_not_mem hx.2⟩

variable (D) in
theorem fundamental {Γtc : Tctx} {e : Exp rT} {τ : Ty} (Hty : Typed Γtc e τ) (Δ : TyEnv rT GF)
    (Γrc : RelCtx rT GF) (HCtx : TctxRelated D Δ Γtc Γrc) :
    ⊢@{IProp GF} bin_log_related_ty D ⊤ Δ Γrc e e τ := by
  induction Hty generalizing Δ Γrc with
  | @fvar _ x τ hx => exact bin_log_related_var Δ Γrc x τ (HCtx.lookup_some hx)
  | @lit_int _ n => exact bin_log_related_lit Γrc _ (lrel_int_lit n)
  | @lit_real _ r => exact bin_log_related_lit Γrc _ (lrel_real_lit r)
  | @lit_bool _ b => exact bin_log_related_lit Γrc _ (lrel_bool_lit b)
  | lit_unit => exact bin_log_related_lit Γrc _ lrel_unit_lit
  | «urand» => exact bin_log_related_urand Δ Γrc
  | unop_real _ Hres ih =>
    iintro; iapply bin_log_related_real_unop Δ Γrc _ Hres $$ %(ih Δ Γrc HCtx)
  | unop_int _ Hres ih =>
    iintro; iapply bin_log_related_int_unop Δ Γrc _ Hres $$ %(ih Δ Γrc HCtx)
  | unop_bool _ Hres ih =>
    iintro; iapply bin_log_related_bool_unop Δ Γrc _ Hres $$ %(ih Δ Γrc HCtx)
  | binop_real _ _ Hres ih1 ih2 =>
    iintro
    iapply bin_log_related_real_binop Δ Γrc _ Hres $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | binop_int _ _ Hres ih1 ih2 =>
    iintro
    iapply bin_log_related_int_binop Δ Γrc _ Hres $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | binop_bool _ _ Hres ih1 ih2 =>
    iintro
    iapply bin_log_related_bool_binop Δ Γrc _ Hres $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | unboxed_eq HUnboxed _ _ ih1 ih2 =>
    iintro
    iapply bin_log_related_unboxed_eq Δ Γrc HUnboxed $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | pair _ _ ih1 ih2 =>
    iintro; iapply bin_log_related_pair $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | fst _ ih => iintro; iapply bin_log_related_fst $$ %(ih Δ Γrc HCtx)
  | snd _ ih => iintro; iapply bin_log_related_snd $$ %(ih Δ Γrc HCtx)
  | inl _ ih => iintro; iapply bin_log_related_injl $$ %(ih Δ Γrc HCtx)
  | inr _ ih => iintro; iapply bin_log_related_injr $$ %(ih Δ Γrc HCtx)
  | «case» _ _ _ ih0 ih1 ih2 =>
    iintro
    iapply bin_log_related_case $$ %(ih0 Δ Γrc HCtx) %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | cond _ _ _ ih0 ih1 ih2 =>
    iintro
    iapply bin_log_related_if $$ %(ih0 Δ Γrc HCtx) %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | app _ _ ih1 ih2 =>
    iintro; iapply bin_log_related_app $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | alloc _ ih => iintro; iapply bin_log_related_alloc $$ %(ih Δ Γrc HCtx)
  | load _ ih => iintro; iapply bin_log_related_load $$ %(ih Δ Γrc HCtx)
  | store _ _ ih1 ih2 =>
    iintro; iapply bin_log_related_store $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | alloc_tape _ ih => iintro; iapply bin_log_related_alloctape $$ %(ih Δ Γrc HCtx)
  | rand _ _ ih1 ih2 =>
    iintro; iapply bin_log_related_rand_tape $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | rand_unit _ _ ih1 ih2 =>
    iintro; iapply bin_log_related_rand_unit $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | «scrut» _ Hpat ih => iintro; iapply bin_log_related_scrut Δ Γrc Hpat $$ %(ih Δ Γrc HCtx)
  | tfold _ ih => iintro; iapply bin_log_related_fold $$ %(ih Δ Γrc HCtx)
  | tunfold _ ih => iintro; iapply bin_log_related_unfold $$ %(ih Δ Γrc HCtx)
  | tapp _ ih => iintro; iapply bin_log_related_tapp $$ %(ih Δ Γrc HCtx)
  | tpack _ ih => iintro; iapply bin_log_related_pack $$ %(ih Δ Γrc HCtx)
  | @lam L Γtc' e τ1 τ2 Hbody ih =>
    let L' : Finset Var := L ∪ (Γrc.map (·.1)).toFinset
    have he_fv := fv_subset_of_cofinite HCtx Hbody
    have he_lc : ∀ x ∉ L', (open' e (.fvar x)).IsLocallyClosed := fun x hx =>
      (Hbody x (not_mem_union_dom hx).1).isLocallyClosed
    exact bin_log_related_lam Δ Γrc L' he_lc he_lc he_fv he_fv fun x hx =>
      ih x (not_mem_union_dom hx).1 Δ _ (HCtx.insert x τ1 (not_mem_union_dom hx).2)
  | @«fix» L Γtc' e τ1 τ2 Hbody ih =>
    let L' : Finset Var := L ∪ (Γrc.map (·.1)).toFinset
    have he_fv := fv_subset_of_cofinite HCtx Hbody
    have he_lc : ∀ x ∉ L', (open' e (.fvar x)).IsLocallyClosed := fun x hx =>
      (Hbody x (not_mem_union_dom hx).1).isLocallyClosed
    exact bin_log_related_fix Δ Γrc L' he_lc he_lc he_fv he_fv fun x hx =>
      ih x (not_mem_union_dom hx).1 Δ _ (HCtx.insert x (.arrow τ1 τ2) (not_mem_union_dom hx).2)
  | @tlam Γtc' e τ Hbody ih =>
    have hLC := Hbody.isLocallyClosed
    have he_fv := fv_subset_relCtxDom (HCtx.shift default) Hbody
    refine bin_log_related_tlam Δ Γrc hLC hLC he_fv he_fv fun A => ?_
    imodintro
    iapply ih (TyEnv.cons A Δ) Γrc (HCtx.shift A)
  | @tunpack L Γtc' e1 e2 τ τ2 Hty1 Hbody2 ih1 ih2 =>
    let L' : Finset Var := L ∪ (Γrc.map (·.1)).toFinset
    have he2_lc : ∀ x ∉ L', (open' e2 (.fvar x)).IsLocallyClosed := fun x hx =>
      (Hbody2 x (not_mem_union_dom hx).1).isLocallyClosed
    exact bin_log_related_unpack Δ Γrc L' (ih1 Δ Γrc HCtx) he2_lc he2_lc fun A x hx =>
      ih2 x (not_mem_union_dom hx).1 (TyEnv.cons A Δ) _
        ((HCtx.shift A).insert x τ (not_mem_union_dom hx).2)

theorem refines_typed (Δ : TyEnv rT GF) {e : Exp rT} {τ : Ty} (Hty : Typed Tctx.empty e τ) :
    ⊢@{IProp GF} refines D ⊤ e e (interp D τ Δ) := by
  have Hfund := fundamental D Hty Δ [] (by intro x; simp [Tctx.empty, RelCtx.lookup])
  unfold bin_log_related_ty bin_log_related at Hfund
  show ⊢@{IProp GF} refines D ⊤ (substMap (ValSubstMap.fst ([] : ValSubstMap rT)) e)
    (substMap (ValSubstMap.snd ([] : ValSubstMap rT)) e) (interp D τ Δ)
  iapply Hfund $$ %([] : ValSubstMap rT)
  iapply env_ltyped2_empty

end Fundamental

end ProbLang
