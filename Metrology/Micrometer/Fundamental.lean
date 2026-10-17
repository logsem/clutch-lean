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
  GradedLifting

namespace ProbLang

open Cslib Exp

section Fundamental
variable {rT : Type} [LawfulProbLangℝ rT]
variable {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B]
  [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors} [IR : MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind]

/-! ## Tctx → RelCtx lifting -/

variable (L) in
/-- The typing context `Γtc` is interpreted pointwise as the relational context `Γrc`. -/
def TctxRelated (Δ : TyEnv rT GF) (Γtc : Tctx) (Γrc : RelCtx rT GF) : Prop :=
  ∀ x, (Γtc x).map (fun τ => interp L τ Δ) = Γrc.lookup x

/-! ## Compatibility lemmas -/

omit [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind] in
theorem bin_log_related_var (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (x : Var) (τ : Ty)
    (hΓ : Γ.lookup x = some (interp L τ Δ)) :
    ⊢@{IProp GF} bin_log_related_ty L ⊤ Δ Γ (.fvar x) (.fvar x) τ := by
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  icases env_ltyped2_lookup Γ vs x (interp L τ Δ) hΓ $$ Hvs with ⟨%v1, %v2, %hvs_eq, HA⟩
  ihave %hfst_closed := env_ltyped2_fst_allClosed Γ vs $$ Hvs
  ihave %hsnd_closed := env_ltyped2_snd_allClosed Γ vs $$ Hvs
  rw [substMap_fvar_lookup_some _ _ hfst_closed (by rw [ValSubstMap.fst_lookup, hvs_eq]; rfl),
    substMap_fvar_lookup_some _ _ hsnd_closed (by rw [ValSubstMap.snd_lookup, hvs_eq]; rfl)]
  iapply refines_ret rfl rfl
  imodintro
  iexact HA

omit [LawfulProbLangℝ rT] in
private theorem exists_fresh_var (S : Finset Var) (e e' : Exp rT) (vs : ValSubstMap rT) :
    ∃ x, x ∉ S ∧ x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ (vs.map (·.1)).toFinset := by
  obtain ⟨x, hx⟩ := HasFresh.fresh_exists (S ∪ e.fv ∪ e'.fv ∪ (vs.map (·.1)).toFinset)
  simp only [Finset.mem_union, not_or] at hx
  exact ⟨x, hx.1.1.1, hx.1.1.2, hx.1.2, hx.2⟩

private theorem substMap_open_fresh_pair {vs : ValSubstMap rT} {x : Var} {v v' : Val rT}
    {e e' : Exp rT} (hfst : SubstMap.AllClosed vs.fst) (hsnd : SubstMap.AllClosed vs.snd)
    (hxe : x ∉ e.fv) (hxe' : x ∉ e'.fv) (hxdom : x ∉ (vs.map (·.1)).toFinset)
    (hv : v.1.isClosedEmpty) (hv' : v'.1.isClosedEmpty) :
    substMap (ValSubstMap.fst ((x, (v, v')) :: vs)) (open' e (.fvar x)) =
      open' (substMap vs.fst e) v.1 ∧
    substMap (ValSubstMap.snd ((x, (v, v')) :: vs)) (open' e' (.fvar x)) =
      open' (substMap vs.snd e') v'.1 :=
  ⟨substMap_open_fresh hfst hxe (ValSubstMap.fst_lookup_eq_none_of_not_mem hxdom) hv.1,
    substMap_open_fresh hsnd hxe' (ValSubstMap.snd_lookup_eq_none_of_not_mem hxdom) hv'.1⟩

private theorem fv_subset_substMap_dom {Γ : RelCtx rT GF} {vs : ValSubstMap rT} {e e' : Exp rT}
    (hdom : (Γ.map (·.1)).toFinset ⊆ (vs.map (·.1)).toFinset)
    (he : e.fv ⊆ (Γ.map (·.1)).toFinset) (he' : e'.fv ⊆ (Γ.map (·.1)).toFinset) :
    e.fv ⊆ (vs.fst.map (·.1)).toFinset ∧ e'.fv ⊆ (vs.snd.map (·.1)).toFinset := by
  rw [ValSubstMap.fst_dom, ValSubstMap.snd_dom]
  exact ⟨he.trans hdom, he'.trans hdom⟩

private theorem env_ltyped2_allClosed_pair (Γ : RelCtx rT GF) (vs : ValSubstMap rT) :
    env_ltyped2 Γ vs ⊢ ⌜SubstMap.AllClosed vs.fst ∧ SubstMap.AllClosed vs.snd⌝ := by
  iintro Hvs
  ihave %hfst := env_ltyped2_fst_allClosed Γ vs $$ Hvs
  ihave %hsnd := env_ltyped2_snd_allClosed Γ vs $$ Hvs
  ipureintro
  exact ⟨hfst, hsnd⟩

private theorem substMap_lam_lc {vs : ValSubstMap rT} {e e' : Exp rT} {S : Finset Var}
    (hvs : SubstMap.AllClosed vs.fst ∧ SubstMap.AllClosed vs.snd)
    (he_lc : ∀ x ∉ S, (open' e (.fvar x)).IsLocallyClosed)
    (he'_lc : ∀ x ∉ S, (open' e' (.fvar x)).IsLocallyClosed) :
    (Exp.lam (substMap vs.fst e)).IsLocallyClosed ∧
      (Exp.lam (substMap vs.snd e')).IsLocallyClosed :=
  ⟨lam_substMap_isLocallyClosed hvs.1
      (fun _ hy => ValSubstMap.fst_lookup_eq_none_of_not_mem hy) he_lc,
    lam_substMap_isLocallyClosed hvs.2
      (fun _ hy => ValSubstMap.snd_lookup_eq_none_of_not_mem hy) he'_lc⟩

private theorem substMap_lam_closed {Γ : RelCtx rT GF} {vs : ValSubstMap rT} {e e' : Exp rT}
    {S : Finset Var} (hvs : SubstMap.AllClosed vs.fst ∧ SubstMap.AllClosed vs.snd)
    (hdom : (Γ.map (·.1)).toFinset ⊆ (vs.map (·.1)).toFinset)
    (he_lc : ∀ x ∉ S, (open' e (.fvar x)).IsLocallyClosed)
    (he'_lc : ∀ x ∉ S, (open' e' (.fvar x)).IsLocallyClosed)
    (he_fv : e.fv ⊆ (Γ.map (·.1)).toFinset) (he'_fv : e'.fv ⊆ (Γ.map (·.1)).toFinset) :
    (Exp.lam (substMap vs.fst e)).isClosedEmpty ∧ (Exp.lam (substMap vs.snd e')).isClosedEmpty := by
  obtain ⟨he_dom_fst, he_dom_snd⟩ := fv_subset_substMap_dom hdom he_fv he'_fv
  obtain ⟨hlam_lc, hlam'_lc⟩ := substMap_lam_lc hvs he_lc he'_lc
  exact ⟨⟨hlam_lc, substMap_fv_eq_empty hvs.1 he_dom_fst⟩,
    ⟨hlam'_lc, substMap_fv_eq_empty hvs.2 he_dom_snd⟩⟩

private theorem substMap_fix_closed {Γ : RelCtx rT GF} {vs : ValSubstMap rT} {e e' : Exp rT}
    {S : Finset Var} (hvs : SubstMap.AllClosed vs.fst ∧ SubstMap.AllClosed vs.snd)
    (hdom : (Γ.map (·.1)).toFinset ⊆ (vs.map (·.1)).toFinset)
    (he_lc : ∀ f ∉ S, (open' e (.fvar f)).IsLocallyClosed)
    (he'_lc : ∀ f ∉ S, (open' e' (.fvar f)).IsLocallyClosed)
    (he_fv : e.fv ⊆ (Γ.map (·.1)).toFinset) (he'_fv : e'.fv ⊆ (Γ.map (·.1)).toFinset) :
    (Exp.fix (substMap vs.fst e)).isClosedEmpty ∧ (Exp.fix (substMap vs.snd e')).isClosedEmpty := by
  obtain ⟨he_dom_fst, he_dom_snd⟩ := fv_subset_substMap_dom hdom he_fv he'_fv
  exact ⟨⟨fix_substMap_isLocallyClosed hvs.1
      (fun _ hy => ValSubstMap.fst_lookup_eq_none_of_not_mem hy) he_lc,
      substMap_fv_eq_empty hvs.1 he_dom_fst⟩,
    ⟨fix_substMap_isLocallyClosed hvs.2
      (fun _ hy => ValSubstMap.snd_lookup_eq_none_of_not_mem hy) he'_lc,
      substMap_fv_eq_empty hvs.2 he_dom_snd⟩⟩

private theorem refines_beta {e e' : Exp rT} {v v' : Val rT} {A : lrel rT GF}
    (he : (Exp.lam e).IsLocallyClosed) (he' : (Exp.lam e').IsLocallyClosed) : iprop%
    ▷ refines L ⊤ (open' e v.1) (open' e' v'.1) A ⊢
    refines L ⊤ (.app (.lam e) v.1) (.app (.lam e') v'.1) A := by
  rw [Ectx.eq_fill_nil (.app (.lam e) v.1), Ectx.eq_fill_nil (.app (.lam e') v'.1)]
  iintro H
  iapply refines_pure_l (Hex := pureExec_app_lam) ⟨v.2.toIsValue, he⟩
  inext
  iapply refines_pure_r (Hex := pureExec_app_lam) ⟨v'.2.toIsValue, he'⟩
  simp only [Ectx.fill_nil]
  iexact H

/-! ### Lifting `refines` compatibility to `bin_log_related`

`bin_log_related_lift{1,2,3}` push `substMap` through a constructor `f` and apply a
`refines` rule for `f`. -/

omit [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind] in
private theorem bin_log_related_lift1 {Γ : RelCtx rT GF} {e e' : Exp rT} {A C : lrel rT GF}
    {f : Exp rT → Exp rT} (hf : ∀ σ t, substMap σ (f t) = f (substMap σ t))
    (H : ∀ t t', refines L ⊤ t t' A ⊢ refines L ⊤ (f t) (f t') C) :
    bin_log_related L ⊤ Γ e e' A ⊢ bin_log_related L ⊤ Γ (f e) (f e') C := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  rw [hf, hf]
  iapply H _ _ $$ (IH $$ %vs Hvs)

omit [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind] in
private theorem bin_log_related_lift2 {Γ : RelCtx rT GF} {e1 e2 e1' e2' : Exp rT}
    {A1 A2 C : lrel rT GF} {f : Exp rT → Exp rT → Exp rT}
    (hf : ∀ σ t1 t2, substMap σ (f t1 t2) = f (substMap σ t1) (substMap σ t2))
    (H : ∀ t1 t2 t1' t2', iprop%
      refines L ⊤ t1 t1' A1 ⊢ refines L ⊤ t2 t2' A2 -∗ refines L ⊤ (f t1 t2) (f t1' t2') C) : iprop%
    bin_log_related L ⊤ Γ e1 e1' A1 ⊢
    bin_log_related L ⊤ Γ e2 e2' A2 -∗ bin_log_related L ⊤ Γ (f e1 e2) (f e1' e2') C := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  rw [hf, hf]
  iapply H _ _ _ _ $$ (IH1 $$ %vs Hvs) (IH2 $$ %vs Hvs)

omit [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind] in
private theorem bin_log_related_lift3 {Γ : RelCtx rT GF} {e0 e1 e2 e0' e1' e2' : Exp rT}
    {A0 A1 A2 C : lrel rT GF} {f : Exp rT → Exp rT → Exp rT → Exp rT}
    (hf : ∀ σ t0 t1 t2,
      substMap σ (f t0 t1 t2) = f (substMap σ t0) (substMap σ t1) (substMap σ t2))
    (H : ∀ t0 t1 t2 t0' t1' t2', iprop%
      refines L ⊤ t0 t0' A0 ⊢ refines L ⊤ t1 t1' A1 -∗ refines L ⊤ t2 t2' A2 -∗
      refines L ⊤ (f t0 t1 t2) (f t0' t1' t2') C) : iprop%
    bin_log_related L ⊤ Γ e0 e0' A0 ⊢
    bin_log_related L ⊤ Γ e1 e1' A1 -∗ bin_log_related L ⊤ Γ e2 e2' A2 -∗
    bin_log_related L ⊤ Γ (f e0 e1 e2) (f e0' e1' e2') C := by
  unfold bin_log_related
  iintro IH0 IH1 IH2 %vs #Hvs
  rw [hf, hf]
  iapply H _ _ _ _ _ _ $$ (IH0 $$ %vs Hvs) (IH1 $$ %vs Hvs) (IH2 $$ %vs Hvs)

omit [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind] in
private theorem bin_log_related_lit (Γ : RelCtx rT GF) (l : BaseLit rT) {A : lrel rT GF}
    (HA : ⊢@{IProp GF} A.car (.ofBaseLit l) (.ofBaseLit l)) :
    ⊢@{IProp GF} bin_log_related L ⊤ Γ (.lit l) (.lit l) A := by
  unfold bin_log_related
  iintro %vs -
  rw [substMap_lit, substMap_lit, show lit l = (Val.ofBaseLit l).1 from rfl]
  iapply refines_ret rfl rfl
  imodintro
  iapply HA

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] in
theorem bin_log_related_pair (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e1 e2 e1' e2' : Exp rT}
    {τ1 τ2 : Ty} : iprop%
    bin_log_related_ty L ⊤ Δ Γ e1 e1' τ1 ⊢
    bin_log_related_ty L ⊤ Δ Γ e2 e2' τ2 -∗
    bin_log_related_ty L ⊤ Δ Γ (.pair e1 e2) (.pair e1' e2') (.prod τ1 τ2) :=
  bin_log_related_lift2 substMap_pair fun _ _ _ _ => refines_pair

theorem bin_log_related_fst (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ1 τ2 : Ty} :
    bin_log_related_ty L ⊤ Δ Γ e e' (.prod τ1 τ2) ⊢
    bin_log_related_ty L ⊤ Δ Γ (.fst e) (.fst e') τ1 :=
  bin_log_related_lift1 substMap_fst fun _ _ => refines_fst

theorem bin_log_related_snd (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ1 τ2 : Ty} :
    bin_log_related_ty L ⊤ Δ Γ e e' (.prod τ1 τ2) ⊢
    bin_log_related_ty L ⊤ Δ Γ (.snd e) (.snd e') τ2 :=
  bin_log_related_lift1 substMap_snd fun _ _ => refines_snd

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] in
theorem bin_log_related_injl (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ1 τ2 : Ty} :
    bin_log_related_ty L ⊤ Δ Γ e e' τ1 ⊢
    bin_log_related_ty L ⊤ Δ Γ (.inl e) (.inl e') (.sum τ1 τ2) :=
  bin_log_related_lift1 substMap_inl fun _ _ => refines_injl

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] in
theorem bin_log_related_injr (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ1 τ2 : Ty} :
    bin_log_related_ty L ⊤ Δ Γ e e' τ2 ⊢
    bin_log_related_ty L ⊤ Δ Γ (.inr e) (.inr e') (.sum τ1 τ2) :=
  bin_log_related_lift1 substMap_inr fun _ _ => refines_injr

theorem bin_log_related_case (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e0 e1 e2 e0' e1' e2' : Exp rT} {τ1 τ2 τ3 : Ty} : iprop%
    bin_log_related_ty L ⊤ Δ Γ e0 e0' (.sum τ1 τ2) ⊢
    bin_log_related_ty L ⊤ Δ Γ e1 e1' (.arrow τ1 τ3) -∗
    bin_log_related_ty L ⊤ Δ Γ e2 e2' (.arrow τ2 τ3) -∗
    bin_log_related_ty L ⊤ Δ Γ (.case e0 e1 e2) (.case e0' e1' e2') τ3 :=
  bin_log_related_lift3 substMap_case fun _ _ _ _ _ _ => refines_case

theorem bin_log_related_if (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e0 e1 e2 e0' e1' e2' : Exp rT} {τ : Ty} : iprop%
    bin_log_related_ty L ⊤ Δ Γ e0 e0' .bool ⊢
    bin_log_related_ty L ⊤ Δ Γ e1 e1' τ -∗
    bin_log_related_ty L ⊤ Δ Γ e2 e2' τ -∗
    bin_log_related_ty L ⊤ Δ Γ (.cond e0 e1 e2) (.cond e0' e1' e2') τ :=
  bin_log_related_lift3 substMap_cond fun _ _ _ _ _ _ => refines_if

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] in
theorem bin_log_related_app (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e1 e2 e1' e2' : Exp rT}
    {τ1 τ2 : Ty} : iprop%
    bin_log_related_ty L ⊤ Δ Γ e1 e1' (.arrow τ1 τ2) ⊢
    bin_log_related_ty L ⊤ Δ Γ e2 e2' τ1 -∗
    bin_log_related_ty L ⊤ Δ Γ (.app e1 e2) (.app e1' e2') τ2 :=
  bin_log_related_lift2 substMap_app fun _ _ _ _ => refines_app

theorem bin_log_related_lam (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ1 τ2 : Ty}
    (S : Finset Var) (he_lc : ∀ x ∉ S, (open' e (.fvar x)).IsLocallyClosed)
    (he'_lc : ∀ x ∉ S, (open' e' (.fvar x)).IsLocallyClosed)
    (he_fv : e.fv ⊆ (Γ.map (·.1)).toFinset) (he'_fv : e'.fv ⊆ (Γ.map (·.1)).toFinset)
    (Hbody : ∀ x ∉ S, ⊢@{IProp GF} bin_log_related_ty L ⊤ Δ ((x, interp L τ1 Δ) :: Γ)
      (open' e (.fvar x)) (open' e' (.fvar x)) τ2) :
    ⊢@{IProp GF} bin_log_related_ty L ⊤ Δ Γ (.lam e) (.lam e') (.arrow τ1 τ2) := by
  unfold bin_log_related_ty bin_log_related at Hbody ⊢
  iintro %vs #Hvs
  rw [substMap_lam, substMap_lam, interp_arrow]
  ihave %hvs := env_ltyped2_allClosed_pair Γ vs $$ Hvs
  ihave %hΓdomVs := env_ltyped2_domSubset Γ vs $$ Hvs
  have hlam_closed := substMap_lam_closed hvs hΓdomVs he_lc he'_lc he_fv he'_fv
  have ⟨⟨hlam_lc, _⟩, hlam'_lc, _⟩ := hlam_closed
  obtain ⟨hvsfst_closed, hvssnd_closed⟩ := hvs
  iapply refines_arrow_val (v := ⟨.lam (substMap vs.fst e), IsVal.lam (by is_lc), by is_lc⟩)
    (v' := ⟨.lam (substMap vs.snd e'), IsVal.lam (by is_lc), by is_lc⟩) hlam_closed
  iintro !> %v1 %v2 #HA
  ihave %hv1v2_closed := interp_closed τ1 v1 v2 $$ HA
  obtain ⟨x, hxL, hxFvE, hxFvE', hxNotDom⟩ := exists_fresh_var S e e' vs
  ihave Hvs' := env_ltyped2_insert Γ vs x (interp L τ1 Δ) v1 v2
    hv1v2_closed.1.toFvSubsetEmpty hv1v2_closed.2.toFvSubsetEmpty $$ [$HA $Hvs]
  ihave HBody := Hbody x hxL $$ Hvs'
  obtain ⟨hbridge_fst, hbridge_snd⟩ := substMap_open_fresh_pair
    hvsfst_closed hvssnd_closed hxFvE hxFvE' hxNotDom hv1v2_closed.1 hv1v2_closed.2
  isimp only [hbridge_fst, hbridge_snd] at HBody
  iapply refines_beta hlam_lc hlam'_lc
  inext
  iexact HBody

theorem bin_log_related_fix (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ1 τ2 : Ty}
    (S : Finset Var) (he_lc : ∀ f ∉ S, (open' e (.fvar f)).IsLocallyClosed)
    (he'_lc : ∀ f ∉ S, (open' e' (.fvar f)).IsLocallyClosed)
    (he_fv : e.fv ⊆ (Γ.map (·.1)).toFinset) (he'_fv : e'.fv ⊆ (Γ.map (·.1)).toFinset)
    (Hbody : ∀ f ∉ S, ⊢@{IProp GF} bin_log_related_ty L ⊤ Δ ((f, interp L (.arrow τ1 τ2) Δ) :: Γ)
      (open' e (.fvar f)) (open' e' (.fvar f)) (.arrow τ1 τ2)) :
    ⊢@{IProp GF} bin_log_related_ty L ⊤ Δ Γ (.fix e) (.fix e') (.arrow τ1 τ2) := by
  unfold bin_log_related_ty bin_log_related at Hbody ⊢
  iintro %vs #Hvs
  rw [substMap_fix, substMap_fix, interp_arrow]
  ihave %hvs := env_ltyped2_allClosed_pair Γ vs $$ Hvs
  ihave %hΓdomVs := env_ltyped2_domSubset Γ vs $$ Hvs
  have hfix_closed := substMap_fix_closed hvs hΓdomVs he_lc he'_lc he_fv he'_fv
  have ⟨⟨hfix_lc, _⟩, hfix'_lc, _⟩ := hfix_closed
  obtain ⟨hvsfst_closed, hvssnd_closed⟩ := hvs
  obtain ⟨f, hfL, hfFvE, hfFvE', hfNotDom⟩ := exists_fresh_var S e e' vs
  let fixv : Val rT := ⟨.fix (substMap vs.fst e), IsVal.fix (by is_lc), by is_lc⟩
  let fixv' : Val rT := ⟨.fix (substMap vs.snd e'), IsVal.fix (by is_lc), by is_lc⟩
  iapply refines_ret (v1 := fixv) (v2 := fixv') rfl rfl
  imodintro
  iapply loeb_wand
  iintro !> #IH
  unfold lrel_arr
  isplitr; · ipureintro; exact hfix_closed
  iintro !> %v1 %v2 #HA
  rw [Ectx.eq_fill_nil (.app (.fix (substMap vs.fst e)) v1.1),
    Ectx.eq_fill_nil (.app (.fix (substMap vs.snd e')) v2.1)]
  iapply refines_pure_l (Hex := pureExec_app_fix) ⟨v1.2.toIsValue, by is_lc⟩
  inext
  iapply refines_pure_r (Hex := pureExec_app_fix) ⟨v2.2.toIsValue, by is_lc⟩
  ihave Hvs' := env_ltyped2_insert Γ vs f (interp L (.arrow τ1 τ2) Δ) fixv fixv'
    hfix_closed.1.toFvSubsetEmpty hfix_closed.2.toFvSubsetEmpty $$ [IH $Hvs]
  · rw [interp_arrow]
    iunfold lrel_arr
    iexact IH
  ihave HBody := Hbody f hfL $$ Hvs'
  obtain ⟨hbridge_fst, hbridge_snd⟩ := substMap_open_fresh_pair (v := fixv) (v' := fixv')
    hvsfst_closed hvssnd_closed hfFvE hfFvE' hfNotDom hfix_closed.1 hfix_closed.2
  isimp only [hbridge_fst, hbridge_snd, interp_arrow] at HBody
  ihave HArgs : iprop(refines L ⊤ v1.1 v2.1 (interp L τ1 Δ)) $$ [HA]
  · iapply refines_ret rfl rfl
    imodintro
    iexact HA
  simp only [Ectx.fill_nil]
  iapply refines_app $$ HBody HArgs

/-! ### Heap and tape cases -/

section Discrete

theorem bin_log_related_alloc (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ : Ty} :
    bin_log_related_ty L ⊤ Δ Γ e e' τ ⊢
    bin_log_related_ty L ⊤ Δ Γ (.alloc e) (.alloc e') (.ref τ) :=
  bin_log_related_lift1 substMap_alloc fun _ _ => refines_alloc

theorem bin_log_related_load (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ : Ty} :
    bin_log_related_ty L ⊤ Δ Γ e e' (.ref τ) ⊢ bin_log_related_ty L ⊤ Δ Γ (.load e) (.load e') τ :=
  bin_log_related_lift1 substMap_load fun _ _ => refines_load

theorem bin_log_related_store (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e1 e2 e1' e2' : Exp rT}
    {τ : Ty} : iprop%
    bin_log_related_ty L ⊤ Δ Γ e1 e1' (.ref τ) ⊢
    bin_log_related_ty L ⊤ Δ Γ e2 e2' τ -∗
    bin_log_related_ty L ⊤ Δ Γ (.store e1 e2) (.store e1' e2') .unit :=
  bin_log_related_lift2 substMap_store fun _ _ _ _ => refines_store

theorem bin_log_related_alloctape (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} :
    bin_log_related_ty L ⊤ Δ Γ e e' .int ⊢ bin_log_related_ty L ⊤ Δ Γ (.tape e) (.tape e') .tape :=
  bin_log_related_lift1 substMap_tape fun _ _ => refines_alloctape

theorem bin_log_related_rand_tape (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e1 e1' e2 e2' : Exp rT} : iprop%
    bin_log_related_ty L ⊤ Δ Γ e1 e1' .int ⊢
    bin_log_related_ty L ⊤ Δ Γ e2 e2' .tape -∗
    bin_log_related_ty L ⊤ Δ Γ (.rand e1 e2) (.rand e1' e2') .int :=
  bin_log_related_lift2 substMap_rand fun _ _ _ _ => refines_rand_tape_int

theorem bin_log_related_rand_unit (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e1 e1' e2 e2' : Exp rT} : iprop%
    bin_log_related_ty L ⊤ Δ Γ e1 e1' .int ⊢
    bin_log_related_ty L ⊤ Δ Γ e2 e2' .unit -∗
    bin_log_related_ty L ⊤ Δ Γ (.rand e1 e2) (.rand e1' e2') .int :=
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

theorem bin_log_related_tlam (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ : Ty}
    (he_lc : e.IsLocallyClosed) (he'_lc : e'.IsLocallyClosed)
    (he_fv : e.fv ⊆ (Γ.map (·.1)).toFinset) (he'_fv : e'.fv ⊆ (Γ.map (·.1)).toFinset)
    (Hbody : ∀ A, ⊢@{IProp GF} □ (bin_log_related_ty L ⊤ (TyEnv.cons A Δ) Γ e e' τ)) :
    ⊢@{IProp GF} bin_log_related_ty L ⊤ Δ Γ (.lam e) (.lam e') (.forall' τ) := by
  unfold bin_log_related_ty bin_log_related at Hbody ⊢
  iintro %vs #Hvs
  rw [substMap_lam, substMap_lam]
  ihave %hvs := env_ltyped2_allClosed_pair Γ vs $$ Hvs
  obtain ⟨hvsfst_closed, hvssnd_closed⟩ := hvs
  ihave %hΓdomVs := env_ltyped2_domSubset Γ vs $$ Hvs
  obtain ⟨he_dom_fst, he_dom_snd⟩ := fv_subset_substMap_dom hΓdomVs he_fv he'_fv
  rw [show interp L (.forall' τ) Δ = lrel_forall L fun A => interp L τ (TyEnv.cons A Δ) from rfl]
  iapply refines_forall (substMap_lc hvsfst_closed he_lc) (substMap_lc hvssnd_closed he'_lc)
    (substMap_fv_eq_empty hvsfst_closed he_dom_fst) (substMap_fv_eq_empty hvssnd_closed he_dom_snd)
  iintro !> %A
  iapply Hbody A $$ Hvs

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] in
theorem bin_log_related_tapp (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ τ' : Ty} :
    bin_log_related_ty L ⊤ Δ Γ e e' (.forall' τ) ⊢
    bin_log_related_ty L ⊤ Δ Γ (.app e pl(#(.unit))) (.app e' pl(#(.unit))) (τ.single τ') := by
  unfold bin_log_related_ty bin_log_related
  iintro IH %vs #Hvs
  rw [substMap_app, substMap_app, substMap_lit, substMap_lit,
    show app (substMap vs.fst e) pl(#(.unit)) =
      Ectx.fill [EctxItem.appL .unit] (substMap vs.fst e) from rfl,
    show app (substMap vs.snd e') pl(#(.unit)) =
      Ectx.fill [EctxItem.appL .unit] (substMap vs.snd e') from rfl]
  iapply refines_bind [EctxItem.appL .unit] [EctxItem.appL .unit] $$ (IH $$ %vs Hvs)
  iintro %v %v' Hv
  isimp only [show (interp L (.forall' τ) Δ).car v v' =
    (lrel_forall L fun A => interp L τ (TyEnv.cons A Δ)).car v v' from rfl] at Hv
  iunfold lrel_forall at Hv
  ihave HvArr := lrel_arr_unfold_wand lrel_unit (interp L τ (TyEnv.cons (interp L τ' Δ) Δ)) v v'
    $$ (Hv $$ %(interp L τ' Δ))
  rw [interp_subst τ' τ Δ,
    show Ectx.fill [EctxItem.appL .unit] v.1 = app v.1 pl(#(.unit)) from rfl,
    show Ectx.fill [EctxItem.appL .unit] v'.1 = app v'.1 pl(#(.unit)) from rfl]
  iapply HvArr $$ %(.unit : Val rT) %(.unit : Val rT)
  iapply lrel_unit_lit

omit [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind] in
private theorem interp_rec_car (Δ : TyEnv rT GF) (τ : Ty) (v v' : Val rT) :
    (interp L (.rec' τ) Δ).car v v' = iprop(⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝ ∗
      ▷ (interp L τ (TyEnv.cons (interp L (.rec' τ) Δ) Δ)).car v v') :=
  congrArg (fun A => A.car v v') (lrel_rec_unfold
    { f := fun X => interp L τ (TyEnv.cons X Δ)
      ne := ⟨fun {_ _ _} hXY => (interpNE L τ).ne (TyEnv.cons_ne_head hXY)⟩ })

omit [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind] in
private theorem interp_exists_car (Δ : TyEnv rT GF) (τ : Ty) (v v' : Val rT) :
    (interp L (.exists' τ) Δ).car v v' = iprop(⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝ ∗
      ∃ A, (interp L τ (TyEnv.cons A Δ)).car v v') :=
  rfl

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] in
theorem bin_log_related_fold (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ : Ty} :
    bin_log_related_ty L ⊤ Δ Γ e e' (τ.single (.rec' τ)) ⊢
    bin_log_related_ty L ⊤ Δ Γ e e' (.rec' τ) := by
  unfold bin_log_related_ty bin_log_related
  iintro IH %vs #Hvs
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
    bin_log_related_ty L ⊤ Δ Γ e e' (.rec' τ) ⊢
    bin_log_related_ty L ⊤ Δ Γ (.app recUnfold e) (.app recUnfold e') (τ.single (.rec' τ)) := by
  unfold bin_log_related_ty bin_log_related
  iintro IH %vs #Hvs
  have hru : ∀ σ : SubstMap rT, substMap σ recUnfold = recUnfold := fun σ => by
    show substMap σ (.lam (.bvar 0)) = _
    simp [substMap_lam, substMap_bvar, recUnfold]
  rw [substMap_app, substMap_app, hru, hru, ← Ectx.fill_appR recUnfold,
    ← Ectx.fill_appR recUnfold]
  iapply refines_bind [EctxItem.appR recUnfold] [EctxItem.appR recUnfold] $$ (IH $$ %vs Hvs)
  iintro %v %v' Hv
  isimp only [interp_rec_car Δ τ v v'] at Hv
  icases Hv with ⟨-, HvL⟩
  rw [show Ectx.fill [EctxItem.appR recUnfold] v.1 = .app (.lam (.bvar 0)) v.1 from rfl,
    show Ectx.fill [EctxItem.appR recUnfold] v'.1 = .app (.lam (.bvar 0)) v'.1 from rfl]
  have hopen : ∀ w : Exp rT, open' (.bvar 0) w = w := fun w => by simp [open', openRec]
  iapply refines_beta (by is_lc) (by is_lc)
  rw [hopen, hopen]
  inext
  iapply refines_ret rfl rfl
  imodintro
  rw [interp_subst (.rec' τ) τ Δ]
  iexact HvL

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] in
theorem bin_log_related_pack (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ τ' : Ty} :
    bin_log_related_ty L ⊤ Δ Γ e e' (τ.single τ') ⊢
    bin_log_related_ty L ⊤ Δ Γ e e' (.exists' τ) := by
  unfold bin_log_related_ty bin_log_related
  iintro IH %vs #Hvs
  ihave IH' := IH $$ %vs Hvs
  isimp only [interp_subst τ' τ Δ] at IH'
  iapply refines_wand $$ IH'
  iintro %v %v' #Hv !>
  ihave %Hclosed := interp_closed τ v v' $$ Hv
  rw [interp_exists_car Δ τ v v']
  iframe %Hclosed
  iexists interp L τ' Δ
  iexact Hv

theorem bin_log_related_unpack (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (S : Finset Var)
    {e1 e1' e2 e2' : Exp rT} {τ τ2 : Ty}
    (HIH1 : ⊢@{IProp GF} bin_log_related_ty L ⊤ Δ Γ e1 e1' (.exists' τ))
    (he2_lc : ∀ x ∉ S, (open' e2 (.fvar x)).IsLocallyClosed)
    (he2'_lc : ∀ x ∉ S, (open' e2' (.fvar x)).IsLocallyClosed)
    (HIH2 : ∀ A : lrel rT GF, ∀ x ∉ S, ⊢@{IProp GF} bin_log_related_ty L ⊤ (TyEnv.cons A Δ)
      ((x, interp L τ (TyEnv.cons A Δ)) :: Γ) (open' e2 (.fvar x)) (open' e2' (.fvar x)) τ2.shift) :
    ⊢@{IProp GF} bin_log_related_ty L ⊤ Δ Γ (.app (.lam e2) e1) (.app (.lam e2') e1') τ2 := by
  unfold bin_log_related_ty bin_log_related at HIH1 HIH2 ⊢
  iintro %vs #Hvs
  ihave HIH1' := HIH1 $$ %vs Hvs
  rw [substMap_app, substMap_app, substMap_lam, substMap_lam]
  ihave %hvs := env_ltyped2_allClosed_pair Γ vs $$ Hvs
  obtain ⟨hlam2_lc, hlam2'_lc⟩ := substMap_lam_lc hvs he2_lc he2'_lc
  obtain ⟨hvsfst_closed, hvssnd_closed⟩ := hvs
  rw [← Ectx.fill_appR (.lam (substMap vs.fst e2)), ← Ectx.fill_appR (.lam (substMap vs.snd e2'))]
  iapply refines_bind [EctxItem.appR (.lam (substMap vs.fst e2))]
    [EctxItem.appR (.lam (substMap vs.snd e2'))] $$ HIH1'
  iintro %v %v' #Hv
  isimp only [interp_exists_car Δ τ v v'] at Hv
  icases Hv with ⟨%hvc, %A, #HvA⟩
  obtain ⟨x, hxL, hxFvE2, hxFvE2', hxNotDom⟩ := exists_fresh_var S e2 e2' vs
  rw [Ectx.fill_appR, Ectx.fill_appR]
  iapply refines_beta hlam2_lc hlam2'_lc
  inext
  ihave Hvs' := env_ltyped2_insert Γ vs x (interp L τ (TyEnv.cons A Δ)) v v'
    hvc.1.toFvSubsetEmpty hvc.2.toFvSubsetEmpty $$ [$HvA $Hvs]
  ihave HBody := HIH2 A x hxL $$ Hvs'
  obtain ⟨hbridge_fst, hbridge_snd⟩ := substMap_open_fresh_pair
    hvsfst_closed hvssnd_closed hxFvE2 hxFvE2' hxNotDom hvc.1 hvc.2
  isimp only [hbridge_fst, hbridge_snd, interp_ren τ2 A Δ] at HBody
  iexact HBody

/-! ### Operator compatibility

`lrel_int`, `lrel_bool` and `lrel_real` relate exactly equal literals, so each operator
lemma binds the operands (`refines_{un,bin}op_bind`) and takes one pure step. -/

private theorem refines_binop_val (op : BinOp) (w1 w2 : Val rT) {l : BaseLit rT}
    {A : lrel rT GF} (heval : op.eval w1.1 w2.1 = some (.lit l))
    (HA : ⊢@{IProp GF} A.car (.ofBaseLit l) (.ofBaseLit l)) :
    ⊢@{IProp GF} refines L ⊤ (.binop op w1.1 w2.1) (.binop op w1.1 w2.1) A :=
  refines_binop_pure op _ _ _ w1.2 w2.2 IsVal.lit heval HA

private theorem refines_unop_val (op : UnOp) (w : Val rT) {l : BaseLit rT} {A : lrel rT GF}
    (heval : op.eval w.1 = some (.lit l)) (HA : ⊢@{IProp GF} A.car (.ofBaseLit l) (.ofBaseLit l)) :
    ⊢@{IProp GF} refines L ⊤ (.unop op w.1) (.unop op w.1) A :=
  refines_unop_pure op _ _ w.2 IsVal.lit heval HA

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] in
private theorem refines_binop_bind (op : BinOp) {ι : Type _} (V : ι → Val rT) {A C : lrel rT GF}
    {e1 e2 e1' e2' : Exp rT} (hA : ∀ v v', A.car v v' ⊢ ∃ i, ⌜v = V i ∧ v' = V i⌝) : iprop%
    refines L ⊤ e1 e1' A ⊢
    refines L ⊤ e2 e2' A -∗
    (∀ i1 i2, refines L ⊤ (.binop op (V i1).1 (V i2).1) (.binop op (V i1).1 (V i2).1) C) -∗
    refines L ⊤ (.binop op e1 e2) (.binop op e1' e2') C := by
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

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] in
private theorem refines_unop_bind (op : UnOp) {ι : Type _} (V : ι → Val rT) {A C : lrel rT GF}
    {e e' : Exp rT} (hA : ∀ v v', A.car v v' ⊢ ∃ i, ⌜v = V i ∧ v' = V i⌝) : iprop%
    refines L ⊤ e e' A ⊢
    (∀ i, refines L ⊤ (.unop op (V i).1) (.unop op (V i).1) C) -∗
    refines L ⊤ (.unop op e) (.unop op e') C := by
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
    bin_log_related_ty L ⊤ Δ Γ e1 e1' .int ⊢
    bin_log_related_ty L ⊤ Δ Γ e2 e2' .int -∗
    bin_log_related_ty L ⊤ Δ Γ (.binop op e1 e2) (.binop op e1' e2') τ :=
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
    bin_log_related_ty L ⊤ Δ Γ e1 e1' .bool ⊢
    bin_log_related_ty L ⊤ Δ Γ e2 e2' .bool -∗
    bin_log_related_ty L ⊤ Δ Γ (.binop op e1 e2) (.binop op e1' e2') τ :=
  bin_log_related_lift2 (fun σ => substMap_binop σ op) fun _ _ _ _ => by
    rw [interp_bool]
    iintro IH1 IH2
    iapply refines_binop_bind op Val.bool (fun _ _ => .rfl) $$ IH1 IH2
    iintro %b1 %b2
    cases op <;> simp [BinOp.boolResTy] at Hres <;> subst Hres
    all_goals (rw [interp_bool]; iapply refines_binop_val _ _ _ rfl (lrel_bool_lit _))

theorem bin_log_related_int_unop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (op : UnOp)
    {e e' : Exp rT} {τ : Ty} (Hres : op.intResTy = some τ) :
    bin_log_related_ty L ⊤ Δ Γ e e' .int ⊢
    bin_log_related_ty L ⊤ Δ Γ (.unop op e) (.unop op e') τ :=
  bin_log_related_lift1 (fun σ => substMap_unop σ op) fun _ _ => by
    rw [interp_int]
    iintro IH
    iapply refines_unop_bind op Val.int (fun _ _ => .rfl) $$ IH
    iintro %n
    cases op <;> simp [UnOp.intResTy] at Hres <;> subst Hres
    all_goals first
      | (rw [interp_int]; iapply refines_unop_val _ _ rfl (lrel_int_lit _))
      | (rw [interp_real]; iapply refines_unop_val _ _ rfl (lrel_real_lit _))

theorem bin_log_related_bool_unop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (op : UnOp)
    {e e' : Exp rT} {τ : Ty} (Hres : op.boolResTy = some τ) :
    bin_log_related_ty L ⊤ Δ Γ e e' .bool ⊢
    bin_log_related_ty L ⊤ Δ Γ (.unop op e) (.unop op e') τ :=
  bin_log_related_lift1 (fun σ => substMap_unop σ op) fun _ _ => by
    rw [interp_bool]
    iintro IH
    iapply refines_unop_bind op Val.bool (fun _ _ => .rfl) $$ IH
    iintro %b
    cases op <;> simp [UnOp.boolResTy] at Hres
    subst Hres
    rw [interp_bool]
    iapply refines_unop_val _ _ rfl (lrel_bool_lit _)

/-! ### The real fragment -/

theorem bin_log_related_real_unop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (op : UnOp)
    {e e' : Exp rT} {τ : Ty} (Hres : op.realResTy = some τ) :
    bin_log_related_ty L ⊤ Δ Γ e e' .real ⊢
    bin_log_related_ty L ⊤ Δ Γ (.unop op e) (.unop op e') τ :=
  bin_log_related_lift1 (fun σ => substMap_unop σ op) fun _ _ => by
    rw [interp_real]
    iintro IH
    iapply refines_unop_bind op Val.real (fun _ _ => .rfl) $$ IH
    iintro %r
    cases op <;> simp [UnOp.realResTy] at Hres <;> subst Hres
    all_goals (rw [interp_real]; iapply refines_unop_val _ _ rfl (lrel_real_lit _))

theorem bin_log_related_real_binop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (op : BinOp)
    {e1 e2 e1' e2' : Exp rT} {τ : Ty} (Hres : op.realResTy = some τ) : iprop%
    bin_log_related_ty L ⊤ Δ Γ e1 e1' .real ⊢
    bin_log_related_ty L ⊤ Δ Γ e2 e2' .real -∗
    bin_log_related_ty L ⊤ Δ Γ (.binop op e1 e2) (.binop op e1' e2') τ :=
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
    ⊢@{IProp GF} bin_log_related_ty L ⊤ Δ Γ .urand .urand .real := by
  unfold bin_log_related_ty bin_log_related
  iintro %vs -
  rw [substMap_urand, substMap_urand, interp_real,
    show (Exp.urand : Exp rT) = Ectx.fill [] Exp.urand from rfl]
  iapply refines_couple_urands_lr id (MeasureTheory.MeasurePreserving.id _)
  iintro %r -
  simp only [id_eq, Ectx.fill_nil]
  iapply refines_ret (v1 := .real r) (v2 := .real r) rfl rfl
  imodintro
  iapply lrel_real_lit r

/-! ### Equality and pattern matching -/

theorem bin_log_related_unboxed_eq (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e1 e2 e1' e2' : Exp rT}
    {τ : Ty} (HUnboxed : UnboxedType τ) : iprop%
    bin_log_related_ty L ⊤ Δ Γ e1 e1' τ ⊢
    bin_log_related_ty L ⊤ Δ Γ e2 e2' τ -∗
    bin_log_related_ty L ⊤ Δ Γ (.binop .eq e1 e2) (.binop .eq e1' e2') .bool := by
  unfold bin_log_related_ty bin_log_related
  iintro IH1 IH2 %vs #Hvs
  rw [substMap_binop, substMap_binop, ← Ectx.fill_binopR .eq (substMap vs.fst e1),
    ← Ectx.fill_binopR .eq (substMap vs.snd e1')]
  iapply refines_bind [EctxItem.binopR .eq (substMap vs.fst e1)]
    [EctxItem.binopR .eq (substMap vs.snd e1')] $$ (IH2 $$ %vs Hvs)
  iintro %v2 %v2' #Hv2
  rw [show Ectx.fill [EctxItem.binopR .eq (substMap vs.fst e1)] v2.1 =
      Ectx.fill [EctxItem.binopL .eq v2] (substMap vs.fst e1) from rfl,
    show Ectx.fill [EctxItem.binopR .eq (substMap vs.snd e1')] v2'.1 =
      Ectx.fill [EctxItem.binopL .eq v2'] (substMap vs.snd e1') from rfl]
  iapply refines_bind [EctxItem.binopL .eq v2] [EctxItem.binopL .eq v2'] $$ (IH1 $$ %vs Hvs)
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
      (w = w' ↔ m = m') := fun hw hw' => by simp [Val.ext_iff, hw, hw']
  have hdec : decide (l1 = l2) = decide (l1' = l2') := decide_eq_decide.mpr <| calc
    l1 = l2 ↔ v1 = v2 := (hval hv1eq hv2eq).symm
    _ ↔ v1' = v2' := heqIff
    _ ↔ l1' = l2' := hval hv1'eq hv2'eq
  have hφ : ∀ l l' : BaseLit rT, (Exp.lit l).isValue ∧ (Exp.lit l').isValue ∧
      BinOp.eval .eq (.lit l) (.lit l') = some pl(#(.bool (decide (l = l')))) :=
    fun _ _ => ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, by rw [← Bool.beq_eq_decide_eq]; rfl⟩
  rw [Ectx.eq_fill_nil (.binop .eq (.lit l1) (.lit l2)),
    Ectx.eq_fill_nil (.binop .eq (.lit l1') (.lit l2'))]
  iapply refines_pure_l (hφ l1 l2)
  inext
  iapply refines_pure_r (hφ l1' l2')
  simp only [Ectx.fill_nil]
  iapply refines_ret (v1 := .bool (decide (l1 = l2))) (v2 := .bool (decide (l1' = l2'))) rfl rfl
  imodintro
  rw [interp_bool, hdec]
  iapply lrel_bool_lit _

omit [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind] in
private theorem pat_match_lit {Δ : TyEnv rT GF} {l l' : BaseLit rT} {v v' : Val rT}
    (hv : v = .ofBaseLit l') (hv' : v' = .ofBaseLit l') (hll : l = l' ∨ ¬ (l == l') = true) :
    ⊢@{IProp GF} (∃ (b b' : Val rT), ⌜Pat.tryMatch (.lit l) v.1 = some b.1 ∧
      Pat.tryMatch (.lit l) v'.1 = some b'.1⌝ ∗ (interp L Ty.unit Δ).car b b') ∨
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

omit [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind] in
theorem pat_match_related {Δ : TyEnv rT GF} {τs τb : Ty} {p : Pat rT}
    (Hpat : PatTyped τs p τb) (v v' : Val rT) :
    (interp L τs Δ).car v v' ⊢@{IProp GF}
      (∃ (b b' : Val rT), ⌜Pat.tryMatch p v.1 = some b.1 ∧ Pat.tryMatch p v'.1 = some b'.1⌝ ∗
        (interp L τb Δ).car b b') ∨
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
        ¬ ((BaseLit.int z : BaseLit rT) == .int n) = true := by
      by_cases hzn : z = n <;> simp [hzn]
    iapply pat_match_lit h.1 h.2 hll
  | @lit_bool b =>
    rw [interp_bool]
    iintro Hv
    iunfold lrel_bool at Hv
    icases Hv with ⟨%b', %h⟩
    have hll : (BaseLit.bool b : BaseLit rT) = .bool b' ∨
        ¬ ((BaseLit.bool b : BaseLit rT) == .bool b') = true := by
      by_cases hbb : b = b' <;> simp [hbb]
    iapply pat_match_lit h.1 h.2 hll
  | lit_unit =>
    show iprop(⌜v = .unit ∧ v' = .unit⌝) ⊢ _
    iintro %h
    iapply pat_match_lit h.1 h.2 (.inl rfl)
  | @pair τ1 τ2 p1 p2 b1 b2 Hpat1 Hpat2 ih1 ih2 =>
    rw [interp_prod]
    iintro Hv
    iunfold lrel_prod at Hv
    icases Hv with ⟨%a1, %a2, %c1, %c2, %hv1, %hv2, HA, HC⟩
    icases ih1 a1 a2 $$ HA with (⟨%ba, %ba', %hra, HBa⟩ | %hna)
    · icases ih2 c1 c2 $$ HC with (⟨%bb, %bb', %hrb, HBb⟩ | %hnb)
      · ileft
        iexists .pair ba bb, .pair ba' bb'
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
    bin_log_related_ty L ⊤ Δ Γ e e' τs ⊢
    bin_log_related_ty L ⊤ Δ Γ (.scrut e p) (.scrut e' p) (.sum τb .unit) := by
  unfold bin_log_related_ty bin_log_related
  iintro IH %vs #Hvs
  rw [substMap_scrut, substMap_scrut, ← Ectx.fill_scrut p, ← Ectx.fill_scrut p]
  iapply refines_bind [EctxItem.scrut p] [EctxItem.scrut p] $$ (IH $$ %vs Hvs)
  iintro %v %v' #Hv
  rw [show Ectx.fill [EctxItem.scrut p] v.1 = Ectx.fill [] (.scrut v.1 p) from rfl,
    show Ectx.fill [EctxItem.scrut p] v'.1 = Ectx.fill [] (.scrut v'.1 p) from rfl]
  icases pat_match_related Hpat v v' $$ Hv with (⟨%bb, %bb', %hr, Hbnd⟩ | %hn)
  · iapply refines_pure_l (Hex := pureExec_scrut_some) ⟨v.2.toIsValue, hr.1⟩
    inext
    iapply refines_pure_r (Hex := pureExec_scrut_some) ⟨v'.2.toIsValue, hr.2⟩
    simp only [Ectx.fill_nil]
    iapply refines_ret (v1 := .inl bb) (v2 := .inl bb') rfl rfl
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
    simp only [Ectx.fill_nil]
    iapply refines_ret (v1 := .inr .unit) (v2 := .inr .unit) rfl rfl
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

omit [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind] in
theorem TctxRelated.lookup_isSome {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated L Δ Γtc Γrc) {x : Var} (hx : (Γtc x).isSome) : (Γrc.lookup x).isSome := by
  rw [← HCtx x]
  simpa using hx

omit [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind] in
theorem TctxRelated.lookup_some {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated L Δ Γtc Γrc) {x : Var} {τ : Ty} (hx : Γtc x = some τ) :
    Γrc.lookup x = some (interp L τ Δ) := by
  rw [← HCtx x, hx]
  rfl

omit [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind] in
theorem TctxRelated.shift {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated L Δ Γtc Γrc) (A : lrel rT GF) :
    TctxRelated L (TyEnv.cons A Δ) Γtc.shift Γrc := by
  intro x
  simpa [Tctx.shift, Option.map_map, Function.comp_def, interp_ren] using HCtx x

omit [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind] in
theorem TctxRelated.insert {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated L Δ Γtc Γrc) (x : Var) (τ : Ty) (hfresh : Γrc.lookup x = none) :
    TctxRelated L Δ (Γtc.insert x τ) ((x, interp L τ Δ) :: Γrc) := by
  intro y
  by_cases hyx : y = x
  · subst hyx
    simp [Tctx.insert, RelCtx.lookup_cons, hfresh]
  · rw [Tctx.insert, ite_eq_right hyx, RelCtx.lookup_cons, ← HCtx y]
    cases Γtc y <;> simp [hyx]

omit [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind] in
theorem fv_subset_relCtxDom {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated L Δ Γtc Γrc) {e : Exp rT} {τ : Ty} (Hty : Typed Γtc e τ) :
    e.fv ⊆ (Γrc.map (·.1)).toFinset :=
  fun x hx => RelCtx.mem_of_lookup_isSome (HCtx.lookup_isSome (Hty.fvSubset x hx))

omit [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind] in
private theorem fv_subset_of_cofinite {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated L Δ Γtc Γrc) {S : Finset Var} {e : Exp rT} {τ1 τ2 : Ty}
    (Hbody : ∀ x ∉ S, Typed (Γtc.insert x τ1) (open' e (.fvar x)) τ2) :
    e.fv ⊆ (Γrc.map (·.1)).toFinset := by
  intro z hz
  obtain ⟨y, hy⟩ := HasFresh.fresh_exists (S ∪ (Γrc.map (·.1)).toFinset ∪ {z})
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
  have hzdom := fv_subset_relCtxDom (HCtx.insert y τ1 (RelCtx.lookup_eq_none_of_not_mem hy.1.2))
    (Hbody y hy.1.1) (fv_subset_open e y hz)
  simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert] at hzdom
  exact hzdom.resolve_left fun h => hy.2 h.symm

omit [LawfulProbLangℝ rT] in
private theorem not_mem_union_dom {S : Finset Var} {Γrc : RelCtx rT GF} {x : Var}
    (hx : x ∉ S ∪ (Γrc.map (·.1)).toFinset) : x ∉ S ∧ Γrc.lookup x = none := by
  simp only [Finset.mem_union, not_or] at hx
  exact ⟨hx.1, RelCtx.lookup_eq_none_of_not_mem hx.2⟩

variable (L) in
theorem fundamental {Γtc : Tctx} {e : Exp rT} {τ : Ty} (Hty : Typed Γtc e τ) (Δ : TyEnv rT GF)
    (Γrc : RelCtx rT GF) (HCtx : TctxRelated L Δ Γtc Γrc) :
    ⊢@{IProp GF} bin_log_related_ty L ⊤ Δ Γrc e e τ := by
  induction Hty generalizing Δ Γrc with
  | @fvar _ x τ hx => exact bin_log_related_var Δ Γrc x τ (HCtx.lookup_some hx)
  | @lit_int _ n => exact bin_log_related_lit Γrc _ (lrel_int_lit n)
  | @lit_real _ r => exact bin_log_related_lit Γrc _ (lrel_real_lit r)
  | @lit_bool _ b => exact bin_log_related_lit Γrc _ (lrel_bool_lit b)
  | lit_unit => exact bin_log_related_lit Γrc _ lrel_unit_lit
  | «urand» => exact bin_log_related_urand Δ Γrc
  | unop_real _ Hres ih => iapply bin_log_related_real_unop Δ Γrc _ Hres $$ %(ih Δ Γrc HCtx)
  | unop_int _ Hres ih => iapply bin_log_related_int_unop Δ Γrc _ Hres $$ %(ih Δ Γrc HCtx)
  | unop_bool _ Hres ih => iapply bin_log_related_bool_unop Δ Γrc _ Hres $$ %(ih Δ Γrc HCtx)
  | binop_real _ _ Hres ih1 ih2 =>
    iapply bin_log_related_real_binop Δ Γrc _ Hres $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | binop_int _ _ Hres ih1 ih2 =>
    iapply bin_log_related_int_binop Δ Γrc _ Hres $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | binop_bool _ _ Hres ih1 ih2 =>
    iapply bin_log_related_bool_binop Δ Γrc _ Hres $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | unboxed_eq HUnboxed _ _ ih1 ih2 =>
    iapply bin_log_related_unboxed_eq Δ Γrc HUnboxed $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | pair _ _ ih1 ih2 => iapply bin_log_related_pair $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | fst _ ih => iapply bin_log_related_fst $$ %(ih Δ Γrc HCtx)
  | snd _ ih => iapply bin_log_related_snd $$ %(ih Δ Γrc HCtx)
  | inl _ ih => iapply bin_log_related_injl $$ %(ih Δ Γrc HCtx)
  | inr _ ih => iapply bin_log_related_injr $$ %(ih Δ Γrc HCtx)
  | «case» _ _ _ ih0 ih1 ih2 =>
    iapply bin_log_related_case $$ %(ih0 Δ Γrc HCtx) %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | cond _ _ _ ih0 ih1 ih2 =>
    iapply bin_log_related_if $$ %(ih0 Δ Γrc HCtx) %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | app _ _ ih1 ih2 => iapply bin_log_related_app $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | alloc _ ih => iapply bin_log_related_alloc $$ %(ih Δ Γrc HCtx)
  | load _ ih => iapply bin_log_related_load $$ %(ih Δ Γrc HCtx)
  | store _ _ ih1 ih2 => iapply bin_log_related_store $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | alloc_tape _ ih => iapply bin_log_related_alloctape $$ %(ih Δ Γrc HCtx)
  | rand _ _ ih1 ih2 => iapply bin_log_related_rand_tape $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | rand_unit _ _ ih1 ih2 => iapply bin_log_related_rand_unit $$ %(ih1 Δ Γrc HCtx) %(ih2 Δ Γrc HCtx)
  | «scrut» _ Hpat ih => iapply bin_log_related_scrut Δ Γrc Hpat $$ %(ih Δ Γrc HCtx)
  | tfold _ ih => iapply bin_log_related_fold $$ %(ih Δ Γrc HCtx)
  | tunfold _ ih => iapply bin_log_related_unfold $$ %(ih Δ Γrc HCtx)
  | tapp _ ih => iapply bin_log_related_tapp $$ %(ih Δ Γrc HCtx)
  | tpack _ ih => iapply bin_log_related_pack $$ %(ih Δ Γrc HCtx)
  | @lam S _ e τ1 τ2 Hbody ih =>
    let S' : Finset Var := S ∪ (Γrc.map (·.1)).toFinset
    have he_fv := fv_subset_of_cofinite HCtx Hbody
    have he_lc : ∀ x ∉ S', (open' e (.fvar x)).IsLocallyClosed := fun x hx =>
      (Hbody x (not_mem_union_dom hx).1).isLocallyClosed
    exact bin_log_related_lam Δ Γrc S' he_lc he_lc he_fv he_fv fun x hx =>
      ih x (not_mem_union_dom hx).1 Δ _ (HCtx.insert x τ1 (not_mem_union_dom hx).2)
  | @«fix» S _ e τ1 τ2 Hbody ih =>
    let S' : Finset Var := S ∪ (Γrc.map (·.1)).toFinset
    have he_fv := fv_subset_of_cofinite HCtx Hbody
    have he_lc : ∀ x ∉ S', (open' e (.fvar x)).IsLocallyClosed := fun x hx =>
      (Hbody x (not_mem_union_dom hx).1).isLocallyClosed
    exact bin_log_related_fix Δ Γrc S' he_lc he_lc he_fv he_fv fun x hx =>
      ih x (not_mem_union_dom hx).1 Δ _ (HCtx.insert x (.arrow τ1 τ2) (not_mem_union_dom hx).2)
  | @tlam _ e τ Hbody ih =>
    have hLC := Hbody.isLocallyClosed
    have he_fv := fv_subset_relCtxDom (HCtx.shift default) Hbody
    refine bin_log_related_tlam Δ Γrc hLC hLC he_fv he_fv fun A => ?_
    imodintro
    iapply ih (TyEnv.cons A Δ) Γrc (HCtx.shift A)
  | @tunpack S _ e1 e2 τ τ2 _ Hbody2 ih1 ih2 =>
    let S' : Finset Var := S ∪ (Γrc.map (·.1)).toFinset
    have he2_lc : ∀ x ∉ S', (open' e2 (.fvar x)).IsLocallyClosed := fun x hx =>
      (Hbody2 x (not_mem_union_dom hx).1).isLocallyClosed
    exact bin_log_related_unpack Δ Γrc S' (ih1 Δ Γrc HCtx) he2_lc he2_lc fun A x hx =>
      ih2 x (not_mem_union_dom hx).1 (TyEnv.cons A Δ) _
        ((HCtx.shift A).insert x τ (not_mem_union_dom hx).2)

theorem refines_typed (Δ : TyEnv rT GF) {e : Exp rT} {τ : Ty} (Hty : Typed Tctx.empty e τ) :
    ⊢@{IProp GF} refines L ⊤ e e (interp L τ Δ) := by
  have Hfund := fundamental L Hty Δ [] (by intro x; simp [Tctx.empty, RelCtx.lookup])
  unfold bin_log_related_ty bin_log_related at Hfund
  show ⊢@{IProp GF} refines L ⊤ (substMap (ValSubstMap.fst ([] : ValSubstMap rT)) e)
    (substMap (ValSubstMap.snd ([] : ValSubstMap rT)) e) (interp L τ Δ)
  iapply Hfund $$ %([] : ValSubstMap rT)
  iapply env_ltyped2_empty

end Fundamental

end ProbLang
