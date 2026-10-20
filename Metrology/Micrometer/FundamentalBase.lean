module

public import Metrology.Micrometer.CompatibilityState
public import Metrology.Micrometer.ContinuousSampler
public import Metrology.Micrometer.BinLogRelated
import Metrology.ProbLang.Syntax.Notation

/-! Shared helpers of the compatibility lemmas for `bin_log_related`. -/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting

namespace ProbLang

open Cslib Exp

section Fresh
variable {rT : Type} {GF : BundledGFunctors}

theorem exists_fresh_var (S : Finset Var) (e e' : Exp rT) (vs : ValSubstMap rT) :
    ∃ x, x ∉ S ∧ x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ (vs.map (·.1)).toFinset := by
  obtain ⟨x, hx⟩ := HasFresh.fresh_exists (S ∪ e.fv ∪ e'.fv ∪ (vs.map (·.1)).toFinset)
  simp only [Finset.mem_union, not_or] at hx
  exact ⟨x, hx.1.1.1, hx.1.1.2, hx.1.2, hx.2⟩

theorem not_mem_union_dom {S : Finset Var} {Γrc : RelCtx rT GF} {x : Var}
    (hx : x ∉ S ∪ (Γrc.map (·.1)).toFinset) : x ∉ S ∧ Γrc.lookup x = none := by
  simp only [Finset.mem_union, not_or] at hx
  exact ⟨hx.1, RelCtx.lookup_eq_none_of_not_mem hx.2⟩

end Fresh

section Fundamental
variable {rT : Type} [LawfulProbLangℝ rT] {hlc : HasLC} {B : Type} [AddCommMonoid B]
  [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors}
  [IR : MicrometerRGS rT hlc GF] [BudgetCreditGS B GF]

theorem substMap_open_fresh_pair {vs : ValSubstMap rT} {x : Var} {v v' : Val rT}
    {e e' : Exp rT} (hfst : SubstMap.AllClosed vs.fst) (hsnd : SubstMap.AllClosed vs.snd)
    (hxe : x ∉ e.fv) (hxe' : x ∉ e'.fv) (hxdom : x ∉ (vs.map (·.1)).toFinset)
    (hv : v.1.isClosedEmpty) (hv' : v'.1.isClosedEmpty) :
    substMap (ValSubstMap.fst ((x, (v, v')) :: vs)) (open' e (.fvar x)) =
      open' (substMap vs.fst e) v.1 ∧
    substMap (ValSubstMap.snd ((x, (v, v')) :: vs)) (open' e' (.fvar x)) =
      open' (substMap vs.snd e') v'.1 :=
  ⟨substMap_open_fresh hfst hxe (ValSubstMap.fst_lookup_eq_none_of_not_mem hxdom) hv.1,
    substMap_open_fresh hsnd hxe' (ValSubstMap.snd_lookup_eq_none_of_not_mem hxdom) hv'.1⟩

theorem fv_subset_substMap_dom {Γ : RelCtx rT GF} {vs : ValSubstMap rT} {e e' : Exp rT}
    (hdom : (Γ.map (·.1)).toFinset ⊆ (vs.map (·.1)).toFinset)
    (he : e.fv ⊆ (Γ.map (·.1)).toFinset) (he' : e'.fv ⊆ (Γ.map (·.1)).toFinset) :
    e.fv ⊆ (vs.fst.map (·.1)).toFinset ∧ e'.fv ⊆ (vs.snd.map (·.1)).toFinset := by
  rw [ValSubstMap.fst_dom, ValSubstMap.snd_dom]
  exact ⟨he.trans hdom, he'.trans hdom⟩

theorem env_ltyped2_allClosed_pair (Γ : RelCtx rT GF) (vs : ValSubstMap rT) :
    env_ltyped2 Γ vs ⊢ ⌜SubstMap.AllClosed vs.fst ∧ SubstMap.AllClosed vs.snd⌝ := by
  iintro Hvs
  ihave %hfst := env_ltyped2_fst_allClosed Γ vs $$ Hvs
  ihave %hsnd := env_ltyped2_snd_allClosed Γ vs $$ Hvs
  ipureintro
  exact ⟨hfst, hsnd⟩

theorem substMap_lam_lc {vs : ValSubstMap rT} {e e' : Exp rT} {S : Finset Var}
    (hvs : SubstMap.AllClosed vs.fst ∧ SubstMap.AllClosed vs.snd)
    (he_lc : ∀ x ∉ S, (open' e (.fvar x)).IsLocallyClosed)
    (he'_lc : ∀ x ∉ S, (open' e' (.fvar x)).IsLocallyClosed) :
    (Exp.lam (substMap vs.fst e)).IsLocallyClosed ∧
      (Exp.lam (substMap vs.snd e')).IsLocallyClosed :=
  ⟨lam_substMap_isLocallyClosed hvs.1
      (fun _ hy => ValSubstMap.fst_lookup_eq_none_of_not_mem hy) he_lc,
    lam_substMap_isLocallyClosed hvs.2
      (fun _ hy => ValSubstMap.snd_lookup_eq_none_of_not_mem hy) he'_lc⟩

theorem substMap_lam_closed {Γ : RelCtx rT GF} {vs : ValSubstMap rT} {e e' : Exp rT}
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

theorem substMap_fix_closed {Γ : RelCtx rT GF} {vs : ValSubstMap rT} {e e' : Exp rT}
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

/-! ## Lifting `refines` rules to `bin_log_related`

`bin_log_related_lift{1,2,3}` push `substMap` through a constructor `f` and apply a
`refines` rule for `f`. -/

theorem bin_log_related_lift1 {Γ : RelCtx rT GF} {e e' : Exp rT} {A C : lrel rT GF}
    {f : Exp rT → Exp rT} (hf : ∀ σ t, substMap σ (f t) = f (substMap σ t))
    (H : ∀ t t', refines L ⊤ t t' A ⊢ refines L ⊤ (f t) (f t') C) :
    bin_log_related L ⊤ Γ e e' A ⊢ bin_log_related L ⊤ Γ (f e) (f e') C := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  rw [hf, hf]
  iapply H _ _ $$ (IH $$ %vs Hvs)

theorem bin_log_related_lift2 {Γ : RelCtx rT GF} {e1 e2 e1' e2' : Exp rT}
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

theorem bin_log_related_lift3 {Γ : RelCtx rT GF} {e0 e1 e2 e0' e1' e2' : Exp rT}
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

theorem bin_log_related_lit (Γ : RelCtx rT GF) (l : BaseLit rT) {A : lrel rT GF}
    (HA : ⊢@{IProp GF} A.car (.ofBaseLit l) (.ofBaseLit l)) :
    ⊢@{IProp GF} bin_log_related L ⊤ Γ (.lit l) (.lit l) A := by
  unfold bin_log_related
  iintro %vs -
  rw [substMap_lit, substMap_lit, show lit l = (Val.ofBaseLit l).1 from rfl]
  iapply refines_ret rfl rfl
  imodintro
  iapply HA

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

section Steps
variable [L.IsLawful] [L.IsTopAbsorbing]

theorem refines_beta {e e' : Exp rT} {v v' : Val rT} {A : lrel rT GF}
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

end Steps

end Fundamental

end ProbLang
