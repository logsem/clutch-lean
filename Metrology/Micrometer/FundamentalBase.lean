module

public import Metrology.Micrometer.CompatibilityState
public import Metrology.Micrometer.ContinuousSampler
public import Metrology.Micrometer.BinLogRelated
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

/-! # Open compatibility helpers

Rules for lifting closed `refines` lemmas to the open judgement `bin_log_related`
(`lift1`/`2`/`3`, literals, variables, `refines_beta`), and closedness facts for substitutions. -/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting

namespace ProbLang

variable {rT : Type} {GF : BundledGFunctors}

open Cslib Exp ValSubstMap RelCtx Ectx SubstMap

section Substitution
variable {Γ : RelCtx rT GF} {vs : ValSubstMap rT} {e e' : Exp rT} {S : Finset Var}

/-- Substituting a fresh variable bound to a value pair commutes with opening, on both sides. -/
theorem substMap_open_fresh_pair {x : Var} {v v' : Val rT}
    (hfst : AllClosed vs.fst) (hsnd : AllClosed vs.snd)
    (hxe : x ∉ e.fv) (hxe' : x ∉ e'.fv) (hxdom : x ∉ (vs.map (·.1)).toFinset)
    (hv : v.1.IsClosedEmpty) (hv' : v'.1.IsClosedEmpty) :
    substMap (fst ((x, (v, v')) :: vs)) (open' e (.fvar x)) = open' (substMap vs.fst e) v.1 ∧
      substMap (snd ((x, (v, v')) :: vs)) (open' e' (.fvar x)) = open' (substMap vs.snd e') v'.1 :=
  ⟨substMap_open_fresh hfst hxe (fst_lookup_eq_none_of_notMem hxdom) hv.1,
    substMap_open_fresh hsnd hxe' (snd_lookup_eq_none_of_notMem hxdom) hv'.1⟩

/-- Free variables of both terms lie in the domains of the left and right substitutions. -/
theorem fv_subset_substMap_dom (hdom : (Γ.map (·.1)).toFinset ⊆ (vs.map (·.1)).toFinset)
    (he : e.fv ⊆ (Γ.map (·.1)).toFinset) (he' : e'.fv ⊆ (Γ.map (·.1)).toFinset) :
    e.fv ⊆ (vs.fst.map (·.1)).toFinset ∧ e'.fv ⊆ (vs.snd.map (·.1)).toFinset := by
  rw [fst_dom, snd_dom]
  exact ⟨he.trans hdom, he'.trans hdom⟩


/-- Substituting into a `lam` body keeps both sides locally closed. -/
theorem substMap_lam_lc (hvs : AllClosed vs.fst ∧ AllClosed vs.snd)
    (he_lc : ∀ x ∉ S, (open' e (.fvar x)).IsLocallyClosed)
    (he'_lc : ∀ x ∉ S, (open' e' (.fvar x)).IsLocallyClosed) :
    (lam (substMap vs.fst e)).IsLocallyClosed ∧ (lam (substMap vs.snd e')).IsLocallyClosed :=
  ⟨lam_substMap_isLocallyClosed hvs.1 (fun _ hy => fst_lookup_eq_none_of_notMem hy) he_lc,
    lam_substMap_isLocallyClosed hvs.2 (fun _ hy => snd_lookup_eq_none_of_notMem hy) he'_lc⟩

section Closed
variable (hvs : AllClosed vs.fst ∧ AllClosed vs.snd)
  (hdom : (Γ.map (·.1)).toFinset ⊆ (vs.map (·.1)).toFinset)
  (he_lc : ∀ x ∉ S, (open' e (.fvar x)).IsLocallyClosed)
  (he'_lc : ∀ x ∉ S, (open' e' (.fvar x)).IsLocallyClosed)
  (he_fv : e.fv ⊆ (Γ.map (·.1)).toFinset) (he'_fv : e'.fv ⊆ (Γ.map (·.1)).toFinset)
include hvs hdom he_lc he'_lc he_fv he'_fv

/-- Both substituted `lam` terms are closed. -/
theorem substMap_lam_closed :
    (lam (substMap vs.fst e)).IsClosedEmpty ∧ (lam (substMap vs.snd e')).IsClosedEmpty := by
  obtain ⟨he_dom_fst, he_dom_snd⟩ := fv_subset_substMap_dom hdom he_fv he'_fv
  obtain ⟨hlam_lc, hlam'_lc⟩ := substMap_lam_lc hvs he_lc he'_lc
  exact ⟨⟨hlam_lc, substMap_fv_eq_empty hvs.1 he_dom_fst⟩,
    ⟨hlam'_lc, substMap_fv_eq_empty hvs.2 he_dom_snd⟩⟩

/-- Both substituted `fix` terms are closed. -/
theorem substMap_fix_closed :
    (fix (substMap vs.fst e)).IsClosedEmpty ∧ (fix (substMap vs.snd e')).IsClosedEmpty := by
  obtain ⟨he_dom_fst, he_dom_snd⟩ := fv_subset_substMap_dom hdom he_fv he'_fv
  exact ⟨⟨fix_substMap_isLocallyClosed hvs.1 (fun _ hy => fst_lookup_eq_none_of_notMem hy) he_lc,
      substMap_fv_eq_empty hvs.1 he_dom_fst⟩,
    ⟨fix_substMap_isLocallyClosed hvs.2 (fun _ hy => snd_lookup_eq_none_of_notMem hy) he'_lc,
      substMap_fv_eq_empty hvs.2 he_dom_snd⟩⟩

end Closed

end Substitution

section Fundamental
variable [MeasurableSpace rT] [LawfulProbLangℝ rT] {hlc : HasLC} {B : Type} [AddCommMonoid B]
    [PartialOrder B]
  [OrderTop B] {L : GradedLifting.{0} B} [IR : MicrometerRGS rT hlc GF] [BudgetCreditGS B GF]
local bi IProp GF
variable {Γ : RelCtx rT GF} {vs : ValSubstMap rT} {e e' : Exp rT} {A C : lrel rT GF}
  {S : Finset Var}

/-! ## Lifting `refines` rules to `bin_log_related` -/

/-- Lift a unary `refines` rule for `f` to open terms by pushing `substMap` through `f`. -/
theorem bin_log_related_lift1 {f : Exp rT → Exp rT}
    (hf : ∀ σ t, substMap σ (f t) = f (substMap σ t))
    (H : ∀ t t', refines L ⊤ t t' A ⊢ refines L ⊤ (f t) (f t') C) :
    bin_log_related L ⊤ Γ e e' A ⊢ bin_log_related L ⊤ Γ (f e) (f e') C := by
  unfold bin_log_related
  iintro IH %vs #Hvs
  rw [hf, hf]
  iapply H _ _ $$ (IH $$ %vs Hvs)

/-- Lift a binary `refines` rule for `f` to open terms. -/
theorem bin_log_related_lift2 {e1 e2 e1' e2' : Exp rT}
    {A1 A2 : lrel rT GF} {f : Exp rT → Exp rT → Exp rT}
    (hf : ∀ σ t1 t2, substMap σ (f t1 t2) = f (substMap σ t1) (substMap σ t2))
    (H : ∀ t1 t2 t1' t2', iprop%
      refines L ⊤ t1 t1' A1 ⊢ refines L ⊤ t2 t2' A2 -∗ refines L ⊤ (f t1 t2) (f t1' t2') C) : iprop%
    bin_log_related L ⊤ Γ e1 e1' A1 ⊢
      bin_log_related L ⊤ Γ e2 e2' A2 -∗ bin_log_related L ⊤ Γ (f e1 e2) (f e1' e2') C := by
  unfold bin_log_related
  iintro IH1 IH2 %vs #Hvs
  rw [hf, hf]
  iapply H _ _ _ _ $$ (IH1 $$ %vs Hvs) (IH2 $$ %vs Hvs)

/-- Lift a ternary `refines` rule for `f` to open terms. -/
theorem bin_log_related_lift3 {e0 e1 e2 e0' e1' e2' : Exp rT}
    {A0 A1 A2 : lrel rT GF} {f : Exp rT → Exp rT → Exp rT → Exp rT}
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

/-- Literals are related to themselves at any type containing them. -/
theorem bin_log_related_lit (Γ : RelCtx rT GF) (l : BaseLit rT)
    (HA : ⊢ A.car (.ofBaseLit l) (.ofBaseLit l)) :
    ⊢ bin_log_related L ⊤ Γ (.lit l) (.lit l) A := by
  unfold bin_log_related
  iintro %vs -
  rw [substMap_lit, substMap_lit, show lit l = (Val.ofBaseLit l).1 from rfl]
  iapply refines_ret rfl rfl
  imodintro
  iapply HA

/-- A variable is related to itself at the type the context assigns it. -/
theorem bin_log_related_var (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (x : Var) (τ : Ty)
    (hΓ : Γ.lookup x = some (interp L τ Δ)) :
    ⊢ bin_log_related_ty L ⊤ Δ Γ (.fvar x) (.fvar x) τ := by
  unfold bin_log_related_ty bin_log_related
  iintro %vs #Hvs
  icases env_ltyped2_lookup Γ vs x (interp L τ Δ) hΓ $$ Hvs with ⟨%v1, %v2, %hvs_eq, HA⟩
  ihave %hfst_closed := env_ltyped2_fst_allClosed Γ vs $$ Hvs
  ihave %hsnd_closed := env_ltyped2_snd_allClosed Γ vs $$ Hvs
  rw [substMap_fvar_lookup_some _ _ hfst_closed (by rw [fst_lookup, hvs_eq]; rfl),
    substMap_fvar_lookup_some _ _ hsnd_closed (by rw [snd_lookup, hvs_eq]; rfl)]
  iapply refines_ret rfl rfl
  imodintro
  iexact HA

section Steps
variable [L.IsLawful] [L.IsTopAbsorbing]

/-- Beta reduction on both sides, one step later, as a closed `refines` rule. -/
theorem refines_beta {v v' : Val rT}
    (he : (lam e).IsLocallyClosed) (he' : (lam e').IsLocallyClosed) : iprop%
    ▷ refines L ⊤ (open' e v.1) (open' e' v'.1) A ⊢
      refines L ⊤ (.app (.lam e) v.1) (.app (.lam e') v'.1) A := by
  rw [eq_fill_nil (.app (.lam e) v.1), eq_fill_nil (.app (.lam e') v'.1)]
  iintro H
  iapply refines_pure_l (Hex := pureExec_app_lam) ⟨v.2.toIsValue, he⟩
  inext
  iapply refines_pure_r (Hex := pureExec_app_lam) ⟨v'.2.toIsValue, he'⟩
  simp only [fill_nil]
  iexact H

end Steps

/-! ## Substitution and closedness helpers -/

/-- A related substitution is closed on both sides. -/
theorem env_ltyped2_allClosed_pair (Γ : RelCtx rT GF) (vs : ValSubstMap rT) :
    env_ltyped2 Γ vs ⊢ ⌜AllClosed vs.fst ∧ AllClosed vs.snd⌝ := by
  iintro Hvs
  ihave %hfst := env_ltyped2_fst_allClosed Γ vs $$ Hvs
  ihave %hsnd := env_ltyped2_snd_allClosed Γ vs $$ Hvs
  ipureintro
  exact ⟨hfst, hsnd⟩

end Fundamental

section Fresh

/-- A variable fresh for a set, both terms and a substitution domain exists. -/
theorem exists_fresh_var (S : Finset Var) (e e' : Exp rT) (vs : ValSubstMap rT) :
    ∃ x, x ∉ S ∧ x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ (vs.map (·.1)).toFinset := by
  obtain ⟨x, hx⟩ := HasFresh.fresh_exists (S ∪ e.fv ∪ e'.fv ∪ (vs.map (·.1)).toFinset)
  simp only [Finset.mem_union, not_or] at hx
  exact ⟨x, hx.1.1.1, hx.1.1.2, hx.1.2, hx.2⟩

/-- A variable outside the set and the context domain is unbound in the context. -/
theorem not_mem_union_dom {S : Finset Var} {Γrc : RelCtx rT GF} {x : Var}
    (hx : x ∉ S ∪ (Γrc.map (·.1)).toFinset) : x ∉ S ∧ Γrc.lookup x = none := by
  simp only [Finset.mem_union, not_or] at hx
  exact ⟨hx.1, lookup_eq_none_of_notMem hx.2⟩

end Fresh

end ProbLang
