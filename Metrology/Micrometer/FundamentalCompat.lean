module

public import Metrology.Micrometer.FundamentalBase
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! Compatibility of `bin_log_related` with the pure and type-level constructors. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting

namespace ProbLang

open Cslib Exp

section Fundamental
variable {rT : Type} [LawfulProbLangℝ rT] {hlc : HasLC} {B : Type} [AddCommMonoid B]
  [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors}
  [IR : MicrometerRGS rT hlc GF] [BudgetCreditGS B GF]

section Steps
variable [L.IsLawful] [L.IsTopAbsorbing]

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

theorem bin_log_related_injl (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ1 τ2 : Ty} :
    bin_log_related_ty L ⊤ Δ Γ e e' τ1 ⊢
    bin_log_related_ty L ⊤ Δ Γ (.inl e) (.inl e') (.sum τ1 τ2) :=
  bin_log_related_lift1 substMap_inl fun _ _ => refines_injl

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

theorem bin_log_related_app (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e1 e2 e1' e2' : Exp rT}
    {τ1 τ2 : Ty} : iprop%
    bin_log_related_ty L ⊤ Δ Γ e1 e1' (.arrow τ1 τ2) ⊢
    bin_log_related_ty L ⊤ Δ Γ e2 e2' τ1 -∗
    bin_log_related_ty L ⊤ Δ Γ (.app e1 e2) (.app e1' e2') τ2 :=
  bin_log_related_lift2 substMap_app fun _ _ _ _ => refines_app

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

/-! ## Polymorphic and recursive types -/

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

/-- `unpack` compatibility, as an entailment from the relation of the unpacked term. -/
theorem bin_log_related_unpack_wand (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (S : Finset Var)
    {e1 e1' e2 e2' : Exp rT} {τ τ2 : Ty}
    (he2_lc : ∀ x ∉ S, (open' e2 (.fvar x)).IsLocallyClosed)
    (he2'_lc : ∀ x ∉ S, (open' e2' (.fvar x)).IsLocallyClosed)
    (HIH2 : ∀ A : lrel rT GF, ∀ x ∉ S, ⊢@{IProp GF} bin_log_related_ty L ⊤ (TyEnv.cons A Δ)
      ((x, interp L τ (TyEnv.cons A Δ)) :: Γ) (open' e2 (.fvar x)) (open' e2' (.fvar x)) τ2.shift) :
    bin_log_related_ty L ⊤ Δ Γ e1 e1' (.exists' τ) ⊢
      bin_log_related_ty L ⊤ Δ Γ (.app (.lam e2) e1) (.app (.lam e2') e1') τ2 := by
  unfold bin_log_related_ty bin_log_related at HIH2 ⊢
  iintro HIH1 %vs #Hvs
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

/-- `unpack` compatibility for `bin_log_related`. -/
theorem bin_log_related_unpack (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (S : Finset Var)
    {e1 e1' e2 e2' : Exp rT} {τ τ2 : Ty}
    (HIH1 : ⊢@{IProp GF} bin_log_related_ty L ⊤ Δ Γ e1 e1' (.exists' τ))
    (he2_lc : ∀ x ∉ S, (open' e2 (.fvar x)).IsLocallyClosed)
    (he2'_lc : ∀ x ∉ S, (open' e2' (.fvar x)).IsLocallyClosed)
    (HIH2 : ∀ A : lrel rT GF, ∀ x ∉ S, ⊢@{IProp GF} bin_log_related_ty L ⊤ (TyEnv.cons A Δ)
      ((x, interp L τ (TyEnv.cons A Δ)) :: Γ) (open' e2 (.fvar x)) (open' e2' (.fvar x)) τ2.shift) :
    ⊢@{IProp GF} bin_log_related_ty L ⊤ Δ Γ (.app (.lam e2) e1) (.app (.lam e2') e1') τ2 :=
  HIH1.trans (bin_log_related_unpack_wand Δ Γ S he2_lc he2'_lc HIH2)

end Steps

end Fundamental

end ProbLang
