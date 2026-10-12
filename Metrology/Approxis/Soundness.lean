module

public import Metrology.Approxis.PrimitiveLaws
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Approxis.Model
public import Metrology.Approxis.AdequacyRel
public import Metrology.Approxis.Interp
public import Metrology.Approxis.Fundamental
public import Metrology.ProbLang.ContextualRefinement

@[expose] public section

/-! # Soundness -/

namespace ProbLang

open ProbLang.Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS

section Soundness
variable {rT : Type _} [LawfulProbLangℝ rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ApproxisRGS rT hlc GF]

def Ctx.BindersFresh : Ctx rT → Finset Var → Prop
  | [], _ => True
  | k :: K', S =>
    (∀ x ∈ k.binderAtoms, x ∉ S) ∧ Ctx.BindersFresh K' (S ∪ k.binderAtoms)

theorem Ctx.BindersFresh.mono {K : Ctx rT} {S T : Finset Var} (hST : S ⊆ T)
    (h : Ctx.BindersFresh K T) : Ctx.BindersFresh K S := by
  induction K generalizing S T with
  | nil => trivial
  | cons k K' ih =>
    exact ⟨fun y hy hyS => h.1 y hy (hST hyS),
      ih (Finset.union_subset_union hST Finset.Subset.rfl) h.2⟩

theorem binders_tail {k : CtxItem rT} {K' : Ctx rT} {e e' : Exp rT}
    (Hb : ∀ x ∈ Ctx.binderAtoms (k :: K'), x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ Ctx.payloadFv (k :: K')) :
    ∀ x ∈ Ctx.binderAtoms K', x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ Ctx.payloadFv K' := by
  intro x hxK'
  obtain ⟨h1, h2, h3⟩ := Hb x (Finset.mem_union_right _ hxK')
  exact ⟨h1, h2, h3 ∘ Finset.mem_union_right _⟩

theorem TctxRelated.empty_nil {Δ : TyEnv rT GF} : TctxRelated Δ Tctx.empty ([] : RelCtx rT GF) := by
  intro x; simp [Tctx.empty, RelCtx.lookup]

theorem TctxRelated.eq_nil_of_empty {Δ : TyEnv rT GF} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated Δ Tctx.empty Γrc) : Γrc = [] := by
  cases Γrc with
  | nil => rfl
  | cons p rest =>
    have h := HCtx p.1
    simp only [Tctx.empty, RelCtx.lookup] at h
    cases hr : RelCtx.lookup rest p.1 <;> rw [hr] at h <;> simp at h

theorem ctx_fill_lc_fv {Γtc : Tctx} {Γrc : RelCtx rT GF} {Δ : TyEnv rT GF} {K : Ctx rT}
    {e : Exp rT} {τ : Ty} (HCtxRel : TctxRelated Δ Γtc Γrc) (Hty : Typed Γtc (K.fill e) τ) :
    (K.fill e).IsLocallyClosed ∧ (K.fill e).fv ⊆ (Γrc.map (·.1)).toFinset :=
  ⟨Hty.isLocallyClosed, fv_subset_relCtxDom HCtxRel Hty⟩

omit [LawfulProbLangℝ rT] in
theorem RelCtx.dom_cons (x : Var) (A : lrel rT GF) (Γrc : RelCtx rT GF) :
    (((x, A) :: Γrc).map (·.1)).toFinset = (Γrc.map (·.1)).toFinset ∪ {x} := by
  simp [List.map_cons, List.toFinset_cons, Finset.union_comm]

theorem Ctx.BindersFresh.cons_extend {K' : Ctx rT} {Γrc : RelCtx rT GF} {x : Var}
    {A : lrel rT GF} {bAtoms : Finset Var} (hSingleton : bAtoms = {x})
    (h : Ctx.BindersFresh K' ((Γrc.map (·.1)).toFinset ∪ bAtoms)) :
    Ctx.BindersFresh K' (((x, A) :: Γrc).map (·.1)).toFinset :=
  RelCtx.dom_cons x A Γrc ▸ hSingleton ▸ h

theorem bin_log_related_close_cofinite {Δ : TyEnv rT GF} {Γrc' : RelCtx rT GF} {x : Var}
    {A : lrel rT GF} {τ : Ty} {Ke Ke' : Exp rT} (hxRc : x ∉ (Γrc'.map (·.1)).toFinset)
    (hKe_lc : Ke.IsLocallyClosed) (hKe'_lc : Ke'.IsLocallyClosed)
    (Hbody : ⊢ bin_log_related_ty ⊤ Δ ((x, A) :: Γrc') Ke Ke' τ) :
    ∀ y, y ∉ (Γrc'.map (·.1)).toFinset ∪ {x} ∪ Ke.fv ∪ Ke'.fv →
      ⊢ bin_log_related_ty ⊤ Δ ((y, A) :: Γrc')
        (Exp.open' (Ke.close x) (.fvar y)) (Exp.open' (Ke'.close x) (.fvar y)) τ := by
  intro y hyNotL
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyNotL
  obtain ⟨⟨⟨hyNotRc, hyNotX⟩, hyNotFvKe⟩, hyNotFvKe'⟩ := hyNotL
  rw [Exp.open_close_subst_lc x y _ hKe_lc, Exp.open_close_subst_lc x y _ hKe'_lc]
  exact Hbody.trans (bin_log_related_ty_rename (Ne.symm hyNotX) hxRc hyNotRc hyNotFvKe hyNotFvKe')

omit [LawfulProbLangℝ rT] in
theorem close_fv_in_outer_dom {Γrc' : RelCtx rT GF} {x : Var} {Ke : Exp rT} {A : lrel rT GF}
    (hKe_fv : Ke.fv ⊆ (((x, A) :: Γrc').map (·.1)).toFinset) {z : Var}
    (hz : z ∈ (Ke.close x).fv) : z ∈ (Γrc'.map (·.1)).toFinset := by
  have hzKeDom := hKe_fv (Exp.close_fv_subset _ x hz)
  rw [RelCtx.dom_cons] at hzKeDom
  rcases Finset.mem_union.mp hzKeDom with hz_outer | hz_x
  · exact hz_outer
  · exact absurd (Finset.mem_singleton.mp hz_x ▸ hz) (Exp.close_var_not_fvar x Ke)

omit [LawfulProbLangℝ rT] in
theorem open_close_subst_lc_at {Ke : Exp rT} (x y : Var) (hKe_lc : Ke.IsLocallyClosed) :
    (Exp.open' (Ke.close x) (.fvar y)).IsLocallyClosed := by
  rw [Exp.open_close_subst_lc x y _ hKe_lc]
  exact Exp.subst_lc hKe_lc (Exp.IsLocallyClosed.fvar y)

theorem bin_log_related_lam_step {Δ : TyEnv rT GF} {Γrc' : RelCtx rT GF} {x : Var}
    {τ_arg τ_body : Ty} {Ke Ke' : Exp rT} (hxRc : x ∉ (Γrc'.map (·.1)).toFinset)
    (hKe_lc : Ke.IsLocallyClosed) (hKe'_lc : Ke'.IsLocallyClosed)
    (hKe_fv : Ke.fv ⊆ (((x, interp τ_arg Δ) :: Γrc').map (·.1)).toFinset)
    (hKe'_fv : Ke'.fv ⊆ (((x, interp τ_arg Δ) :: Γrc').map (·.1)).toFinset)
    (Hbody : ⊢ bin_log_related_ty ⊤ Δ ((x, interp τ_arg Δ) :: Γrc') Ke Ke' τ_body) :
    ⊢ bin_log_related_ty ⊤ Δ Γrc' (.lam (Ke.close x)) (.lam (Ke'.close x))
      (.arrow τ_arg τ_body) := by
  apply bin_log_related_lam _ _ ((Γrc'.map (·.1)).toFinset ∪ {x} ∪ Ke.fv ∪ Ke'.fv)
  · exact fun y _ => open_close_subst_lc_at x y hKe_lc
  · exact fun y _ => open_close_subst_lc_at x y hKe'_lc
  · exact fun _ => close_fv_in_outer_dom hKe_fv
  · exact fun _ => close_fv_in_outer_dom hKe'_fv
  exact bin_log_related_close_cofinite hxRc hKe_lc hKe'_lc Hbody

theorem bin_log_related_fix_step {Δ : TyEnv rT GF} {Γrc' : RelCtx rT GF} {f : Var}
    {τ1 τ2 : Ty} {Ke Ke' : Exp rT} (hfRc : f ∉ (Γrc'.map (·.1)).toFinset)
    (hKe_lc : Ke.IsLocallyClosed) (hKe'_lc : Ke'.IsLocallyClosed)
    (hKe_fv : Ke.fv ⊆ (((f, interp (.arrow τ1 τ2) Δ) :: Γrc').map (·.1)).toFinset)
    (hKe'_fv : Ke'.fv ⊆ (((f, interp (.arrow τ1 τ2) Δ) :: Γrc').map (·.1)).toFinset)
    (Hbody : ⊢ bin_log_related_ty ⊤ Δ ((f, interp (.arrow τ1 τ2) Δ) :: Γrc') Ke Ke'
      (.arrow τ1 τ2)) :
    ⊢ bin_log_related_ty ⊤ Δ Γrc' (.fix (Ke.close f)) (.fix (Ke'.close f))
      (.arrow τ1 τ2) := by
  apply bin_log_related_fix _ _ ((Γrc'.map (·.1)).toFinset ∪ {f} ∪ Ke.fv ∪ Ke'.fv)
  · exact fun y _ => open_close_subst_lc_at f y hKe_lc
  · exact fun y _ => open_close_subst_lc_at f y hKe'_lc
  · exact fun _ => close_fv_in_outer_dom hKe_fv
  · exact fun _ => close_fv_in_outer_dom hKe'_fv
  exact bin_log_related_close_cofinite hfRc hKe_lc hKe'_lc Hbody

theorem bin_log_related_under_typed_ctx {Γtc : Tctx} {e e' : Exp rT} {τ : Ty} {Γtc' : Tctx}
    {τ' : Ty} {K : Ctx rT} (HK : TypedCtx K Γtc τ Γtc' τ') (Hty_e : Typed Γtc e τ)
    (Hty_e' : Typed Γtc e' τ)
    (Hbinders : ∀ x ∈ Ctx.binderAtoms K, x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ Ctx.payloadFv K)
    (Hrel : ∀ (Δ : TyEnv rT GF) (Γrc : RelCtx rT GF), TctxRelated Δ Γtc Γrc →
      ⊢ bin_log_related_ty ⊤ Δ Γrc e e' τ) :
    ∀ (Δ : TyEnv rT GF) (Γrc' : RelCtx rT GF), TctxRelated Δ Γtc' Γrc' →
      Ctx.BindersFresh K (Γrc'.map (·.1)).toFinset →
      ⊢ bin_log_related_ty ⊤ Δ Γrc' (K.fill e) (K.fill e') τ' := by
  induction K generalizing Γtc' τ' with
  | nil =>
    intro Δ Γrc HCtx _
    cases HK
    exact Hrel Δ Γrc HCtx
  | cons k K' ih =>
    intro Δ Γrc' HCtx Hfresh
    cases HK with
    | @cons _ _ _ _ _ _ _ _ HKitem HKtail =>
    obtain ⟨HfreshHead, HfreshTail⟩ := Hfresh
    have HbindersK' := binders_tail Hbinders
    have IHinner := ih HKtail HbindersK' Δ
    have Hfr : Ctx.BindersFresh K' (Γrc'.map (·.1)).toFinset :=
      HfreshTail.mono Finset.subset_union_left
    have Fund := fun {e₀ : Exp rT} {τ₀ : Ty} (h : Typed Γtc' e₀ τ₀) => fundamental h Δ Γrc' HCtx
    have HtyK := TypedCtx.fill_typed Hty_e HKtail
      fun y hy => ⟨(HbindersK' y hy).1, (HbindersK' y hy).2.2⟩
    have HtyK' := TypedCtx.fill_typed Hty_e' HKtail
      fun y hy => ⟨(HbindersK' y hy).2.1, (HbindersK' y hy).2.2⟩
    simp only [Ctx.fill_cons, CtxItem.fill]
    cases HKitem with
    | appL Hty2 => iapply bin_log_related_app $$ %(IHinner Γrc' HCtx Hfr) %(Fund Hty2)
    | appR Hty1 => iapply bin_log_related_app $$ %(Fund Hty1) %(IHinner Γrc' HCtx Hfr)
    | pairL Hty2 => iapply bin_log_related_pair $$ %(IHinner Γrc' HCtx Hfr) %(Fund Hty2)
    | pairR Hty1 => iapply bin_log_related_pair $$ %(Fund Hty1) %(IHinner Γrc' HCtx Hfr)
    | fst => iapply bin_log_related_fst $$ %(IHinner Γrc' HCtx Hfr)
    | snd => iapply bin_log_related_snd $$ %(IHinner Γrc' HCtx Hfr)
    | inl => iapply bin_log_related_injl $$ %(IHinner Γrc' HCtx Hfr)
    | inr => iapply bin_log_related_injr $$ %(IHinner Γrc' HCtx Hfr)
    | caseL Hty1 Hty2 =>
      iapply bin_log_related_case $$ %(IHinner Γrc' HCtx Hfr) %(Fund Hty1) %(Fund Hty2)
    | caseM Hty0 Hty2 =>
      iapply bin_log_related_case $$ %(Fund Hty0) %(IHinner Γrc' HCtx Hfr) %(Fund Hty2)
    | caseR Hty0 Hty1 =>
      iapply bin_log_related_case $$ %(Fund Hty0) %(Fund Hty1) %(IHinner Γrc' HCtx Hfr)
    | ifL Hty1 Hty2 =>
      iapply bin_log_related_if $$ %(IHinner Γrc' HCtx Hfr) %(Fund Hty1) %(Fund Hty2)
    | ifM Hty0 Hty2 =>
      iapply bin_log_related_if $$ %(Fund Hty0) %(IHinner Γrc' HCtx Hfr) %(Fund Hty2)
    | ifR Hty0 Hty1 =>
      iapply bin_log_related_if $$ %(Fund Hty0) %(Fund Hty1) %(IHinner Γrc' HCtx Hfr)
    | alloc => iapply bin_log_related_alloc $$ %(IHinner Γrc' HCtx Hfr)
    | load => iapply bin_log_related_load $$ %(IHinner Γrc' HCtx Hfr)
    | storeL Hty2 => iapply bin_log_related_store $$ %(IHinner Γrc' HCtx Hfr) %(Fund Hty2)
    | storeR Hty1 => iapply bin_log_related_store $$ %(Fund Hty1) %(IHinner Γrc' HCtx Hfr)
    | allocTape => iapply bin_log_related_alloctape $$ %(IHinner Γrc' HCtx Hfr)
    | randL_unit Hty2 => iapply bin_log_related_rand_unit $$ %(IHinner Γrc' HCtx Hfr) %(Fund Hty2)
    | randL_tape Hty2 => iapply bin_log_related_rand_tape $$ %(IHinner Γrc' HCtx Hfr) %(Fund Hty2)
    | randR_unit Hty1 => iapply bin_log_related_rand_unit $$ %(Fund Hty1) %(IHinner Γrc' HCtx Hfr)
    | randR_tape Hty1 => iapply bin_log_related_rand_tape $$ %(Fund Hty1) %(IHinner Γrc' HCtx Hfr)
    | @unop_int _ op _ Hres =>
      iapply bin_log_related_int_unop Δ Γrc' op Hres $$ %(IHinner Γrc' HCtx Hfr)
    | @unop_real _ op _ Hres =>
      iapply bin_log_related_real_unop Δ Γrc' op Hres $$ %(IHinner Γrc' HCtx Hfr)
    | @binopL_real _ op _ _ Hty2 Hres =>
      iapply bin_log_related_real_binop Δ Γrc' op Hres $$ %(IHinner Γrc' HCtx Hfr) %(Fund Hty2)
    | @binopR_real _ op _ _ Hty1 Hres =>
      iapply bin_log_related_real_binop Δ Γrc' op Hres $$ %(Fund Hty1) %(IHinner Γrc' HCtx Hfr)
    | @unop_bool _ op _ Hres =>
      iapply bin_log_related_bool_unop Δ Γrc' op Hres $$ %(IHinner Γrc' HCtx Hfr)
    | @binopL_int _ op _ _ Hty2 Hres =>
      iapply bin_log_related_int_binop Δ Γrc' op Hres $$ %(IHinner Γrc' HCtx Hfr) %(Fund Hty2)
    | @binopR_int _ op _ _ Hty1 Hres =>
      iapply bin_log_related_int_binop Δ Γrc' op Hres $$ %(Fund Hty1) %(IHinner Γrc' HCtx Hfr)
    | @binopL_bool _ op _ _ Hty2 Hres =>
      iapply bin_log_related_bool_binop Δ Γrc' op Hres $$ %(IHinner Γrc' HCtx Hfr) %(Fund Hty2)
    | @binopR_bool _ op _ _ Hty1 Hres =>
      iapply bin_log_related_bool_binop Δ Γrc' op Hres $$ %(Fund Hty1) %(IHinner Γrc' HCtx Hfr)
    | binopL_unboxedEq Hub Hty2 =>
      iapply bin_log_related_unboxed_eq Δ Γrc' Hub $$ %(IHinner Γrc' HCtx Hfr) %(Fund Hty2)
    | binopR_unboxedEq Hub Hty1 =>
      iapply bin_log_related_unboxed_eq Δ Γrc' Hub $$ %(Fund Hty1) %(IHinner Γrc' HCtx Hfr)
    | fold => iapply bin_log_related_fold $$ %(IHinner Γrc' HCtx Hfr)
    | unfold => iapply bin_log_related_unfold $$ %(IHinner Γrc' HCtx Hfr)
    | tapp => iapply bin_log_related_tapp $$ %(IHinner Γrc' HCtx Hfr)
    | @lam _ x τ _ =>
      have hxRc : x ∉ (Γrc'.map (·.1)).toFinset := HfreshHead x (Finset.mem_singleton_self _)
      have HCtxInner : TctxRelated Δ (Γtc'.insert x τ) ((x, interp τ Δ) :: Γrc') :=
        HCtx.insert x τ (RelCtx.lookup_eq_none_of_not_mem hxRc)
      obtain ⟨hKfe_lc, hKfe_fv⟩ := ctx_fill_lc_fv HCtxInner HtyK
      obtain ⟨hKfe'_lc, hKfe'_fv⟩ := ctx_fill_lc_fv HCtxInner HtyK'
      exact bin_log_related_lam_step hxRc hKfe_lc hKfe'_lc hKfe_fv hKfe'_fv
        (IHinner _ HCtxInner (Ctx.BindersFresh.cons_extend rfl HfreshTail))
    | @fix _ f τ τ' =>
      have hfRc : f ∉ (Γrc'.map (·.1)).toFinset := HfreshHead f (Finset.mem_singleton_self _)
      have HCtxInner : TctxRelated Δ (Γtc'.insert f (.arrow τ τ'))
          ((f, interp (.arrow τ τ') Δ) :: Γrc') :=
        HCtx.insert f (.arrow τ τ') (RelCtx.lookup_eq_none_of_not_mem hfRc)
      obtain ⟨hKfe_lc, hKfe_fv⟩ := ctx_fill_lc_fv HCtxInner HtyK
      obtain ⟨hKfe'_lc, hKfe'_fv⟩ := ctx_fill_lc_fv HCtxInner HtyK'
      exact bin_log_related_fix_step hfRc hKfe_lc hKfe'_lc hKfe_fv hKfe'_fv
        (IHinner _ HCtxInner (Ctx.BindersFresh.cons_extend rfl HfreshTail))
    | tlam =>
      have HCtxShift := HCtx.shift (default : lrel rT GF)
      obtain ⟨hKfe_lc, hKfe_fv⟩ := ctx_fill_lc_fv HCtxShift HtyK
      obtain ⟨hKfe'_lc, hKfe'_fv⟩ := ctx_fill_lc_fv HCtxShift HtyK'
      refine bin_log_related_tlam Δ Γrc' hKfe_lc hKfe'_lc hKfe_fv hKfe'_fv fun A => ?_
      imodintro
      iapply ih HKtail HbindersK' (TyEnv.cons A Δ) Γrc' (HCtx.shift A) Hfr
    | @unpackL x e2 _ τ_pkg _ hxFvE2 Hty_e2 =>
      have hRen := fun y (hy : y ∉ insert x e2.fv) => Typed.rename_unpack hxFvE2 Hty_e2 y hy
      refine bin_log_related_unpack Δ Γrc' (insert x e2.fv ∪ (Γrc'.map (·.1)).toFinset)
        (IHinner Γrc' HCtx Hfr)
        (fun y hyL => (hRen y (hyL ∘ Finset.mem_union_left _)).isLocallyClosed)
        (fun y hyL => (hRen y (hyL ∘ Finset.mem_union_left _)).isLocallyClosed) fun A y hyL => ?_
      exact fundamental (hRen y (hyL ∘ Finset.mem_union_left _)) (TyEnv.cons A Δ) _
        ((HCtx.shift A).insert y τ_pkg
          (RelCtx.lookup_eq_none_of_not_mem (hyL ∘ Finset.mem_union_right _)))
    | @unpackR x e1 _ τ_pkg _ Hty_e1 =>
      have hxRc : x ∉ (Γrc'.map (·.1)).toFinset := HfreshHead x (Finset.mem_singleton_self _)
      refine bin_log_related_unpack Δ Γrc'
        ((Γrc'.map (·.1)).toFinset ∪ {x} ∪ (Ctx.fill K' e).fv ∪ (Ctx.fill K' e').fv)
        (Fund Hty_e1) ?_ ?_ ?_
      · exact fun y _ => Exp.open_close_isLocallyClosed x y HtyK.isLocallyClosed
      · exact fun y _ => Exp.open_close_isLocallyClosed x y HtyK'.isLocallyClosed
      intro A y hyL
      exact bin_log_related_close_cofinite hxRc HtyK.isLocallyClosed HtyK'.isLocallyClosed
        (ih HKtail HbindersK' (TyEnv.cons A Δ) _
          ((HCtx.shift A).insert x τ_pkg (RelCtx.lookup_eq_none_of_not_mem hxRc))
          (Ctx.BindersFresh.cons_extend rfl HfreshTail)) y hyL

end Soundness

section RefinesSound
open MeasureTheory
variable {rT : Type _} [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} [RefinesPreGS rT GF]

def boolEqVal (v v' : Val rT) : Prop :=
  ∃ b : Bool, v = .bool b ∧ v' = .bool b

omit [RefinesPreGS rT GF] in
theorem lrel_bool_to_boolEqVal [ApproxisRGS rT .hasNoLC GF] (v v' : Val rT) :
    ⊢@{IProp GF} lrel_bool.car v v' -∗ ⌜boolEqVal v v'⌝ := by
  iintro Hbool
  iunfold lrel_bool at Hbool
  icases Hbool with ⟨%b, %h⟩
  ipureintro
  exact ⟨b, h⟩

theorem refines_sound_open_fresh (Γtc : Tctx) (e e' : Exp rT) (τ : Ty) (Hty_e : Typed Γtc e τ)
    (Hty_e' : Typed Γtc e' τ)
    (Hlog : ∀ (_IR : ApproxisRGS rT .hasNoLC GF) (Δ : TyEnv rT GF) (Γrc : RelCtx rT GF),
      TctxRelated Δ Γtc Γrc → ⊢@{IProp GF} bin_log_related_ty (hlc := .hasNoLC) ⊤ Δ Γrc e e' τ) :
    ∀ (K : Ctx rT) (σ₀ : State rT) (b : Bool), TypedCtx K Γtc τ Tctx.empty .bool →
      Ctx.BindersFresh K ∅ → (∀ x ∈ Ctx.binderAtoms K, x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ Ctx.payloadFv K) →
      limExec ⟨K.fill e, σ₀⟩ (finalBool b) ≤ limExec ⟨K.fill e', σ₀⟩ (finalBool b) := by
  intro K σ₀ b Htyped HfreshK Hbinders
  have hRewriteFb : ∀ e0, limExec ⟨e0, σ₀⟩ (finalBool b) = limExecV ⟨e0, σ₀⟩ {pl(#(.bool b))} := by
    intro e0
    unfold limExecV asExpr
    rw [Measure.map_apply (by fun_prop) (MeasurableSet.singleton _)]
    rfl
  rw [hRewriteFb (K.fill e), hRewriteFb (K.fill e')]
  have hCpl : AddCoupl 0 (adequacyRel boolEqVal) (limExecV ⟨K.fill e, σ₀⟩)
      (limExecV ⟨K.fill e', σ₀⟩) := by
    apply refines_coupling (GF := GF) (A := fun _ => lrel_bool)
    · exact fun _ v v' => lrel_bool_to_boolEqVal v v'
    · intro IR
      have HrelClosed : ⊢@{IProp GF}
          bin_log_related_ty ⊤ (default : TyEnv rT GF) [] (K.fill e) (K.fill e') .bool :=
        bin_log_related_under_typed_ctx Htyped Hty_e Hty_e' Hbinders (Hlog IR) _ _
          TctxRelated.empty_nil HfreshK
      unfold bin_log_related_ty bin_log_related at HrelClosed
      show ⊢@{IProp GF} refines ⊤ (Exp.substMap (ValSubstMap.fst ([] : ValSubstMap rT)) (K.fill e))
        (Exp.substMap (ValSubstMap.snd ([] : ValSubstMap rT)) (K.fill e'))
        (interp Ty.bool (default : TyEnv rT GF))
      iapply HrelClosed $$ %([] : ValSubstMap rT)
      iapply env_ltyped2_empty
  apply hCpl.set_leq_zero (.singleton _) (.singleton _)
  rintro a b' ⟨v, v', hv, hv', b'', hvb1, hvb2⟩ ha
  have hv1 : v.1 = pl(#(.bool b'')) := congrArg Val.fst hvb1
  rw [show v.1 = pl(#(.bool b)) from (Exp.ofVal_of_toVal_some hv).trans ha] at hv1
  obtain rfl : b'' = b := by simpa using hv1.symm
  exact (Exp.ofVal_of_toVal_some hv').symm.trans (congrArg Val.fst hvb2)

theorem refines_sound_fresh (e e' : Exp rT) (τ : Ty) (Hty_e : Typed Tctx.empty e τ)
    (Hty_e' : Typed Tctx.empty e' τ)
    (Hlog : ∀ (_IR : ApproxisRGS rT .hasNoLC GF) (Δ : TyEnv rT GF),
      ⊢@{IProp GF} refines (hlc := .hasNoLC) ⊤ e e' (interp τ Δ)) :
    ∀ (K : Ctx rT) (σ₀ : State rT) (b : Bool), TypedCtx K Tctx.empty τ Tctx.empty .bool →
      Ctx.BindersFresh K ∅ → (∀ x ∈ Ctx.binderAtoms K, x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ Ctx.payloadFv K) →
      limExec ⟨K.fill e, σ₀⟩ (finalBool b) ≤ limExec ⟨K.fill e', σ₀⟩ (finalBool b) := by
  apply refines_sound_open_fresh (GF := GF) Tctx.empty e e' τ Hty_e Hty_e'
  intro IR Δ Γrc HCtx
  obtain rfl := HCtx.eq_nil_of_empty
  unfold bin_log_related_ty bin_log_related
  iintro %vs Hvs
  ihave ⟨%hvs_nil⟩ := env_ltyped2_empty_inv vs $$ Hvs
  rw [hvs_nil]
  iclear Hvs
  show ⊢@{IProp GF} refines ⊤ e e' (interp τ Δ)
  exact Hlog IR Δ

end RefinesSound

end ProbLang
