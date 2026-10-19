module

public import Metrology.Micrometer.PrimitiveLaws
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Micrometer.Model
public import Metrology.Micrometer.BinLogRelated
public import Metrology.Micrometer.Fundamental
public import Metrology.ProbLang.ContextualRefinement

/-! The semantic typing judgement under typed and linear contexts. -/

@[expose] public section

namespace ProbLang

open GradedLifting ProbLang.Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang
open ProbLang.MicrometerWpGS

section Syntax
variable {rT : Type} {GF : BundledGFunctors}

theorem RelCtx.dom_cons (x : Var) (A : lrel rT GF) (Γrc : RelCtx rT GF) :
    (((x, A) :: Γrc).map (·.1)).toFinset = (Γrc.map (·.1)).toFinset ∪ {x} := by
  simp [Finset.union_comm]

theorem close_fv_in_outer_dom {Γrc' : RelCtx rT GF} {x : Var} {Ke : Exp rT} {A : lrel rT GF}
    (hKe_fv : Ke.fv ⊆ (((x, A) :: Γrc').map (·.1)).toFinset) {z : Var}
    (hz : z ∈ (Ke.close x).fv) : z ∈ (Γrc'.map (·.1)).toFinset := by
  have hz' := hKe_fv (Exp.close_fv_subset _ x hz)
  rw [RelCtx.dom_cons] at hz'
  rcases Finset.mem_union.mp hz' with h | h
  · exact h
  · exact absurd (Finset.mem_singleton.mp h ▸ hz) (Exp.close_var_not_fvar x Ke)

theorem open_close_subst_lc_at {Ke : Exp rT} (x y : Var) (hKe_lc : Ke.IsLocallyClosed) :
    (Exp.open' (Ke.close x) (.fvar y)).IsLocallyClosed := by
  rw [Exp.open_close_subst_lc x y _ hKe_lc]
  exact Exp.subst_lc hKe_lc (Exp.IsLocallyClosed.fvar y)

end Syntax

section Soundness
variable {rT : Type} [LawfulProbLangℝ rT] {hlc : HasLC} {B : Type} [AddCommMonoid B]
  [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors}
  [MicrometerRGS rT hlc GF] [BudgetCreditGS B GF]

/-- The binders of each item of `K` avoid `S` and the binders of the items inside it. -/
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

section Bookkeeping

theorem TctxRelated.empty_nil {Δ : TyEnv rT GF} :
    TctxRelated L Δ Tctx.empty ([] : RelCtx rT GF) := by
  intro x; simp [Tctx.empty, RelCtx.lookup]

theorem TctxRelated.eq_nil_of_empty {Δ : TyEnv rT GF} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated L Δ Tctx.empty Γrc) : Γrc = [] := by
  cases Γrc with
  | nil => rfl
  | cons p rest =>
    have h := HCtx p.1
    simp only [Tctx.empty, RelCtx.lookup] at h
    split at h <;> simp at h

theorem ctx_fill_lc_fv {Γtc : Tctx} {Γrc : RelCtx rT GF} {Δ : TyEnv rT GF} {K : Ctx rT}
    {e : Exp rT} {τ : Ty} (HCtxRel : TctxRelated L Δ Γtc Γrc) (Hty : Typed Γtc (K.fill e) τ) :
    (K.fill e).IsLocallyClosed ∧ (K.fill e).fv ⊆ (Γrc.map (·.1)).toFinset :=
  ⟨Hty.isLocallyClosed, fv_subset_relCtxDom HCtxRel Hty⟩

theorem Ctx.BindersFresh.cons_extend {K' : Ctx rT} {Γrc : RelCtx rT GF} {x : Var}
    {A : lrel rT GF} {bAtoms : Finset Var} (hSingleton : bAtoms = {x})
    (h : Ctx.BindersFresh K' ((Γrc.map (·.1)).toFinset ∪ bAtoms)) :
    Ctx.BindersFresh K' (((x, A) :: Γrc).map (·.1)).toFinset :=
  RelCtx.dom_cons x A Γrc ▸ hSingleton ▸ h

theorem bin_log_related_close_cofinite {Δ : TyEnv rT GF} {Γrc' : RelCtx rT GF} {x : Var}
    {A : lrel rT GF} {τ : Ty} {Ke Ke' : Exp rT} (hxRc : x ∉ (Γrc'.map (·.1)).toFinset)
    (hKe_lc : Ke.IsLocallyClosed) (hKe'_lc : Ke'.IsLocallyClosed)
    (Hbody : ⊢ bin_log_related_ty L ⊤ Δ ((x, A) :: Γrc') Ke Ke' τ) :
    ∀ y, y ∉ (Γrc'.map (·.1)).toFinset ∪ {x} ∪ Ke.fv ∪ Ke'.fv →
      ⊢ bin_log_related_ty L ⊤ Δ ((y, A) :: Γrc')
        (Exp.open' (Ke.close x) (.fvar y)) (Exp.open' (Ke'.close x) (.fvar y)) τ := by
  intro y hy
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
  obtain ⟨⟨⟨hyRc, hyX⟩, hyKe⟩, hyKe'⟩ := hy
  rw [Exp.open_close_subst_lc x y _ hKe_lc, Exp.open_close_subst_lc x y _ hKe'_lc]
  exact Hbody.trans (bin_log_related_ty_rename (Ne.symm hyX) hxRc hyRc hyKe hyKe')

end Bookkeeping

section Steps
variable [L.IsLawful] [L.IsTopAbsorbing]

theorem bin_log_related_lam_step {Δ : TyEnv rT GF} {Γrc' : RelCtx rT GF} {x : Var}
    {τ_arg τ_body : Ty} {Ke Ke' : Exp rT} (hxRc : x ∉ (Γrc'.map (·.1)).toFinset)
    (hKe_lc : Ke.IsLocallyClosed) (hKe'_lc : Ke'.IsLocallyClosed)
    (hKe_fv : Ke.fv ⊆ (((x, interp L τ_arg Δ) :: Γrc').map (·.1)).toFinset)
    (hKe'_fv : Ke'.fv ⊆ (((x, interp L τ_arg Δ) :: Γrc').map (·.1)).toFinset)
    (Hbody : ⊢ bin_log_related_ty L ⊤ Δ ((x, interp L τ_arg Δ) :: Γrc') Ke Ke' τ_body) :
    ⊢ bin_log_related_ty L ⊤ Δ Γrc' (.lam (Ke.close x)) (.lam (Ke'.close x))
      (.arrow τ_arg τ_body) :=
  bin_log_related_lam _ _ _
    (fun y _ => open_close_subst_lc_at x y hKe_lc) (fun y _ => open_close_subst_lc_at x y hKe'_lc)
    (fun _ => close_fv_in_outer_dom hKe_fv) (fun _ => close_fv_in_outer_dom hKe'_fv)
    (bin_log_related_close_cofinite hxRc hKe_lc hKe'_lc Hbody)

theorem bin_log_related_fix_step {Δ : TyEnv rT GF} {Γrc' : RelCtx rT GF} {f : Var}
    {τ1 τ2 : Ty} {Ke Ke' : Exp rT} (hfRc : f ∉ (Γrc'.map (·.1)).toFinset)
    (hKe_lc : Ke.IsLocallyClosed) (hKe'_lc : Ke'.IsLocallyClosed)
    (hKe_fv : Ke.fv ⊆ (((f, interp L (.arrow τ1 τ2) Δ) :: Γrc').map (·.1)).toFinset)
    (hKe'_fv : Ke'.fv ⊆ (((f, interp L (.arrow τ1 τ2) Δ) :: Γrc').map (·.1)).toFinset)
    (Hbody : ⊢ bin_log_related_ty L ⊤ Δ ((f, interp L (.arrow τ1 τ2) Δ) :: Γrc') Ke Ke'
      (.arrow τ1 τ2)) :
    ⊢ bin_log_related_ty L ⊤ Δ Γrc' (.fix (Ke.close f)) (.fix (Ke'.close f))
      (.arrow τ1 τ2) :=
  bin_log_related_fix _ _ _
    (fun y _ => open_close_subst_lc_at f y hKe_lc) (fun y _ => open_close_subst_lc_at f y hKe'_lc)
    (fun _ => close_fv_in_outer_dom hKe_fv) (fun _ => close_fv_in_outer_dom hKe'_fv)
    (bin_log_related_close_cofinite hfRc hKe_lc hKe'_lc Hbody)

section Prim
variable [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] [L.HasBind]

theorem bin_log_related_under_typed_ctx {Γtc : Tctx} {e e' : Exp rT} {τ : Ty} {Γtc' : Tctx}
    {τ' : Ty} {K : Ctx rT} (HK : TypedCtx K Γtc τ Γtc' τ') (Hty_e : Typed Γtc e τ)
    (Hty_e' : Typed Γtc e' τ)
    (Hbinders : ∀ x ∈ Ctx.binderAtoms K, x ∉ e.fv ∧ x ∉ e'.fv ∧ x ∉ Ctx.payloadFv K)
    (Hrel : ∀ (Δ : TyEnv rT GF) (Γrc : RelCtx rT GF), TctxRelated L Δ Γtc Γrc →
      ⊢ bin_log_related_ty L ⊤ Δ Γrc e e' τ) :
    ∀ (Δ : TyEnv rT GF) (Γrc' : RelCtx rT GF), TctxRelated L Δ Γtc' Γrc' →
      Ctx.BindersFresh K (Γrc'.map (·.1)).toFinset →
      ⊢ bin_log_related_ty L ⊤ Δ Γrc' (K.fill e) (K.fill e') τ' := by
  induction K generalizing Γtc' τ' with
  | nil =>
    intro Δ Γrc HCtx _
    cases HK
    exact Hrel Δ Γrc HCtx
  | cons k K' ih =>
    intro Δ Γrc' HCtx ⟨HfreshHead, HfreshTail⟩
    cases HK with | cons HKitem HKtail =>
    have HbindersK' := binders_tail Hbinders
    have IHinner := ih HKtail HbindersK' Δ
    have Hfr := HfreshTail.mono Finset.subset_union_left
    have Fund := fun {e₀ : Exp rT} {τ₀ : Ty} (h : Typed Γtc' e₀ τ₀) => fundamental L h Δ Γrc' HCtx
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
      have hxRc := HfreshHead x (Finset.mem_singleton_self _)
      have HCtxInner := HCtx.insert x τ (RelCtx.lookup_eq_none_of_not_mem hxRc)
      obtain ⟨hKfe_lc, hKfe_fv⟩ := ctx_fill_lc_fv HCtxInner HtyK
      obtain ⟨hKfe'_lc, hKfe'_fv⟩ := ctx_fill_lc_fv HCtxInner HtyK'
      exact bin_log_related_lam_step hxRc hKfe_lc hKfe'_lc hKfe_fv hKfe'_fv
        (IHinner _ HCtxInner (Ctx.BindersFresh.cons_extend rfl HfreshTail))
    | @fix _ f τ τ' =>
      have hfRc := HfreshHead f (Finset.mem_singleton_self _)
      have HCtxInner := HCtx.insert f (.arrow τ τ') (RelCtx.lookup_eq_none_of_not_mem hfRc)
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
      have hRen := fun y (hy : y ∉ insert x e2.fv ∪ (Γrc'.map (·.1)).toFinset) =>
        Typed.rename_unpack hxFvE2 Hty_e2 y (hy ∘ Finset.mem_union_left _)
      refine bin_log_related_unpack Δ Γrc' _ (IHinner Γrc' HCtx Hfr)
        (fun y hy => (hRen y hy).isLocallyClosed) (fun y hy => (hRen y hy).isLocallyClosed)
        fun A y hy => ?_
      exact fundamental L (hRen y hy) (TyEnv.cons A Δ) _
        ((HCtx.shift A).insert y τ_pkg
          (RelCtx.lookup_eq_none_of_not_mem (hy ∘ Finset.mem_union_right _)))
    | @unpackR x e1 _ τ_pkg _ Hty_e1 =>
      have hxRc := HfreshHead x (Finset.mem_singleton_self _)
      refine bin_log_related_unpack Δ Γrc'
        ((Γrc'.map (·.1)).toFinset ∪ {x} ∪ (Ctx.fill K' e).fv ∪ (Ctx.fill K' e').fv)
        (Fund Hty_e1)
        (fun y _ => Exp.open_close_isLocallyClosed x y HtyK.isLocallyClosed)
        (fun y _ => Exp.open_close_isLocallyClosed x y HtyK'.isLocallyClosed) fun A y hy => ?_
      exact bin_log_related_close_cofinite hxRc HtyK.isLocallyClosed HtyK'.isLocallyClosed
        (ih HKtail HbindersK' (TyEnv.cons A Δ) _
          ((HCtx.shift A).insert x τ_pkg (RelCtx.lookup_eq_none_of_not_mem hxRc))
          (Ctx.BindersFresh.cons_extend rfl HfreshTail)) y hy

/-- The item runs its hole at most once: it does not put the hole under a binder. -/
def CtxItem.IsLinear : CtxItem rT → Prop
  | .lam _ | .fix _ | .tlam | .unpackR _ _ => False
  | _ => True

/-- Every item of `K` runs its hole at most once, so `K` may consume a non-duplicable frame. -/
def Ctx.IsLinear : Ctx rT → Prop
  | [] => True
  | k :: K' => k.IsLinear ∧ Ctx.IsLinear K'

set_option hygiene false in
/-- Specialize the induction hypothesis of `bin_log_related_under_linear_ctx` to the frame. -/
local macro "ih_frame" : tactic => `(tactic| ihave H := ih HKtail Hlin.2 Δ Γrc' HCtx $$ HP)

/-- `bin_log_related_under_typed_ctx` under a frame `P` such as budget credits, for contexts
that run the hole at most once (the context's own steps are budget-free). -/
theorem bin_log_related_under_linear_ctx {P : IProp GF} {Γtc : Tctx} {e e' : Exp rT} {τ : Ty}
    {Γtc' : Tctx} {τ' : Ty} {K : Ctx rT} (HK : TypedCtx K Γtc τ Γtc' τ') (Hlin : K.IsLinear)
    (Hrel : ∀ (Δ : TyEnv rT GF) (Γrc : RelCtx rT GF), TctxRelated L Δ Γtc Γrc →
      ⊢ P -∗ bin_log_related_ty L ⊤ Δ Γrc e e' τ) :
    ∀ (Δ : TyEnv rT GF) (Γrc' : RelCtx rT GF), TctxRelated L Δ Γtc' Γrc' →
      ⊢ P -∗ bin_log_related_ty L ⊤ Δ Γrc' (K.fill e) (K.fill e') τ' := by
  induction K generalizing Γtc' τ' with
  | nil =>
    intro Δ Γrc HCtx
    cases HK
    exact Hrel Δ Γrc HCtx
  | cons k K' ih =>
    intro Δ Γrc' HCtx
    cases HK with | cons HKitem HKtail =>
    have Fund := fun {e₀ : Exp rT} {τ₀ : Ty} (h : Typed Γtc' e₀ τ₀) => fundamental L h Δ Γrc' HCtx
    simp only [Ctx.fill_cons, CtxItem.fill]
    iintro HP
    cases HKitem with
    | lam | fix | tlam | unpackR => exact (Hlin.1 : False).elim
    | appL Hty2 => ih_frame; iapply bin_log_related_app $$ H %(Fund Hty2)
    | appR Hty1 => ih_frame; iapply bin_log_related_app $$ %(Fund Hty1) H
    | pairL Hty2 => ih_frame; iapply bin_log_related_pair $$ H %(Fund Hty2)
    | pairR Hty1 => ih_frame; iapply bin_log_related_pair $$ %(Fund Hty1) H
    | fst => ih_frame; iapply bin_log_related_fst $$ H
    | snd => ih_frame; iapply bin_log_related_snd $$ H
    | inl => ih_frame; iapply bin_log_related_injl $$ H
    | inr => ih_frame; iapply bin_log_related_injr $$ H
    | caseL Hty1 Hty2 => ih_frame; iapply bin_log_related_case $$ H %(Fund Hty1) %(Fund Hty2)
    | caseM Hty0 Hty2 => ih_frame; iapply bin_log_related_case $$ %(Fund Hty0) H %(Fund Hty2)
    | caseR Hty0 Hty1 => ih_frame; iapply bin_log_related_case $$ %(Fund Hty0) %(Fund Hty1) H
    | ifL Hty1 Hty2 => ih_frame; iapply bin_log_related_if $$ H %(Fund Hty1) %(Fund Hty2)
    | ifM Hty0 Hty2 => ih_frame; iapply bin_log_related_if $$ %(Fund Hty0) H %(Fund Hty2)
    | ifR Hty0 Hty1 => ih_frame; iapply bin_log_related_if $$ %(Fund Hty0) %(Fund Hty1) H
    | alloc => ih_frame; iapply bin_log_related_alloc $$ H
    | load => ih_frame; iapply bin_log_related_load $$ H
    | storeL Hty2 => ih_frame; iapply bin_log_related_store $$ H %(Fund Hty2)
    | storeR Hty1 => ih_frame; iapply bin_log_related_store $$ %(Fund Hty1) H
    | allocTape => ih_frame; iapply bin_log_related_alloctape $$ H
    | randL_unit Hty2 => ih_frame; iapply bin_log_related_rand_unit $$ H %(Fund Hty2)
    | randL_tape Hty2 => ih_frame; iapply bin_log_related_rand_tape $$ H %(Fund Hty2)
    | randR_unit Hty1 => ih_frame; iapply bin_log_related_rand_unit $$ %(Fund Hty1) H
    | randR_tape Hty1 => ih_frame; iapply bin_log_related_rand_tape $$ %(Fund Hty1) H
    | @unop_int _ op _ Hres => ih_frame; iapply bin_log_related_int_unop Δ Γrc' op Hres $$ H
    | @unop_real _ op _ Hres => ih_frame; iapply bin_log_related_real_unop Δ Γrc' op Hres $$ H
    | @unop_bool _ op _ Hres => ih_frame; iapply bin_log_related_bool_unop Δ Γrc' op Hres $$ H
    | @binopL_real _ op _ _ Hty2 Hres =>
      ih_frame
      iapply bin_log_related_real_binop Δ Γrc' op Hres $$ H %(Fund Hty2)
    | @binopR_real _ op _ _ Hty1 Hres =>
      ih_frame
      iapply bin_log_related_real_binop Δ Γrc' op Hres $$ %(Fund Hty1) H
    | @binopL_int _ op _ _ Hty2 Hres =>
      ih_frame
      iapply bin_log_related_int_binop Δ Γrc' op Hres $$ H %(Fund Hty2)
    | @binopR_int _ op _ _ Hty1 Hres =>
      ih_frame
      iapply bin_log_related_int_binop Δ Γrc' op Hres $$ %(Fund Hty1) H
    | @binopL_bool _ op _ _ Hty2 Hres =>
      ih_frame
      iapply bin_log_related_bool_binop Δ Γrc' op Hres $$ H %(Fund Hty2)
    | @binopR_bool _ op _ _ Hty1 Hres =>
      ih_frame
      iapply bin_log_related_bool_binop Δ Γrc' op Hres $$ %(Fund Hty1) H
    | binopL_unboxedEq Hub Hty2 =>
      ih_frame
      iapply bin_log_related_unboxed_eq Δ Γrc' Hub $$ H %(Fund Hty2)
    | binopR_unboxedEq Hub Hty1 =>
      ih_frame
      iapply bin_log_related_unboxed_eq Δ Γrc' Hub $$ %(Fund Hty1) H
    | fold => ih_frame; iapply bin_log_related_fold $$ H
    | unfold => ih_frame; iapply bin_log_related_unfold $$ H
    | tapp => ih_frame; iapply bin_log_related_tapp $$ H
    | @unpackL x e2 _ τ_pkg _ hxFvE2 Hty_e2 =>
      ih_frame
      have hRen := fun y (hy : y ∉ insert x e2.fv ∪ (Γrc'.map (·.1)).toFinset) =>
        Typed.rename_unpack hxFvE2 Hty_e2 y (hy ∘ Finset.mem_union_left _)
      iapply bin_log_related_unpack_wand Δ Γrc' _
        (fun y hy => (hRen y hy).isLocallyClosed) (fun y hy => (hRen y hy).isLocallyClosed)
        (fun A y hy => fundamental L (hRen y hy) (TyEnv.cons A Δ) _
          ((HCtx.shift A).insert y τ_pkg
            (RelCtx.lookup_eq_none_of_not_mem (hy ∘ Finset.mem_union_right _)))) $$ H

end Prim

end Steps

end Soundness

end ProbLang
