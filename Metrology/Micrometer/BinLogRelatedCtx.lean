module

public import Metrology.Micrometer.PrimitiveLaws
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI
public import Metrology.Micrometer.Model
public import Metrology.Micrometer.BinLogRelated
public import Metrology.Micrometer.Fundamental
public import Metrology.ProbLang.ContextualRefinement

/-! # Plugging into a context

From `e ≤log e'` to `K[e] ≤log K[e']` for a typed context `K` (`bin_log_related_under_typed_ctx`),
and under a resource `P` such as budget credits when `K.IsLinear`. -/

@[expose] public section

namespace ProbLang
open GradedLifting Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE
open MicrometerWpGS
open Exp Finset RelCtx Ctx Typed TypedCtx

variable {rT : Type} {GF : BundledGFunctors}

/-! ## Closing a binder over a hole -/

/-- Consing a binding adds its variable to the domain of a relational context. -/
theorem RelCtx.dom_cons (x : Var) (A : lrel rT GF) (Γrc : RelCtx rT GF) :
    (((x, A) :: Γrc).map (·.1)).toFinset = (Γrc.map (·.1)).toFinset ∪ {x} := by
  simp [union_comm]

/-- Closing `x` in a term with free variables in `x :: Γrc'` leaves them in `Γrc'`. -/
theorem close_fv_in_outer_dom {Ke : Exp rT} {Γrc' : RelCtx rT GF} {x : Var} {A : lrel rT GF}
    (hKe_fv : Ke.fv ⊆ (((x, A) :: Γrc').map (·.1)).toFinset) {z : Var}
    (hz : z ∈ (Ke.close x).fv) : z ∈ (Γrc'.map (·.1)).toFinset := by
  have hz' := hKe_fv (close_fv_subset _ x hz)
  rw [dom_cons] at hz'
  rcases mem_union.mp hz' with h | h
  · exact h
  · exact absurd (mem_singleton.mp h ▸ hz) (close_var_not_fvar x Ke)

section CtxLemmas
variable [MeasurableSpace rT] [LawfulProbLangℝ rT] {hlc : HasLC} {B : Type} [AddCommMonoid B]
  [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B} [MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF]
variable {Δ : TyEnv rT GF} {Γrc Γrc' : RelCtx rT GF} {x : Var} {A : lrel rT GF} {Ke Ke' : Exp rT}
  {τ : Ty}
local bi IProp GF

/-! ## Binder freshness -/

/-- The binders of each item of `K` avoid `S` and the binders of the items enclosing it. -/
def Ctx.BindersFresh : Ctx rT → Finset Var → Prop
  | [], _ => True
  | k :: K', S =>
    (∀ x ∈ k.binderAtoms, x ∉ S) ∧ BindersFresh K' (S ∪ k.binderAtoms)

/-- `Ctx.BindersFresh` is antitone in the set to avoid. -/
theorem Ctx.BindersFresh.mono {K : Ctx rT} {S T : Finset Var} (hST : S ⊆ T)
    (h : BindersFresh K T) : BindersFresh K S := by
  induction K generalizing S T with
  | nil => trivial
  | cons k K' ih =>
    exact ⟨fun y hy hyS => h.1 y hy (hST hyS),
      ih (union_subset_union hST Subset.rfl) h.2⟩

/-! ## Bookkeeping for binder frames -/

/-- The empty typing context is related to the empty relational context. -/
theorem TctxRelated.empty_nil : TctxRelated L Δ .empty ([] : RelCtx rT GF) := by
  intro x; simp [Tctx.empty, lookup]

/-- A relational context related to the empty typing context is empty. -/
theorem TctxRelated.eq_nil_of_empty (HCtx : TctxRelated L Δ .empty Γrc) : Γrc = [] := by
  cases Γrc with
  | nil => rfl
  | cons p rest =>
    have h := HCtx p.1
    simp only [Tctx.empty, lookup] at h
    split at h <;> simp at h

/-- Binder freshness for a context transfers when a singleton binder `x` is added to the domain. -/
theorem Ctx.BindersFresh.cons_extend {K' : Ctx rT}
    (h : BindersFresh K' ((Γrc.map (·.1)).toFinset ∪ {x})) :
    BindersFresh K' (((x, A) :: Γrc).map (·.1)).toFinset :=
  dom_cons x A Γrc ▸ h

/-- A body related at the binder `x` is related at every fresh `y` after `close x`, `open y`. -/
theorem bin_log_related_close_cofinite (hxRc : x ∉ (Γrc'.map (·.1)).toFinset)
    (hKe_lc : Ke.IsLocallyClosed) (hKe'_lc : Ke'.IsLocallyClosed)
    (Hbody : ⊢ bin_log_related_ty L ⊤ Δ ((x, A) :: Γrc') Ke Ke' τ) :
    ∀ y, y ∉ (Γrc'.map (·.1)).toFinset ∪ {x} ∪ Ke.fv ∪ Ke'.fv →
      ⊢ bin_log_related_ty L ⊤ Δ ((y, A) :: Γrc')
        (open' (Ke.close x) (.fvar y)) (open' (Ke'.close x) (.fvar y)) τ := by
  intro y hy
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
  obtain ⟨⟨⟨hyRc, hyX⟩, hyKe⟩, hyKe'⟩ := hy
  rw [open_close_subst_lc x y _ hKe_lc, open_close_subst_lc x y _ hKe'_lc]
  exact Hbody.trans (bin_log_related_ty_rename (Ne.symm hyX) hxRc hyRc hyKe hyKe')

/-! ## Compatibility at `lam` and `fix` frames -/

section Steps
variable [L.IsLawful] [L.IsTopAbsorbing]

/-- `bin_log_related_lam` for a context frame `.lam (close x Ke)`. -/
theorem bin_log_related_lam_step {τ_arg τ_body : Ty} (hxRc : x ∉ (Γrc'.map (·.1)).toFinset)
    (hKe_lc : Ke.IsLocallyClosed) (hKe'_lc : Ke'.IsLocallyClosed)
    (hKe_fv : Ke.fv ⊆ (((x, interp L τ_arg Δ) :: Γrc').map (·.1)).toFinset)
    (hKe'_fv : Ke'.fv ⊆ (((x, interp L τ_arg Δ) :: Γrc').map (·.1)).toFinset)
    (Hbody : ⊢ bin_log_related_ty L ⊤ Δ ((x, interp L τ_arg Δ) :: Γrc') Ke Ke' τ_body) :
    ⊢ bin_log_related_ty L ⊤ Δ Γrc' (.lam (Ke.close x)) (.lam (Ke'.close x))
      (.arrow τ_arg τ_body) :=
  bin_log_related_lam _ _ _ (fun y _ => open_close_isLocallyClosed x y hKe_lc)
    (fun y _ => open_close_isLocallyClosed x y hKe'_lc)
    (fun _ => close_fv_in_outer_dom hKe_fv) (fun _ => close_fv_in_outer_dom hKe'_fv)
    (bin_log_related_close_cofinite hxRc hKe_lc hKe'_lc Hbody)

/-- `bin_log_related_fix` for a context frame `.fix (close f Ke)`. -/
theorem bin_log_related_fix_step {f : Var} {τ1 τ2 : Ty} (hfRc : f ∉ (Γrc'.map (·.1)).toFinset)
    (hKe_lc : Ke.IsLocallyClosed) (hKe'_lc : Ke'.IsLocallyClosed)
    (hKe_fv : Ke.fv ⊆ (((f, interp L (.arrow τ1 τ2) Δ) :: Γrc').map (·.1)).toFinset)
    (hKe'_fv : Ke'.fv ⊆ (((f, interp L (.arrow τ1 τ2) Δ) :: Γrc').map (·.1)).toFinset)
    (Hbody : ⊢ bin_log_related_ty L ⊤ Δ ((f, interp L (.arrow τ1 τ2) Δ) :: Γrc') Ke Ke'
      (.arrow τ1 τ2)) :
    ⊢ bin_log_related_ty L ⊤ Δ Γrc' (.fix (Ke.close f)) (.fix (Ke'.close f)) (.arrow τ1 τ2) :=
  bin_log_related_fix _ _ _ (fun y _ => open_close_isLocallyClosed f y hKe_lc)
    (fun y _ => open_close_isLocallyClosed f y hKe'_lc)
    (fun _ => close_fv_in_outer_dom hKe_fv) (fun _ => close_fv_in_outer_dom hKe'_fv)
    (bin_log_related_close_cofinite hfRc hKe_lc hKe'_lc Hbody)

section Prim
variable [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] [L.HasBind]

/-! ## Typed contexts -/

variable {Γtc : Tctx} {e e' : Exp rT} {K : Ctx rT}

/-- The frame does not put its hole inside a binder body. -/
def CtxItem.IsLinear : CtxItem rT → Prop
  | .lam _ | .fix _ | .tlam | .unpackR _ _ => False
  | _ => True

/-- Every frame of `K` is linear, so `K` may use a non-duplicable resource for its hole. -/
def Ctx.IsLinear : Ctx rT → Prop
  | [] => True
  | k :: K' => k.IsLinear ∧ IsLinear K'

/-- A linear frame leaves the typing context unchanged. -/
theorem TypedCtxItem.ctx_eq_of_isLinear {k : CtxItem rT} {Γ₁ Γ₂ : Tctx} {τ₁ τ₂ : Ty}
    (HKitem : TypedCtxItem k Γ₁ τ₁ Γ₂ τ₂) (Hlin : k.IsLinear) : Γ₁ = Γ₂ := by
  cases HKitem <;> first | rfl | exact (Hlin : False).elim

/-- A linear frame preserves `≤log`. -/
theorem bin_log_related_ctxItem_linear {k : CtxItem rT} {Γ₁ Γ : Tctx} {τ₁ τ₂ : Ty}
    {Δ : TyEnv rT GF} {Γrc : RelCtx rT GF} {Ke Ke' : Exp rT} (HKitem : TypedCtxItem k Γ₁ τ₁ Γ τ₂)
    (Hlin : k.IsLinear) (HCtx : TctxRelated L Δ Γ Γrc) :
    bin_log_related_ty L ⊤ Δ Γrc Ke Ke' τ₁ ⊢
      bin_log_related_ty L ⊤ Δ Γrc (k.fill Ke) (k.fill Ke') τ₂ := by
  have Fund := fun {e₀ : Exp rT} {τ₀ : Ty} (h : Typed Γ e₀ τ₀) => fundamental L h Δ Γrc HCtx
  simp only [CtxItem.fill]
  iintro H
  cases HKitem with
  | lam | fix | tlam | unpackR => exact (Hlin : False).elim
  | appL Hty2 => iapply bin_log_related_app $$ H %(Fund Hty2)
  | appR Hty1 => iapply bin_log_related_app $$ %(Fund Hty1) H
  | pairL Hty2 => iapply bin_log_related_pair $$ H %(Fund Hty2)
  | pairR Hty1 => iapply bin_log_related_pair $$ %(Fund Hty1) H
  | fst => iapply bin_log_related_fst $$ H
  | snd => iapply bin_log_related_snd $$ H
  | inl => iapply bin_log_related_injl $$ H
  | inr => iapply bin_log_related_injr $$ H
  | caseL Hty1 Hty2 => iapply bin_log_related_case $$ H %(Fund Hty1) %(Fund Hty2)
  | caseM Hty0 Hty2 => iapply bin_log_related_case $$ %(Fund Hty0) H %(Fund Hty2)
  | caseR Hty0 Hty1 => iapply bin_log_related_case $$ %(Fund Hty0) %(Fund Hty1) H
  | ifL Hty1 Hty2 => iapply bin_log_related_if $$ H %(Fund Hty1) %(Fund Hty2)
  | ifM Hty0 Hty2 => iapply bin_log_related_if $$ %(Fund Hty0) H %(Fund Hty2)
  | ifR Hty0 Hty1 => iapply bin_log_related_if $$ %(Fund Hty0) %(Fund Hty1) H
  | alloc => iapply bin_log_related_alloc $$ H
  | load => iapply bin_log_related_load $$ H
  | storeL Hty2 => iapply bin_log_related_store $$ H %(Fund Hty2)
  | storeR Hty1 => iapply bin_log_related_store $$ %(Fund Hty1) H
  | allocTape => iapply bin_log_related_alloctape $$ H
  | randL_unit Hty2 => iapply bin_log_related_rand_unit $$ H %(Fund Hty2)
  | randL_tape Hty2 => iapply bin_log_related_rand_tape $$ H %(Fund Hty2)
  | randR_unit Hty1 => iapply bin_log_related_rand_unit $$ %(Fund Hty1) H
  | randR_tape Hty1 => iapply bin_log_related_rand_tape $$ %(Fund Hty1) H
  | @unop_int _ op _ Hres => iapply bin_log_related_int_unop Δ Γrc op Hres $$ H
  | @unop_real _ op _ Hres => iapply bin_log_related_real_unop Δ Γrc op Hres $$ H
  | @unop_bool _ op _ Hres => iapply bin_log_related_bool_unop Δ Γrc op Hres $$ H
  | @binopL_real _ op _ _ Hty2 Hres =>
    iapply bin_log_related_real_binop Δ Γrc op Hres $$ H %(Fund Hty2)
  | @binopR_real _ op _ _ Hty1 Hres =>
    iapply bin_log_related_real_binop Δ Γrc op Hres $$ %(Fund Hty1) H
  | @binopL_int _ op _ _ Hty2 Hres =>
    iapply bin_log_related_int_binop Δ Γrc op Hres $$ H %(Fund Hty2)
  | @binopR_int _ op _ _ Hty1 Hres =>
    iapply bin_log_related_int_binop Δ Γrc op Hres $$ %(Fund Hty1) H
  | @binopL_bool _ op _ _ Hty2 Hres =>
    iapply bin_log_related_bool_binop Δ Γrc op Hres $$ H %(Fund Hty2)
  | @binopR_bool _ op _ _ Hty1 Hres =>
    iapply bin_log_related_bool_binop Δ Γrc op Hres $$ %(Fund Hty1) H
  | binopL_unboxedEq Hub Hty2 => iapply bin_log_related_unboxed_eq Δ Γrc Hub $$ H %(Fund Hty2)
  | binopR_unboxedEq Hub Hty1 => iapply bin_log_related_unboxed_eq Δ Γrc Hub $$ %(Fund Hty1) H
  | fold => iapply bin_log_related_fold $$ H
  | unfold => iapply bin_log_related_unfold $$ H
  | tapp => iapply bin_log_related_tapp $$ H
  | @unpackL x e2 _ τ_pkg _ Hty_e2 =>
    have hRen := fun y (hy : y ∉ insert x e2.fv ∪ (Γrc.map (·.1)).toFinset) =>
      rename_unpack Hty_e2 y (hy ∘ mem_union_left _)
    iapply bin_log_related_unpack_wand Δ Γrc _
      (fun y hy => (hRen y hy).isLocallyClosed) (fun y hy => (hRen y hy).isLocallyClosed)
      (fun A y hy => fundamental L (hRen y hy) (.cons A Δ) _
        ((HCtx.shift A).insert y τ_pkg (lookup_eq_none_of_notMem (hy ∘ mem_union_right _)))) $$ H

/-- From `e ≤log e'` at `τ` under `Γtc`, `K[e] ≤log K[e']` at `τ'` for a typed context `K` whose
binders are fresh for the relational context. -/
theorem bin_log_related_under_typed_ctx {Γtc' : Tctx} {τ' : Ty} (HK : TypedCtx K Γtc τ Γtc' τ')
    (Hty_e : Typed Γtc e τ) (Hty_e' : Typed Γtc e' τ)
    (Hrel : ∀ (Δ : TyEnv rT GF) (Γrc : RelCtx rT GF), TctxRelated L Δ Γtc Γrc →
      ⊢ bin_log_related_ty L ⊤ Δ Γrc e e' τ) :
    ∀ (Δ : TyEnv rT GF) (Γrc' : RelCtx rT GF), TctxRelated L Δ Γtc' Γrc' →
      BindersFresh K (Γrc'.map (·.1)).toFinset →
      ⊢ bin_log_related_ty L ⊤ Δ Γrc' (K.fill e) (K.fill e') τ' := by
  induction K generalizing Γtc' τ' with
  | nil =>
    intro Δ Γrc HCtx _
    cases HK
    exact Hrel Δ Γrc HCtx
  | cons k K' ih =>
    intro Δ Γrc' HCtx ⟨HfreshHead, HfreshTail⟩
    cases HK with | cons HKitem HKtail =>
    have IHinner := ih HKtail Δ
    have Hfr := HfreshTail.mono subset_union_left
    -- linear frames are handled by `bin_log_related_ctxItem_linear`
    by_cases Hlin : k.IsLinear
    · obtain rfl := HKitem.ctx_eq_of_isLinear Hlin
      exact (IHinner Γrc' HCtx Hfr).trans (bin_log_related_ctxItem_linear HKitem Hlin HCtx)
    have HtyK := fill_typed Hty_e HKtail
    have HtyK' := fill_typed Hty_e' HKtail
    simp only [fill_cons]
    -- binder frames: the hole sits under a fresh variable added to the relational context
    cases HKitem with
    | @lam _ x τ _ =>
      have hxRc := HfreshHead x (mem_singleton_self _)
      have HCtxInner := HCtx.insert x τ (lookup_eq_none_of_notMem hxRc)
      exact bin_log_related_lam_step hxRc HtyK.isLocallyClosed HtyK'.isLocallyClosed
        (fv_subset_relCtxDom HCtxInner HtyK) (fv_subset_relCtxDom HCtxInner HtyK')
        (IHinner _ HCtxInner (.cons_extend HfreshTail))
    | @fix _ f τ τ' =>
      have hfRc := HfreshHead f (mem_singleton_self _)
      have HCtxInner := HCtx.insert f (.arrow τ τ') (lookup_eq_none_of_notMem hfRc)
      exact bin_log_related_fix_step hfRc HtyK.isLocallyClosed HtyK'.isLocallyClosed
        (fv_subset_relCtxDom HCtxInner HtyK) (fv_subset_relCtxDom HCtxInner HtyK')
        (IHinner _ HCtxInner (.cons_extend HfreshTail))
    | tlam =>
      -- type binders extend `Δ`
      have HCtxShift := HCtx.shift default
      refine bin_log_related_tlam Δ Γrc' HtyK.isLocallyClosed HtyK'.isLocallyClosed
        (fv_subset_relCtxDom HCtxShift HtyK) (fv_subset_relCtxDom HCtxShift HtyK') fun A => ?_
      imodintro
      iapply ih HKtail (.cons A Δ) Γrc' (HCtx.shift A) Hfr
    | @unpackR x e1 _ τ_pkg _ Hty_e1 =>
      have hxRc := HfreshHead x (mem_singleton_self _)
      refine bin_log_related_unpack Δ Γrc'
        ((Γrc'.map (·.1)).toFinset ∪ {x} ∪ (fill K' e).fv ∪ (fill K' e').fv)
        (fundamental L Hty_e1 Δ Γrc' HCtx)
        (fun y _ => open_close_isLocallyClosed x y HtyK.isLocallyClosed)
        (fun y _ => open_close_isLocallyClosed x y HtyK'.isLocallyClosed) fun A y hy => ?_
      exact bin_log_related_close_cofinite hxRc HtyK.isLocallyClosed HtyK'.isLocallyClosed
        (ih HKtail (.cons A Δ) _
          ((HCtx.shift A).insert x τ_pkg (lookup_eq_none_of_notMem hxRc))
          (.cons_extend HfreshTail)) y hy
    | _ => exact (Hlin trivial).elim  -- the remaining frames are linear

/-- `bin_log_related_under_typed_ctx` for a hypothesis under a resource `P`, for linear contexts
and with no freshness hypotheses. -/
theorem bin_log_related_under_linear_ctx {P} {Γtc' : Tctx} {τ' : Ty}
    (HK : TypedCtx K Γtc τ Γtc' τ') (Hlin : K.IsLinear)
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
    obtain rfl := HKitem.ctx_eq_of_isLinear Hlin.1
    rw [fill_cons, fill_cons]
    iintro HP
    ihave H := ih HKtail Hlin.2 Δ Γrc' HCtx $$ HP
    iapply bin_log_related_ctxItem_linear HKitem Hlin.1 HCtx $$ H

end Prim

end Steps

end CtxLemmas

end ProbLang
