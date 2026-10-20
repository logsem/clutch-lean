module

public import Metrology.Micrometer.FundamentalOps
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! The fundamental theorem: every well-typed expression is related to itself. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting

namespace ProbLang

open Cslib Exp

section Fundamental
variable {rT : Type} [LawfulProbLangℝ rT] {hlc : HasLC} {B : Type} [AddCommMonoid B]
  [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors}
  [IR : MicrometerRGS rT hlc GF] [BudgetCreditGS B GF]

variable (L) in
/-- The typing context `Γtc` is interpreted pointwise as the relational context `Γrc`. -/
def TctxRelated (Δ : TyEnv rT GF) (Γtc : Tctx) (Γrc : RelCtx rT GF) : Prop :=
  ∀ x, (Γtc x).map (fun τ => interp L τ Δ) = Γrc.lookup x

theorem TctxRelated.lookup_isSome {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated L Δ Γtc Γrc) {x : Var} (hx : (Γtc x).isSome) : (Γrc.lookup x).isSome := by
  rw [← HCtx x]
  simpa using hx

theorem TctxRelated.lookup_some {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated L Δ Γtc Γrc) {x : Var} {τ : Ty} (hx : Γtc x = some τ) :
    Γrc.lookup x = some (interp L τ Δ) := by
  rw [← HCtx x, hx]
  rfl

theorem TctxRelated.shift {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated L Δ Γtc Γrc) (A : lrel rT GF) :
    TctxRelated L (TyEnv.cons A Δ) Γtc.shift Γrc := by
  intro x
  simpa [Tctx.shift, Option.map_map, Function.comp_def, interp_ren] using HCtx x

theorem TctxRelated.insert {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated L Δ Γtc Γrc) (x : Var) (τ : Ty) (hfresh : Γrc.lookup x = none) :
    TctxRelated L Δ (Γtc.insert x τ) ((x, interp L τ Δ) :: Γrc) := by
  intro y
  by_cases hyx : y = x
  · subst hyx
    simp [Tctx.insert, RelCtx.lookup_cons, hfresh]
  · rw [Tctx.insert, ite_eq_right hyx, RelCtx.lookup_cons, ← HCtx y]
    cases Γtc y <;> simp [hyx]

theorem fv_subset_relCtxDom {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
    (HCtx : TctxRelated L Δ Γtc Γrc) {e : Exp rT} {τ : Ty} (Hty : Typed Γtc e τ) :
    e.fv ⊆ (Γrc.map (·.1)).toFinset :=
  fun x hx => RelCtx.mem_of_lookup_isSome (HCtx.lookup_isSome (Hty.fvSubset x hx))

theorem fv_subset_of_cofinite {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF}
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

section Steps
variable [L.IsLawful] [L.IsTopAbsorbing]

section Bind
variable [L.HasBind]

section Prim
variable [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal]

variable (L) in
/-- Every well-typed expression is related to itself under any related contexts. -/
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

/-- A closed well-typed expression refines itself at its type. -/
theorem refines_typed (Δ : TyEnv rT GF) {e : Exp rT} {τ : Ty} (Hty : Typed Tctx.empty e τ) :
    ⊢@{IProp GF} refines L ⊤ e e (interp L τ Δ) := by
  have Hfund := fundamental L Hty Δ [] (by intro x; simp [Tctx.empty, RelCtx.lookup])
  iapply bin_log_related_nil_elim
  iapply Hfund

end Prim

end Bind

end Steps

end Fundamental

end ProbLang
