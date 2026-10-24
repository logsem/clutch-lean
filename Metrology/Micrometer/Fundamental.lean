module

public import Metrology.Micrometer.FundamentalOps
import Metrology.Iris.LocalBI
import Metrology.ProbLang.Syntax.Notation

/-! # The fundamental theorem

Every well-typed expression is related to itself (`fundamental`), by induction
on typing with one `bin_log_related_*` lemma per rule; `refines_typed` is the closed form.
-/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting

namespace ProbLang

open Cslib Exp RelCtx

/-- The body of a cofinitely typed binder is locally closed away from `S` and any finite `D`. -/
theorem isLocallyClosed_of_cofinite {rT : Type} {e : Exp rT} {Γtc : Tctx}
    {S D : Finset Var} {τ1 τ2 : Ty}
    (Hbody : ∀ x ∉ S, Typed (Γtc.insert x τ1) (open' e (.fvar x)) τ2) :
    ∀ x ∉ S ∪ D, (open' e (.fvar x)).IsLocallyClosed := fun x hx =>
  (Hbody x (Finset.notMem_union.1 hx).1).isLocallyClosed

section Fundamental
variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT] {hlc : HasLC} {B : Type}
  [AddCommMonoid B] [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B}
  {GF : BundledGFunctors} [MicrometerRGS rT hlc GF] [BudgetCreditGS B GF] {e : Exp rT} {τ : Ty}
local bi IProp GF

/-! ## Typing contexts as relational contexts -/

variable (L) in
/-- The typing context `Γtc` is interpreted pointwise as the relational context `Γrc`. -/
def TctxRelated (Δ : TyEnv rT GF) (Γtc : Tctx) (Γrc : RelCtx rT GF) : Prop :=
  ∀ x, (Γtc x).map (fun τ => interp L τ Δ) = Γrc.lookup x

section TctxLemmas
variable {Δ : TyEnv rT GF} {Γtc : Tctx} {Γrc : RelCtx rT GF} {x : Var}
  (HCtx : TctxRelated L Δ Γtc Γrc)
include HCtx

/-- A variable typed in `Γtc` is bound in `Γrc`. -/
theorem TctxRelated.lookup_isSome (hx : (Γtc x).isSome) : (Γrc.lookup x).isSome := by
  rw [← HCtx x]
  simpa using hx

/-- A variable of type `τ` in `Γtc` maps to `interp L τ Δ` in `Γrc`. -/
theorem TctxRelated.lookup_some (hx : Γtc x = some τ) : Γrc.lookup x = some (interp L τ Δ) := by
  rw [← HCtx x, hx]
  rfl

/-- Relatedness survives entering a type binder: shift `Γtc` and extend `Δ` by `A`. -/
theorem TctxRelated.shift (A : lrel rT GF) : TctxRelated L (.cons A Δ) Γtc.shift Γrc := by
  intro x
  simpa [Tctx.shift, Option.map_map, Function.comp_def, interp_ren] using HCtx x

/-- Relatedness survives binding a fresh term variable `x : τ` on both sides. -/
theorem TctxRelated.insert (x : Var) (τ : Ty) (hfresh : Γrc.lookup x = none) :
    TctxRelated L Δ (Γtc.insert x τ) ((x, interp L τ Δ) :: Γrc) := by
  intro y
  by_cases hyx : y = x
  · subst hyx
    simp [Tctx.insert, lookup_cons, hfresh]
  · rw [Tctx.insert, ite_eq_right hyx, lookup_cons, ← HCtx y]
    cases Γtc y <;> simp [hyx]

/-- The free variables of a term typed in `Γtc` lie in the domain of `Γrc`. -/
theorem fv_subset_relCtxDom (Hty : Typed Γtc e τ) : e.fv ⊆ (Γrc.map (·.1)).toFinset :=
  fun x hx => mem_of_lookup_isSome (HCtx.lookup_isSome (Hty.fvSubset x hx))

/-- The free variables of a cofinitely typed binder body lie in the domain of `Γrc`. -/
theorem fv_subset_of_cofinite {S : Finset Var} {τ1 τ2 : Ty}
    (Hbody : ∀ x ∉ S, Typed (Γtc.insert x τ1) (open' e (.fvar x)) τ2) :
    e.fv ⊆ (Γrc.map (·.1)).toFinset := by
  intro z hz
  obtain ⟨y, hy⟩ := HasFresh.fresh_exists (S ∪ (Γrc.map (·.1)).toFinset ∪ {z})
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
  have hzdom := fv_subset_relCtxDom (HCtx.insert y τ1 (lookup_eq_none_of_notMem hy.1.2))
    (Hbody y hy.1.1) (fv_subset_open e y hz)
  simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert] at hzdom
  exact hzdom.resolve_left fun h => hy.2 h.symm

end TctxLemmas

/-! ## The fundamental theorem -/

variable [L.IsLawful] [L.IsTopAbsorbing] [L.HasBind] [CanonicallyOrderedAdd B] [L.IsReflexive]
  [L.IsSupportLocal]

variable (L) in
/-- Every well-typed expression is related to itself under any related contexts. -/
theorem fundamental {Γtc : Tctx} (Hty : Typed Γtc e τ) (Δ : TyEnv rT GF) (Γrc : RelCtx rT GF)
    (HCtx : TctxRelated L Δ Γtc Γrc) :
    ⊢ bin_log_related_ty L ⊤ Δ Γrc e e τ := by
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
  -- Binder cases: enlarge the cofinite set to `S ∪ dom Γrc`, so the fresh variable is also
  -- fresh for `Γrc` and `HCtx.insert` applies.
  | @lam S _ e τ1 τ2 Hbody ih =>
    have he_fv := fv_subset_of_cofinite HCtx Hbody
    have he_lc := isLocallyClosed_of_cofinite (D := (Γrc.map (·.1)).toFinset) Hbody
    exact bin_log_related_lam Δ Γrc _ he_lc he_lc he_fv he_fv fun x hx =>
      ih x (not_mem_union_dom hx).1 Δ _ (HCtx.insert x τ1 (not_mem_union_dom hx).2)
  | @«fix» S _ e τ1 τ2 Hbody ih =>
    have he_fv := fv_subset_of_cofinite HCtx Hbody
    have he_lc := isLocallyClosed_of_cofinite (D := (Γrc.map (·.1)).toFinset) Hbody
    exact bin_log_related_fix Δ Γrc _ he_lc he_lc he_fv he_fv fun x hx =>
      ih x (not_mem_union_dom hx).1 Δ _ (HCtx.insert x (.arrow τ1 τ2) (not_mem_union_dom hx).2)
  | @tlam _ e τ Hbody ih =>
    have hLC := Hbody.isLocallyClosed
    have he_fv := fv_subset_relCtxDom (HCtx.shift default) Hbody
    refine bin_log_related_tlam Δ Γrc hLC hLC he_fv he_fv fun A => ?_
    imodintro
    iapply ih (.cons A Δ) Γrc (HCtx.shift A)
  | @tunpack S _ e1 e2 τ τ2 _ Hbody2 ih1 ih2 =>
    have he2_lc := isLocallyClosed_of_cofinite (D := (Γrc.map (·.1)).toFinset) Hbody2
    exact bin_log_related_unpack Δ Γrc _ (ih1 Δ Γrc HCtx) he2_lc he2_lc fun A x hx =>
      ih2 x (not_mem_union_dom hx).1 (.cons A Δ) _
        ((HCtx.shift A).insert x τ (not_mem_union_dom hx).2)

/-- A closed well-typed expression refines itself at its type. -/
theorem refines_typed (Δ : TyEnv rT GF) (Hty : Typed .empty e τ) :
    ⊢ refines L ⊤ e e (interp L τ Δ) := by
  have Hfund := fundamental L Hty Δ [] (by intro x; simp [Tctx.empty, lookup])
  iapply bin_log_related_nil_elim
  iapply Hfund

end Fundamental

end ProbLang
