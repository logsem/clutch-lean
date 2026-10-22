module

public import Metrology.ProbLang.Syntax.Types
public import Metrology.ProbLang.Exec

@[expose] public section

/-!
# Contextual refinement

Program contexts `Ctx`, their typing `TypedCtx`, and contextual refinement `Γ ⊨ e ≤ctx≤ e' : τ`,
a congruence. Port of Clutch's `theories/prob_lang/typing/contextual_refinement.v`.
-/

namespace ProbLang

variable {rT : Type _} [LawfulProbLangℝ rT]

open MeasureTheory Exp Finset

/-! ## Single-frame context items -/

/-- One frame of a general program context; unlike `Ectx` the hole may be under a binder
(`lam`/`fix`/`unpack` close the plugged term at the given atom). Clutch's `letrec f x body` is the
two frames `fix f :: lam x :: K`. -/
inductive CtxItem (rT : Type _) [LawfulProbLangℝ rT]
  | lam (x : Var)
  | fix (f : Var)
  | tlam
  | appL (e2 : Exp rT)
  | appR (e1 : Exp rT)
  | unop (op : UnOp)
  | binopL (op : BinOp) (e2 : Exp rT)
  | binopR (op : BinOp) (e1 : Exp rT)
  | ifL (e1 e2 : Exp rT)
  | ifM (e0 e2 : Exp rT)
  | ifR (e0 e1 : Exp rT)
  | pairL (e2 : Exp rT)
  | pairR (e1 : Exp rT)
  | fst
  | snd
  | inl
  | inr
  | caseL (e1 e2 : Exp rT)
  | caseM (e0 e2 : Exp rT)
  | caseR (e0 e1 : Exp rT)
  | alloc
  | load
  | storeL (e2 : Exp rT)
  | storeR (e1 : Exp rT)
  | fold
  | unfold
  | tapp
  /-- `unpack x := □ in e2`, i.e. `app (lam (close e2 x)) □`. -/
  | unpackL (x : Var) (e2 : Exp rT)
  /-- `unpack x := e1 in □`, i.e. `app (lam (close □ x)) e1`. -/
  | unpackR (x : Var) (e1 : Exp rT)
  | allocTape
  | randL (e2 : Exp rT)
  | randR (e1 : Exp rT)

namespace CtxItem

/-- Plugs `e` into the hole of a single-frame context. -/
def fill : CtxItem rT → Exp rT → Exp rT
  | .lam x,          e => .lam (close e x)
  | .fix f,          e => .fix (close e f)
  -- types are erased: `Λ` is a thunk `lam`, type application applies it to `()`; `fold` is the
  -- identity, `unfold` applies `recUnfold`
  | .tlam,           e => .lam e
  | .appL e2,        e => .app e e2
  | .appR e1,        e => .app e1 e
  | .unop op,        e => .unop op e
  | .binopL op e2,   e => .binop op e e2
  | .binopR op e1,   e => .binop op e1 e
  | .ifL e1 e2,      e => .cond e e1 e2
  | .ifM e0 e2,      e => .cond e0 e e2
  | .ifR e0 e1,      e => .cond e0 e1 e
  | .pairL e2,       e => .pair e e2
  | .pairR e1,       e => .pair e1 e
  | .fst,            e => .fst e
  | .snd,            e => .snd e
  | .inl,            e => .inl e
  | .inr,            e => .inr e
  | .caseL e1 e2,    e => .case e e1 e2
  | .caseM e0 e2,    e => .case e0 e e2
  | .caseR e0 e1,    e => .case e0 e1 e
  | .alloc,          e => .alloc e
  | .load,           e => .load e
  | .storeL e2,      e => .store e e2
  | .storeR e1,      e => .store e1 e
  | .fold,           e => e
  | .unfold,         e => .app recUnfold e
  | .tapp,           e => .app e (.lit .unit)
  | .unpackL x e2,   e => .app (.lam (close e2 x)) e
  | .unpackR x e1,   e => .app (.lam (close e x)) e1
  | .allocTape,      e => .tape e
  | .randL e2,       e => .rand e e2
  | .randR e1,       e => .rand e1 e

end CtxItem

/-! ## Multi-frame contexts -/

/-- Frames listed outermost first: `[outer, …, inner].fill e = outer[…inner[e]…]`, as in Clutch. -/
abbrev Ctx (rT : Type _) [LawfulProbLangℝ rT] := List (CtxItem rT)

namespace Ctx

/-- Plugs `e` into the hole of a multi-frame context. -/
def fill (K : Ctx rT) (e : Exp rT) : Exp rT := K.foldr CtxItem.fill e

@[simp] theorem fill_nil (e : Exp rT) : fill ([] : Ctx rT) e = e := rfl

@[simp] theorem fill_cons (k : CtxItem rT) (K : Ctx rT) (e : Exp rT) :
    fill (k :: K) e = k.fill (K.fill e) := rfl

/-- Filling with a concatenation fills with the inner context first. -/
theorem fill_append (K K' : Ctx rT) (e : Exp rT) :
    fill (K' ++ K) e = fill K' (fill K e) := by
  simp [fill, List.foldr_append]

end Ctx

/-! ## Well-typed single-frame contexts -/

/-- `TypedCtxItem k Γ τ Γ' τ'`: filling `k` with a `Γ ⊢ τ` term gives a `Γ' ⊢ τ'` term. -/
inductive TypedCtxItem : CtxItem rT → Tctx → Ty → Tctx → Ty → Prop
  | lam {Γ x τ τ'} :
      TypedCtxItem (.lam x) (Γ.insert x τ) τ' Γ (.arrow τ τ')
  | fix {Γ f τ τ'} :
      TypedCtxItem (.fix f) (Γ.insert f (.arrow τ τ')) (.arrow τ τ') Γ (.arrow τ τ')
  | appL {Γ e2 τ τ'} :
      Typed Γ e2 τ →
      TypedCtxItem (.appL e2) Γ (.arrow τ τ') Γ τ'
  | appR {Γ e1 τ τ'} :
      Typed Γ e1 (.arrow τ τ') →
      TypedCtxItem (.appR e1) Γ τ Γ τ'
  | unop_int {Γ op τ} :
      op.intResTy = some τ →
      TypedCtxItem (.unop op) Γ .int Γ τ
  | unop_bool {Γ op τ} :
      op.boolResTy = some τ →
      TypedCtxItem (.unop op) Γ .bool Γ τ
  | binopL_int {Γ op e2 τ} :
      Typed Γ e2 .int → op.intResTy = some τ →
      TypedCtxItem (.binopL op e2) Γ .int Γ τ
  | binopR_int {Γ op e1 τ} :
      Typed Γ e1 .int → op.intResTy = some τ →
      TypedCtxItem (.binopR op e1) Γ .int Γ τ
  | binopL_bool {Γ op e2 τ} :
      Typed Γ e2 .bool → op.boolResTy = some τ →
      TypedCtxItem (.binopL op e2) Γ .bool Γ τ
  | binopR_bool {Γ op e1 τ} :
      Typed Γ e1 .bool → op.boolResTy = some τ →
      TypedCtxItem (.binopR op e1) Γ .bool Γ τ
  | unop_real {Γ op τ} :
      op.realResTy = some τ →
      TypedCtxItem (.unop op) Γ .real Γ τ
  | binopL_real {Γ op e2 τ} :
      Typed Γ e2 .real → op.realResTy = some τ →
      TypedCtxItem (.binopL op e2) Γ .real Γ τ
  | binopR_real {Γ op e1 τ} :
      Typed Γ e1 .real → op.realResTy = some τ →
      TypedCtxItem (.binopR op e1) Γ .real Γ τ
  | binopL_unboxedEq {Γ e2 τ} :
      UnboxedType τ → Typed Γ e2 τ →
      TypedCtxItem (.binopL .eq e2) Γ τ Γ .bool
  | binopR_unboxedEq {Γ e1 τ} :
      UnboxedType τ → Typed Γ e1 τ →
      TypedCtxItem (.binopR .eq e1) Γ τ Γ .bool
  | ifL {Γ e1 e2 τ} :
      Typed Γ e1 τ → Typed Γ e2 τ →
      TypedCtxItem (.ifL e1 e2) Γ .bool Γ τ
  | ifM {Γ e0 e2 τ} :
      Typed Γ e0 .bool → Typed Γ e2 τ →
      TypedCtxItem (.ifM e0 e2) Γ τ Γ τ
  | ifR {Γ e0 e1 τ} :
      Typed Γ e0 .bool → Typed Γ e1 τ →
      TypedCtxItem (.ifR e0 e1) Γ τ Γ τ
  | pairL {Γ e2 τ τ'} :
      Typed Γ e2 τ' →
      TypedCtxItem (.pairL e2) Γ τ Γ (.prod τ τ')
  | pairR {Γ e1 τ τ'} :
      Typed Γ e1 τ →
      TypedCtxItem (.pairR e1) Γ τ' Γ (.prod τ τ')
  | fst {Γ τ τ'} :
      TypedCtxItem .fst Γ (.prod τ τ') Γ τ
  | snd {Γ τ τ'} :
      TypedCtxItem .snd Γ (.prod τ τ') Γ τ'
  | inl {Γ τ τ'} :
      TypedCtxItem .inl Γ τ Γ (.sum τ τ')
  | inr {Γ τ τ'} :
      TypedCtxItem .inr Γ τ' Γ (.sum τ τ')
  | caseL {Γ e1 e2 τ1 τ2 τ'} :
      Typed Γ e1 (.arrow τ1 τ') → Typed Γ e2 (.arrow τ2 τ') →
      TypedCtxItem (.caseL e1 e2) Γ (.sum τ1 τ2) Γ τ'
  | caseM {Γ e0 e2 τ1 τ2 τ'} :
      Typed Γ e0 (.sum τ1 τ2) → Typed Γ e2 (.arrow τ2 τ') →
      TypedCtxItem (.caseM e0 e2) Γ (.arrow τ1 τ') Γ τ'
  | caseR {Γ e0 e1 τ1 τ2 τ'} :
      Typed Γ e0 (.sum τ1 τ2) → Typed Γ e1 (.arrow τ1 τ') →
      TypedCtxItem (.caseR e0 e1) Γ (.arrow τ2 τ') Γ τ'
  | alloc {Γ τ} :
      TypedCtxItem .alloc Γ τ Γ (.ref τ)
  | load {Γ τ} :
      TypedCtxItem .load Γ (.ref τ) Γ τ
  | storeL {Γ e2 τ} :
      Typed Γ e2 τ → TypedCtxItem (.storeL e2) Γ (.ref τ) Γ .unit
  | storeR {Γ e1 τ} :
      Typed Γ e1 (.ref τ) → TypedCtxItem (.storeR e1) Γ τ Γ .unit
  | fold {Γ τ} :
      TypedCtxItem .fold Γ (τ.single (.rec' τ)) Γ (.rec' τ)
  | unfold {Γ τ} :
      TypedCtxItem .unfold Γ (.rec' τ) Γ (τ.single (.rec' τ))
  | tlam {Γ τ} :
      TypedCtxItem .tlam Γ.shift τ Γ (.forall' τ)
  | tapp {Γ τ τ'} :
      TypedCtxItem .tapp Γ (.forall' τ) Γ (τ.single τ')
  | unpackL {x : Var} {e2 Γ τ τ2} :
      x ∉ e2.fv →
      Typed ((Γ.shift).insert x τ) e2 τ2.shift →
      TypedCtxItem (.unpackL x e2) Γ (.exists' τ) Γ τ2
  | unpackR {x : Var} {e1 Γ τ τ2} :
      Typed Γ e1 (.exists' τ) →
      TypedCtxItem (.unpackR x e1) ((Γ.shift).insert x τ) τ2.shift Γ τ2
  | allocTape {Γ} :
      TypedCtxItem .allocTape Γ .int Γ .tape
  | randL_unit {Γ e2} :
      Typed Γ e2 .unit → TypedCtxItem (.randL e2) Γ .int Γ .int
  | randL_tape {Γ e2} :
      Typed Γ e2 .tape → TypedCtxItem (.randL e2) Γ .int Γ .int
  | randR_unit {Γ e1} :
      Typed Γ e1 .int → TypedCtxItem (.randR e1) Γ .unit Γ .int
  | randR_tape {Γ e1} :
      Typed Γ e1 .int → TypedCtxItem (.randR e1) Γ .tape Γ .int

/-! ## Well-typed multi-frame contexts -/

/-- `TypedCtx K Γ τ Γ' τ'`: filling `K` with a `Γ ⊢ τ` term gives a `Γ' ⊢ τ'` term. -/
inductive TypedCtx : Ctx rT → Tctx → Ty → Tctx → Ty → Prop
  | nil {Γ τ} : TypedCtx [] Γ τ Γ τ
  | cons {K k Γ1 τ1 Γ2 τ2 Γ3 τ3} :
      TypedCtxItem k Γ2 τ2 Γ3 τ3 →
      TypedCtx K Γ1 τ1 Γ2 τ2 →
      TypedCtx (k :: K) Γ1 τ1 Γ3 τ3

/-! ## Filling typed contexts -/

/-- Filling a well-typed frame with a well-typed term is well typed (Clutch
`typed_ctx_item_typed`). -/
theorem TypedCtxItem.fill_typed {k : CtxItem rT} {Γ τ Γ' τ'} {e : Exp rT}
    (he : Typed Γ e τ) (hk : TypedCtxItem k Γ τ Γ' τ') :
    Typed Γ' (k.fill e) τ' := by
  induction hk with
  | @lam _ x =>
      exact Typed.lam (insert x e.fv) (Typed.rename_lam he)
  | @fix _ f =>
      exact Typed.fix (insert f e.fv) (Typed.rename_fix he)
  | appL h2     => exact .app he h2
  | appR h1     => exact .app h1 he
  | unop_int hop       => exact .unop_int he hop
  | unop_bool hop      => exact .unop_bool he hop
  | binopL_int h2 hop  => exact .binop_int he h2 hop
  | binopR_int h1 hop  => exact .binop_int h1 he hop
  | binopL_bool h2 hop => exact .binop_bool he h2 hop
  | binopR_bool h1 hop => exact .binop_bool h1 he hop
  | unop_real hop       => exact .unop_real he hop
  | binopL_real h2 hop  => exact .binop_real he h2 hop
  | binopR_real h1 hop  => exact .binop_real h1 he hop
  | binopL_unboxedEq hu h2 => exact .unboxed_eq hu he h2
  | binopR_unboxedEq hu h1 => exact .unboxed_eq hu h1 he
  | ifL h1 h2   => exact .cond he h1 h2
  | ifM h0 h2   => exact .cond h0 he h2
  | ifR h0 h1   => exact .cond h0 h1 he
  | pairL h2    => exact .pair he h2
  | pairR h1    => exact .pair h1 he
  | fst         => exact .fst he
  | snd         => exact .snd he
  | inl         => exact .inl he
  | inr         => exact .inr he
  | caseL h1 h2 => exact .case he h1 h2
  | caseM h0 h2 => exact .case h0 he h2
  | caseR h0 h1 => exact .case h0 h1 he
  | alloc       => exact .alloc he
  | load        => exact .load he
  | storeL h2   => exact .store he h2
  | storeR h1   => exact .store h1 he
  | fold        => exact .tfold he
  | unfold      => exact (.tunfold he : Typed _ (.app recUnfold _) _)
  | tlam        => exact .tlam he
  | tapp        => exact .tapp he
  | @unpackL x e2 _ _ _ _ h2 =>
      exact Typed.tunpack (insert x e2.fv) he (Typed.rename_unpack h2)
  | @unpackR x _ _ _ _ h1 =>
      exact Typed.tunpack (insert x e.fv) h1 (Typed.rename_unpack he)
  | allocTape   => exact .alloc_tape he
  | randL_unit h2 => exact .rand_unit he h2
  | randL_tape h2 => exact .rand he h2
  | randR_unit h1 => exact .rand_unit h1 he
  | randR_tape h1 => exact .rand h1 he

/-- Filling a well-typed context with a well-typed term is well typed (Clutch `typed_ctx_typed`). -/
theorem TypedCtx.fill_typed {K : Ctx rT} {Γ τ Γ' τ'} {e : Exp rT}
    (he : Typed Γ e τ) (hK : TypedCtx K Γ τ Γ' τ') :
    Typed Γ' (K.fill e) τ' := by
  induction hK with
  | nil => exact he
  | @cons K k _ _ _ _ _ _ hk _ ih =>
      rw [Ctx.fill_cons]
      exact hk.fill_typed (ih he)

/-- Well-typed contexts compose (Clutch `typed_ctx_compose`). -/
theorem TypedCtx.compose {K K' : Ctx rT} {Γ1 Γ2 Γ3 τ1 τ2 τ3}
    (hK : TypedCtx K Γ1 τ1 Γ2 τ2) (hK' : TypedCtx K' Γ2 τ2 Γ3 τ3) :
    TypedCtx (K' ++ K) Γ1 τ1 Γ3 τ3 := by
  induction hK' with
  | nil => exact hK
  | cons hk _ ih => exact .cons hk (ih hK)

/-! ## Contextual refinement -/

/-- The configurations that have returned the boolean `b`. -/
def finalBool (b : Bool) : Set (Cfg rT) :=
  { ρ | ρ.expr = .lit (.bool b) }

/-- `Γ ⊨ e ≤ctx≤ e' : τ`: for every closing Bool context `K`, initial state and Boolean `b`, `K[e]`
returns `b` with at most the probability that `K[e']` does (Clutch `ctx_refines`, in `ENNReal`). -/
def CtxRefines (Γ : Tctx) (e e' : Exp rT) (τ : Ty) : Prop :=
  ∀ (K : Ctx rT) (σ₀ : State rT) (b : Bool),
    TypedCtx K Γ τ Tctx.empty .bool →
    limExec ⟨K.fill e,  σ₀⟩ (finalBool b) ≤
    limExec ⟨K.fill e', σ₀⟩ (finalBool b)

@[inherit_doc]
scoped notation Γ " ⊨ " e " ≤ctx≤ " e' " : " τ => CtxRefines Γ e e' τ

namespace CtxRefines

variable {Γ : Tctx} {τ : Ty}

/-- Contextual refinement is reflexive. -/
theorem refl (e : Exp rT) : CtxRefines Γ e e τ :=
  fun _ _ _ _ => le_rfl

/-- Contextual refinement is transitive. -/
theorem trans {e1 e2 e3 : Exp rT}
    (h12 : CtxRefines Γ e1 e2 τ) (h23 : CtxRefines Γ e2 e3 τ) :
    CtxRefines Γ e1 e3 τ :=
  fun K σ₀ b hK => (h12 K σ₀ b hK).trans (h23 K σ₀ b hK)

/-- Contextual refinement is a congruence (Clutch `ctx_refines_congruence`). -/
theorem congr {Γ' τ'} {e1 e2 : Exp rT} {K : Ctx rT}
    (hK : TypedCtx K Γ τ Γ' τ')
    (href : CtxRefines Γ e1 e2 τ) :
    CtxRefines Γ' (K.fill e1) (K.fill e2) τ' := by
  -- `K'[K[e]] = (K' ++ K)[e]`, and `K' ++ K` is a typed closing context for `e`
  intro K' σ₀ b hty
  rw [← Ctx.fill_append, ← Ctx.fill_append]
  exact href (K' ++ K) σ₀ b (hK.compose hty)

end CtxRefines

/-! ## Contextual equivalence -/

/-- Contextual equivalence: refinement in both directions. -/
def CtxEquiv (Γ : Tctx) (e1 e2 : Exp rT) (τ : Ty) : Prop :=
  CtxRefines Γ e1 e2 τ ∧ CtxRefines Γ e2 e1 τ

@[inherit_doc]
scoped notation Γ " ⊨ " e " =ctx= " e' " : " τ => CtxEquiv Γ e e' τ

namespace CtxEquiv

variable {Γ : Tctx} {τ : Ty}

/-- Contextual equivalence is reflexive. -/
theorem refl (e : Exp rT) : CtxEquiv Γ e e τ :=
  ⟨.refl e, .refl e⟩

/-- Contextual equivalence is symmetric. -/
theorem symm {e1 e2 : Exp rT} (h : CtxEquiv Γ e1 e2 τ) : CtxEquiv Γ e2 e1 τ :=
  ⟨h.2, h.1⟩

/-- Contextual equivalence is transitive. -/
theorem trans {e1 e2 e3 : Exp rT}
    (h12 : CtxEquiv Γ e1 e2 τ) (h23 : CtxEquiv Γ e2 e3 τ) :
    CtxEquiv Γ e1 e3 τ :=
  ⟨h12.1.trans h23.1, h23.2.trans h12.2⟩

end CtxEquiv

/-! ## Free variables and binders of contexts

`binderAtoms` and `payloadFv` bound the atoms a context can capture or contribute; Soundness's
precongruence picks atoms fresh for them. -/

/-- The atoms a frame binds. -/
def CtxItem.binderAtoms : CtxItem rT → Finset Var
  | .lam x => {x}
  | .fix f => {f}
  | .unpackL x _ => {x}
  | .unpackR x _ => {x}
  | _ => ∅

/-- The free variables of the expressions stored in a frame. -/
def CtxItem.payloadFv : CtxItem rT → Finset Var
  | .appL e2 => e2.fv
  | .appR e1 => e1.fv
  | .binopL _ e2 => e2.fv
  | .binopR _ e1 => e1.fv
  | .ifL e1 e2 => e1.fv ∪ e2.fv
  | .ifM e0 e2 => e0.fv ∪ e2.fv
  | .ifR e0 e1 => e0.fv ∪ e1.fv
  | .pairL e2 => e2.fv
  | .pairR e1 => e1.fv
  | .caseL e1 e2 => e1.fv ∪ e2.fv
  | .caseM e0 e2 => e0.fv ∪ e2.fv
  | .caseR e0 e1 => e0.fv ∪ e1.fv
  | .storeL e2 => e2.fv
  | .storeR e1 => e1.fv
  | .unpackL _ e2 => e2.fv
  | .unpackR _ e1 => e1.fv
  | .randL e2 => e2.fv
  | .randR e1 => e1.fv
  | _ => ∅

/-- Closing a term at an atom introduces no new free variables. -/
theorem closeRec_fv_subset (e : Exp α) (x : Var) (k : Nat) (y : Var)
    (hy : y ∈ (closeRec k x e).fv) : y ∈ e.fv := by
  induction e generalizing k with
  | bvar _ => simp [closeRec, fv] at hy
  | fvar z =>
      simp [closeRec] at hy
      by_cases hxz : x = z
      · rw [ite_eq_left hxz] at hy; simp [fv] at hy
      · rw [ite_eq_right hxz] at hy; exact hy
  | lit _ | fail | urand => simp [closeRec, fv] at hy
  | lam e ih | fix e ih =>
      simp only [closeRec, fv] at hy ⊢
      exact ih (k+1) hy
  | unop _ e ih | fst e ih | snd e ih
  | inl e ih | inr e ih | alloc e ih | load e ih | tape e ih | scrut e _ ih =>
      simp only [closeRec, fv] at hy ⊢
      exact ih k hy
  | app e1 e2 ih1 ih2 | binop _ e1 e2 ih1 ih2 | pair e1 e2 ih1 ih2
  | store e1 e2 ih1 ih2 | rand e1 e2 ih1 ih2 =>
      simp only [closeRec, fv, mem_union] at hy ⊢
      exact hy.imp (ih1 k) (ih2 k)
  | cond e0 e1 e2 ih0 ih1 ih2 | case e0 e1 e2 ih0 ih1 ih2 =>
      simp only [closeRec, fv, mem_union] at hy ⊢
      exact hy.imp (Or.imp (ih0 k) (ih1 k)) (ih2 k)

/-- Closing a term introduces no new free variables. -/
theorem close_fv_subset (e : Exp α) (x : Var) : (close e x).fv ⊆ e.fv :=
  fun y hy => closeRec_fv_subset e x 0 y hy

/-- Filling a frame adds at most the free variables stored in the frame. -/
theorem CtxItem.fv_fill_subset (k : CtxItem rT) (body : Exp rT) :
    (k.fill body).fv ⊆ k.payloadFv ∪ body.fv := by
  intro y hy
  cases k <;>
    simp only [CtxItem.fill, CtxItem.payloadFv, fv,
      mem_union, empty_union, ProbLang.recUnfold] at hy ⊢
  all_goals first
    | tauto
    | (rename_i x; exact close_fv_subset _ x hy)
    | (rename_i x _; exact hy.imp_left fun h => close_fv_subset _ x h)
    | (rename_i x _; exact hy.symm.imp_right fun h => close_fv_subset _ x h)

/-- The atoms bound by the frames of a context. -/
def Ctx.binderAtoms (K : Ctx rT) : Finset Var :=
  K.foldr (fun k acc => k.binderAtoms ∪ acc) ∅

/-- The free variables of the expressions stored in the frames of a context. -/
def Ctx.payloadFv (K : Ctx rT) : Finset Var :=
  K.foldr (fun k acc => k.payloadFv ∪ acc) ∅

/-- Filling a context adds at most the free variables stored in its frames. -/
theorem Ctx.fv_fill_subset (K : Ctx rT) (e : Exp rT) :
    (K.fill e).fv ⊆ Ctx.payloadFv K ∪ e.fv := by
  induction K with
  | nil => exact subset_union_right
  | cons k K ih =>
      rw [Ctx.fill_cons]
      refine (CtxItem.fv_fill_subset k (Ctx.fill K e)).trans ?_
      simp only [Ctx.payloadFv, List.foldr_cons, union_assoc]
      exact union_subset_union subset_rfl ih

end ProbLang
