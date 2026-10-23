module

public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.Syntax.LocallyClosed

@[expose] public section

/-!
# Typing for ProbLang (System F_μ_ref with tapes)

The judgment `Typed Γ e τ` with cofinite binder rules over de Bruijn types and contexts `Tctx`.
-/

namespace ProbLang
open Cslib Exp

variable {rT : Type _}

/-! ## Type variables: renaming and substitution -/

/-- A renaming of de Bruijn type variables. -/
abbrev Renaming := Nat → Nat
/-- A substitution of types for de Bruijn type variables. -/
abbrev Substitution := Nat → Ty

/-- Transform a renaming `ξ` into one that applies under a binder. -/
@[simp] def Renaming.under (ξ : Renaming) : Renaming | 0 => 0 | n + 1 => ξ n + 1

/-- Apply a renaming to the type variables of a type. -/
def Ty.rename (ξ : Renaming) : Ty → Ty
  | .int          => .int
  | .bool         => .bool
  | .unit         => .unit
  | .real         => .real
  | .tape         => .tape
  | .prod τ1 τ2   => .prod (τ1.rename ξ) (τ2.rename ξ)
  | .sum  τ1 τ2   => .sum  (τ1.rename ξ) (τ2.rename ξ)
  | .arrow τ1 τ2  => .arrow (τ1.rename ξ) (τ2.rename ξ)
  | .ref τ        => .ref (τ.rename ξ)
  | .var n        => .var (ξ n)
  | .rec' τ       => .rec' (τ.rename ξ.under)
  | .forall' τ    => .forall' (τ.rename ξ.under)
  | .exists' τ    => .exists' (τ.rename ξ.under)

/-- Transform a substitution `σ` into one that applies under a binder. -/
def up (σ : Substitution) : Substitution | 0  => .var 0 | n + 1 => (σ n).rename (· + 1)

/-- Apply a substitution to the type variables of a type. -/
def Ty.subst (σ : Substitution) : Ty → Ty
  | .int          => .int
  | .bool         => .bool
  | .unit         => .unit
  | .real         => .real
  | .tape         => .tape
  | .prod τ1 τ2   => .prod (τ1.subst σ) (τ2.subst σ)
  | .sum  τ1 τ2   => .sum  (τ1.subst σ) (τ2.subst σ)
  | .arrow τ1 τ2  => .arrow (τ1.subst σ) (τ2.subst σ)
  | .ref τ        => .ref (τ.subst σ)
  | .var n        => σ n
  | .rec' τ       => .rec'    (τ.subst (up σ))
  | .forall' τ    => .forall' (τ.subst (up σ))
  | .exists' τ    => .exists' (τ.subst (up σ))

/-- `τ.single τ'` substitutes `τ'` for variable 0 in `τ`, written `τ[τ'/0]`. -/
def Ty.single (τ τ' : Ty) : Ty := τ.subst (fun n => match n with | 0 => τ' | k + 1 => .var k)

/-- Shift every type variable up by one. -/
def Ty.shift (τ : Ty) : Ty := τ.rename (· + 1)

/-! ## Operand classes and operator result types -/

/-- The operand types the `unboxed_eq` typing rule allows for `=` (excluding `tape`). -/
inductive UnboxedType : Ty → Prop
  | unit                           : UnboxedType .unit
  | int                            : UnboxedType .int
  | bool                           : UnboxedType .bool
  | ref (τ : Ty)                   : UnboxedType (.ref τ)

/-- Types on which value equality is decidable by structure (literals, products, sums). -/
inductive EqType : Ty → Prop
  | unit                           : EqType .unit
  | int                            : EqType .int
  | bool                           : EqType .bool
  | prod {τ τ'}                    : EqType τ → EqType τ' → EqType (.prod τ τ')
  | sum  {τ τ'}                    : EqType τ → EqType τ' → EqType (.sum τ τ')

/-- Unboxed types are equality types or references; the `tape` disjunct is kept from Clutch's
statement and is unreachable here. -/
theorem unboxed_type_ref_or_eqtype {τ : Ty} (h : UnboxedType τ) :
    EqType τ ∨ (∃ τ', τ = .ref τ') ∨ τ = .tape :=
  match h with
  | .unit  => .inl .unit
  | .int   => .inl .int
  | .bool  => .inl .bool
  | .ref τ => .inr (.inl ⟨τ, rfl⟩)

/-- Result type of a binary operation on integer operands. -/
def BinOp.intResTy : BinOp → Option Ty
  | .plus | .minus | .mult | .div | .mod  => some .int
  | .shl  | .shr                          => some .int
  | .and  | .or    | .xor                 => none
  | .eq   | .lt    | .le                  => some .bool

/-- Result type of a binary operation on boolean operands. -/
def BinOp.boolResTy : BinOp → Option Ty
  | .plus | .minus | .mult | .div | .mod  => none
  | .shl  | .shr                          => none
  | .and  | .or    | .xor                 => some .bool
  | .eq                                   => some .bool
  | .lt   | .le                           => none

/-- Result type of a unary operation on an integer operand. -/
def UnOp.intResTy : UnOp → Option Ty
  | .neg   => none
  | .minus => some .int
  | .toReal => some .real
  | .frac  => none

/-- Result type of a unary operation on a boolean operand. -/
def UnOp.boolResTy : UnOp → Option Ty
  | .neg   => some .bool
  | .minus => none
  | .toReal => none
  | .frac  => none

/-- Result type of a unary operation on a real operand. -/
def UnOp.realResTy : UnOp → Option Ty
  | .neg    => none
  | .minus  => some .real
  | .toReal => some .real
  | .frac   => some .real

/-- Result type of a binary operation when both operands are real; mixed int/real operands stay
stuck, so programs coerce with `UnOp.toReal`. -/
def BinOp.realResTy : BinOp → Option Ty
  | .plus                                => some .real
  | .minus | .mult | .div | .mod         => none
  | .shl   | .shr                        => none
  | .and   | .or   | .xor                => none
  | .eq    | .lt   | .le                 => some .bool

/-! ## Typing contexts -/

/-- A typing context: a partial map from free variables to types. -/
abbrev Tctx := Var → Option Ty

namespace Tctx

/-- The empty typing context. -/
def empty : Tctx := fun _ => none

/-- Assign type `τ` to the atom `x`. -/
def insert (Γ : Tctx) (x : Var) (τ : Ty) : Tctx :=
  fun y => if y = x then some τ else Γ y

/-- Shift the type variables of every type in the context. -/
def shift (Γ : Tctx) : Tctx := fun x => (Γ x).map Ty.shift

end Tctx

/-! ## Recursive-type unfolding and pattern typing -/

/-- `λ x. x`; wrapping `unfold` in it makes unfolding a recursive type take a real step. -/
def recUnfold : Exp rT := .lam (.bvar 0)

/-- Matches `p` against a scrutinee of type `τs`, yielding bindings of type `τb` (`.wildcard` binds
the whole scrutinee, as bindings live outside `Pat`). -/
inductive PatTyped : Ty → Pat rT → Ty → Prop
  /-- The wildcard binds the whole scrutinee. -/
  | wildcard {τ} : PatTyped τ .wildcard τ
  /-- An integer literal pattern. -/
  | lit_int {z} : PatTyped .int (.lit (.int z)) .unit
  /-- A boolean literal pattern. -/
  | lit_bool {b} : PatTyped .bool (.lit (.bool b)) .unit
  /-- The unit literal pattern. -/
  | lit_unit : PatTyped .unit (.lit .unit) .unit
  /-- A pair pattern matches componentwise. -/
  | pair {τ1 τ2 p1 p2 b1 b2} :
      PatTyped τ1 p1 b1 → PatTyped τ2 p2 b2 →
      PatTyped (.prod τ1 τ2) (.pair p1 p2) (.prod b1 b2)
  /-- A left-injection pattern matches a left summand. -/
  | inl {τ1 τ2 p b} : PatTyped τ1 p b → PatTyped (.sum τ1 τ2) (.inl p) b
  /-- A right-injection pattern matches a right summand. -/
  | inr {τ1 τ2 p b} : PatTyped τ2 p b → PatTyped (.sum τ1 τ2) (.inr p) b

/-! ## Typing judgment

Clutch's `letrec f x body` is `fix (lam body)`; derive it from `Typed.fix` and `Typed.lam`. -/

/-- Expression `e` has type `τ` under context `Γ`. -/
inductive Typed : Tctx → Exp rT → Ty → Prop
  | fvar {Γ x τ} : Γ x = some τ → Typed Γ (.fvar x) τ
  | lit_int  {Γ z} : Typed Γ (.lit (.int z)) .int
  | lit_bool {Γ b} : Typed Γ (.lit (.bool b)) .bool
  | lit_unit {Γ}   : Typed Γ (.lit .unit)     .unit
  | lit_real {Γ r} : Typed Γ (.lit (.real r)) .real
  /-- The continuous sampler draws a real from `Uniform[0,1]`. -/
  | urand {Γ}      : Typed Γ .urand           .real
  | unop_real {Γ op e τ} :
      Typed Γ e .real → op.realResTy = some τ →
      Typed Γ (.unop op e) τ
  | binop_real {Γ op e1 e2 τ} :
      Typed Γ e1 .real → Typed Γ e2 .real →
      op.realResTy = some τ →
      Typed Γ (.binop op e1 e2) τ
  | binop_int {Γ op e1 e2 τ} :
      Typed Γ e1 .int → Typed Γ e2 .int →
      op.intResTy = some τ →
      Typed Γ (.binop op e1 e2) τ
  | binop_bool {Γ op e1 e2 τ} :
      Typed Γ e1 .bool → Typed Γ e2 .bool →
      op.boolResTy = some τ →
      Typed Γ (.binop op e1 e2) τ
  | unop_int {Γ op e τ} :
      Typed Γ e .int → op.intResTy = some τ →
      Typed Γ (.unop op e) τ
  | unop_bool {Γ op e τ} :
      Typed Γ e .bool → op.boolResTy = some τ →
      Typed Γ (.unop op e) τ
  | unboxed_eq {Γ e1 e2 τ} :
      UnboxedType τ →
      Typed Γ e1 τ → Typed Γ e2 τ →
      Typed Γ (.binop .eq e1 e2) .bool
  | pair {Γ e1 e2 τ1 τ2} :
      Typed Γ e1 τ1 → Typed Γ e2 τ2 →
      Typed Γ (.pair e1 e2) (.prod τ1 τ2)
  | fst {Γ e τ1 τ2} :
      Typed Γ e (.prod τ1 τ2) → Typed Γ (.fst e) τ1
  | snd {Γ e τ1 τ2} :
      Typed Γ e (.prod τ1 τ2) → Typed Γ (.snd e) τ2
  | inl {Γ e τ1 τ2} :
      Typed Γ e τ1 → Typed Γ (.inl e) (.sum τ1 τ2)
  | inr {Γ e τ1 τ2} :
      Typed Γ e τ2 → Typed Γ (.inr e) (.sum τ1 τ2)
  | case {Γ e0 e1 e2 τ1 τ2 τ3} :
      Typed Γ e0 (.sum τ1 τ2) →
      Typed Γ e1 (.arrow τ1 τ3) →
      Typed Γ e2 (.arrow τ2 τ3) →
      Typed Γ (.case e0 e1 e2) τ3
  | cond {Γ e0 e1 e2 τ} :
      Typed Γ e0 .bool →
      Typed Γ e1 τ → Typed Γ e2 τ →
      Typed Γ (.cond e0 e1 e2) τ
  | lam (L : Finset Var) {Γ e τ1 τ2} :
      (∀ x ∉ L, Typed (Γ.insert x τ1) (open' e (.fvar x)) τ2) →
      Typed Γ (.lam e) (.arrow τ1 τ2)
  | fix (L : Finset Var) {Γ e τ1 τ2} :
      (∀ f ∉ L, Typed (Γ.insert f (.arrow τ1 τ2)) (open' e (.fvar f)) (.arrow τ1 τ2)) →
      Typed Γ (.fix e) (.arrow τ1 τ2)
  | app {Γ e1 e2 τ1 τ2} :
      Typed Γ e1 (.arrow τ1 τ2) →
      Typed Γ e2 τ1 →
      Typed Γ (.app e1 e2) τ2
  /-- Type abstraction is a thunk `λ_. e`; `e` is typed under the shifted context, not opened:
the thunk's argument is unused, and typing forces `e` to be locally closed. -/
  | tlam {Γ e τ} :
      Typed Γ.shift e τ →
      Typed Γ (.lam e) (.forall' τ)
  /-- Type application forces the thunk with `()`. -/
  | tapp {Γ e τ τ'} :
      Typed Γ e (.forall' τ) →
      Typed Γ (.app e (.lit .unit)) (τ.single τ')
  /-- `fold` is erased: no term change. -/
  | tfold {Γ e τ} :
      Typed Γ e (τ.single (.rec' τ)) →
      Typed Γ e (.rec' τ)
  /-- `unfold` is `recUnfold e`, so it takes one step. -/
  | tunfold {Γ e τ} :
      Typed Γ e (.rec' τ) →
      Typed Γ (.app recUnfold e) (τ.single (.rec' τ))
  /-- `pack` is erased: no term change. -/
  | tpack {Γ e τ τ'} :
      Typed Γ e (τ.single τ') →
      Typed Γ e (.exists' τ)
  /-- `unpack e1 as x in e2` is `(λx. e2) e1`. -/
  | tunpack (L : Finset Var) {Γ e1 e2 τ τ2} :
      Typed Γ e1 (.exists' τ) →
      (∀ x ∉ L, Typed (Γ.shift.insert x τ) (open' e2 (.fvar x)) τ2.shift) →
      Typed Γ (.app (.lam e2) e1) τ2
  | alloc {Γ e τ} :
      Typed Γ e τ → Typed Γ (.alloc e) (.ref τ)
  | load {Γ e τ} :
      Typed Γ e (.ref τ) → Typed Γ (.load e) τ
  | store {Γ e e' τ} :
      Typed Γ e (.ref τ) → Typed Γ e' τ →
      Typed Γ (.store e e') .unit
  | alloc_tape {Γ e} :
      Typed Γ e .int → Typed Γ (.tape e) .tape
  | rand {Γ e1 e2} :
      Typed Γ e1 .int → Typed Γ e2 .tape →
      Typed Γ (.rand e1 e2) .int
  | rand_unit {Γ e1 e2} :
      Typed Γ e1 .int → Typed Γ e2 .unit →
      Typed Γ (.rand e1 e2) .int
  | scrut {Γ e p τs τb} :
      Typed Γ e τs → PatTyped τs p τb →
      Typed Γ (.scrut e p) (.sum τb .unit)

@[inherit_doc] scoped notation Γ " ⊢ₜ " e " : " τ => Typed Γ e τ

/-! ## Typed terms are locally closed and have free variables in the context -/

variable {Γ : Tctx} {e : Exp rT} {τ : Ty}

/-- Typed expressions are locally closed. -/
theorem Typed.isLocallyClosed
    (h : Typed Γ e τ) : IsLocallyClosed e := by
  induction h with
  | fvar _ => exact .fvar _
  | lit_int | lit_bool | lit_unit | lit_real => exact .lit _
  | urand => exact .urand
  | unop_real _ _ ih => exact .unop _ ih
  | binop_real _ _ _ ih1 ih2 => exact .binop _ ih1 ih2
  | binop_int _ _ _ ih1 ih2 => exact .binop _ ih1 ih2
  | binop_bool _ _ _ ih1 ih2 => exact .binop _ ih1 ih2
  | unop_int _ _ ih => exact .unop _ ih
  | unop_bool _ _ ih => exact .unop _ ih
  | unboxed_eq _ _ _ ih1 ih2 => exact .binop _ ih1 ih2
  | pair _ _ ih1 ih2 => exact .pair ih1 ih2
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ih0 ih1 ih2 => exact .case ih0 ih1 ih2
  | cond _ _ _ ih0 ih1 ih2 => exact .cond ih0 ih1 ih2
  | @lam L Γ e τ1 τ2 _ ih => exact .lam L e ih
  | @fix L Γ e τ1 τ2 _ ih => exact .fix L e ih
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | @tlam Γ e τ _ ih =>
      refine .lam ∅ e (fun x _ => ?_)
      rwa [open', ← open_lc 0 (Exp.fvar x) e ih]
  | tapp _ ih => exact .app ih (.lit _)
  | tfold _ ih => exact ih
  | tunfold _ ih =>
      refine .app (.lam ∅ (.bvar 0) (fun x _ => ?_)) ih
      simp [open', openRec]; exact .fvar x
  | tpack _ ih => exact ih
  | @tunpack L Γ e1 e2 τ τ2 _ _ ih1 ih2 => exact .app (.lam L e2 ih2) ih1
  | alloc _ ih => exact .alloc ih
  | load _ ih => exact .load ih
  | store _ _ ih1 ih2 => exact .store ih1 ih2
  | alloc_tape _ ih => exact .tape ih
  | rand _ _ ih1 ih2 => exact .rand ih1 ih2
  | rand_unit _ _ ih1 ih2 => exact .rand ih1 ih2
  | scrut _ _ ih => exact .scrut _ ih

/-- A free variable of a binder body, opened at a fresh atom, lies in the context's domain. -/
private theorem isSome_of_mem_fv_open {L : Finset Var}
    {x : Var} (ih : ∀ y ∉ L, ∀ z ∈ (open' e (.fvar y)).fv, (Γ.insert y τ z).isSome)
    (hx : x ∈ e.fv) : (Γ x).isSome := by
  obtain ⟨y, hy⟩ := HasFresh.fresh_exists (L ∪ {x})
  have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
  have hxy : x ≠ y := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h.symm))
  have hres := ih y hyL x (fv_subset_open e y hx)
  unfold Tctx.insert at hres
  rwa [ite_eq_right hxy] at hres

/-- Every typed expression's free variables lie in the typing context's domain. -/
theorem Typed.fvSubset
    (h : Typed Γ e τ) : ∀ x ∈ e.fv, (Γ x).isSome := by
  induction h with
  | fvar hx =>
    intro x hx'
    simp [fv, Finset.mem_singleton] at hx'
    subst hx'; rw [hx]; rfl
  | lit_int | lit_bool | lit_unit | lit_real | urand => intro x hx; simp [fv] at hx
  | binop_real _ _ _ ih1 ih2 | binop_int _ _ _ ih1 ih2 | binop_bool _ _ _ ih1 ih2
  | unboxed_eq _ _ _ ih1 ih2 | pair _ _ ih1 ih2 | app _ _ ih1 ih2
  | store _ _ ih1 ih2 | rand _ _ ih1 ih2 | rand_unit _ _ ih1 ih2 =>
    intro x hx
    simp only [fv, Finset.mem_union] at hx
    exact hx.elim (ih1 x) (ih2 x)
  | unop_int _ _ ih | unop_bool _ _ ih | unop_real _ _ ih
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih | tapp _ ih
  | alloc _ ih | load _ ih | alloc_tape _ ih | scrut _ _ ih =>
    intro x hx; simp [fv] at hx; exact ih x hx
  | case _ _ _ ih0 ih1 ih2 | cond _ _ _ ih0 ih1 ih2 =>
    intro x hx
    simp only [fv, Finset.mem_union] at hx
    exact hx.elim (Or.elim · (ih0 x) (ih1 x)) (ih2 x)
  | lam _ _ ih | fix _ _ ih => exact fun x hx => isSome_of_mem_fv_open ih hx
  | tlam _ ih =>
    intro x hx
    have hres := ih x hx
    unfold Tctx.shift at hres
    rwa [Option.isSome_map] at hres
  | tfold _ ih | tpack _ ih => exact ih
  | tunfold _ ih =>
    intro x hx
    apply ih
    simpa [fv, recUnfold] using hx
  | tunpack _ _ _ ih1 ih2 =>
    intro x hx
    simp only [fv, Finset.mem_union] at hx
    refine hx.elim (fun hx => ?_) (ih1 x)
    have hres := isSome_of_mem_fv_open ih2 hx
    unfold Tctx.shift at hres
    rwa [Option.isSome_map] at hres

/-- Inserting two distinct atoms commutes. -/
theorem Tctx.insert_swap (Γ : Tctx) {x z : Var} (hxz : x ≠ z) (τ τ' : Ty) :
    (Γ.insert x τ).insert z τ' = (Γ.insert z τ').insert x τ := by
  funext w
  simp only [Tctx.insert]
  by_cases hwz : w = z
  · subst hwz
    have : ¬ (w = x) := fun h => hxz (h ▸ rfl)
    rw [ite_eq_left rfl, ite_eq_right this, ite_eq_left rfl]
  · rw [ite_eq_right hwz]
    by_cases hwx : w = x
    · rw [ite_eq_left hwx, ite_eq_left hwx]
    · rw [ite_eq_right hwx, ite_eq_right hwx, ite_eq_right hwz]

/-- A later insertion of the same atom overwrites the earlier one. -/
theorem Tctx.insert_overwrite (Γ : Tctx) (x : Var) (τ τ' : Ty) :
    (Γ.insert x τ).insert x τ' = Γ.insert x τ' := by
  funext y
  simp only [Tctx.insert]
  by_cases h : y = x
  · subst h; rw [ite_eq_left rfl, ite_eq_left rfl]
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h]

/-- Shifting the context commutes with insertion (the inserted type is shifted too). -/
theorem Tctx.shift_insert (Γ : Tctx) (x : Var) (τ : Ty) :
    (Γ.insert x τ).shift = Γ.shift.insert x τ.shift := by
  funext y
  simp only [Tctx.shift, Tctx.insert]
  by_cases h : y = x
  · subst h; rw [ite_eq_left rfl, ite_eq_left rfl]; rfl
  · rw [ite_eq_right h, ite_eq_right h]

/-! ## Renaming a context atom preserves typing -/

/-- `Typed.rename` for a context presented as `Γ.insert x τ_x`, so induction goes through; binder
cases swap the fresh atom past `x` and `y` (`Tctx.insert_swap`). -/
theorem Typed.rename_aux
    {Γ' : Tctx} (h : Typed Γ' e τ) :
    ∀ (x y : Var) (τ_x : Ty) (Γ : Tctx),
      Γ' = Γ.insert x τ_x → y ∉ e.fv ∪ {x} →
      Typed (Γ.insert y τ_x) (subst e x (Exp.fvar y)) τ := by
  induction h with
    (intro x y τ_x Γ heq hy; subst heq
     simp only [fv, subst, Finset.mem_union, Finset.mem_singleton, not_or] at hy ⊢)
  | @fvar Γ' z τ hz =>
      by_cases hxz : x = z
      · subst hxz
        rw [ite_eq_left rfl]
        obtain rfl : τ = τ_x := by simpa [Tctx.insert] using hz.symm
        exact .fvar (by simp [Tctx.insert])
      · rw [ite_eq_right hxz]
        exact .fvar (by simpa [Tctx.insert, Ne.symm hxz, Ne.symm hy.1] using hz)
  | lit_int | lit_bool | lit_unit | lit_real | urand => constructor
  | binop_real _ _ hop ih1 ih2 =>
      exact .binop_real (ih1 x y τ_x Γ rfl (by simp [hy])) (ih2 x y τ_x Γ rfl (by simp [hy])) hop
  | unop_real _ hop ih => exact .unop_real (ih x y τ_x Γ rfl (by simp [hy])) hop
  | binop_int _ _ hop ih1 ih2 =>
      exact .binop_int (ih1 x y τ_x Γ rfl (by simp [hy])) (ih2 x y τ_x Γ rfl (by simp [hy])) hop
  | binop_bool _ _ hop ih1 ih2 =>
      exact .binop_bool (ih1 x y τ_x Γ rfl (by simp [hy])) (ih2 x y τ_x Γ rfl (by simp [hy])) hop
  | unop_int _ hop ih => exact .unop_int (ih x y τ_x Γ rfl (by simp [hy])) hop
  | unop_bool _ hop ih => exact .unop_bool (ih x y τ_x Γ rfl (by simp [hy])) hop
  | unboxed_eq hu _ _ ih1 ih2 =>
      exact .unboxed_eq hu (ih1 x y τ_x Γ rfl (by simp [hy])) (ih2 x y τ_x Γ rfl (by simp [hy]))
  | pair _ _ ih1 ih2 =>
      exact .pair (ih1 x y τ_x Γ rfl (by simp [hy])) (ih2 x y τ_x Γ rfl (by simp [hy]))
  | fst _ ih => exact .fst (ih x y τ_x Γ rfl (by simp [hy]))
  | snd _ ih => exact .snd (ih x y τ_x Γ rfl (by simp [hy]))
  | inl _ ih => exact .inl (ih x y τ_x Γ rfl (by simp [hy]))
  | inr _ ih => exact .inr (ih x y τ_x Γ rfl (by simp [hy]))
  | case _ _ _ ih0 ih1 ih2 =>
      refine .case (ih0 x y τ_x Γ rfl ?_) (ih1 x y τ_x Γ rfl ?_) (ih2 x y τ_x Γ rfl ?_) <;>
        simp [hy]
  | cond _ _ _ ih0 ih1 ih2 =>
      refine .cond (ih0 x y τ_x Γ rfl ?_) (ih1 x y τ_x Γ rfl ?_) (ih2 x y τ_x Γ rfl ?_) <;>
        simp [hy]
  | @lam L Γ' e τ1 τ2 _ ih =>
      refine .lam (L ∪ {x, y}) fun z hz => ?_
      obtain ⟨hzx, hzy, hzL⟩ : z ≠ x ∧ z ≠ y ∧ z ∉ L := by simpa using hz
      rw [← subst_open_var z x (.fvar y) e hzx.symm (.fvar y),
        Tctx.insert_swap Γ hzy.symm τ_x τ1]
      refine ih z hzL x y τ_x (Γ.insert z τ1) (Tctx.insert_swap Γ hzx.symm τ_x τ1) ?_
      simp only [Finset.mem_union, Finset.mem_singleton, not_or]
      exact ⟨open_fresh_preserve_not_fvar e hy.1 hzy.symm, hy.2⟩
  | @fix L Γ' e τ1 τ2 _ ih =>
      refine .fix (L ∪ {x, y}) fun z hz => ?_
      obtain ⟨hzx, hzy, hzL⟩ : z ≠ x ∧ z ≠ y ∧ z ∉ L := by simpa using hz
      rw [← subst_open_var z x (.fvar y) e hzx.symm (.fvar y),
        Tctx.insert_swap Γ hzy.symm τ_x (.arrow τ1 τ2)]
      refine ih z hzL x y τ_x (Γ.insert z (.arrow τ1 τ2))
        (Tctx.insert_swap Γ hzx.symm τ_x (.arrow τ1 τ2)) ?_
      simp only [Finset.mem_union, Finset.mem_singleton, not_or]
      exact ⟨open_fresh_preserve_not_fvar e hy.1 hzy.symm, hy.2⟩
  | app _ _ ih1 ih2 =>
      exact .app (ih1 x y τ_x Γ rfl (by simp [hy])) (ih2 x y τ_x Γ rfl (by simp [hy]))
  | tlam _ ih =>
      refine .tlam ?_
      rw [Tctx.shift_insert]
      exact ih x y τ_x.shift Γ.shift (Tctx.shift_insert Γ x τ_x) (by simp [hy])
  | tapp _ ih => exact .tapp (ih x y τ_x Γ rfl (by simp [hy]))
  | tfold _ ih => exact .tfold (ih x y τ_x Γ rfl (by simp [hy]))
  | tunfold _ ih =>
      rw [show subst recUnfold x (Exp.fvar y) = recUnfold by
        simp [recUnfold, subst]]
      exact .tunfold (ih x y τ_x Γ rfl (by simp [hy]))
  | tpack _ ih => exact .tpack (ih x y τ_x Γ rfl (by simp [hy]))
  | @tunpack L Γ' e1 e2 τ τ2 _ _ ih1 ih2 =>
      refine .tunpack (L ∪ {x, y}) (ih1 x y τ_x Γ rfl (by simp [hy])) fun z hz => ?_
      obtain ⟨hzx, hzy, hzL⟩ : z ≠ x ∧ z ≠ y ∧ z ∉ L := by simpa using hz
      rw [← subst_open_var z x (.fvar y) e2 hzx.symm (.fvar y),
        Tctx.shift_insert, Tctx.insert_swap Γ.shift hzy.symm τ_x.shift τ]
      refine ih2 z hzL x y τ_x.shift (Γ.shift.insert z τ) ?_ ?_
      · rw [Tctx.shift_insert, Tctx.insert_swap Γ.shift hzx.symm τ_x.shift τ]
      simp only [Finset.mem_union, Finset.mem_singleton, not_or]
      exact ⟨open_fresh_preserve_not_fvar e2 hy.1.1 hzy.symm, hy.2⟩
  | alloc _ ih => exact .alloc (ih x y τ_x Γ rfl (by simp [hy]))
  | load _ ih => exact .load (ih x y τ_x Γ rfl (by simp [hy]))
  | store _ _ ih1 ih2 =>
      exact .store (ih1 x y τ_x Γ rfl (by simp [hy])) (ih2 x y τ_x Γ rfl (by simp [hy]))
  | alloc_tape _ ih => exact .alloc_tape (ih x y τ_x Γ rfl (by simp [hy]))
  | rand _ _ ih1 ih2 =>
      exact .rand (ih1 x y τ_x Γ rfl (by simp [hy])) (ih2 x y τ_x Γ rfl (by simp [hy]))
  | rand_unit _ _ ih1 ih2 =>
      exact .rand_unit (ih1 x y τ_x Γ rfl (by simp [hy])) (ih2 x y τ_x Γ rfl (by simp [hy]))
  | scrut _ hp ih => exact .scrut (ih x y τ_x Γ rfl (by simp [hy])) hp

variable {α : Type _}

/-- Renaming the context atom `x` to a fresh `y` preserves typing. -/
theorem Typed.rename {Γ : Tctx} {e : Exp α} {τ τ_x : Ty}
    (x y : Var) (h : Typed (Γ.insert x τ_x) e τ) (hy : y ∉ e.fv ∪ {x}) :
    Typed (Γ.insert y τ_x) (subst e x (Exp.fvar y)) τ :=
  Typed.rename_aux h x y τ_x Γ rfl hy

/-! ## Lifting a single-atom typing to the cofinite binder premises

`ContextualRefinement` uses these to build `Typed.lam` / `Typed.fix` / `Typed.tunpack`. -/

/-- A typing at one atom lifts to every fresh atom. -/
theorem Typed.rename_lam {Γ : Tctx} {x : Var} {e : Exp α} {τ τ' : Ty}
    (he : Typed (Γ.insert x τ) e τ') :
    ∀ y ∉ insert x e.fv,
      Typed (Γ.insert y τ) (open' (close e x) (Exp.fvar y)) τ' := fun y hy => by
  rw [open_close_subst_lc x y e he.isLocallyClosed]
  exact he.rename x y (by rwa [Finset.union_comm, ← Finset.insert_eq])

/-- `Typed.rename_lam` for `fix` premises. -/
theorem Typed.rename_fix {Γ : Tctx} {f : Var} {e : Exp α} {τ τ' : Ty}
    (he : Typed (Γ.insert f (.arrow τ τ')) e (.arrow τ τ')) :
    ∀ g ∉ insert f e.fv,
      Typed (Γ.insert g (.arrow τ τ')) (open' (close e f) (Exp.fvar g)) (.arrow τ τ') :=
  rename_lam he

/-- `Typed.rename_lam` for `tunpack` premises. -/
theorem Typed.rename_unpack {Γ : Tctx} {x : Var} {e2 : Exp α} {τ τ2 : Ty}
    (he2 : Typed (Γ.shift.insert x τ) e2 τ2.shift) :
    ∀ y ∉ insert x e2.fv,
      Typed (Γ.shift.insert y τ) (open' (close e2 x) (Exp.fvar y)) τ2.shift :=
  rename_lam he2

end ProbLang
