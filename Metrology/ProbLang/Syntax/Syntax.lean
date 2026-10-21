module

public meta import Metrology.Meta.Discrete
public import Std
public import Std.Data.ExtTreeMap.Lemmas
public import Mathlib.Basic.Countable.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Tactic.DeriveCountable
import all Mathlib.Tactic.DeriveCountable
public import Mathlib.Logic.Equiv.List
public import Cslib.Foundations.Data.HasFresh
public import Cslib.Foundations.Syntax.HasSubstitution
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.Probability.Distributions.Uniform

meta import Metrology.Meta

/-! # ProbLang syntax

The reals interface (`ProbLangℝ`, `LawfulProbLangℝ`), expressions (`Exp`, `Ty`, `Pat`), values,
operator evaluation, states, and evaluation contexts with their decomposition (`Exp.decomp`). -/

@[expose] public section

open Std
open Cslib

/-! ## Library helpers -/

/-- A key larger than every key in the map. -/
def Std.ExtTreeMap.fresh (t : ExtTreeMap Int V) : Int :=
  match t.maxKey? with | none => 1 | some v => v + 1

theorem Std.ExtTreeMap.fresh_get? (t : ExtTreeMap Int V) :
    t[t.fresh]? = none := by
  unfold ExtTreeMap.fresh
  rcases hM : t.maxKey? with _ | v
  · simp [maxKey?_eq_none_iff.mp hM]
  · apply getElem?_eq_none
    intro hmem
    have hle := ExtTreeMap.le_maxKey?_of_mem hmem
      (Option.get_of_eq_some (isSome_maxKey?_of_mem hmem) hM)
    simp [compare, compareOfLessAndEq] at hle

/-- `maxKey?` in `getElem?` and `<` terms, the form measurability arguments need. -/
theorem Std.ExtTreeMap.maxKey?_eq_some_iff_getElem? (t : ExtTreeMap Int V) (n : Int) :
    t.maxKey? = some n ↔ t[n]?.isSome ∧ ∀ k : Int, n < k → t[k]?.isNone := by
  rw [maxKey?_eq_some_iff_mem_and_forall, mem_iff_isSome_getElem?]
  refine and_congr_right fun _ => ⟨fun h k hlt => ?_, fun h k hkmem => ?_⟩
  · rcases hk : t[k]? with _ | v
    · simp
    · have hkmem : k ∈ t := mem_iff_isSome_getElem?.mpr (by rw [hk]; rfl)
      have : k ≤ n := (Std.LawfulOrderOrd.isLE_compare k n).mp (h k hkmem)
      omega
  · rw [Std.LawfulOrderOrd.isLE_compare]
    by_contra hgt
    have hkNone := h k (lt_of_not_ge hgt)
    have hkSome := mem_iff_isSome_getElem?.mp hkmem
    rcases hk : t[k]? with _ | v
    · rw [hk] at hkSome; simp at hkSome
    · rw [hk] at hkNone; simp at hkNone

-- TODO: PR back to mathlib
instance instCountableChar : Countable Char where
  exists_injective_nat' := by
    exists (·.1.toNat)
    rintro ⟨v1, _⟩ ⟨v2, _⟩
    simp only [Char.mk.injEq]
    exact UInt32.toNat_inj.mp

-- TODO: PR back to mathlib
instance instCountableString : Countable String where
  exists_injective_nat' := by
    have ⟨f, hf⟩ : Countable (List Char) := by infer_instance
    exists (fun s => f s.toList)
    exact fun _ _ h => String.toList_inj.mp (hf h)

namespace ProbLang

/-! ## Variables and locations -/

/-- Free variables: user-named, or generated internally. -/
@[uncurriedProjections, constructors]
inductive Var : Type where
  | named (s : String)
  | internal (n : Nat)
  deriving Inhabited, DecidableEq, Countable, Repr, BEq

instance : Coe String Var := ⟨.named⟩

instance : Coe Nat Var := ⟨.internal⟩

/-- The index of an internal variable (0 for named ones). -/
def Var.genId : Var → Nat | .named _ => 0 | .internal n => n

instance : Cslib.HasFresh Var where
  fresh s := .internal <| s.sup (·.genId) + 1
  fresh_notMem L := by
    rw [← Finset.forall_mem_not_eq]
    intro b hb
    rcases b with (_|n); (· simp)
    simp only [Var.internal.injEq]
    refine Nat.ne_of_gt (Order.lt_add_one_iff.mpr ?_)
    apply Finset.le_sup_of_le hb
    simp [Var.genId]

/-- Heap locations. -/
abbrev Loc : Type := Int

/-- Tape labels. -/
abbrev Lbl : Type := Int

/-! ## The type of reals -/

/-- The operations ProbLang needs on its type of reals. This class is pure data, so a
computable type such as `Float` can be an instance and run in the interpreter; the laws
the semantics needs live in `LawfulProbLangℝ`. -/
class ProbLangℝ (T : Type _) extends BEq T, Inhabited T where
  -- The operations are plain functions, not `LT`/`LE`/`Add`/`Neg` instances, to avoid
  -- `DecidableEq`/order/algebra diamonds.
  realLt : T → T → Bool
  realLe : T → T → Bool
  realAdd : T → T → T
  realNeg : T → T
  realOfInt : Int → T
  /-- Lets a program generic in the reals write a constant such as `1/2`. -/
  realOfRat : ℚ → T
  /-- Intended: `realFrac r ∈ [0,1)` with `r - realFrac r` integral. The class demands only
  measurability; laws that need more (e.g. rotation-invariance of `unifUnit`) are proved
  per instance. -/
  realFrac : T → T

/-- A type of reals with a σ-algebra and the laws the semantics needs. -/
class LawfulProbLangℝ (T : Type _) extends ProbLangℝ T, MeasurableSpace T, LawfulBEq T,
    MeasurableEq T where
  /-- Decidable equality, kept as data to avoid a diamond with `BEq`. -/
  instDecidableEq : DecidableEq T
  /-- The uniform distribution on the unit interval, sampled by `urand`. -/
  unifUnit : MeasureTheory.Measure T
  unifUnit_isProbabilityMeasure : MeasureTheory.IsProbabilityMeasure unifUnit
  /-- A measurable set carrying all of `unifUnit`'s mass (at `ℝ`: `(0, 1)`). -/
  unifUnitSupport : Set T
  unifUnitSupportMeasurable : MeasurableSet unifUnitSupport
  unifUnitIsConcentrated : unifUnit unifUnitSupportᶜ = 0
  measurable_realLt : Measurable (Function.uncurry realLt)
  measurable_realLe : Measurable (Function.uncurry realLe)
  measurable_realAdd : Measurable (Function.uncurry realAdd)
  measurable_realNeg : Measurable realNeg
  measurable_realFrac : Measurable realFrac

attribute [reducible, instance] LawfulProbLangℝ.instDecidableEq
attribute [instance] LawfulProbLangℝ.unifUnit_isProbabilityMeasure

theorem LawfulProbLangℝ.unifUnitSupport_nonempty (T : Type _) [LawfulProbLangℝ T] :
    (LawfulProbLangℝ.unifUnitSupport (T := T)).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  rintro hempty
  have h1 : LawfulProbLangℝ.unifUnit (Set.univ : Set T) = 0 := by
    have : (LawfulProbLangℝ.unifUnitSupport (T := T))ᶜ = Set.univ := by rw [hempty]; simp
    rw [← this]; exact LawfulProbLangℝ.unifUnitIsConcentrated
  rw [MeasureTheory.measure_univ] at h1
  exact one_ne_zero h1

/-! ## Syntax: literals, operators, types, patterns, expressions -/

/-- Literals: integers, booleans, unit, locations, labels and reals. -/
@[uncurriedProjections, constructors]
inductive BaseLit (rT : Type _)
  | int (z : Int)
  | bool (b : Bool)
  | unit
  | loc (loc : Loc)
  | lbl (lbl : Lbl)
  | real (r : rT)
  deriving Countable, BEq, Repr

/-- Unary operators. -/
@[uncurriedProjections, constructors]
inductive UnOp
  /-- Boolean not (`~e`). -/
  | neg
  /-- Arithmetic negation on ints and reals (`-e`). -/
  | minus
  /-- Int to real coercion. -/
  | toReal
  /-- Fractional part of a real. -/
  | frac
  deriving Inhabited, Countable, Repr, BEq

/-- Binary operators; `and`, `or`, `xor` are boolean only, and `eq` works on literals and on
`inl`/`inr` of literals. -/
@[uncurriedProjections, constructors]
inductive BinOp | plus | minus | mult | div | mod | and | or | xor | eq | lt | le | shl | shr
  deriving Inhabited, Countable, Repr, BEq

/-- System F_μ_ref types with tapes, used only by `Typed` (Types.lean) and contextual refinement;
`pl_ty(…)` covers only the monomorphic part. -/
@[uncurriedProjections, constructors]
inductive Ty
  | int | bool | unit
  | real
  | prod (τ1 τ2 : Ty)
  | sum (τ1 τ2 : Ty)
  | arrow (τ1 τ2 : Ty)
  | ref (τ : Ty)
  | tape
  /-- De Bruijn type variable. -/
  | var (n : Nat)
  /-- Iso-recursive type; binds `var 0` in `τ`. -/
  | rec' (τ : Ty)
  /-- Universal type; binds `var 0` in `τ`. -/
  | forall' (τ : Ty)
  /-- Existential type; binds `var 0` in `τ`. -/
  | exists' (τ : Ty)
  deriving Inhabited, DecidableEq, Countable, Repr, BEq

/-- Patterns for `scrut`. -/
@[uncurriedProjections, constructors]
inductive Pat (rT : Type _)
  | wildcard
  | lit (b : BaseLit rT)
  | pair (p1 p2 : Pat rT)
  | inl (p : Pat rT)
  | inr (p : Pat rT)
  deriving Inhabited, Countable, BEq, Repr

/-- ProbLang expressions, with de Bruijn bound variables and named free variables. -/
@[uncurriedProjections, constructors]
inductive Exp (rT : Type _)
  | bvar (n : Nat)
  | fvar (x : Var)
  | lit (b : BaseLit rT)
  /-- Binds its argument. -/
  | lam (e : Exp rT)
  /-- Binds the whole expression. -/
  | fix (e : Exp rT)
  | app (e1 e2 : Exp rT)
  | unop (u : UnOp) (e : Exp rT)
  | binop (b : BinOp) (e1 e2 : Exp rT)
  | cond (ec et ef : Exp rT)
  | pair (e1 e2 : Exp rT)
  | fst (e : Exp rT)
  | snd (e : Exp rT)
  | inl (e : Exp rT)
  | inr (e : Exp rT)
  /-- Branches `el`/`er` are functions, applied to the `inl`/`inr` payload; no binder. -/
  | case (ec el er : Exp rT)
  | alloc (e : Exp rT)
  | load (e : Exp rT)
  | store (el ev : Exp rT)
  /-- Allocate a random tape with bound `e`. -/
  | tape (e : Exp rT)
  /-- Uniform sample from `[0, en)`; `et` is a tape label, or `()` for an untaped draw. -/
  | rand (en et : Exp rT)
  /-- Has no step: a stuck term. -/
  | fail
  /-- Continuous uniform sample from the unit interval. -/
  | urand
  /-- Matches `e` against `pat`: `inl bindings` (see `Pat.tryMatch`) or `inr ()`. -/
  | scrut (e : Exp rT) (pat : Pat rT)
  deriving Inhabited, Countable, BEq, Repr

section WithRealParam

variable {rT : Type _} [ProbLangℝ rT]

/-- A type annotation that is erased. -/
@[reducible] def Exp.annotated (_τ : Ty) (e : Exp rT) : Exp rT := e

namespace Exp

/-! ### Open, close, substitute, free variables -/

/-- Replaces bound variable `i` by `sub`. -/
@[simp, scoped grind =] def openRec (i : Nat) (sub : Exp rT) : Exp rT → Exp rT
  | bvar j => if i = j then sub else bvar j
  | fvar x => fvar x
  | lit b => lit b
  | lam e => lam (openRec (i+1) sub e)
  | fix e => fix (openRec (i+1) sub e)
  | app e1 e2 => app (openRec i sub e1) (openRec i sub e2)
  | unop op e => unop op (openRec i sub e)
  | binop op e1 e2 => binop op (openRec i sub e1) (openRec i sub e2)
  | cond ec et ef => cond (openRec i sub ec) (openRec i sub et) (openRec i sub ef)
  | pair e1 e2 => pair (openRec i sub e1) (openRec i sub e2)
  | fst e => fst (openRec i sub e)
  | snd e => snd (openRec i sub e)
  | inl e => inl (openRec i sub e)
  | inr e => inr (openRec i sub e)
  | case ec el er => case (openRec i sub ec) (openRec i sub el) (openRec i sub er)
  | alloc e => alloc (openRec i sub e)
  | load e => load (openRec i sub e)
  | store e1 e2 => store (openRec i sub e1) (openRec i sub e2)
  | tape e => tape (openRec i sub e)
  | rand e1 e2 => rand (openRec i sub e1) (openRec i sub e2)
  | fail => fail
  | urand => urand
  | scrut e p => scrut (openRec i sub e) p

/-- Instantiates the outermost bound variable with `sub`. -/
@[simp, scoped grind =] def open' (e sub : Exp rT) : Exp rT := openRec 0 sub e

/-- Replaces the free variable `x` by bound variable `i`. -/
@[simp, scoped grind =] def closeRec (i : Nat) (x : Var) : Exp rT → Exp rT
  | bvar j => bvar j
  | fvar y => if x = y then bvar i else fvar y
  | lit b => lit b
  | lam e => lam (closeRec (i+1) x e)
  | fix e => fix (closeRec (i+1) x e)
  | app e1 e2 => app (closeRec i x e1) (closeRec i x e2)
  | unop op e => unop op (closeRec i x e)
  | binop op e1 e2 => binop op (closeRec i x e1) (closeRec i x e2)
  | cond ec et ef => cond (closeRec i x ec) (closeRec i x et) (closeRec i x ef)
  | pair e1 e2 => pair (closeRec i x e1) (closeRec i x e2)
  | fst e => fst (closeRec i x e)
  | snd e => snd (closeRec i x e)
  | inl e => inl (closeRec i x e)
  | inr e => inr (closeRec i x e)
  | case ec el er => case (closeRec i x ec) (closeRec i x el) (closeRec i x er)
  | alloc e => alloc (closeRec i x e)
  | load e => load (closeRec i x e)
  | store e1 e2 => store (closeRec i x e1) (closeRec i x e2)
  | tape e => tape (closeRec i x e)
  | rand e1 e2 => rand (closeRec i x e1) (closeRec i x e2)
  | fail => fail
  | urand => urand
  | scrut e p => scrut (closeRec i x e) p

/-- Abstracts the free variable `x` as the outermost bound variable. -/
@[simp, scoped grind =] def close (e : Exp rT) (x : Var) : Exp rT := closeRec 0 x e

/-- Substitutes `sub` for the free variable `x`. -/
@[simp, scoped grind =] def subst (e : Exp rT) (x : Var) (sub : Exp rT) : Exp rT :=
  match e with
  | bvar j => bvar j
  | fvar y => if x = y then sub else fvar y
  | lit b => lit b
  | lam e => lam (subst e x sub)
  | fix e => fix (subst e x sub)
  | app e1 e2 => app (subst e1 x sub) (subst e2 x sub)
  | unop op e => unop op (subst e x sub)
  | binop op e1 e2 => binop op (subst e1 x sub) (subst e2 x sub)
  | cond ec et ef => cond (subst ec x sub) (subst et x sub) (subst ef x sub)
  | pair e1 e2 => pair (subst e1 x sub) (subst e2 x sub)
  | fst e => fst (subst e x sub)
  | snd e => snd (subst e x sub)
  | inl e => inl (subst e x sub)
  | inr e => inr (subst e x sub)
  | case ec el er => case (subst ec x sub) (subst el x sub) (subst er x sub)
  | alloc e => alloc (subst e x sub)
  | load e => load (subst e x sub)
  | store e1 e2 => store (subst e1 x sub) (subst e2 x sub)
  | tape e => tape (subst e x sub)
  | rand e1 e2 => rand (subst e1 x sub) (subst e2 x sub)
  | fail => fail
  | urand => urand
  | scrut e p => scrut (subst e x sub) p

instance : HasSubstitution (Exp rT) Var (Exp rT) where
  subst := Exp.subst

/-- The free variables of an expression. -/
@[simp, scoped grind =] def fv : Exp rT → Finset Var
  | bvar _ => {}
  | fvar x => {x}
  | lit _ => {}
  | lam e => fv e
  | fix e => fv e
  | app e1 e2 => fv e1 ∪ fv e2
  | unop _ e => fv e
  | binop _ e1 e2 => fv e1 ∪ fv e2
  | cond ec et ef => fv ec ∪ fv et ∪ fv ef
  | pair e1 e2 => fv e1 ∪ fv e2
  | fst e => fv e
  | snd e => fv e
  | inl e => fv e
  | inr e => fv e
  | case ec el er => fv ec ∪ fv el ∪ fv er
  | alloc e => fv e
  | load e => fv e
  | store e1 e2 => fv e1 ∪ fv e2
  | tape e => fv e
  | rand e1 e2 => fv e1 ∪ fv e2
  | fail => {}
  | urand => {}
  | scrut e _ => fv e

/-! ### Local closedness -/

/-- No dangling bound variables, using cofinite quantification at binders. -/
inductive IsLocallyClosed : Exp rT → Prop
  | fvar (x : Var) :
    IsLocallyClosed (fvar x)
  | lit (b : BaseLit rT) :
    IsLocallyClosed (lit b)
  | lam (L : Finset Var) (e : Exp rT) :
    (∀ x ∉ L, IsLocallyClosed (open' e (fvar x))) →
    IsLocallyClosed (lam e)
  | fix (L : Finset Var) (e : Exp rT) :
    (∀ x ∉ L, IsLocallyClosed (open' e (fvar x))) →
    IsLocallyClosed (fix e)
  | app {e1 e2} :
    IsLocallyClosed e1 →
    IsLocallyClosed e2 →
    IsLocallyClosed (app e1 e2)
  | unop (op : UnOp) {e} :
    IsLocallyClosed e →
    IsLocallyClosed (unop op e)
  | binop (op : BinOp) {e1 e2} :
    IsLocallyClosed e1 →
    IsLocallyClosed e2 →
    IsLocallyClosed (binop op e1 e2)
  | cond {ec et ef} :
    IsLocallyClosed ec →
    IsLocallyClosed et →
    IsLocallyClosed ef →
    IsLocallyClosed (cond ec et ef)
  | pair {e1 e2} :
    IsLocallyClosed e1 →
    IsLocallyClosed e2 →
    IsLocallyClosed (pair e1 e2)
  | fst {e} :
    IsLocallyClosed e →
    IsLocallyClosed (fst e)
  | snd {e} :
    IsLocallyClosed e →
    IsLocallyClosed (snd e)
  | inl {e} :
    IsLocallyClosed e →
    IsLocallyClosed (inl e)
  | inr {e} :
    IsLocallyClosed e →
    IsLocallyClosed (inr e)
  | case {ec el er} :
    IsLocallyClosed ec →
    IsLocallyClosed el →
    IsLocallyClosed er →
    IsLocallyClosed (case ec el er)
  | alloc {e} :
    IsLocallyClosed e →
    IsLocallyClosed (alloc e)
  | load {e} :
    IsLocallyClosed e →
    IsLocallyClosed (load e)
  | store {e1 e2} :
    IsLocallyClosed e1 →
    IsLocallyClosed e2 →
    IsLocallyClosed (store e1 e2)
  | tape {e} :
    IsLocallyClosed e →
    IsLocallyClosed (tape e)
  | rand {e1 e2} :
    IsLocallyClosed e1 →
    IsLocallyClosed e2 →
    IsLocallyClosed (rand e1 e2)
  | fail :
    IsLocallyClosed fail
  | urand :
    IsLocallyClosed urand
  | scrut {e} (p : Pat rT) :
    IsLocallyClosed e →
    IsLocallyClosed (scrut e p)

attribute [scoped grind .]
  IsLocallyClosed.fvar
  IsLocallyClosed.lit
  IsLocallyClosed.app
  IsLocallyClosed.unop
  IsLocallyClosed.binop
  IsLocallyClosed.cond
  IsLocallyClosed.pair
  IsLocallyClosed.fst
  IsLocallyClosed.snd
  IsLocallyClosed.inl
  IsLocallyClosed.inr
  IsLocallyClosed.case
  IsLocallyClosed.alloc
  IsLocallyClosed.load
  IsLocallyClosed.store
  IsLocallyClosed.tape
  IsLocallyClosed.rand
  IsLocallyClosed.fail
  IsLocallyClosed.urand
  IsLocallyClosed.scrut

/-- Number of nodes; the termination measure for `Exp.decomp`. -/
@[simp]
def size : Exp α → Nat
  | bvar _ | fvar _ | lit _ => 1
  | lam e => 1 + e.size
  | fix e => 1 + e.size
  | app e1 e2 => 1 + e1.size + e2.size
  | binop _ e1 e2 => 1 + e1.size + e2.size
  | pair e1 e2 => 1 + e1.size + e2.size
  | store e1 e2 => 1 + e1.size + e2.size
  | rand e1 e2 => 1 + e1.size + e2.size
  | unop _ e => 1 + e.size
  | fst e => 1 + e.size
  | snd e => 1 + e.size
  | inl e => 1 + e.size
  | inr e => 1 + e.size
  | alloc e => 1 + e.size
  | load e => 1 + e.size
  | tape e => 1 + e.size
  | .cond e0 e1 e2 => 1 + e0.size + e1.size + e2.size
  | .case e0 e1 e2 => 1 + e0.size + e1.size + e2.size
  | scrut e _ => 1 + e.size
  | fail => 1
  | urand => 1

/-- Decides local closedness under `k` binders: `lcb 0 e ↔ IsLocallyClosed e`. -/
def lcb (k : Nat) : Exp α → Bool
  | .bvar j => decide (j < k)
  | .fvar _ | .lit _ | .fail | .urand => true
  | .lam e | .fix e => lcb (k+1) e
  | .app e1 e2 | .binop _ e1 e2 | .pair e1 e2 | .store e1 e2 | .rand e1 e2 =>
      lcb k e1 && lcb k e2
  | .cond e0 e1 e2 | .case e0 e1 e2 => lcb k e0 && lcb k e1 && lcb k e2
  | .unop _ e | .fst e | .snd e | .inl e | .inr e | .alloc e | .load e | .tape e | .scrut e _ =>
      lcb k e

theorem lcb_openRec_fvar (x : Var) : ∀ (k : Nat) (e : Exp α),
    lcb (k+1) e = true → lcb k (openRec k (fvar x) e) = true := by
  intro k e
  induction e generalizing k with
  | bvar j =>
      intro h
      simp only [lcb, decide_eq_true_eq] at h
      simp only [openRec]
      split
      · rfl
      · simp only [lcb, decide_eq_true_eq]; omega
  | _ => intro h; simp_all [lcb, openRec]

theorem size_openRec_fvar (x : Var) : ∀ (k : Nat) (e : Exp α),
    (openRec k (fvar x) e).size = e.size := by
  intro k e
  induction e generalizing k with
  | bvar j => simp only [openRec]; split <;> rfl
  | _ => simp_all [openRec, Exp.size]

private theorem lcb_imp_lc_aux : ∀ (n : Nat) (e : Exp α), e.size ≤ n → lcb 0 e = true →
    IsLocallyClosed e := by
  intro n
  -- Fuel on size: the `lam`/`fix` cases recurse on `open' e (fvar x)`, not a subterm
  -- (`size_openRec_fvar`).
  induction n with
  | zero => intro e he _; exfalso; cases e <;> simp [Exp.size] at he
  | succ n ih =>
      intro e hle hlc
      cases e with
      | bvar j => simp [lcb] at hlc
      | fvar x => exact .fvar x
      | lit b => exact .lit b
      | fail => exact .fail
      | urand => exact .urand
      | lam e =>
          refine .lam ∅ e (fun x _ => ?_)
          refine ih (open' e (fvar x)) ?_ ?_
          · rw [open', size_openRec_fvar]; simp only [Exp.size] at hle; omega
          · exact lcb_openRec_fvar x 0 e (by simpa [lcb] using hlc)
      | fix e =>
          refine .fix ∅ e (fun x _ => ?_)
          refine ih (open' e (fvar x)) ?_ ?_
          · rw [open', size_openRec_fvar]; simp only [Exp.size] at hle; omega
          · exact lcb_openRec_fvar x 0 e (by simpa [lcb] using hlc)
      | app e1 e2 =>
          simp only [lcb, Bool.and_eq_true] at hlc; simp only [Exp.size] at hle
          exact .app (ih e1 (by omega) hlc.1) (ih e2 (by omega) hlc.2)
      | unop op e =>
          simp only [lcb] at hlc; simp only [Exp.size] at hle
          exact .unop op (ih e (by omega) hlc)
      | binop op e1 e2 =>
          simp only [lcb, Bool.and_eq_true] at hlc; simp only [Exp.size] at hle
          exact .binop op (ih e1 (by omega) hlc.1) (ih e2 (by omega) hlc.2)
      | cond e0 e1 e2 =>
          simp only [lcb, Bool.and_eq_true] at hlc; simp only [Exp.size] at hle
          exact .cond (ih e0 (by omega) hlc.1.1) (ih e1 (by omega) hlc.1.2) (ih e2 (by omega) hlc.2)
      | pair e1 e2 =>
          simp only [lcb, Bool.and_eq_true] at hlc; simp only [Exp.size] at hle
          exact .pair (ih e1 (by omega) hlc.1) (ih e2 (by omega) hlc.2)
      | fst e =>
          simp only [lcb] at hlc; simp only [Exp.size] at hle
          exact .fst (ih e (by omega) hlc)
      | snd e =>
          simp only [lcb] at hlc; simp only [Exp.size] at hle
          exact .snd (ih e (by omega) hlc)
      | inl e =>
          simp only [lcb] at hlc; simp only [Exp.size] at hle
          exact .inl (ih e (by omega) hlc)
      | inr e =>
          simp only [lcb] at hlc; simp only [Exp.size] at hle
          exact .inr (ih e (by omega) hlc)
      | case e0 e1 e2 =>
          simp only [lcb, Bool.and_eq_true] at hlc; simp only [Exp.size] at hle
          exact .case (ih e0 (by omega) hlc.1.1) (ih e1 (by omega) hlc.1.2) (ih e2 (by omega) hlc.2)
      | alloc e =>
          simp only [lcb] at hlc; simp only [Exp.size] at hle
          exact .alloc (ih e (by omega) hlc)
      | load e =>
          simp only [lcb] at hlc; simp only [Exp.size] at hle
          exact .load (ih e (by omega) hlc)
      | store e1 e2 =>
          simp only [lcb, Bool.and_eq_true] at hlc; simp only [Exp.size] at hle
          exact .store (ih e1 (by omega) hlc.1) (ih e2 (by omega) hlc.2)
      | tape e =>
          simp only [lcb] at hlc; simp only [Exp.size] at hle
          exact .tape (ih e (by omega) hlc)
      | rand e1 e2 =>
          simp only [lcb, Bool.and_eq_true] at hlc; simp only [Exp.size] at hle
          exact .rand (ih e1 (by omega) hlc.1) (ih e2 (by omega) hlc.2)
      | scrut e p =>
          simp only [lcb] at hlc; simp only [Exp.size] at hle
          exact .scrut p (ih e (by omega) hlc)

theorem lcb_imp_lc {e : Exp α} (h : lcb 0 e = true) : IsLocallyClosed e :=
  lcb_imp_lc_aux e.size e le_rfl h

theorem lcb_openRec_fvar_rev (x : Var) : ∀ (k : Nat) (e : Exp α),
    lcb k (openRec k (fvar x) e) = true → lcb (k+1) e = true := by
  intro k e
  induction e generalizing k with
  | bvar j =>
      intro h
      simp only [openRec] at h
      split at h
      · simp only [lcb, decide_eq_true_eq]; omega
      · simp only [lcb, decide_eq_true_eq] at h ⊢; omega
  | _ => intro h; simp_all [lcb, openRec]

theorem lc_imp_lcb {e : Exp α} (h : IsLocallyClosed e) : lcb 0 e = true := by
  induction h with
  | lam L e' _ ih | fix L e' _ ih =>
      obtain ⟨x, hx⟩ := Cslib.HasFresh.fresh_exists L
      have hx' := ih x hx
      simp only [open'] at hx'
      simpa [lcb] using lcb_openRec_fvar_rev x 0 e' hx'
  | _ => simp_all [lcb]

end Exp

/-! ### Literals and pattern matching -/

-- Hand-written: `BaseLit` derives only `BEq`, and this instance needs just `[DecidableEq α]`.
instance [DecidableEq α] : DecidableEq (BaseLit α)
  | .int z1, .int z2 => decidable_of_iff (z1 = z2) (by simp)
  | .bool b1, .bool b2 => decidable_of_iff (b1 = b2) (by simp)
  | .unit, .unit => isTrue rfl
  | .loc l1, .loc l2 => decidable_of_iff (l1 = l2) (by simp)
  | .lbl l1, .lbl l2 => decidable_of_iff (l1 = l2) (by simp)
  | .real r1, .real r2 => decidable_of_iff (r1 = r2) (by simp)
  | .int _, .bool _ | .int _, .unit | .int _, .loc _ | .int _, .lbl _ | .int _, .real _
  | .bool _, .int _ | .bool _, .unit | .bool _, .loc _ | .bool _, .lbl _ | .bool _, .real _
  | .unit, .int _ | .unit, .bool _ | .unit, .loc _ | .unit, .lbl _ | .unit, .real _
  | .loc _, .int _ | .loc _, .bool _ | .loc _, .unit | .loc _, .lbl _ | .loc _, .real _
  | .lbl _, .int _ | .lbl _, .bool _ | .lbl _, .unit | .lbl _, .loc _ | .lbl _, .real _
  | .real _, .int _ | .real _, .bool _ | .real _, .unit | .real _, .loc _ | .real _, .lbl _ =>
      isFalse (by intro h; cases h)

/-- Matches `p` against `e`. On success returns the bindings: `e` itself at a wildcard, `()` at a
literal, the pair of sub-bindings at a pair, and the inner bindings under inl/inr. -/
def Pat.tryMatch : Pat rT → Exp rT → Option (Exp rT)
  | .wildcard, e => some e
  | .lit b, .lit b' => if b == b' then some (.lit .unit) else none
  | .pair p1 p2, .pair e1 e2 => do
      let b1 ← p1.tryMatch e1
      let b2 ← p2.tryMatch e2
      return .pair b1 b2
  | .inl p, .inl e => p.tryMatch e
  | .inr p, .inr e => p.tryMatch e
  | _, _ => none

theorem BaseLit.beq_self_true [LawfulBEq rT] (l : BaseLit rT) : (l == l) = true := by
  cases l with
  | int z =>
    show (Int.decEq z z).decide = true
    exact decide_eq_true rfl
  | bool b => cases b <;> rfl
  | unit => rfl
  | loc l =>
    show decide (l = l) = true
    rw [decide_eq_true rfl]
  | lbl l => exact of_decide_eq_self_eq_true _
  | real r =>
    show (r == r) = true
    exact BEq.refl r

instance instLawfulBEqBaseLit [LawfulBEq rT] : LawfulBEq (BaseLit rT) where
  eq_of_beq {l1 l2} h := by
    cases l1 <;> cases l2 <;> simp_all <;>
      first
        | (exact (decide_eq_true_eq.mp h))
        | (exact LawfulBEq.eq_of_beq h)
  rfl {l} := BaseLit.beq_self_true l

theorem Pat.tryMatch_lit_eq [LawfulBEq rT] (l : BaseLit rT) :
    Pat.tryMatch (.lit l) (.lit l) = some (.lit .unit) := by
  show (if (l == l) = true then some (Exp.lit BaseLit.unit) else none) = _
  refine Option.ite_some_none_eq_some.mpr ⟨?_, rfl⟩
  exact BaseLit.beq_self_true l

theorem Pat.tryMatch_lit_ne {l1 l2 : BaseLit rT} (h : ¬ (l1 == l2) = true) :
    Pat.tryMatch (.lit l1) (.lit l2) = none := by
  show (if (l1 == l2) = true then some (Exp.lit BaseLit.unit) else none) = _
  rw [ite_eq_right h]

/-! ## Sublanguages -/

/-- A sublanguage, given as a type of witnesses for each expression. -/
abbrev Fragment (rT : Type _) := Exp rT → Type

/-- Expressions together with a witness that they lie in the fragment. -/
abbrev FragExp (F : Fragment rT) := (e : Exp rT) × F e

/-- Expressions in both fragments. -/
def Both (F G : Fragment rT) : Fragment rT :=
  fun e => F e × G e

/-- Expressions in either fragment. -/
def Either (F G : Fragment rT) : Fragment rT :=
  fun e => F e ⊕ G e

/-- The fragment of all expressions. -/
def Any : Fragment rT :=
  fun _ => Unit

/-- The empty fragment. -/
def None : Fragment rT :=
  fun _ => Empty

/-- Pairs each witness of `F` with extra data `M`. -/
def Overlay (F : Fragment rT) (M : Exp rT → Type) : Fragment rT :=
  fun e => F e × M e

/-- Inclusion of fragments: a map from `F`-witnesses to `G`-witnesses. -/
def SubFrag (F G : Fragment rT) :=
  ∀ e, F e → G e
scoped infixr:25 " ⊆f " => SubFrag

def SubFrag.id : F ⊆f F := fun _ x => x
def SubFrag.comp (f : F ⊆f G) (g : G ⊆f H) : F ⊆f H := fun e x => g e (f e x)
def SubFrag.map (f : F ⊆f G) : FragExp F → FragExp G
  | ⟨e, w⟩ => ⟨e, f e w⟩

/-- The underlying expression. -/
def FragExp.erase {F : Fragment rT} : FragExp F → Exp rT := Sigma.fst

/-- Fragments whose membership can be decided by a function. -/
class Checkable (F : Fragment rT) where
  check? : (e : Exp rT) → Option (F e)

/-- Checks `e` against the fragment. -/
def FragExp.mk? {F : Fragment rT} [Checkable F] (e : Exp rT) : Option (FragExp F) :=
  (Checkable.check? e).map (⟨e, ·⟩)

instance [Checkable F] [Checkable G] : Checkable (Both F G) where
  check? e := do return (← Checkable.check? e, ← Checkable.check? e)

/-! ## Values -/

/-- Witness that an expression is a value; `Type`-valued so that `check?` can return the witness
and `IsVal` is a `Fragment`. It is a subsingleton, and `Exp.isValue` is its `Prop` form. -/
inductive IsVal : Exp rT → Type
  | lit  : IsVal (.lit b)
  -- A runtime function is closed, so `IsVal e → IsLocallyClosed e` (`IsVal.lc`).
  | lam  : Exp.IsLocallyClosed (.lam e) → IsVal (.lam e)
  | fix  : Exp.IsLocallyClosed (.fix e) → IsVal (.fix e)
  | pair : IsVal e1 → IsVal e2 → IsVal (.pair e1 e2)
  | inl  : IsVal e → IsVal (.inl e)
  | inr  : IsVal e → IsVal (.inr e)

omit [ProbLangℝ rT] in
theorem IsVal.lc : {e : Exp rT} → IsVal e → Exp.IsLocallyClosed e
  | _, .lit => .lit _
  | _, .lam h => h
  | _, .fix h => h
  | _, .pair w1 w2 => .pair w1.lc w2.lc
  | _, .inl w => .inl w.lc
  | _, .inr w => .inr w.lc

/-- A value: an expression with a witness that it is a value, and its local closedness.
A `structure`, not `(e : Exp α) × IsVal e`, so that `Val α` does not reduce to `Sigma`:
its measurable space (`CoreMeasures/Val.lean`) is the comap of `Val.fst`, not the coarser
`Sigma.instMeasurableSpace`. -/
structure Val (α : Type _) where
  fst : Exp α
  snd : IsVal fst
  /-- Lets proofs rewrite `open'` on an abstract value to the value itself (`open_lc`). -/
  lc : fst.IsLocallyClosed

/-- The value of a literal. `@[reducible]` because the proof-mode unifier (`iapply`) matches at
reducible transparency. -/
@[reducible, coe] def Val.ofBaseLit (b : BaseLit rT) : Val rT :=
  ⟨.lit b, .lit, Exp.IsLocallyClosed.lit b⟩

instance : Coe (BaseLit rT) (Val rT) := ⟨Val.ofBaseLit⟩

instance : Coe (Val rT) (Exp rT) := ⟨Val.fst⟩

/-! Coercions into `BaseLit`, so `#z` works for `z : Int` (also `Bool`, `Unit`, `rT`). Locations
and labels are `Int` abbreviations, so they have no coercion: write `#loc l`, `#lbl l`. -/

instance : Coe Int (BaseLit rT) := ⟨.int⟩
instance : Coe Bool (BaseLit rT) := ⟨.bool⟩
instance : Coe Unit (BaseLit rT) := ⟨fun _ => .unit⟩
instance : Coe rT (BaseLit rT) := ⟨.real⟩

abbrev Val.int  (n : Int) : Val rT  := Val.ofBaseLit (.int n)
abbrev Val.bool (b : Bool) : Val rT := Val.ofBaseLit (.bool b)
abbrev Val.unit : Val rT            := Val.ofBaseLit .unit
abbrev Val.loc  (l : Loc) : Val rT  := Val.ofBaseLit (.loc l)
abbrev Val.lbl  (l : Lbl) : Val rT  := Val.ofBaseLit (.lbl l)
abbrev Val.real (r : rT) : Val rT   := Val.ofBaseLit (.real r)

@[reducible] def Val.pair (v w : Val rT) : Val rT :=
  ⟨.pair v.1 w.1, .pair v.2 w.2, .pair v.lc w.lc⟩

@[reducible] def Val.inl (v : Val rT) : Val rT := ⟨.inl v.1, .inl v.2, .inl v.lc⟩

@[reducible] def Val.inr (v : Val rT) : Val rT := ⟨.inr v.1, .inr v.2, .inr v.lc⟩

/-- `NONE = inl ()`, `SOME v = inr v`. -/
@[reducible] def Val.option : Option (Val rT) → Val rT
  | none => .inl .unit
  | some v => .inr v

omit [ProbLangℝ rT] in
@[simp] theorem Val.pair_fst (v w : Val rT) : (Val.pair v w).1 = .pair v.1 w.1 := rfl
omit [ProbLangℝ rT] in
@[simp] theorem Val.inl_fst (v : Val rT) : (Val.inl v).1 = .inl v.1 := rfl
omit [ProbLangℝ rT] in
@[simp] theorem Val.inr_fst (v : Val rT) : (Val.inr v).1 = .inr v.1 := rfl

namespace IsVal

/-- Decides whether an expression is a value. -/
def check? : (e : Exp rT) → Option (IsVal e)
  | .lit _ => some .lit
  | .lam e => if h : Exp.lcb 0 (.lam e) = true then some (.lam (Exp.lcb_imp_lc h)) else none
  | .fix e => if h : Exp.lcb 0 (.fix e) = true then some (.fix (Exp.lcb_imp_lc h)) else none
  | .pair e1 e2 => do return .pair (← check? e1) (← check? e2)
  | .inl e => do return .inl (← check? e)
  | .inr e => do return .inr (← check? e)
  | _ => none

theorem subsingleton : (w1 w2 : IsVal e) → w1 = w2
  | .lit, .lit => rfl
  | .lam _, .lam _ => rfl
  | .fix _, .fix _ => rfl
  | .pair h1 h2, .pair h1' h2' => by rw [subsingleton h1 h1', subsingleton h2 h2']
  | .inl h, .inl h' => by rw [subsingleton h h']
  | .inr h, .inr h' => by rw [subsingleton h h']

instance : Subsingleton (IsVal e) := ⟨subsingleton⟩

end IsVal

instance : Checkable (@IsVal rT) where check? := IsVal.check?

/-- Propositional form of `IsVal`. -/
def Exp.isValue (e : Exp rT) : Prop := Nonempty (IsVal e)

theorem IsVal.toIsValue (w : IsVal e) : e.isValue := ⟨w⟩

noncomputable def IsVal.ofIsValue (h : e.isValue) : IsVal e := h.some

theorem IsVal.check?_some : (w : IsVal e) → ∃ w', IsVal.check? e = some w'
  | .lit => ⟨.lit, rfl⟩
  | .lam h => ⟨.lam h, by simp only [check?, dite_eq_left (Exp.lc_imp_lcb h)]⟩
  | .fix h => ⟨.fix h, by simp only [check?, dite_eq_left (Exp.lc_imp_lcb h)]⟩
  | .pair h1 h2 => by
      obtain ⟨w1, hw1⟩ := check?_some h1; obtain ⟨w2, hw2⟩ := check?_some h2
      exact ⟨.pair w1 w2, by simp [check?, hw1, hw2]⟩
  | .inl h => by obtain ⟨w, hw⟩ := check?_some h; exact ⟨.inl w, by simp [check?, hw]⟩
  | .inr h => by obtain ⟨w, hw⟩ := check?_some h; exact ⟨.inr w, by simp [check?, hw]⟩

/-- Value shape, ignoring local closedness (`R` for raw). With `lcb 0 e` it characterizes
`isValue` (`isValue_iff_isValueR`), which lets proofs decide value-ness by shape. -/
@[simp] def Exp.isValueR : Exp rT → Prop
  | .lit _ | .lam _ | .fix _ => True
  | .pair e1 e2 => e1.isValueR ∧ e2.isValueR
  | .inl e | .inr e => e.isValueR
  | _ => False

theorem Exp.isValue_iff_isValueR {e : Exp α} :
    e.isValue ↔ e.isValueR ∧ Exp.lcb 0 e = true := by
  constructor
  · rintro ⟨w⟩
    refine ⟨?_, Exp.lc_imp_lcb w.lc⟩
    induction w with
    | lit | lam | fix => trivial
    | pair _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
    | inl _ ih | inr _ ih => exact ih
  · rintro ⟨hr, hl⟩
    induction e with
    | lit => exact ⟨.lit⟩
    | lam e' _ => exact ⟨.lam (Exp.lcb_imp_lc hl)⟩
    | fix e' _ => exact ⟨.fix (Exp.lcb_imp_lc hl)⟩
    | pair e1 e2 ih1 ih2 =>
        obtain ⟨hr1, hr2⟩ := hr
        simp only [lcb, Bool.and_eq_true] at hl
        exact ⟨.pair (ih1 hr1 hl.1).some (ih2 hr2 hl.2).some⟩
    | inl e' ih => exact ⟨.inl (ih hr (by simpa only [lcb] using hl)).some⟩
    | inr e' ih => exact ⟨.inr (ih hr (by simpa only [lcb] using hl)).some⟩
    | _ => exact absurd hr id

theorem Exp.isValueR_of_isValue {e : Exp α} (h : e.isValue) : e.isValueR :=
  (Exp.isValue_iff_isValueR.mp h).1

theorem Exp.not_isValue_of_not_isValueR {e : Exp α} (h : ¬e.isValueR) : ¬e.isValue :=
  fun hv => h (Exp.isValueR_of_isValue hv)

theorem IsVal.not_isValue_of_check?_none {e : Exp α} (h : IsVal.check? e = none) : ¬e.isValue :=
  fun ⟨w⟩ => by obtain ⟨_, hw⟩ := w.check?_some; simp_all

theorem IsVal.check?_eq_none {e : Exp α} (h : ¬e.isValue) : IsVal.check? e = none := by
  cases hc : IsVal.check? e with
  | none => rfl
  | some w => exact absurd ⟨w⟩ h

instance Exp.decIsValue (e : Exp α) : Decidable e.isValue :=
  match hc : IsVal.check? e with
  | some w => isTrue ⟨w⟩
  | none => isFalse (IsVal.not_isValue_of_check?_none hc)

@[simp] theorem Val.isValue (v : @Val α) : v.fst.isValue := ⟨v.snd⟩

theorem Val.ext {v1 v2 : Val α} (h : v1.fst = v2.fst) : v1 = v2 := by
  obtain ⟨e1, w1, h1⟩ := v1; obtain ⟨e2, w2, h2⟩ := v2
  simp at h; subst h; congr 1; exact IsVal.subsingleton w1 w2

theorem Val.ext_iff {v1 v2 : Val α} : v1 = v2 ↔ v1.fst = v2.fst :=
  ⟨congrArg _, Val.ext⟩

instance [Countable α] : Countable (Val α) :=
  Function.Injective.countable (f := Val.fst) fun _ _ => Val.ext

/-- The value an expression denotes, if it is one. -/
def Exp.toVal? (e : Exp α) : Option (Val α) :=
  match IsVal.check? e with
  | some w => some ⟨e, w, w.lc⟩
  | none => none

theorem Exp.toVal?_none_of_not_isValue {e : Exp α} (h : ¬e.isValue) : e.toVal? = none := by
  simp only [toVal?, IsVal.check?_eq_none h]

theorem Exp.toVal?_eq_some_of_isValue {e : Exp α} (h : e.isValue) : ∃ v, e.toVal? = some v := by
  obtain ⟨w, hw⟩ := h.some.check?_some
  exact ⟨⟨e, w, w.lc⟩, by simp only [Exp.toVal?, hw]⟩

@[simp] theorem Exp.toVal?_eq_none {e : Exp α} : e.toVal? = none ↔ ¬e.isValue := by
  constructor
  · intro h
    simp only [toVal?] at h
    exact IsVal.not_isValue_of_check?_none (by cases hc : IsVal.check? e <;> simp_all)
  · intro h; simp [toVal?, IsVal.check?_eq_none h]

/-! ### Non-values

Side conditions of the weakest-precondition lifting rules. -/

theorem Exp.alloc_not_isValue {e : Exp α} : ¬ (Exp.alloc e).isValue := fun ⟨w⟩ => nomatch w
theorem Exp.load_not_isValue {e : Exp α} : ¬ (Exp.load e).isValue := fun ⟨w⟩ => nomatch w
theorem Exp.store_not_isValue {e₁ e₂ : Exp α} :
    ¬ (Exp.store e₁ e₂).isValue := fun ⟨w⟩ => nomatch w
theorem Exp.tape_not_isValue {e : Exp α} : ¬ (Exp.tape e).isValue := fun ⟨w⟩ => nomatch w
theorem Exp.rand_not_isValue {e₁ e₂ : Exp α} :
    ¬ (Exp.rand e₁ e₂).isValue := fun ⟨w⟩ => nomatch w
theorem Exp.urand_not_isValue : ¬ (Exp.urand : Exp α).isValue := fun ⟨w⟩ => nomatch w

theorem Exp.alloc_toVal?_eq_none {e : Exp α} : (Exp.alloc e).toVal? = none :=
  Exp.toVal?_eq_none.mpr Exp.alloc_not_isValue
theorem Exp.load_toVal?_eq_none {e : Exp α} : (Exp.load e).toVal? = none :=
  Exp.toVal?_eq_none.mpr Exp.load_not_isValue
theorem Exp.store_toVal?_eq_none {e₁ e₂ : Exp α} : (Exp.store e₁ e₂).toVal? = none :=
  Exp.toVal?_eq_none.mpr Exp.store_not_isValue
theorem Exp.tape_toVal?_eq_none {e : Exp α} : (Exp.tape e).toVal? = none :=
  Exp.toVal?_eq_none.mpr Exp.tape_not_isValue
theorem Exp.rand_toVal?_eq_none {e₁ e₂ : Exp α} : (Exp.rand e₁ e₂).toVal? = none :=
  Exp.toVal?_eq_none.mpr Exp.rand_not_isValue
theorem Exp.urand_toVal?_eq_none : (Exp.urand : Exp α).toVal? = none :=
  Exp.toVal?_eq_none.mpr Exp.urand_not_isValue

/-- Same as `Val.fst`, under its own head symbol so that frame lemmas (`fillItem`) and the
`delabExpOfVal` delaborator can match it syntactically. -/
def Exp.ofVal (v : Val α) : Exp α := v.1

theorem Exp.toVal?_ofVal (v : Val α) : (Exp.ofVal v).toVal? = some v := by
  obtain ⟨e, w, hlc⟩ := v
  simp only [Exp.ofVal, Exp.toVal?]
  cases hc : IsVal.check? e with
  | none => exact absurd w.toIsValue (IsVal.not_isValue_of_check?_none hc)
  | some w' => exact congrArg some (Val.ext rfl)

omit [ProbLangℝ rT] in
/-- `v.snd`, typed for lemmas keyed on the syntactic `Exp.ofVal` shape. -/
def Val.isVal_ofVal (v : Val rT) : IsVal (Exp.ofVal v) := v.2

@[simp] theorem Val.toVal?_fst (v : Val α) : v.fst.toVal? = some v := Exp.toVal?_ofVal v

theorem Exp.ofVal_of_toVal_some {e : Exp α} {v : Val α} (h : e.toVal? = some v)
    : Exp.ofVal v = e := by
  simp only [toVal?] at h
  split at h
  · simp at h; exact congrArg Val.fst h.symm
  · simp at h

theorem Exp.ofVal_injective : Function.Injective (@Exp.ofVal α) :=
  fun _ _ h => Val.ext h

/-! ## Operator evaluation -/

/-- Evaluates a unary operator on a value. -/
def UnOp.eval [ProbLangℝ α] (op : UnOp) (v : Exp α) : Option (Exp α) :=
  match op, v with
  | neg, .lit (.bool b) => some <| .lit <| .bool <| ¬ b
  | minus, .lit (.int z) => some <| .lit <| .int <| z.neg
  | minus, .lit (.real r) => some <| .lit <| .real <| ProbLangℝ.realNeg r
  | toReal, .lit (.int z) => some <| .lit <| .real <| ProbLangℝ.realOfInt z
  | toReal, .lit (.real r) => some <| .lit <| .real r
  -- Integer literals must be coerced with `toReal` first.
  | frac, .lit (.real r) => some <| .lit <| .real <| ProbLangℝ.realFrac r
  | _, _ => none

/-- Evaluates a binary operator on two values. -/
def BinOp.eval (op : BinOp) (v1 v2 : Exp rT) : Option (Exp rT) :=
  match op, v1, v2 with
  | plus,  .lit (.int z1),  .lit (.int z2)  => some <| .lit <| .int (z1 + z2)
  | minus, .lit (.int z1),  .lit (.int z2)  => some <| .lit <| .int (z1 - z2)
  | mult,  .lit (.int z1),  .lit (.int z2)  => some <| .lit <| .int (z1 * z2)
  -- Total (n / 0 = 0, n % 0 = n), agreeing with Rocq's `Z.quot`/`Z.rem`.
  | div,   .lit (.int z1),  .lit (.int z2)  => some <| .lit <| .int (z1 / z2)
  | mod,   .lit (.int z1),  .lit (.int z2)  => some <| .lit <| .int (z1 % z2)
  | and,   .lit (.bool b1), .lit (.bool b2) => some <| .lit <| .bool (b1 && b2)
  | or,    .lit (.bool b1), .lit (.bool b2) => some <| .lit <| .bool (b1 || b2)
  | xor,   .lit (.bool b1), .lit (.bool b2) => some <| .lit <| .bool (b1 ^^ b2)
  | eq,    .lit l1,         .lit l2         => some <| .lit <| .bool (l1 == l2)
  | eq,    .inl (.lit l1),  .inl (.lit l2)  => some <| .lit <| .bool (l1 == l2)
  | eq,    .inr (.lit l1),  .inr (.lit l2)  => some <| .lit <| .bool (l1 == l2)
  | eq,    .inl (.lit _),   .inr (.lit _)   => some <| .lit <| .bool false
  | eq,    .inr (.lit _),   .inl (.lit _)   => some <| .lit <| .bool false
  | lt,    .lit (.int z1),  .lit (.int z2)  => some <| .lit <| .bool (decide (z1 < z2))
  | le,    .lit (.int z1),  .lit (.int z2)  => some <| .lit <| .bool (decide (z1 ≤ z2))
  | lt,    .lit (.real r1), .lit (.real r2) => some <| .lit <| .bool (ProbLangℝ.realLt r1 r2)
  | le,    .lit (.real r1), .lit (.real r2) => some <| .lit <| .bool (ProbLangℝ.realLe r1 r2)
  -- Mixed int/real operands are stuck: programs coerce with `UnOp.toReal`.
  | plus,  .lit (.real r1), .lit (.real r2) => some <| .lit <| .real (ProbLangℝ.realAdd r1 r2)
  -- A negative shift amount counts as 0.
  | shl,   .lit (.int z1),  .lit (.int z2)  => some <| .lit <| .int (z1 * 2 ^ z2.toNat)
  | shr,   .lit (.int z1),  .lit (.int z2)  => some <| .lit <| .int (z1 / 2 ^ z2.toNat)
  |_,      _,        _        => none

/-! ## States and configurations -/

/-- A random tape: a bound `N` and a queue of presampled values in `[0, N)`; `rand` reads from the
front, presampling appends at the back. -/
structure Tape where
  bound : Int
  presamples : List { z : Int // 0 ≤ z ∧ z < bound}
  deriving Inhabited, Countable

/-- An empty tape with the given bound. -/
def Tape.empty (z : Int) : Tape := ⟨z, []⟩

instance instCountableExtTreeMapLoc {V : Type _} [Countable V] :
    Countable (ExtTreeMap Loc V compare) :=
  Function.Injective.countable (f := ExtTreeMap.toList) fun _ _ => ExtTreeMap.toList_inj.mp

/-- Finite maps keyed by `Int` (heap locations and tape labels). Hides the representation from
typeclass inference. -/
@[reducible] def LocHeap (V : Type _) : Type _ := ExtTreeMap Loc V compare

instance : Inhabited (LocHeap V) := inferInstanceAs (Inhabited (ExtTreeMap _ _ _))

instance [Countable V] : Countable (LocHeap V) :=
  inferInstanceAs (Countable (ExtTreeMap _ _ _))

instance : GetElem? (LocHeap V) Loc V (fun (m : ExtTreeMap Loc V compare) k => k ∈ m) :=
  inferInstanceAs (GetElem? (ExtTreeMap Loc V compare) _ _ _)

/-- Machine state: the heap and the random tapes. -/
structure State (α : Type _) where
  heap  : LocHeap (Val α)
  tapes : LocHeap Tape
  deriving Inhabited, Countable

/-- Applies `f` to the heap. -/
def State.update_heap (σ : State α) (f : ExtTreeMap Loc (Val α) → ExtTreeMap Loc (Val α))
    : State α :=
  ⟨f σ.heap, σ.tapes⟩

/-- Applies `f` to the tapes. -/
def State.update_tapes (σ : State α) (f : ExtTreeMap Loc Tape → ExtTreeMap Loc Tape) : State α :=
  ⟨σ.heap, f σ.tapes⟩

theorem State.update_tapes_twice (σ : State α) (l : Loc) (ys xs : Tape) :
    (σ.update_tapes (·.insert l xs)).update_tapes (·.insert l ys) =
    σ.update_tapes (·.insert l ys) := by
  unfold State.update_tapes; simp; grind

theorem State.update_tapes_same {σ σ' : State α}
    (h : σ.update_tapes (·.insert l xs) = σ'.update_tapes (·.insert l ys)) :
    xs = ys := by
  simpa [State.update_tapes, LocHeap] using congrArg (·.tapes[l]?) h

theorem State.update_tapes_no_change {σ : State α} (h : σ.tapes[l]? = some ys) :
    σ.update_tapes (·.insert l ys) = σ := by
  unfold State.update_tapes; congr 2; grind

/-- Injectivity form of `update_tapes_same`: the presampled values appended to tape `l` agree. -/
theorem State.update_tapes_same' {σ σ' : State α} {xs : List { z : Int // 0 ≤ z ∧ z < n }}
    {x y : { z : Int // 0 ≤ z ∧ z < n }}
    (h : σ.update_tapes (·.insert l ⟨n, xs ++ [x]⟩) = σ'.update_tapes (·.insert l ⟨n, xs ++ [y]⟩)) :
    x = y := by
  simpa [Tape.mk.injEq] using State.update_tapes_same h

/-- Presampling different values onto tape `l` gives different states. -/
theorem State.update_tapes_neq' {σ σ' : State α} {xs : List { z : Int // 0 ≤ z ∧ z < n }}
    {x y : { z : Int // 0 ≤ z ∧ z < n }} (hne : x ≠ y) :
    σ.update_tapes (·.insert l ⟨n, xs ++ [x]⟩) ≠ σ'.update_tapes (·.insert l ⟨n, xs ++ [y]⟩) :=
  (hne <| State.update_tapes_same' ·)

/-- A configuration: an expression and a state. -/
structure Cfg α where
  expr : Exp α
  state : State α
  deriving Countable

/-! ## Evaluation contexts -/

/-- One-hole frames. `…L v` has the hole in the left operand with the right already a value;
`…R e` has the hole in the right operand. Evaluation is right-to-left, as in Clutch/HeapLang. -/
@[uncurriedProjections, constructors]
inductive EctxItem (α : Type _)
  | appL (v2 : Val α)
  | appR (e1 : Exp α)
  | unop (op : UnOp)
  | binopL (op : BinOp) (v2 : Val α)
  | binopR (op : BinOp) (e1 : Exp α)
  | condC (e1 e2 : Exp α)
  | pairL (v2 : Val α)
  | pairR (e1 : Exp α)
  | fst
  | snd
  | inl
  | inr
  | case (e1 e2 : Exp α)
  | alloc
  | load
  | storeL (v2 : Val α)
  | storeR (e1 : Exp α)
  | tape
  | randL (v2 : Val α)
  | randR (e1 : Exp α)
  | scrut (p : Pat α)
  deriving Countable

/-- Plugs `e` into the hole of a frame. -/
@[simp] def EctxItem.fillItem (Ki : EctxItem α) (e : Exp α) : Exp α :=
  match Ki with
  | appL v2 => .app e (.ofVal v2)
  | appR e1 => .app e1 e
  | unop op => .unop op e
  | binopL op v2 => .binop op e (.ofVal v2)
  | binopR op e1 => .binop op e1 e
  | condC e1 e2 => .cond e e1 e2
  | .pairL v2 => .pair e (.ofVal v2)
  | .pairR e1 => .pair e1 e
  | .fst => .fst e
  | .snd => .snd e
  | .inl => .inl e
  | .inr => .inr e
  | .case e1 e2 => .case e e1 e2
  | .alloc => .alloc e
  | .load => .load e
  | .storeL v2 => .store e (.ofVal v2)
  | .storeR e1 => .store e1 e
  | .tape => .tape e
  | .randL v2 => .rand e (.ofVal v2)
  | .randR e1 => .rand e1 e
  | .scrut p => .scrut e p

theorem EctxItem.fillItem_isLocallyClosed {Ki : EctxItem α} {e : Exp α}
    (h : (Ki.fillItem e).IsLocallyClosed) : e.IsLocallyClosed := by
  cases Ki <;> (simp only [fillItem] at h; cases h; assumption)

/-- Splits off the outermost frame whose hole is the next subterm to evaluate, trying the
right operand first. It is `none` when every operand that is evaluated is already a value (so `e`
is a head redex, a value, or has no subterm to evaluate). Operands are tested with `toVal?`, so an
open `lam`/`fix` counts as unevaluated. -/
def Exp.decompItem (e : Exp α) : Option (EctxItem α × Exp α) :=
  match e with
  | app e1 e2 =>
    e2.toVal?.casesOn (some (.appR e1, e2)) fun v2 =>
    e1.toVal?.casesOn (some (.appL v2, e1)) fun _ => none
  | unop op e1 =>
    e1.toVal?.casesOn (some (.unop op, e1)) fun _ => none
  | binop op e1 e2 =>
    e2.toVal?.casesOn (some (.binopR op e1, e2)) fun v2 =>
    e1.toVal?.casesOn (some (.binopL op v2, e1)) fun _ => none
  | .cond ec et ef =>
    ec.toVal?.casesOn (some (.condC et ef, ec)) fun _ => none
  | pair e1 e2 =>
    e2.toVal?.casesOn (some (.pairR e1, e2)) fun v2 =>
    e1.toVal?.casesOn (some (.pairL v2, e1)) fun _ => none
  | fst e1 =>
    e1.toVal?.casesOn (some (.fst, e1)) fun _ => none
  | snd e1 =>
    e1.toVal?.casesOn (some (.snd, e1)) fun _ => none
  | inl e1 =>
    e1.toVal?.casesOn (some (.inl, e1)) fun _ => none
  | inr e1 =>
    e1.toVal?.casesOn (some (.inr, e1)) fun _ => none
  | alloc e1 =>
    e1.toVal?.casesOn (some (.alloc, e1)) fun _ => none
  | load e1 =>
    e1.toVal?.casesOn (some (.load, e1)) fun _ => none
  | store e1 e2 =>
    e2.toVal?.casesOn (some (.storeR e1, e2)) fun v2 =>
    e1.toVal?.casesOn (some (.storeL v2, e1)) fun _ => none
  | rand e1 e2 =>
    e2.toVal?.casesOn (some (.randR e1, e2)) fun v2 =>
    e1.toVal?.casesOn (some (.randL v2, e1)) fun _ => none
  | .case ec el er =>
    ec.toVal?.casesOn (some (.case el er, ec)) fun _ => none
  | tape e1 =>
    e1.toVal?.casesOn (some (.tape, e1)) fun _ => none
  | scrut e1 p =>
    e1.toVal?.casesOn (some (.scrut p, e1)) fun _ => none
  | _ => none

theorem EctxItem.fillItem_injective : Function.Injective (EctxItem.fillItem K) := by
  cases K <;> simp [Function.Injective, EctxItem.fillItem]

theorem EctxItem.fillItem_isValue {K : EctxItem α} : (K.fillItem e).isValue → e.isValue := by
  rintro ⟨w⟩
  cases K <;> (simp only [EctxItem.fillItem] at w; cases w) <;> exact ‹IsVal e›.toIsValue

theorem EctxItem.fillItem_isValueR {Ki : EctxItem α} {e : Exp α}
    (h : (Ki.fillItem e).isValueR) : e.isValueR := by
  cases Ki <;> simp_all [EctxItem.fillItem, Exp.isValueR, Exp.ofVal]

theorem EctxItem.fillItem_noVal_inj {Ki1 Ki2 : EctxItem α} {e1 e2 : Exp α}
    (hv1 : ¬e1.isValue) (hv2 : ¬e2.isValue)
    (h : Ki1.fillItem e1 = Ki2.fillItem e2) : Ki1 = Ki2 := by
  cases Ki1 <;> cases Ki2 <;> simp_all [EctxItem.fillItem, Exp.ofVal] <;>
    grind [Val.ext_iff, Val.isValue, Exp.isValue_iff_isValueR]

theorem EctxItem.decompItem_fillItem (Ki : EctxItem α) {e : Exp α} (hv : ¬e.isValue) :
    (Ki.fillItem e).decompItem = some (Ki, e) := by
  cases Ki with
  | appL v2 | binopL _ v2 | pairL v2 | storeL v2 | randL v2 =>
    simp [EctxItem.fillItem, Exp.decompItem, Exp.toVal?_none_of_not_isValue hv,
         Val.toVal?_fst, Exp.ofVal]
  | _ => simp [EctxItem.fillItem, Exp.decompItem, Exp.toVal?_none_of_not_isValue hv]

theorem Exp.decompItem_fill {e e' : Exp α} {Ki : EctxItem α}
    (h : e.decompItem = some (Ki, e')) : Ki.fillItem e' = e ∧ ¬e'.isValue := by
  simp only [decompItem, toVal?] at h
  have aux : ∀ x : Exp α, IsVal.check? x = none → ¬x.isValue :=
    fun x h => IsVal.not_isValue_of_check?_none h
  cases e <;> simp_all [Exp.ofVal] <;>
    (split at h <;> simp_all <;> (try obtain ⟨rfl, rfl⟩ := h; simp_all)) <;>
    (split at h <;> simp_all <;> (try obtain ⟨rfl, rfl⟩ := h; simp_all))

theorem EctxItem.fillItem_noVal {Ki : EctxItem α} {e : Exp α} (hv : ¬e.isValue) :
    ¬(Ki.fillItem e).isValue := (hv <| EctxItem.fillItem_isValue ·)

/-- Evaluation contexts: a list of frames, innermost first. -/
abbrev Ectx α := List (EctxItem α)

/-- The empty context. -/
def Ectx.empty : Ectx α := []

/-- Composition: `(comp K1 K2).fill e = K1.fill (K2.fill e)`. -/
def Ectx.comp (K1 K2 : Ectx α) : Ectx α := K2 ++ K1

/-- Plugs `e` into the context. -/
def Ectx.fill (K : Ectx α) (e : Exp α) : Exp α := K.foldl (flip EctxItem.fillItem) e

theorem Ectx.fill_append (K1 K2 : Ectx α) e : (K1 ++ K2).fill e = K2.fill (K1.fill e) :=
  List.foldl_append

@[simp] theorem Ectx.fill_snoc (K : Ectx α) (Ki : EctxItem α) (e : Exp α) :
    Ectx.fill (K ++ [Ki]) e = Ki.fillItem (K.fill e) :=
  List.foldl_append

/-! ### Single-frame contexts: `Ectx.fill [Ki] e` equations

The `refines_bind` / `refines_pure_*` rules match `K.fill _` syntactically, so a goal
about a bare redex has to be re-bracketed first. Each lemma below states the relevant
definitional equality in the reducing direction; use `←` to re-bracket a goal. -/

@[simp] theorem Ectx.fill_nil (e : Exp α) : Ectx.fill ([] : Ectx α) e = e := rfl

theorem Ectx.eq_fill_nil (e : Exp α) : e = Ectx.fill ([] : Ectx α) e := rfl

theorem Ectx.fill_appL (v2 : Val α) (e : Exp α) :
    Ectx.fill [.appL v2] e = .app e (.ofVal v2) := rfl

theorem Ectx.fill_appR (e1 : Exp α) (e : Exp α) :
    Ectx.fill [.appR e1] e = .app e1 e := rfl

theorem Ectx.fill_unop (op : UnOp) (e : Exp α) :
    Ectx.fill [.unop op] e = .unop op e := rfl

theorem Ectx.fill_binopL (op : BinOp) (v2 : Val α) (e : Exp α) :
    Ectx.fill [.binopL op v2] e = .binop op e (.ofVal v2) := rfl

theorem Ectx.fill_binopR (op : BinOp) (e1 : Exp α) (e : Exp α) :
    Ectx.fill [.binopR op e1] e = .binop op e1 e := rfl

theorem Ectx.fill_condC (e1 e2 : Exp α) (e : Exp α) :
    Ectx.fill [.condC e1 e2] e = .cond e e1 e2 := rfl

theorem Ectx.fill_pairL (v2 : Val α) (e : Exp α) :
    Ectx.fill [.pairL v2] e = .pair e (.ofVal v2) := rfl

theorem Ectx.fill_pairR (e1 : Exp α) (e : Exp α) :
    Ectx.fill [.pairR e1] e = .pair e1 e := rfl

theorem Ectx.fill_fst (e : Exp α) :
    Ectx.fill [.fst] e = .fst e := rfl

theorem Ectx.fill_snd (e : Exp α) :
    Ectx.fill [.snd] e = .snd e := rfl

theorem Ectx.fill_inl (e : Exp α) :
    Ectx.fill [.inl] e = .inl e := rfl

theorem Ectx.fill_inr (e : Exp α) :
    Ectx.fill [.inr] e = .inr e := rfl

theorem Ectx.fill_case (e1 e2 : Exp α) (e : Exp α) :
    Ectx.fill [.case e1 e2] e = .case e e1 e2 := rfl

theorem Ectx.fill_alloc (e : Exp α) :
    Ectx.fill [.alloc] e = .alloc e := rfl

theorem Ectx.fill_load (e : Exp α) :
    Ectx.fill [.load] e = .load e := rfl

theorem Ectx.fill_storeL (v2 : Val α) (e : Exp α) :
    Ectx.fill [.storeL v2] e = .store e (.ofVal v2) := rfl

theorem Ectx.fill_storeR (e1 : Exp α) (e : Exp α) :
    Ectx.fill [.storeR e1] e = .store e1 e := rfl

theorem Ectx.fill_tape (e : Exp α) :
    Ectx.fill [.tape] e = .tape e := rfl

theorem Ectx.fill_randL (v2 : Val α) (e : Exp α) :
    Ectx.fill [.randL v2] e = .rand e (.ofVal v2) := rfl

theorem Ectx.fill_randR (e1 : Exp α) (e : Exp α) :
    Ectx.fill [.randR e1] e = .rand e1 e := rfl

theorem Ectx.fill_scrut (p : Pat α) (e : Exp α) :
    Ectx.fill [.scrut p] e = .scrut e p := rfl

/-! ### Properties of `Ectx.fill` -/

theorem Ectx.fill_comp (K1 K2 : Ectx α) (e : Exp α) :
    K1.fill (K2.fill e) = (K1.comp K2).fill e := by
  simp [Ectx.comp, Ectx.fill_append]

theorem Ectx.fill_injective (K : Ectx α) : Function.Injective K.fill := by
  induction K with
  | nil => intro _ _ h; exact h
  | cons Ki K ih => exact fun _ _ h => EctxItem.fillItem_injective (ih h)

theorem Ectx.fill_noVal {K : Ectx α} {e : Exp α} (hv : ¬e.isValue) : ¬(K.fill e).isValue := by
  induction K generalizing e with
  | nil => exact hv
  | cons Ki K ih => exact ih (EctxItem.fillItem_noVal hv)

theorem Ectx.fill_isValue {K : Ectx α} {e : Exp α} (hv : (K.fill e).isValue) : e.isValue :=
  if h : e.isValue then h else absurd hv (Ectx.fill_noVal h)

theorem Ectx.fill_isValueR {K : Ectx α} {e : Exp α} (h : (K.fill e).isValueR) : e.isValueR := by
  induction K generalizing e with
  | nil => exact h
  | cons Ki K ih => exact EctxItem.fillItem_isValueR (ih h)

theorem Ectx.fill_isLocallyClosed {K : Ectx α} {e : Exp α}
    (h : (K.fill e).IsLocallyClosed) : e.IsLocallyClosed := by
  induction K generalizing e with
  | nil => exact h
  | cons Ki K ih => exact EctxItem.fillItem_isLocallyClosed (ih h)

/-! ### Multi-frame decomposition: `Exp.decomp` -/

theorem Exp.decompItem_size {e : Exp α} (h : e.decompItem = some (Ki, e')) :
    e'.size < e.size := by
  simp only [decompItem, toVal?] at h
  cases e <;> simp_all <;>
    (split at h <;> simp_all <;> try omega) <;>
    (split at h <;> simp_all <;> try omega)

/-- Splits an expression into a maximal evaluation context and the redex in its hole. The context
is innermost frame first (the frame split off first ends up last); `decomp_fill` gives
`K.fill e' = e`; for a value `K = []` (`decomp_val_empty`). -/
def Exp.decomp (e : Exp α) : Ectx α × Exp α :=
  match _h : e.decompItem with
  | some (Ki, e') =>
      let (K, e'') := decomp e'
      (K ++ [Ki], e'')
  | none => ([], e)
  termination_by e.size
  decreasing_by exact Exp.decompItem_size _h

theorem Exp.decomp_unfold (e : Exp α) :
    e.decomp =
      match _ : e.decompItem with
      | some (Ki, e') => let (K, e'') := e'.decomp; (K ++ [Ki], e'')
      | none => ([], e) :=
  Exp.decomp.eq_1 e

theorem Exp.decomp_snd_of_decompItem_none {e : Exp α} (hd : e.decompItem = none) :
    e.decomp.2 = e := by rw [Exp.decomp_unfold, hd]

theorem Exp.decomp_inv_nil {e e' : Exp α} (h : e.decomp = ([], e')) :
    e.decompItem = none ∧ e = e' := by
  rw [Exp.decomp] at h
  split at h
  · simp_all [List.append_eq_nil_iff]
  · exact ⟨by assumption, (Prod.mk.inj h).2⟩

theorem Exp.decomp_inv_cons {Ki : EctxItem α} {K : Ectx α} {e e'' : Exp α}
    (h : e.decomp = (K ++ [Ki], e'')) :
    ∃ e', e.decompItem = some (Ki, e') ∧ e'.decomp = (K, e'') := by
  rw [decomp_unfold] at h
  split at h
  · next Ki' e' hd =>
    simp only at h
    obtain ⟨hK, he⟩ := Prod.mk.inj h
    have hlen : e'.decomp.1.length = K.length := by
      have := congrArg List.length hK
      simp at this
      omega
    obtain ⟨hK', hKi⟩ := List.append_inj hK hlen
    rw [List.singleton_inj.mp hKi] at hd
    exact ⟨e', hd, Prod.ext hK' (by simp [he])⟩
  · simp_all [List.append_eq_nil_iff]

theorem Exp.decomp_fill {K : Ectx α} {e e' : Exp α} (h : e.decomp = (K, e')) :
    K.fill e' = e := by
  induction K using List.reverseRecOn generalizing e e' with
  | nil => exact (decomp_inv_nil h).2.symm
  | append_singleton K Ki ih =>
    obtain ⟨e'', hKi, hK⟩ := decomp_inv_cons h
    rw [Ectx.fill_snoc, ih hK]
    exact (decompItem_fill hKi).1

theorem Exp.decomp_val_empty {K : Ectx α} {e e' : Exp α}
    (hd : e.decomp = (K, e')) (hv : e'.isValue) : K = [] := by
  induction K using List.reverseRecOn generalizing e e' with
  | nil => rfl
  | append_singleton K Ki ih =>
    obtain ⟨e'', hKi, hK⟩ := decomp_inv_cons hd
    rw [ih hK hv] at hK
    rw [(decomp_inv_nil hK).2] at hKi
    exact absurd hv (decompItem_fill hKi).2

/-- Decomposing `K[e]` for a non-value `e` is `e`'s decomposition with `K` appended outside. -/
theorem Exp.decomp_fill_comp {e e' : Exp α} {K K' : Ectx α}
    (hv : ¬e.isValue) (hd : e.decomp = (K', e')) :
    (K.fill e).decomp = (K' ++ K, e') := by
  induction K using List.reverseRecOn with
  | nil => simpa
  | append_singleton K Ki ih =>
    rw [Ectx.fill_snoc, decomp_unfold, EctxItem.decompItem_fillItem Ki (Ectx.fill_noVal hv)]
    simp only [ih, List.append_assoc]

theorem Exp.decomp_snd_fill {K : Ectx α} {e : Exp α} (hv : ¬e.isValue)
    (hd : e.decompItem = none) : (K.fill e).decomp.2 = e := by
  have he : e.decomp = ([], e) := by rw [Exp.decomp_unfold, hd]
  rw [Exp.decomp_fill_comp hv he]

end WithRealParam
end ProbLang
