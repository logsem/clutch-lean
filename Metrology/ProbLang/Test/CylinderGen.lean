module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.Shapes
public import Metrology.ProbLang.CoreMeasures.BaseLit

meta import Metrology.Meta
meta import Metrology.ProbLang.CoreMeasures.CylinderGen
meta import Metrology.ProbLang.CoreMeasures.ArmTactics

@[expose] public section

/-! # Tests for the `MeasurableSpace` deriving handler

Each test type targets one assumption of the generator (names, field types, orders, arities).
`Api` states what the generated declarations promise, as a user would use them. Unsupported inputs
must fail with a clear error. -/

noncomputable section CylinderGenTest

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

namespace CylinderGenTest

set_option hygiene false in
/-- Semantic checks of the generated declarations, run in the namespace of a type `T` applied to
concrete parameters: a value is its shape and its leaves, `T` has the σ-algebra of the sum over
shapes, and the constructors are measurable embeddings. -/
macro "selftest " T:term:max : command => `(
  example (x : $T) : ofSigma (toSigma x) = x := ofSigma_toSigma x
  example : Function.Bijective (toSigma : $T → _) := equivSigma.bijective
  example : (inferInstance : MeasurableSpace $T) = .comap toSigma inferInstance := rfl
  example (x : $T) : measurableEquiv x = toSigma x := rfl
  example : Countable Shape := inferInstance)

set_option hygiene false in
/-- `T` has measurable singletons. -/
macro "singletons_test " T:term:max : command => `(
  example (x : $T) : MeasurableSet {x} := measurableSet_singleton x)

/-! ## Classification -/

namespace Kinds
inductive Tm (rT : Type _)
  | nil
  | k (n : Nat) (b : Bool) (z : Int) (f : Fin 3) (u : Unit) (o : Option Bool) (bn : Bool × Nat)
  | d (r : rT) (l : BaseLit rT) (rn : rT × Nat) (fn : Nat → rT)
  | rc (t : Tm rT) (ts : Tm rT)

/--
info: nil: nullary
k: (n : ℕ) base, (b : Bool) base, (z : ℤ) base, (f : Fin 3) base, (u : Unit) base, (o : Option Bool) data, (bn : Bool × ℕ) base
d: (r : rT) data, (l : BaseLit rT) data, (rn : rT × ℕ) data, (fn : ℕ → rT) data
rc: (t : Tm rT) recursive, (ts : Tm rT) recursive
-/
#guard_msgs in #cylinder_classify Tm
end Kinds

/-! ## Names -/

/-! No parameters; constructors named like the generator's pattern variables (`s`, `c`, `x`,
`S`, `r`, `p`, `b`). -/
namespace NoParams
inductive Tm
  | x
  | s (t : Tm)
  | c (n : Nat) (t : Tm)
  | S (b : Bool)
  | r (t u : Tm)
  | p (q : ℝ) (k : Nat)
  | b (r : ℝ) (t : Tm)
namespace Tm
deriving instance MeasurableSpace for Tm
selftest Tm
singletons_test Tm
example (n : ℕ) (t : Tm) : (Tm.c n t).shape = .c n t.shape := by simp
end Tm
end NoParams

/-! Parameters named like generated binders and type variables. -/
namespace ParamS
inductive Tm (S : Type _) | nil | a (r : S) (t : Tm S)
namespace Tm
deriving instance MeasurableSpace for Tm
selftest (Tm ℝ)
end Tm
end ParamS

namespace ParamC
inductive Tm (c : Type _) (h : Type _) | nil | a (r : c) (t u : Tm c h) | b (q : h) (t : Tm c h)
namespace Tm
deriving instance MeasurableSpace for Tm
selftest (Tm ℝ ℝ)
singletons_test (Tm ℝ ℝ)
end Tm
end ParamC

/-! A parameter named `β`: the threaded parameter of `measurable_casesOn_param` is named `β'`. -/
namespace ParamBeta
inductive Tm (β : Type _) | nil | a (r : β) (t : Tm β)
namespace Tm
deriving instance MeasurableSpace for Tm
selftest (Tm ℝ)
example {β : Type} [MeasurableSpace β] :
    Measurable (fun p : Tm β × ℕ => Tm.casesOn (motive := fun _ => ℕ) p.1 p.2 (fun _ _ => p.2)) :=
  measurable_casesOn_param (α := ℕ) (fun q => q) (fun q => q.1) (by fun_prop) (by fun_prop)
end Tm
end ParamBeta

/-! Fields named like generated declarations (`Shape`, `S`), globals (`Set`), or the parameter
(`rT`). -/
namespace FieldNames
inductive Tm (rT : Type _)
  | nil
  | a (S : Nat) (c : Tm rT) (x : rT)
  | b (Shape : Nat) (t : Tm rT)
  | d (HasMeasurableLeaves : Bool) (t : Tm rT)
  | e (Set : Bool) (r : rT)
  | f (q : rT) (rT : Nat)
  | g : Nat → Tm rT → Tm rT
namespace Tm
deriving instance MeasurableSpace for Tm
selftest (Tm ℝ)
/-- `Shape` keeps the names of the fields, so named arguments work. -/
example (s : Shape) : Shape := Shape.a (S := 3) (c := s)
end Tm
end FieldNames

/-! Constructor names that are keywords or need escaping. -/
namespace Keywords
inductive Tm | «end» | «fun» (t : Tm) | case (n : Nat) | rec' (t : Tm) | «match» (b : Bool) (t : Tm)
namespace Tm
deriving instance MeasurableSpace for Tm
selftest Tm
end Tm
end Keywords

/-! ## Field types and orders -/

/-! Products, sums and functions as field types. -/
namespace Tuples
inductive Tm (rT : Type _)
  | nil
  | pr (bn : Bool × Nat) (t : Tm rT) (k : Nat)
  | fn (f : Nat → rT) (t : Tm rT)
  | pd (q : rT × rT) (o : Option Bool)
  | sm (e : Bool ⊕ Nat) (t : Tm rT) (u : Tm rT)
namespace Tm
deriving instance MeasurableSpace for Tm
selftest (Tm ℝ)
example : MeasurableEmbedding (fun p : (Bool × ℕ) × Tm ℝ × ℕ => Tm.pr p.1 p.2.1 p.2.2) :=
  pr.measurableEmbedding
example : MeasurableEmbedding (fun p : (Bool ⊕ ℕ) × Tm ℝ × Tm ℝ => Tm.sm p.1 p.2.1 p.2.2) :=
  sm.measurableEmbedding
end Tm
end Tuples

/-! Every placement of base, data and recursive fields. -/
namespace Order
inductive Tm (rT : Type _)
  | nil
  | recFirst (t : Tm rT) (n : Nat)
  | dataFirst (r : rT) (n : Nat)
  | sandwich (n : Nat) (t : Tm rT) (m : Bool) (r : rT) (u : Tm rT) (k : Nat)
  | bases (a : Nat) (b : Bool) (c : Int)
namespace Tm
deriving instance MeasurableSpace for Tm
selftest (Tm ℝ)
singletons_test (Tm ℝ)
example (n : ℕ) (t : Tm ℝ) (m : Bool) (r : ℝ) (u : Tm ℝ) (k : ℕ) :
    (Tm.sandwich n t m r u k).shape = .sandwich n t.shape m u.shape k := by simp
example : MeasurableEmbedding
    (fun p : ℕ × Tm ℝ × Bool × ℝ × Tm ℝ × ℕ => Tm.sandwich p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) :=
  sandwich.measurableEmbedding
end Tm
end Order

/-! A single constructor. -/
namespace Single
inductive Tm (rT : Type _) | only (r : rT) (n : Nat)
namespace Tm
deriving instance MeasurableSpace for Tm
selftest (Tm ℝ)
end Tm
end Single

/-! Arity 5 for recursive and base fields. -/
namespace Wide
inductive Tm | nil | five (a b c d e : Tm) | wide (a b c d e : Nat)
namespace Tm
deriving instance MeasurableSpace for Tm
selftest Tm
example : Function.Injective (@Tm.five.ι) := five.ι.inj
end Tm
end Wide

/-! Degenerate base types, reals, and a parameter in `Type` rather than `Type _`. -/
namespace Odd
inductive Tm (rT : Type) | nil | u (x : Unit) (t : Tm rT) | e (x : Empty) | f (i : Fin 3) (t : Tm rT)
  | r (x : ℝ) (y : rT) | rr (x y : ℝ)
namespace Tm
deriving instance MeasurableSpace for Tm
selftest (Tm ℝ)
end Tm
end Odd

/-! ## No nullary constructor, and names the generator uses for its own variables -/

namespace Lemmas
inductive Tm (h : Type _) | c (n : Nat) (t : Tm h) | s (t u : Tm h) | p (r : h)
namespace Tm
deriving instance MeasurableSpace for Tm
selftest (Tm ℝ)
singletons_test (Tm ℝ)
end Tm
end Lemmas

/-! ## The generated API

What deriving `MeasurableSpace` promises, stated as a user would state it, on a small type with one
field of each kind. -/

namespace Api
inductive Tm (rT : Type _) | z | s (n : Nat) (t : Tm rT) (r : rT)
namespace Tm
deriving instance MeasurableSpace for Tm
selftest (Tm ℝ)

/-! A value is its shape and its leaves. -/

example (n : ℕ) (t : Tm ℝ) (r : ℝ) :
    toSigma (Tm.s n t r) = ⟨.s n t.shape, (PUnit.unit, (toSigma t).2, ULift.up r)⟩ := rfl
example (n : ℕ) (t : Tm ℝ) (r : ℝ) : (Tm.s n t r).shape = .s n t.shape := by simp
example (p : Σ s, Leaves (rT := ℝ) s) : toSigma (ofSigma p) = p := toSigma_ofSigma p
example (n : ℕ) : Leaves (rT := ℝ) (.s n .z) = (PUnit × PUnit × ULift ℝ) := rfl

/-! The σ-algebra is that of the sum over shapes. -/

example : (inferInstance : MeasurableSpace (Tm ℝ)) = .comap toSigma inferInstance := rfl
example : Measurable (toSigma : Tm ℝ → _) := measurableEquiv.measurable

/-! Constructors are measurable embeddings with measurable projections, and the automation finds
them. -/

example : Function.Injective (Tm.s.ι (rT := ℝ)) := s.ι.inj
example : Measurable (fun p : ℕ × Tm ℝ × ℝ => Tm.s p.1 p.2.1 p.2.2) := by fun_prop
example (t : Tm ℝ) : Measurable (fun r : ℝ => Tm.s 3 t r) := by fun_prop
example : MeasurableEmbedding (fun _ : Unit => (Tm.z : Tm ℝ)) := z.measurableEmbedding
example : MeasurableEmbedding (fun p : ℕ × Tm ℝ × ℝ => Tm.s p.1 p.2.1 p.2.2) := s.measurableEmbedding
example : Measurable (Tm.s.π (rT := ℝ)) := by fun_prop
example : MeasurableSet (Set.range (Tm.s.ι (rT := ℝ))) := s.measurableEmbedding.measurableSet_range
example : MeasurableSingletonClass (Tm ℝ) := inferInstance

/-! Functions by cases and by structural recursion are measurable when their arms are. -/

example (g : ℝ → ℕ) (hg : Measurable g) :
    Measurable (fun t : Tm ℝ => Tm.casesOn (motive := fun _ => ℕ) t 0 (fun n _ r => n + g r)) :=
  measurable_casesOn (fun _ => 0) (fun p => p.1 + g p.2.2) (by fun_prop)
example :
    Measurable (fun p : Tm ℝ × ℕ => Tm.casesOn (motive := fun _ => ℕ) p.1 p.2 (fun n _ _ => n + p.2)) :=
  measurable_casesOn_param (fun q => q) (fun q => q.2.1 + q.1) (by fun_prop) (by fun_prop)

/-- Sums the base fields. -/
def total : Tm ℝ → ℕ
  | .z => 0
  | .s n t _ => n + total t

example : Measurable total := by
  apply measurable_struct_rec (c_z := 0) (c_s := fun n k _ => n + k)
  case eq_z => rfl
  case eq_s => intro _ _ _; rfl
  case h_s => fun_prop

/-- Sums the base fields, starting from `b`. -/
def totalFrom (b : ℕ) : Tm ℝ → ℕ
  | .z => b
  | .s n t _ => n + totalFrom b t

example : Measurable (Function.uncurry totalFrom) := by
  apply measurable_struct_rec_param (c_z := fun b => b) (c_s := fun _ n k _ => n + k)
  case eq_z => intro _; rfl
  case eq_s => intro _ _ _ _; rfl
  case h_z => fun_prop
  case h_s => fun_prop
  case ht_s => fun_prop

/-- Sums the base fields, each weighted by its depth below `b`: the parameter shifts at `s`. -/
def weighted (b : ℕ) : Tm ℝ → ℕ
  | .z => 0
  | .s n t _ => b * n + weighted (b + 1) t

example : Measurable (Function.uncurry weighted) := by
  apply measurable_struct_rec_param (c_z := fun _ => 0) (c_s := fun b n k _ => b * n + k)
    (t_s := fun b => b + 1)
  case eq_z => intro _; rfl
  case eq_s => intro _ _ _ _; rfl
  case h_z => fun_prop
  case h_s => fun_prop
  case ht_s => fun_prop

/-- The subterm of an `s`, by cases. -/
def child : Tm ℝ → Option (Tm ℝ)
  | .z => none
  | .s _ t _ => some t

example : Measurable child := by apply_arms measurable_cases

/-- The `ℝ` field of an `s`, or `b`. -/
def realOr (b : ℝ) : Tm ℝ → ℝ
  | .z => b
  | .s _ _ r => r

example : Measurable (Function.uncurry realOr) := by apply_arms measurable_cases_param

/-- Arms are read off the definition, also by structural recursion. -/
example : Measurable total := by apply_arms measurable_struct_rec
example : Measurable (Function.uncurry weighted) := by
  apply_arms measurable_struct_rec_param (t_s := fun b => b + 1)

end Tm
end Api

/-! ## Inputs found by adversarial testing -/

namespace KeywordParam
inductive Tm («end» : Type) | nil | a (r : «end») (t : Tm «end»)
namespace Tm
deriving instance MeasurableSpace for Tm
selftest (Tm ℝ)
end Tm
end KeywordParam

namespace SixGreek
inductive Tm (α β γ δ ε ζ : Type) | nil | a (r : α) (s : ζ) (t : Tm α β γ δ ε ζ)
namespace Tm
deriving instance MeasurableSpace for Tm
end Tm
end SixGreek

/-! Fields with default values. -/
namespace Defaults
inductive Tm (rT : Type _) | nil | a (n : ℕ := 3) (t : Tm rT) | b (r : rT := by exact default)
namespace Tm
deriving instance MeasurableSpace for Tm
selftest (Tm ℝ)
end Tm
end Defaults

/-! A field type that prints ambiguously without type ascriptions. -/
namespace Interval
inductive Tm | nil | a (p : Set.Icc (0 : ℝ) 1) (t : Tm)
namespace Tm
deriving instance MeasurableSpace for Tm
selftest Tm
end Tm
end Interval

/-! An uninhabited base field. -/
namespace EmptyFirst
inductive Tm (rT : Type _) | e (x : Empty) | f (n : ℕ) | s (t : Tm rT)
namespace Tm
deriving instance MeasurableSpace for Tm
end Tm
end EmptyFirst

namespace SingleNullary
inductive Tm (rT : Type _) | a
namespace Tm
deriving instance MeasurableSpace for Tm
selftest (Tm ℝ)
end Tm
end SingleNullary

/-! Many base fields (one `if`) and many recursive fields (one case per field). -/
namespace ManyFields
inductive Tm | nil | w (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Bool)
  | big (t0 t1 t2 t3 t4 t5 t6 t7 t8 : Tm)
namespace Tm
deriving instance MeasurableSpace for Tm
end Tm
end ManyFields

/-! Names that need escaping, and arm binders `f_<ctor>` that would coincide. -/
namespace Escaped
inductive «my Tm» | nil | «a b» (t : «my Tm») | f_a | a (n : ℕ) | a' (b : Bool) (t : «my Tm»)
namespace «my Tm»
deriving instance MeasurableSpace for «my Tm»
end «my Tm»
end Escaped

/-! Section variables named like globals the generated code uses. -/
namespace SectionVars
section
variable (Unit : Type) (Fin : ℕ) (x1 : ℕ) {rT : Type}
inductive Tm (rT : Type _) | nil | a (r : rT) (n : ℕ) (t : Tm rT)
namespace Tm
deriving instance MeasurableSpace for Tm
end Tm
end
end SectionVars

/-! Data fields whose type is a product with a small finite factor, next to base fields. -/
namespace FiniteFactors
inductive Tm | nil | c (a : ℝ × Bool) (b : ℕ) | d (b : Fin 1) (a : ℝ × Fin 2) (t : Tm)
namespace Tm
deriving instance MeasurableSpace for Tm
example : Measurable (fun p : (ℝ × Bool) × ℕ => Tm.c p.1 p.2) := by fun_prop
example (f : Tm → ℝ) (hf : Measurable f) :
    Measurable (fun t : Tm => Tm.casesOn (motive := fun _ => ℝ) t 0 (fun _ n => n) (fun _ _ t => f t)) :=
  measurable_casesOn (fun _ => 0) (fun p => (p.2 : ℝ)) (fun p => f p.2.2) (by fun_prop) (by fun_prop)
end Tm
end FiniteFactors

/-! A `Prop` base field, without `open Classical` in scope. -/
namespace PropField
section
open MeasureTheory
inductive Tm | nil | c (b : Prop) (t : Tm)
namespace Tm
deriving instance MeasurableSpace for Tm
end Tm
end
end PropField

/-! ## Names the generated code uses

The generated declarations are built as terms, so the user's names cannot capture anything. -/

namespace ParamNamespace
inductive Tm (CylinderGenTest : Type) | nil | a (r : CylinderGenTest) (t : Tm CylinderGenTest)
namespace Tm
deriving instance MeasurableSpace for Tm
selftest (Tm ℝ)
end Tm
end ParamNamespace

/-! A type without a base case is empty, and still a measurable space. -/
namespace NoBaseCase
inductive Tm | a (t : Tm) | b (t u : Tm)
namespace Tm
deriving instance MeasurableSpace for Tm
selftest Tm
end Tm
end NoBaseCase

namespace ParamSet
inductive Tm (Set : Type) | nil | a (r : Set) (t : Tm Set)
namespace Tm
deriving instance MeasurableSpace for Tm
selftest (Tm ℝ)
end Tm
end ParamSet

namespace CtorNone
inductive Tm | none | some (n : ℕ) (t : Tm)
namespace Tm
deriving instance MeasurableSpace for Tm
selftest Tm
end Tm
end CtorNone

namespace Shadowed
def MeasurableSet (n : ℕ) : ℕ := n
inductive Tm (rT : Type _) | nil | a (r : rT) (t : Tm rT)
namespace Tm
deriving instance MeasurableSpace for Tm
end Tm
end Shadowed

namespace ShadowedDotted
namespace MeasurableSet
theorem singleton : True := trivial
end MeasurableSet
inductive Tm | nil | a (n : ℕ) (t : Tm)
namespace Tm
deriving instance MeasurableSpace for Tm
selftest Tm
end Tm
end ShadowedDotted

/-! Shift binders: `h` + `t_x` and `ht` + `x` must not collide. -/
namespace ShiftClash
inductive Tm (rT : Type _) | nil | x (t : Tm rT) | t_x (t : Tm rT)
namespace Tm
deriving instance MeasurableSpace for Tm
end Tm
end ShiftClash

namespace EscapedShift
inductive Tm (rT : Type _) | nil | «a b» (t : Tm rT) | «if» (t u : Tm rT)
namespace Tm
deriving instance MeasurableSpace for Tm
end Tm
end EscapedShift

/-! A field type that does not print back to itself: the generated code never prints types. -/
namespace Unprintable
inductive Tm | nil | a (s : ({0, 1} : Finset ℤ)) (t : Tm)
namespace Tm
deriving instance MeasurableSpace for Tm
selftest Tm
end Tm
end Unprintable

/-! ## Rejected inputs -/

namespace Rejected

mutual
inductive Ev | zero | succ (o : Od)
inductive Od | succ (e : Ev)
end
/-- error: cylinders: mutual inductive blocks are not supported yet -/
#guard_msgs in #cylinder_classify Ev

inductive Nested | node (ts : List Nested)
/-- error: cylinders: nested inductives are not supported -/
#guard_msgs in #cylinder_classify Nested

inductive Indexed : Nat → Type | z : Indexed 0 | s (n : Nat) (t : Indexed n) : Indexed (n + 1)
/-- error: cylinders: indexed families are not supported -/
#guard_msgs in #cylinder_classify Indexed

inductive Dependent | mk (n : Nat) (i : Fin n)
/-- error: cylinders: dependent field type Fin n is not supported -/
#guard_msgs in #cylinder_classify Dependent

inductive ValueParam (n : Nat) | nil | a (i : Fin n)
/-- error: cylinders: parameter n must be a `Type _`, got ℕ -/
#guard_msgs in #cylinder_classify ValueParam

inductive PropParam (P : Prop) | nil | a (h : P)
/-- error: cylinders: parameter P must be a `Type _`, got Prop -/
#guard_msgs in #cylinder_classify PropParam

structure NoMeas where n : Nat
inductive NoInstance | nil | a (m : NoMeas)
/-- error: cylinders: field type NoMeas has no `MeasurableSpace` instance -/
#guard_msgs in #cylinder_classify NoInstance

inductive Implicit | nil | a {n : Nat} (t : Implicit)
/--
error: cylinders: constructor `CylinderGenTest.Rejected.Implicit.a` has a non-explicit field `n`; only explicit fields are supported
-/
#guard_msgs in #cylinder_classify Implicit

inductive InstImplicit | nil | a [i : Inhabited Nat] (t : InstImplicit)
/--
error: cylinders: constructor `CylinderGenTest.Rejected.InstImplicit.a` has a non-explicit field `i`; only explicit fields are supported
-/
#guard_msgs in #cylinder_classify InstImplicit

inductive CtorShape | nil | Shape (t : CtorShape)
/-- error: cylinders: `CylinderGenTest.Rejected.CtorShape.Shape` already exists -/
#guard_msgs in deriving instance MeasurableSpace for CtorShape

inductive FnRec | nil | a (f : ℕ → FnRec)
/--
error: cylinders: field type ℕ → FnRec contains `CylinderGenTest.Rejected.FnRec` in an unsupported position
-/
#guard_msgs in #cylinder_classify FnRec

inductive ImplicitParam {rT : Type} | nil | c (r : rT) (t : @ImplicitParam rT)
/-- error: cylinders: parameter `rT` must be explicit -/
#guard_msgs in #cylinder_classify ImplicitParam

inductive InProp : Prop | nil | c (t : InProp)
/-- error: cylinders: `CylinderGenTest.Rejected.InProp` is a `Prop` -/
#guard_msgs in #cylinder_classify InProp

end Rejected

end CylinderGenTest

end CylinderGenTest
