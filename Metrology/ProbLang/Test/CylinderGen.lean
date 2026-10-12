module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.Cylinders
public import Metrology.ProbLang.CoreMeasures.BaseLit

meta import Metrology.Meta
meta import Metrology.ProbLang.CoreMeasures.CylinderGen

@[expose] public section

/-! # Tests for the cylinder generator

Each test type targets one assumption of the generator (name clashes, field types, orders,
arities). Unsupported inputs must fail with a clear error. -/

noncomputable section CylinderGenTest

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

namespace CylinderGenTest

set_option hygiene false in
/-- Semantic checks of the generated definitions, run in the type's namespace, for a type `T`
and its cylinder type `C` applied to concrete parameters. -/
macro "selftest " T:term:max C:term:max : command => `(
  example (x : $T) : x ∈ (Shape.cylinder x.shape : $C).flatten := by
    induction x
    all_goals aesop
  example (s : Shape) : (Shape.cylinder s : $C).shape = s := by
    induction s
    all_goals simp_all
  example (x : $T) : (singletonCyl x).flatten = {x} := by
    induction x
    all_goals aesop
  example (x : $T) : (singletonCyl x).shape = x.shape := by
    induction x
    all_goals simp_all
  example (s : Shape) : MeasurableSet (Shape.cylinder s : $C).flatten :=
    flatten_measurable (Shape.cylinder_hasMeasurableLeaves s))

set_option hygiene false in
/-- The generated `measurability` rules fire on cylinders. -/
macro "measurability_test " C:term:max : command => `(
  example (s : Shape) : (Shape.cylinder s : $C).HasMeasurableLeaves := by measurability
  example (c : $C) (h : c.HasMeasurableLeaves) : MeasurableSet c.flatten := by measurability)

/-! ## Classification -/

namespace Kinds
@[uncurriedProjections, constructors]
inductive Tm (rT : Type _)
  | nil
  | k (n : Nat) (b : Bool) (z : Int) (f : Fin 3) (u : Unit) (o : Option Bool) (bn : Bool × Nat)
  | d (r : rT) (l : BaseLit rT) (rn : rT × Nat) (fn : Nat → rT)
  | rc (t : Tm rT) (ts : Tm rT)

/--
info: nil: nullary
k: (n : ℕ) base, (b : Bool) base, (z : ℤ) base, (f : Fin (3 : ℕ)) base, (u : Unit) base, (o : Option Bool) data, (bn : Bool × ℕ) base
d: (r : rT) data, (l : ProbLang.BaseLit rT) data, (rn : rT × ℕ) data, (fn : ℕ → rT) data
rc: (t : CylinderGenTest.Kinds.Tm rT) recursive, (ts : CylinderGenTest.Kinds.Tm rT) recursive
-/
#guard_msgs in #cylinder_classify Tm
end Kinds

/-! ## Names -/

/-! No parameters; constructors named like the generator's pattern variables (`s`, `c`, `x`,
`S`, `r`, `p`, `b`). -/
namespace NoParams
@[uncurriedProjections, constructors]
inductive Tm
  | x
  | s (t : Tm)
  | c (n : Nat) (t : Tm)
  | S (b : Bool)
  | r (t u : Tm)
  | p (q : ℝ) (k : Nat)
  | b (r : ℝ) (t : Tm)
namespace Tm
cylinder_defs Tm
selftest Tm Cylinder
measurability_test Cylinder
example : Cylinder.inter? (.c 1 .x) (.c 1 .x) = some (.c 1 .x) := by simp [Cylinder.inter?]
example : Cylinder.inter? (.c 1 .x) (.c 2 .x) = none := by simp [Cylinder.inter?]
example : Cylinder.inter? (.c 1 .x) (.s .x) = none := by simp [Cylinder.inter?]
example (A B : Set ℝ) : Cylinder.inter? (.p A 3) (.p B 3) = some (.p (A ∩ B) 3) := by
  simp [Cylinder.inter?]
end Tm
end NoParams

/-! Parameters named like generated binders and type variables. -/
namespace ParamS
@[uncurriedProjections, constructors]
inductive Tm (S : Type _) | nil | a (r : S) (t : Tm S)
namespace Tm
cylinder_defs Tm
selftest (Tm ℝ) (Cylinder ℝ)
measurability_test (Cylinder ℝ)
end Tm
end ParamS

namespace ParamC
@[uncurriedProjections, constructors]
inductive Tm (c : Type _) (h : Type _) | nil | a (r : c) (t u : Tm c h) | b (q : h) (t : Tm c h)
namespace Tm
cylinder_defs Tm
selftest (Tm ℝ ℝ) (Cylinder ℝ ℝ)
measurability_test (Cylinder ℝ ℝ)
example {c h : Type _} (s : Shape) : (Shape.cylinder s : Cylinder c h).flatten = Tm.shape ⁻¹' {s} :=
  Shape.cylinder_preimage_shape s
end Tm
end ParamC

/-! A parameter named `β`: `decompCell_param`'s threaded type must not capture it. -/
namespace ParamBeta
@[uncurriedProjections, constructors]
inductive Tm (β : Type _) | nil | a (r : β) (t : Tm β)
namespace Tm
cylinder_defs Tm
selftest (Tm ℝ) (Cylinder ℝ)
example {β γ δ : Type} (S : Set δ) (f_nil : γ × Unit → δ) (f_a : γ × β × Tm β → δ) :
    Fin 2 → Set (Tm β × γ) :=
  decompCell_param S f_nil f_a
example {β δ : Type} (S : Set δ) (f_nil : Unit → δ) (f_a : β × Tm β → δ) : Fin 2 → Set (Tm β) :=
  decompCell S f_nil f_a
end Tm
end ParamBeta

/-! Base fields whose own names would shadow identifiers in the generated code (`Set`,
`Shape`, `HasMeasurableLeaves`), the parameter (`rT`) or generated names (`S`, `c`). -/
namespace FieldNames
@[uncurriedProjections, constructors]
inductive Tm (rT : Type _)
  | nil
  | a (S : Nat) (c : Tm rT) (x : rT)
  | b (Shape : Nat) (t : Tm rT)
  | d (HasMeasurableLeaves : Bool) (t : Tm rT)
  | e (Set : Bool) (r : rT)
  | f (q : rT) (rT : Nat)
  | g : Nat → Tm rT → Tm rT
namespace Tm
cylinder_defs Tm
selftest (Tm ℝ) (Cylinder ℝ)
measurability_test (Cylinder ℝ)
/-- Own names survive where safe, so named arguments keep working. -/
example (c : Cylinder ℝ) (h : c.HasMeasurableLeaves) :
    (Cylinder.a (S := 3) c Set.univ).HasMeasurableLeaves :=
  And.intro h MeasurableSet.univ
end Tm
end FieldNames

/-! Constructor names that are keywords or need escaping. -/
namespace Keywords
@[uncurriedProjections, constructors]
inductive Tm | «end» | «fun» (t : Tm) | case (n : Nat) | rec' (t : Tm) | «match» (b : Bool) (t : Tm)
namespace Tm
cylinder_defs Tm
selftest Tm Cylinder
end Tm
end Keywords

/-! ## Field types and orders -/

/-! Products, sums and functions as field types: these must be parenthesised inside the
generated tuple types. -/
namespace Tuples
@[uncurriedProjections, constructors]
inductive Tm (rT : Type _)
  | nil
  | pr (bn : Bool × Nat) (t : Tm rT) (k : Nat)
  | fn (f : Nat → rT) (t : Tm rT)
  | pd (q : rT × rT) (o : Option Bool)
  | sm (e : Bool ⊕ Nat) (t : Tm rT) (u : Tm rT)
namespace Tm
cylinder_defs Tm
selftest (Tm ℝ) (Cylinder ℝ)
measurability_test (Cylinder ℝ)
example (S : Set ((Bool × ℕ) × Shape × ℕ)) : Set (Tm ℝ) := cover.pr S
example {β γ : Type} (S : Set γ) (f : β × (Bool × ℕ) × Tm ℝ × ℕ → γ) : Set (Tm ℝ × β) :=
  (fun q : β × (Bool × ℕ) × Tm ℝ × ℕ => (Tm.pr q.2.1 q.2.2.1 q.2.2.2, q.1)) '' (f ⁻¹' S)
end Tm
end Tuples

/-! Every placement of base, data and recursive fields, including a non-base field that is not
last and several base fields (nested `if`s in `inter?`). -/
namespace Order
@[uncurriedProjections, constructors]
inductive Tm (rT : Type _)
  | nil
  | recFirst (t : Tm rT) (n : Nat)
  | dataFirst (r : rT) (n : Nat)
  | sandwich (n : Nat) (t : Tm rT) (m : Bool) (r : rT) (u : Tm rT) (k : Nat)
  | bases (a : Nat) (b : Bool) (c : Int)
namespace Tm
cylinder_defs Tm
selftest (Tm ℝ) (Cylinder ℝ)
measurability_test (Cylinder ℝ)
example : Cylinder.inter? (rT := ℝ) (.bases 1 true 2) (.bases 1 true 2) = some (.bases 1 true 2) := by
  simp [Cylinder.inter?]
example : Cylinder.inter? (rT := ℝ) (.bases 1 true 2) (.bases 1 false 2) = none := by
  simp [Cylinder.inter?]
example : Cylinder.inter? (rT := ℝ) (.bases 1 true 2) (.bases 1 true 3) = none := by
  simp [Cylinder.inter?]
end Tm
end Order

/-! A single constructor (no catch-all in `inter?`). -/
namespace Single
@[uncurriedProjections, constructors]
inductive Tm (rT : Type _) | only (r : rT) (n : Nat)
namespace Tm
cylinder_defs Tm
selftest (Tm ℝ) (Cylinder ℝ)
end Tm
end Single

/-! Arity 5 for recursive and base fields. -/
namespace Wide
@[uncurriedProjections, constructors]
inductive Tm | nil | five (a b c d e : Tm) | wide (a b c d e : Nat)
namespace Tm
cylinder_defs Tm
selftest Tm Cylinder
measurability_test Cylinder
example : Function.Injective (@Tm.five.ι) := five.ι.inj
end Tm
end Wide

/-! Degenerate base types, reals, and a parameter in `Type` rather than `Type _`. -/
namespace Odd
@[uncurriedProjections, constructors]
inductive Tm (rT : Type) | nil | u (x : Unit) (t : Tm rT) | e (x : Empty) | f (i : Fin 3) (t : Tm rT)
  | r (x : ℝ) (y : rT) | rr (x y : ℝ)
namespace Tm
cylinder_defs Tm
selftest (Tm ℝ) (Cylinder ℝ)
measurability_test (Cylinder ℝ)
end Tm
end Odd

/-! ## The generated lemmas on an awkward type

Parameter `h`, constructors `c`, `s` and `p`: names the lemma generators also use. No nullary
constructor, so `flatten_isCountablySpanning` falls back to the cylinder of the shape `.p`. -/

namespace Lemmas
@[uncurriedProjections, constructors]
inductive Tm (h : Type _) | c (n : Nat) (t : Tm h) | s (t u : Tm h) | p (r : h)
namespace Tm
cylinder_defs Tm
selftest (Tm ℝ) (Cylinder ℝ)
measurability_test (Cylinder ℝ)

example [MeasurableSpace ℝ] : IsPiSystem
    {S : Set (Tm ℝ) | ∃ c : Cylinder ℝ, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S} :=
  Cylinder.flatten_isPiSystem
end Tm
end Lemmas

/-! ## Generated source

The exact output for a small type, as a regression test. -/

namespace Golden
@[uncurriedProjections, constructors]
inductive Tm (rT : Type _) | z | s (n : Nat) (t : Tm rT) (r : rT)
namespace Tm
/--
info: theorem z.ι.inj {rT : Type _} : Function.Injective (@CylinderGenTest.Golden.Tm.z.ι rT) := by (intro a b h; cases h; rfl)

theorem s.ι.inj {rT : Type _} : Function.Injective (@CylinderGenTest.Golden.Tm.s.ι rT) := by
  (intro a b h; obtain ⟨_, _, _⟩ := a; obtain ⟨_, _, _⟩ := b; cases h; rfl)

/-- Cylinders: values with data fields replaced by sets of values. -/
inductive Cylinder (rT : Type _)
  | z
  | s (n : ℕ) (c2 : Cylinder rT) (S3 : Set rT)

/-- Shapes: values with data fields forgotten, so that `Shape` is countable. -/
inductive Shape
  | z
  | s (n : ℕ) (s2 : Shape)
  deriving Countable

/-- The set of values described by a cylinder. -/
def Cylinder.flatten {rT : Type _} : Cylinder rT → Set (CylinderGenTest.Golden.Tm rT)
  | .z => {@CylinderGenTest.Golden.Tm.z rT}
  | .s x1 c2 S3 =>
    (fun p : CylinderGenTest.Golden.Tm rT × rT => @CylinderGenTest.Golden.Tm.s rT x1 p.1 p.2) ''
      Cylinder.flatten c2 ×ˢ S3

theorem Cylinder.flatten_eqs {rT : Type _} :
    Cylinder.flatten (.z : Cylinder rT) = {@CylinderGenTest.Golden.Tm.z rT} ∧
      ∀ x1 c2 S3,
        Cylinder.flatten (.s x1 c2 S3 : Cylinder rT) =
          (fun p : CylinderGenTest.Golden.Tm rT × rT => @CylinderGenTest.Golden.Tm.s rT x1 p.1 p.2) ''
            Cylinder.flatten c2 ×ˢ S3 :=
  ⟨rfl, fun _ _ _ => rfl⟩

/-- A cylinder has measurable leaves if every set it carries is measurable. -/
def Cylinder.HasMeasurableLeaves {rT : Type _} [MeasurableSpace rT] : Cylinder rT → Prop
  | .z => True
  | .s _ c2 S3 => Cylinder.HasMeasurableLeaves c2 ∧ MeasurableSet S3

instance instMeasurableSpaceTm {rT : Type _} [MeasurableSpace rT] : MeasurableSpace (CylinderGenTest.Golden.Tm rT) :=
  .generateFrom <| Cylinder.flatten '' {c : Cylinder rT | c.HasMeasurableLeaves}

/-- The shape of a value. -/
def _root_.CylinderGenTest.Golden.Tm.shape {rT : Type _} : CylinderGenTest.Golden.Tm rT → Shape
  | .z => .z
  | .s x1 c2 _ => .s x1 (CylinderGenTest.Golden.Tm.shape c2)

theorem _root_.CylinderGenTest.Golden.Tm.shape_eqs {rT : Type _} :
    CylinderGenTest.Golden.Tm.shape (.z : CylinderGenTest.Golden.Tm rT) = .z ∧
      ∀ x1 c2 S3,
        CylinderGenTest.Golden.Tm.shape (.s x1 c2 S3 : CylinderGenTest.Golden.Tm rT) =
          .s x1 (CylinderGenTest.Golden.Tm.shape c2) :=
  ⟨rfl, fun _ _ _ => rfl⟩

/-- The shape of a cylinder. -/
def Cylinder.shape {rT : Type _} : Cylinder rT → Shape
  | .z => .z
  | .s x1 c2 _ => .s x1 (Cylinder.shape c2)

theorem Cylinder.shape_eqs {rT : Type _} :
    Cylinder.shape (.z : Cylinder rT) = .z ∧
      ∀ x1 c2 S3, Cylinder.shape (.s x1 c2 S3 : Cylinder rT) = .s x1 (Cylinder.shape c2) :=
  ⟨rfl, fun _ _ _ => rfl⟩

/-- The cylinder of all values of a given shape: `univ` at every data field. -/
def Shape.cylinder {rT : Type _} : Shape → Cylinder rT
  | .z => .z
  | .s x1 s2 => .s x1 (Shape.cylinder s2) Set.univ

theorem Shape.cylinder_eqs {rT : Type _} :
    Shape.cylinder (rT := rT) (.z : Shape) = .z ∧
      ∀ x1 s2, Shape.cylinder (rT := rT) (.s x1 s2 : Shape) = .s x1 (Shape.cylinder s2) Set.univ :=
  ⟨rfl, fun _ _ => rfl⟩

open Classical in
/-- Partial intersection of cylinders: `none` when the intersection is empty. -/
def Cylinder.inter? {rT : Type _} : Cylinder rT → Cylinder rT → Option (Cylinder rT)
  | .z, .z => some .z
  | .s x1 c2 S3, .s x1' c2' S3' =>
    if x1 = x1' then
      match Cylinder.inter? c2 c2' with
      | some r2 => some (.s x1 r2 (S3 ∩ S3'))
      | none => none
    else none
  | _, _ => none

def cover.z {rT : Type _} (S : Set Unit) : Set (CylinderGenTest.Golden.Tm rT) :=
  ⋃ p ∈ S, Cylinder.flatten (Cylinder.z : Cylinder rT)

def cover.s {rT : Type _} (S : Set (ℕ × Shape)) : Set (CylinderGenTest.Golden.Tm rT) :=
  ⋃ p ∈ S, Cylinder.flatten (Cylinder.s p.1 (Shape.cylinder p.2) (Set.univ : Set rT) : Cylinder rT)

/-- Per-constructor cells of the `casesOn` preimage decomposition. -/
def decompCell {rT : Type _} {α : Type _} (S : Set α) (f_z : Unit → α)
    (f_s : ℕ × CylinderGenTest.Golden.Tm rT × rT → α) : Fin 2 → Set (CylinderGenTest.Golden.Tm rT) :=
  ![CylinderGenTest.Golden.Tm.z.ι '' (f_z ⁻¹' S), CylinderGenTest.Golden.Tm.s.ι '' (f_s ⁻¹' S)]

/-- Per-constructor cells of the parameterised `casesOn` preimage decomposition. -/
def decompCell_param {rT : Type _} {α β : Type _} (S : Set α) (f_z : β × Unit → α)
    (f_s : β × ℕ × CylinderGenTest.Golden.Tm rT × rT → α) : Fin 2 → Set (CylinderGenTest.Golden.Tm rT × β) :=
  ![(fun q : β × Unit => (@CylinderGenTest.Golden.Tm.z rT, q.1)) '' (f_z ⁻¹' S),
    (fun q : β × ℕ × CylinderGenTest.Golden.Tm rT × rT =>
        (@CylinderGenTest.Golden.Tm.s rT q.2.1 q.2.2.1 q.2.2.2, q.1)) ''
      (f_s ⁻¹' S)]

/-- The cylinder containing exactly one value. -/
def singletonCyl {rT : Type _} : CylinderGenTest.Golden.Tm rT → Cylinder rT
  | .z => .z
  | .s x1 c2 S3 => .s x1 (singletonCyl c2) {S3}

theorem singletonCyl_eqs {rT : Type _} :
    singletonCyl (.z : CylinderGenTest.Golden.Tm rT) = .z ∧
      ∀ x1 c2 S3, singletonCyl (.s x1 c2 S3 : CylinderGenTest.Golden.Tm rT) = .s x1 (singletonCyl c2) {S3} :=
  ⟨rfl, fun _ _ _ => rfl⟩

/-- The cylinder of a shape has measurable leaves. -/
theorem Shape.cylinder_hasMeasurableLeaves {rT : Type _} [MeasurableSpace rT] (s : Shape) :
    (s.cylinder (rT := rT)).HasMeasurableLeaves := by
  induction s with
  | z => exact True.intro
  | s x1 s2 ih2 => exact And.intro ih2 MeasurableSet.univ

/-- Flattened cylinders with measurable leaves are measurable. -/
@[measurability]
theorem flatten_measurable {rT : Type _} [MeasurableSpace rT] {c : Cylinder rT} (hc : Cylinder.HasMeasurableLeaves c) :
    MeasurableSet (Cylinder.flatten c) :=
  Cylinders.flatten_measurable rfl hc

theorem Cylinder.shape_of_mem_flatten {rT : Type _} {c : Cylinder rT} {t : CylinderGenTest.Golden.Tm rT}
    (h : t ∈ Cylinder.flatten c) : CylinderGenTest.Golden.Tm.shape t = Cylinder.shape c := by
  induction c generalizing t with
  | z =>
    obtain rfl : t = _ := h
    simp only [CylinderGenTest.Golden.Tm.shape_eqs, Cylinder.shape_eqs]
  | s x1 c2 S3 ih2 =>
    obtain ⟨_, ⟨m2, m3⟩, rfl⟩ := h
    simp only [CylinderGenTest.Golden.Tm.shape_eqs, Cylinder.shape_eqs, ih2 m2]

/-- Flattens of cylinders with different shapes are disjoint. -/
theorem Cylinder.flatten_disjoint_of_shape_ne {rT : Type _} {c₁ c₂ : Cylinder rT}
    (h : Cylinder.shape c₁ ≠ Cylinder.shape c₂) : Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ = ∅ :=
  Cylinders.flatten_disjoint_of_shape_ne (cShape := Cylinder.shape) (fun {_ _} h => Cylinder.shape_of_mem_flatten h) h

/-- The cylinder of a shape flattens to the values of that shape. -/
theorem Shape.cylinder_preimage_shape {rT : Type _} (s : Shape) :
    (s.cylinder (rT := rT)).flatten = CylinderGenTest.Golden.Tm.shape ⁻¹' { s } :=
  Cylinders.cylinder_preimage_shape (cShape := Cylinder.shape) (fun {_ _} h => Cylinder.shape_of_mem_flatten h)
    (fun s => by
      induction s <;>
        simp_all [Shape.cylinder_eqs, Cylinder.shape_eqs, CylinderGenTest.Golden.Tm.shape_eqs, Cylinder.flatten_eqs])
    (fun p => by
      induction p <;>
        simp_all [Shape.cylinder_eqs, Cylinder.shape_eqs, CylinderGenTest.Golden.Tm.shape_eqs, Cylinder.flatten_eqs])
    s

theorem Shape.mem_cylinder_shape {rT : Type _} (p : CylinderGenTest.Golden.Tm rT) :
    p ∈ ((CylinderGenTest.Golden.Tm.shape p).cylinder (rT := rT)).flatten := by rw [Shape.cylinder_preimage_shape];
  exact rfl

open Classical in
theorem Cylinder.flatten_inter.z {rT : Type _} :
    ∀ c₂ : Cylinder rT,
      Cylinder.flatten (.z : Cylinder rT) ∩ Cylinder.flatten c₂ =
        (Cylinder.inter? (.z : Cylinder rT) c₂).elim ∅ Cylinder.flatten :=
  by
  intro c₂
  cases c₂
  case z =>
    rw [show Cylinder.inter? .z .z = some .z from rfl]
    simp only [Cylinder.flatten_eqs, Option.elim, Set.prod_inter_prod, Set.prod_empty, Set.empty_prod, Set.image_empty,
      Set.inter_self]
  all_goals exact Cylinder.flatten_disjoint_of_shape_ne Shape.noConfusion

open Classical in
theorem Cylinder.flatten_inter.s {rT : Type _} (x1 : ℕ) (c2 : Cylinder rT) (S3 : Set rT)
    (ih2 :
      ∀ c₂ : Cylinder rT, Cylinder.flatten c2 ∩ Cylinder.flatten c₂ = (Cylinder.inter? c2 c₂).elim ∅ Cylinder.flatten) :
    ∀ c₂ : Cylinder rT,
      Cylinder.flatten (.s x1 c2 S3 : Cylinder rT) ∩ Cylinder.flatten c₂ =
        (Cylinder.inter? (.s x1 c2 S3 : Cylinder rT) c₂).elim ∅ Cylinder.flatten :=
  by
  intro c₂
  cases c₂
  case s x1' c2' S3' =>
    have h2 := ih2 c2'
    have hF :
      Function.Injective
        (fun p : CylinderGenTest.Golden.Tm rT × rT => @CylinderGenTest.Golden.Tm.s rT x1 p.1 p.2 :
          CylinderGenTest.Golden.Tm rT × rT → CylinderGenTest.Golden.Tm rT) :=
      by (intro a b h; obtain ⟨_, _⟩ := a; obtain ⟨_, _⟩ := b; cases h; rfl)
    rw [show
        Cylinder.inter? (.s x1 c2 S3) (.s x1' c2' S3') =
          if x1 = x1' then
            match Cylinder.inter? c2 c2' with
            | some r2 => some (.s x1 r2 (S3 ∩ S3'))
            | none => none
          else none
        from rfl]
    by_cases hb : x1 = x1'
    case neg => rw [ite_eq_right hb];
      (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp_all [Cylinder.shape_eqs])]; rfl)
    rw [ite_eq_left hb]
    obtain rfl := hb
    rcases e2 : Cylinder.inter? c2 c2' with _ | r2 <;> rw [e2] at h2 <;> simp only [Option.elim] at h2
    ·
      simp only [Cylinder.flatten_eqs, Option.elim, Set.prod_inter_prod, Set.prod_empty, Set.empty_prod,
        Set.image_empty, Set.inter_self, h2, (Set.image_inter hF).symm]
    simp only [Cylinder.flatten_eqs, Option.elim, Set.prod_inter_prod, Set.prod_empty, Set.empty_prod, Set.image_empty,
      Set.inter_self, h2, (Set.image_inter hF).symm]
  all_goals exact Cylinder.flatten_disjoint_of_shape_ne Shape.noConfusion

theorem Cylinder.flatten_inter {rT : Type _} (c₁ : Cylinder rT) :
    ∀ c₂ : Cylinder rT, Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ = (Cylinder.inter? c₁ c₂).elim ∅ Cylinder.flatten :=
  by
  induction c₁ with
  | z => exact Cylinder.flatten_inter.z
  | s x1 c2 S3 ih2 => exact Cylinder.flatten_inter.s x1 c2 S3 ih2

open Classical in
theorem Cylinder.hasMeasurableLeaves_inter.z {rT : Type _} [MeasurableSpace rT] :
    ∀ {c₂ c : Cylinder rT},
      Cylinder.HasMeasurableLeaves (.z : Cylinder rT) →
        c₂.HasMeasurableLeaves → Cylinder.inter? (.z : Cylinder rT) c₂ = some c → c.HasMeasurableLeaves :=
  by
  intro c₂ c h₁ h₂ h
  cases c₂
  case z =>
    rw [show Cylinder.inter? .z .z = some .z from rfl] at h
    try dsimp only at h
    cases h
    exact True.intro
  all_goals nomatch h

open Classical in
theorem Cylinder.hasMeasurableLeaves_inter.s {rT : Type _} [MeasurableSpace rT] (x1 : ℕ) (c2 : Cylinder rT)
    (S3 : Set rT)
    (ih2 :
      ∀ {c₂ c : Cylinder rT},
        Cylinder.HasMeasurableLeaves c2 →
          c₂.HasMeasurableLeaves → Cylinder.inter? c2 c₂ = some c → c.HasMeasurableLeaves) :
    ∀ {c₂ c : Cylinder rT},
      Cylinder.HasMeasurableLeaves (.s x1 c2 S3 : Cylinder rT) →
        c₂.HasMeasurableLeaves → Cylinder.inter? (.s x1 c2 S3 : Cylinder rT) c₂ = some c → c.HasMeasurableLeaves :=
  by
  intro c₂ c h₁ h₂ h
  cases c₂
  case s x1' c2'
    S3' =>
    rw [show
        Cylinder.inter? (.s x1 c2 S3) (.s x1' c2' S3') =
          if x1 = x1' then
            match Cylinder.inter? c2 c2' with
            | some r2 => some (.s x1 r2 (S3 ∩ S3'))
            | none => none
          else none
        from rfl] at h
    obtain ⟨a2, a3⟩ := h₁
    obtain ⟨b2, b3⟩ := h₂
    by_cases hb : x1 = x1'
    case neg => rw [ite_eq_right hb] at h; cases h
    rw [ite_eq_left hb] at h
    obtain rfl := hb
    rcases e2 : Cylinder.inter? c2 c2' with _ | r2 <;> rw [e2] at h
    · simp at h
    try dsimp only at h
    cases h
    exact And.intro (ih2 a2 b2 e2 : Cylinder.HasMeasurableLeaves r2) (MeasurableSet.inter a3 b3)
  all_goals nomatch h

theorem Cylinder.hasMeasurableLeaves_inter {rT : Type _} [MeasurableSpace rT] {c₁ : Cylinder rT} :
    ∀ {c₂ c : Cylinder rT},
      Cylinder.HasMeasurableLeaves c₁ →
        c₂.HasMeasurableLeaves → Cylinder.inter? c₁ c₂ = some c → c.HasMeasurableLeaves :=
  by
  induction c₁ with
  | z => exact Cylinder.hasMeasurableLeaves_inter.z
  | s x1 c2 S3 ih2 => exact Cylinder.hasMeasurableLeaves_inter.s x1 c2 S3 ih2

theorem Cylinder.flatten_inter_some {rT : Type _} {c₁ c₂ c : Cylinder rT} (h : Cylinder.inter? c₁ c₂ = some c) :
    Cylinder.flatten c = Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ :=
  Cylinders.flatten_inter_some Cylinder.flatten_inter h

/-- The flattened cylinders with measurable leaves form a π-system. -/
theorem Cylinder.flatten_isPiSystem {rT : Type _} [MeasurableSpace rT] :
    IsPiSystem
      {S : Set (CylinderGenTest.Golden.Tm rT) | ∃ c : Cylinder rT, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S} :=
  Cylinders.flatten_isPiSystem Cylinder.flatten_inter (fun {_ _ _} => Cylinder.hasMeasurableLeaves_inter)

/-- The flattened cylinders with measurable leaves are countably spanning. -/
theorem Cylinder.flatten_isCountablySpanning {rT : Type _} [MeasurableSpace rT] :
    IsCountablySpanning
      {S : Set (CylinderGenTest.Golden.Tm rT) | ∃ c : Cylinder rT, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S} :=
  Cylinders.flatten_isCountablySpanning Shape.cylinder_hasMeasurableLeaves Shape.cylinder_preimage_shape
    (Shape.cylinder .z) (Shape.cylinder_hasMeasurableLeaves .z)

theorem cover.z.measurable {rT : Type _} [MeasurableSpace rT] (S : Set Unit) :
    MeasurableSet (cover.z S : Set (CylinderGenTest.Golden.Tm rT)) :=
  .biUnion (Set.to_countable _) fun p _ => flatten_measurable True.intro

theorem cover.z_univ_eq_range {rT : Type _} : cover.z Set.univ = Set.range (@CylinderGenTest.Golden.Tm.z.ι rT) :=
  by
  ext t
  constructor
  · (intro h; obtain ⟨p, -, h⟩ := Set.mem_iUnion₂.1 h)
    obtain rfl := h
    exact ⟨⟨⟩, rfl⟩
  · rintro ⟨⟨⟩, rfl⟩
    exact Set.mem_iUnion₂.2 ⟨(), trivial, rfl⟩

theorem z.ι.measurable {rT : Type _} [MeasurableSpace rT] : Measurable (@CylinderGenTest.Golden.Tm.z.ι rT) :=
  measurable_const

theorem z.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable fun _ : Unit => (@CylinderGenTest.Golden.Tm.z rT : CylinderGenTest.Golden.Tm rT) :=
  z.ι.measurable

theorem z.measurableEmbedding {rT : Type _} [MeasurableSpace rT] :
    MeasurableEmbedding fun _ : Unit => (@CylinderGenTest.Golden.Tm.z rT : CylinderGenTest.Golden.Tm rT) :=
  .of_measurable_inverse (g := fun _ => ()) measurable_const
    (by have hS := cover.z.measurable (rT := rT) Set.univ; rw [cover.z_univ_eq_range] at hS; exact hS) measurable_const
    fun _ => rfl

theorem cover.s.measurable {rT : Type _} [MeasurableSpace rT] (S : Set (ℕ × Shape)) :
    MeasurableSet (cover.s S : Set (CylinderGenTest.Golden.Tm rT)) :=
  .biUnion (Set.to_countable _) fun p _ =>
    flatten_measurable (And.intro (Shape.cylinder_hasMeasurableLeaves p.2) MeasurableSet.univ)

theorem cover.s_univ_eq_range {rT : Type _} : cover.s Set.univ = Set.range (@CylinderGenTest.Golden.Tm.s.ι rT) :=
  by
  ext t
  constructor
  · (intro h; obtain ⟨p, -, h⟩ := Set.mem_iUnion₂.1 h)
    obtain ⟨⟨a2, a3⟩, ⟨-, -⟩, rfl⟩ := h
    exact ⟨⟨p.1, a2, a3⟩, rfl⟩
  · rintro ⟨⟨a1, a2, a3⟩, rfl⟩
    exact
      Set.mem_iUnion₂.2
        ⟨⟨a1, CylinderGenTest.Golden.Tm.shape a2⟩, trivial, ⟨⟨a2, a3⟩, ⟨Shape.mem_cylinder_shape a2, trivial⟩, rfl⟩⟩

theorem s.ι.measurable {rT : Type _} [MeasurableSpace rT] : Measurable (@CylinderGenTest.Golden.Tm.s.ι rT) :=
  by
  apply measurable_generateFrom
  rintro _ ⟨s, hS, rfl⟩
  cases s with
  | s x1 c2 S3 =>
    obtain ⟨h2, h3⟩ := hS
    convert (MeasurableSet.singleton x1).prod ((flatten_measurable h2).prod h3) using 1
    ext ⟨a1, a2, a3⟩
    constructor
    · rintro ⟨⟨b2, b3⟩, ⟨m2, m3⟩, h⟩
      cases h
      exact ⟨rfl, m2, m3⟩
    · rintro ⟨rfl, m2, m3⟩
      exact ⟨⟨a2, a3⟩, ⟨m2, m3⟩, rfl⟩
  | _ =>
    exact
      Cylinders.measurableSet_of_forall_notMem fun t h =>
        Shape.noConfusion (Cylinder.shape_of_mem_flatten (Set.mem_preimage.1 h))

theorem s.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable fun (p : ℕ × CylinderGenTest.Golden.Tm rT × rT) => @CylinderGenTest.Golden.Tm.s rT p.1 p.2.1 p.2.2 :=
  s.ι.measurable

theorem s.measurableEmbedding {rT : Type _} [MeasurableSpace rT] :
    MeasurableEmbedding fun (p : ℕ × CylinderGenTest.Golden.Tm rT × rT) =>
      @CylinderGenTest.Golden.Tm.s rT p.1 p.2.1 p.2.2 :=
  measurableEmbedding_of_piSystem₁ (f := @CylinderGenTest.Golden.Tm.s.ι rT) s.ι.inj s.ι.measurable (h_gen :=
    (generateFrom_eq_prod Cylinders.points_generateFrom
        (generateFrom_eq_prod rfl MeasurableSpace.generateFrom_measurableSet Cylinder.flatten_isCountablySpanning
          isCountablySpanning_measurableSet)
        Cylinders.points_isCountablySpanning
        (Cylinder.flatten_isCountablySpanning.prod isCountablySpanning_measurableSet)).symm)
    (h_pi :=
    Cylinders.points_isPiSystem.prod (Cylinder.flatten_isPiSystem.prod MeasurableSpace.isPiSystem_measurableSet))
    (h_basic := by
    rintro _ ⟨_, h1, _, ⟨_, ⟨c2, h2, rfl⟩, S3, h3, rfl⟩, rfl⟩
    rcases h1 with rfl | ⟨x1, rfl⟩
    · simp only [Set.prod_empty, Set.empty_prod, Set.image_empty, MeasurableSet.empty]
    convert flatten_measurable (c := (.s x1 c2 S3 : Cylinder rT)) (And.intro h2 h3) using 1
    ext t
    constructor
    · rintro ⟨⟨a1, a2, a3⟩, ⟨rfl, m2, m3⟩, rfl⟩
      exact ⟨⟨a2, a3⟩, ⟨m2, m3⟩, rfl⟩
    · rintro ⟨⟨a2, a3⟩, ⟨m2, m3⟩, rfl⟩
      exact ⟨⟨x1, a2, a3⟩, ⟨rfl, m2, m3⟩, rfl⟩) (h_cov_meas := cover.s.measurable (rT := rT) Set.univ) (h_cov_range :=
    cover.s_univ_eq_range)

theorem s.π.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable
      (@CylinderGenTest.Golden.Tm.s.π rT :
        CylinderGenTest.Golden.Tm rT → Option (ℕ × CylinderGenTest.Golden.Tm rT × rT)) :=
  Cylinders.proj_measurable s.measurableEmbedding
    (by
      ext t; constructor
      · rintro hS ⟨_, rfl⟩; cases hS
      · intro hS;
        cases t <;>
          first
          | rfl
          | exact absurd ⟨⟨_, _, _⟩, rfl⟩ hS)
    (fun S => by
      ext t; constructor
      · rintro ⟨_, hS, h⟩; cases t <;> cases h; exact ⟨_, hS, rfl⟩
      · rintro ⟨_, hS, rfl⟩; exact ⟨_, hS, rfl⟩)

theorem casesOn_preimage_decomp {rT : Type _} {α : Type _} (S : Set α) (f_z : Unit → α)
    (f_s : ℕ × CylinderGenTest.Golden.Tm rT × rT → α) :
    (fun x : CylinderGenTest.Golden.Tm rT =>
          CylinderGenTest.Golden.Tm.casesOn (motive := fun _ => α) x (f_z ()) fun x1 x2 x3 => f_s (x1, x2, x3)) ⁻¹'
        S =
      ⋃ i, decompCell S f_z f_s i :=
  by
  ext x
  simp only [Set.mem_preimage, Set.mem_iUnion, decompCell]
  constructor
  · intro hx
    cases x
    · exact ⟨0, (), hx, rfl⟩
    · exact ⟨1, ⟨_, _, _⟩, hx, rfl⟩
  · rintro ⟨i, hi⟩; fin_cases i <;> · obtain ⟨q, hq, hx⟩ := hi; cases hx; exact hq

theorem measurable_rec {rT : Type _} [MeasurableSpace rT] {α : Type _} [MeasurableSpace α] (f_z : Unit → α)
    (f_s : ℕ × CylinderGenTest.Golden.Tm rT × rT → α) (h_s : Measurable f_s) :
    Measurable fun x : CylinderGenTest.Golden.Tm rT =>
      CylinderGenTest.Golden.Tm.casesOn (motive := fun _ => α) x (f_z ()) fun x1 x2 x3 => f_s (x1, x2, x3) :=
  by
  intro S hS
  rw [casesOn_preimage_decomp]
  refine .iUnion fun i => ?_
  fin_cases i
  · exact z.measurableEmbedding.measurableSet_image' MeasurableSet.of_discrete
  · exact s.measurableEmbedding.measurableSet_image' (h_s hS)

theorem casesOn_preimage_decomp_param {rT : Type _} {α β : Type _} (S : Set α) (f_z : β × Unit → α)
    (f_s : β × ℕ × CylinderGenTest.Golden.Tm rT × rT → α) :
    (fun p : CylinderGenTest.Golden.Tm rT × β =>
          CylinderGenTest.Golden.Tm.casesOn (motive := fun _ => α) p.1 (f_z (p.2, ())) fun x1 x2 x3 =>
            f_s (p.2, x1, x2, x3)) ⁻¹'
        S =
      ⋃ i, decompCell_param S f_z f_s i :=
  by
  ext ⟨x, y⟩
  simp only [Set.mem_preimage, Set.mem_iUnion, decompCell_param]
  constructor
  · intro hx
    cases x
    · exact ⟨0, (y, ()), hx, rfl⟩
    · exact ⟨1, (y, ⟨_, _, _⟩), hx, rfl⟩
  · rintro ⟨i, hi⟩; fin_cases i <;> · obtain ⟨q, hq, hx⟩ := hi; cases hx; exact hq

theorem measurable_rec_param {rT : Type _} [MeasurableSpace rT] {α : Type _} [MeasurableSpace α] {β : Type _}
    [MeasurableSpace β] (c_z : β × Unit → α) (c_s : β × ℕ × CylinderGenTest.Golden.Tm rT × rT → α)
    (h_z : Measurable c_z) (h_s : Measurable c_s) :
    Measurable fun p : CylinderGenTest.Golden.Tm rT × β =>
      CylinderGenTest.Golden.Tm.casesOn (motive := fun _ => α) p.1 (c_z (p.2, ())) fun x1 x2 x3 =>
        c_s (p.2, x1, x2, x3) :=
  by
  intro S hS
  rw [casesOn_preimage_decomp_param]
  refine .iUnion fun i => ?_
  fin_cases i
  ·
    exact
      ((z.measurableEmbedding.prodMap (.id (α := β))).comp
            MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image'
        (h_z hS)
  ·
    exact
      ((s.measurableEmbedding.prodMap (.id (α := β))).comp
            MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image'
        (h_s hS)

theorem singletonCyl_flatten {rT : Type _} (x : CylinderGenTest.Golden.Tm rT) : (singletonCyl x).flatten = { x } := by
  induction x with
  | z => simp only [singletonCyl_eqs, Cylinder.flatten_eqs, Set.singleton_prod_singleton, Set.image_singleton]
  | s x1 c2 S3 ih2 =>
    simp only [singletonCyl_eqs, Cylinder.flatten_eqs, Set.singleton_prod_singleton, Set.image_singleton, ih2]

theorem singletonCyl_hasMeasurableLeaves {rT : Type _} [MeasurableSpace rT] [MeasurableSingletonClass rT]
    (x : CylinderGenTest.Golden.Tm rT) : (singletonCyl x).HasMeasurableLeaves := by
  induction x with
  | z => exact True.intro
  | s x1 c2 S3 ih2 => exact And.intro ih2 (MeasurableSet.singleton S3)

instance instMeasurableSingletonClass {rT : Type _} [MeasurableSpace rT] [MeasurableSingletonClass rT] :
    MeasurableSingletonClass (CylinderGenTest.Golden.Tm rT) where
  measurableSet_singleton := Cylinders.measurableSet_singleton rfl singletonCyl_flatten singletonCyl_hasMeasurableLeaves

theorem measurable_struct_rec {rT : Type _} {α : Type _} [MeasurableSpace rT] [MeasurableSpace α]
    {f : CylinderGenTest.Golden.Tm rT → α} {c_z : α} {c_s : ℕ → α → rT → α}
    (eq_z : f (@CylinderGenTest.Golden.Tm.z rT) = c_z)
    (eq_s : ∀ x1 x2 x3, f (@CylinderGenTest.Golden.Tm.s rT x1 x2 x3) = c_s x1 (f x2) x3)
    (h_s : Measurable (fun (q : ℕ × α × rT) => c_s q.1 q.2.1 q.2.2)) : Measurable f :=
  by
  apply StructRec.measurable_of_cells CylinderGenTest.Golden.Tm.shape
  intro s
  have hC : ∀ s : Shape, MeasurableSet (CylinderGenTest.Golden.Tm.shape (rT := rT) ⁻¹' { s }) := fun s => by
    rw [← Shape.cylinder_preimage_shape]; exact flatten_measurable (Shape.cylinder_hasMeasurableLeaves s)
  induction s with
  | z =>
    intro U hU
    exact
      Cylinders.cell (ι := @CylinderGenTest.Golden.Tm.z.ι rT) z.measurableEmbedding (hC _) fun p hp =>
        by
        rw [← Set.mem_singleton_iff, ← Set.mem_preimage, ← Shape.cylinder_preimage_shape] at hp
        obtain rfl := hp
        exact ⟨(), rfl⟩ (G := fun q => c_z) (fun q _ => eq_z) (measurable_of_countable _) hU
  | s x1 s2 ih2 =>
    intro U hU
    exact
      Cylinders.cell (ι := @CylinderGenTest.Golden.Tm.s.ι rT) s.measurableEmbedding (hC _) fun p hp =>
        by
        rw [← Set.mem_singleton_iff, ← Set.mem_preimage, ← Shape.cylinder_preimage_shape] at hp
        obtain ⟨⟨b2, b3⟩, ⟨_, _⟩, rfl⟩ := hp
        exact ⟨⟨x1, b2, b3⟩, rfl⟩ (G := fun q => c_s q.1 (f q.2.1) q.2.2) (fun q _ => eq_s q.1 q.2.1 q.2.2)
        (h_s.comp
          ((measurable_fst.comp measurable_subtype_coe).prodMk
            ((Cylinders.restrict_comp (Cylinders.restrict_of_cell @ih2)
                  ((measurable_fst.comp measurable_snd).comp measurable_id) (fun q hq => (Shape.s.inj hq).2)).prodMk
              ((measurable_snd.comp measurable_snd).comp measurable_subtype_coe))))
        hU

theorem measurable_struct_rec_param {rT : Type _} {α : Type _} [MeasurableSpace rT] [MeasurableSpace α] {β : Type _}
    [MeasurableSpace β] {g : β → CylinderGenTest.Golden.Tm rT → α} {c_z : β → α} {c_s : β → ℕ → α → rT → α}
    (eq_z : ∀ b, g b (@CylinderGenTest.Golden.Tm.z rT) = c_z b)
    (eq_s : ∀ b x1 x2 x3, g b (@CylinderGenTest.Golden.Tm.s rT x1 x2 x3) = c_s b x1 (g b x2) x3) (h_z : Measurable c_z)
    (h_s : Measurable (fun (q : β × ℕ × α × rT) => c_s q.1 q.2.1 q.2.2.1 q.2.2.2)) : Measurable (Function.uncurry g) :=
  by
  apply StructRec.measurable_of_cells_param CylinderGenTest.Golden.Tm.shape
  intro s
  have hC : ∀ s : Shape, MeasurableSet (CylinderGenTest.Golden.Tm.shape (rT := rT) ⁻¹' { s }) := fun s => by
    rw [← Shape.cylinder_preimage_shape]; exact flatten_measurable (Shape.cylinder_hasMeasurableLeaves s)
  induction s with
  | z =>
    intro U hU
    exact
      Cylinders.cell_param (ι := @CylinderGenTest.Golden.Tm.z.ι rT) z.measurableEmbedding (hC _) fun p hp =>
        by
        rw [← Set.mem_singleton_iff, ← Set.mem_preimage, ← Shape.cylinder_preimage_shape] at hp
        obtain rfl := hp
        exact ⟨(), rfl⟩ (G := fun q => c_z q.1) (fun b q _ => eq_z b)
        (h_z.comp (measurable_fst.comp measurable_subtype_coe)) hU
  | s x1 s2 ih2 =>
    intro U hU
    exact
      Cylinders.cell_param (ι := @CylinderGenTest.Golden.Tm.s.ι rT) s.measurableEmbedding (hC _) fun p hp =>
        by
        rw [← Set.mem_singleton_iff, ← Set.mem_preimage, ← Shape.cylinder_preimage_shape] at hp
        obtain ⟨⟨b2, b3⟩, ⟨_, _⟩, rfl⟩ := hp
        exact ⟨⟨x1, b2, b3⟩, rfl⟩ (G := fun q => c_s q.1 q.2.1 (g q.1 q.2.2.1) q.2.2.2)
        (fun b q _ => eq_s b q.1 q.2.1 q.2.2)
        (h_s.comp
          ((measurable_fst.comp measurable_subtype_coe).prodMk
            ((measurable_fst.comp (measurable_snd.comp measurable_subtype_coe)).prodMk
              ((Cylinders.restrict_comp (Cylinders.restrict_of_cell @ih2)
                    (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).comp measurable_snd))
                    (fun q hq => (Shape.s.inj hq).2)).prodMk
                ((measurable_snd.comp measurable_snd).comp (measurable_snd.comp measurable_subtype_coe))))))
        hU

attribute [fun_prop] z.measurable s.measurable s.π.measurable measurable_rec measurable_rec_param

attribute [measurability] cover.z.measurable cover.s.measurable

attribute [aesop safe apply (rule_sets := [Measurable])] Shape.cylinder_hasMeasurableLeaves

attribute [simp, cylinder_simp] Cylinder.flatten_eqs CylinderGenTest.Golden.Tm.shape_eqs Cylinder.shape_eqs
  Shape.cylinder_eqs

attribute [cylinder_simp] cover.z cover.s

attribute [simp] singletonCyl_eqs Shape.cylinder_preimage_shape
-/
#guard_msgs in cylinder_defs? Tm
end Tm
end Golden

/-! ## Inputs found by adversarial testing -/

namespace KeywordParam
@[uncurriedProjections, constructors]
inductive Tm («end» : Type) | nil | a (r : «end») (t : Tm «end»)
namespace Tm
cylinder_defs Tm
selftest (Tm ℝ) (Cylinder ℝ)
end Tm
end KeywordParam

namespace SixGreek
@[uncurriedProjections, constructors]
inductive Tm (α β γ δ ε ζ : Type) | nil | a (r : α) (s : ζ) (t : Tm α β γ δ ε ζ)
namespace Tm
cylinder_defs Tm
end Tm
end SixGreek

/-! Fields with default values. -/
namespace Defaults
@[uncurriedProjections, constructors]
inductive Tm (rT : Type _) | nil | a (n : ℕ := 3) (t : Tm rT) | b (r : rT := by exact default)
namespace Tm
cylinder_defs Tm
selftest (Tm ℝ) (Cylinder ℝ)
end Tm
end Defaults

/-! A field type that prints ambiguously without type ascriptions. -/
namespace Interval
@[uncurriedProjections, constructors]
inductive Tm | nil | a (p : Set.Icc (0 : ℝ) 1) (t : Tm)
namespace Tm
cylinder_defs Tm
selftest Tm Cylinder
end Tm
end Interval

/-! The first constructor without recursive fields has an uninhabited base field. -/
namespace EmptyFirst
@[uncurriedProjections, constructors]
inductive Tm (rT : Type _) | e (x : Empty) | f (n : ℕ) | s (t : Tm rT)
namespace Tm
cylinder_defs Tm
end Tm
end EmptyFirst

namespace SingleNullary
@[uncurriedProjections, constructors]
inductive Tm (rT : Type _) | a
namespace Tm
cylinder_defs Tm
selftest (Tm ℝ) (Cylinder ℝ)
end Tm
end SingleNullary

/-! Many base fields (one `if`) and many recursive fields (one case per field). -/
namespace ManyFields
@[uncurriedProjections, constructors]
inductive Tm | nil | w (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Bool)
  | big (t0 t1 t2 t3 t4 t5 t6 t7 t8 : Tm)
namespace Tm
cylinder_defs Tm
end Tm
end ManyFields

/-! Names that need escaping, and `f_<ctor>` binders that would coincide. -/
namespace Escaped
@[uncurriedProjections, constructors]
inductive «my Tm» | nil | «a b» (t : «my Tm») | f_a | a (n : ℕ) | a' (b : Bool) (t : «my Tm»)
namespace «my Tm»
cylinder_defs «my Tm»
end «my Tm»
end Escaped

/-! Section variables named like globals the generated code uses. -/
namespace SectionVars
section
variable (Unit : Type) (Fin : ℕ) (x1 : ℕ) {rT : Type}
@[uncurriedProjections, constructors]
inductive Tm (rT : Type _) | nil | a (r : rT) (n : ℕ) (t : Tm rT)
namespace Tm
cylinder_defs Tm
end Tm
end
end SectionVars

/-! Data fields whose type is a product with a small finite factor, next to base fields:
`simp` would case-split them. -/
namespace FiniteFactors
@[uncurriedProjections, constructors]
inductive Tm | nil | c (a : ℝ × Bool) (b : ℕ) | d (b : Fin 1) (a : ℝ × Fin 2) (t : Tm)
namespace Tm
cylinder_defs Tm
example : Measurable (fun p : (ℝ × Bool) × ℕ => Tm.c p.1 p.2) := by fun_prop
example (f : Tm → ℝ) (hf : Measurable f) :
    Measurable (fun t : Tm => Tm.casesOn (motive := fun _ => ℝ) t 0 (fun _ n => n) (fun _ _ t => f t)) :=
  measurable_rec (fun _ => 0) (fun p => (p.2 : ℝ)) (fun p => f p.2.2) (by fun_prop) (by fun_prop)
end Tm
end FiniteFactors

/-! A `Prop` base field, without `open Classical` in scope. -/
namespace PropField
section
open MeasureTheory
@[uncurriedProjections, constructors]
inductive Tm | nil | c (b : Prop) (t : Tm)
namespace Tm
cylinder_defs Tm
end Tm
end
end PropField

/-! ## Names the generated code uses

The generated code is hygienic, so the user's names cannot capture the globals it refers to. -/

namespace ParamSet
@[uncurriedProjections, constructors]
inductive Tm (Set : Type) | nil | a (r : Set) (t : Tm Set)
namespace Tm
cylinder_defs Tm
selftest (Tm ℝ) (Cylinder ℝ)
end Tm
end ParamSet

namespace CtorNone
@[uncurriedProjections, constructors]
inductive Tm | none | some (n : ℕ) (t : Tm)
namespace Tm
cylinder_defs Tm
selftest Tm Cylinder
end Tm
end CtorNone

namespace Shadowed
def MeasurableSet (n : ℕ) : ℕ := n
@[uncurriedProjections, constructors]
inductive Tm (rT : Type _) | nil | a (r : rT) (t : Tm rT)
namespace Tm
cylinder_defs Tm
end Tm
end Shadowed

namespace ShadowedDotted
namespace MeasurableSet
theorem singleton : True := trivial
end MeasurableSet
@[uncurriedProjections, constructors]
inductive Tm | nil | a (n : ℕ) (t : Tm)
namespace Tm
cylinder_defs Tm
selftest Tm Cylinder
end Tm
end ShadowedDotted

/-! ## Rejected inputs -/

namespace ShiftClash
-- `h` + `t_x` and `ht` + `x` must not collide
@[uncurriedProjections, constructors]
inductive Tm (rT : Type _) | nil | x (t : Tm rT) | t_x (t : Tm rT)
namespace Tm
cylinder_defs Tm shifting x
end Tm
end ShiftClash

namespace EscapedShift
@[uncurriedProjections, constructors]
inductive Tm (rT : Type _) | nil | «a b» (t : Tm rT) | «if» (t u : Tm rT)
namespace Tm
cylinder_defs Tm shifting «a b» «if»
end Tm
end EscapedShift

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

inductive ReservedCtor | nil | flatten (t : ReservedCtor)
/--
error: cylinders: constructor name `flatten` clashes with a name used by the generated code
-/
#guard_msgs in #cylinder_classify ReservedCtor

inductive ReservedCtor2 | nil | cylinder
/--
error: cylinders: constructor name `cylinder` clashes with a name used by the generated code
-/
#guard_msgs in #cylinder_classify ReservedCtor2

inductive CtorShape | nil | Shape (t : CtorShape)
/-- error: cylinders: constructor name `Shape` clashes with a name used by the generated code -/
#guard_msgs in #cylinder_classify CtorShape

inductive ParamNamespace (Rejected : Type) | nil | a (r : Rejected)
/-- error: cylinders: parameter name `Rejected` clashes with a name used by the generated code -/
#guard_msgs in #cylinder_classify ParamNamespace

inductive AutoBound : Type → Type | nil {α} : AutoBound α | a {α} (r : α) (t : AutoBound α) : AutoBound α
/-- error: cylinders: parameters must be named -/
#guard_msgs in #cylinder_classify AutoBound

inductive Unprintable | nil | a (s : ({0, 1} : Finset ℤ))
/--
error: cylinders: cannot reproduce field type ↥{0, 1} as source (printed as `↥{(0 : ℤ), (1 : ℤ)}`)
-/
#guard_msgs in #cylinder_classify Unprintable

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

inductive SuffixClash | nil | a (t : SuffixClash) | a_univ_eq_range (n : ℕ)
/--
error: cylinders: constructors `a` and `a_univ_eq_range` would both define `cover.a_univ_eq_range`
-/
#guard_msgs in #cylinder_classify SuffixClash

namespace NoBaseCase
@[uncurriedProjections, constructors]
inductive Tm | a (t : Tm) | b (t u : Tm)
namespace Tm
/--
error: cylinders: `flatten_isCountablySpanning` needs a constructor without recursive fields whose base fields are `Inhabited`
-/
#guard_msgs in cylinder_defs Tm
end Tm
end NoBaseCase

namespace ShiftNoRec
@[uncurriedProjections, constructors]
inductive Tm (rT : Type _) | nil | lam (t : Tm rT) | z (r : rT)
namespace Tm
/-- error: cylinders: `z` has no recursive fields to shift -/
#guard_msgs in cylinder_defs Tm shifting lam z
end Tm
end ShiftNoRec

end Rejected

end CylinderGenTest

end CylinderGenTest
