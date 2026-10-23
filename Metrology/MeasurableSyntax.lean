module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Basic.Real.Basic
public import Metrology.Meta.Projections
import all Metrology.Meta.Projections
import all Metrology.Meta.Build

@[expose] public section

/-! # Measurable syntax -/

open Set

variable {α : Type _}

local instance instMeasurableSpaceOption_measurableSyntax [MeasurableSpace α] :
    MeasurableSpace (Option α) :=
  .generateFrom <| {{ none }} ∪ ((some '' ·) '' MeasurableSet)

section Option

variable [MeasurableSpace α]

open MeasurableSpace

/-- The set `{none}` is measurable. -/
theorem measurableSet_none : MeasurableSet { none (α := α) } :=
  measurableSet_generateFrom (mem_union_left _ rfl)

/-- The image of a measurable set under `some` is measurable. -/
theorem measurableSet_some {S : Set α} (HS : MeasurableSet S) : MeasurableSet (some '' S) :=
  measurableSet_generateFrom <| mem_union_right _ (mem_image_of_mem _ HS)

/-- The range of `some` is measurable. -/
theorem measurableSet_range_some : MeasurableSet (range (some (α := α))) :=
  image_univ ▸ measurableSet_some .univ

/-- A set of options is measurable iff its part inside the range of `some` is. -/
theorem measurableSet_iff_inter_range_some {S : Set (Option α)} :
    MeasurableSet S ↔ MeasurableSet (S ∩ range some) := by
  refine ⟨(MeasurableSet.inter · measurableSet_range_some), fun H => ?_⟩
  rw [show S = (S ∩ range some) ∪ (S ∩ { none }) by simp [← inter_union_distrib_left]]
  refine H.union ?_
  obtain h | h : S ∩ { none } = ∅ ∨ S ∩ { none } = { none } := by simp [em' (none ∈ S)]
  · rw [h]; exact .empty
  · rw [h]; exact measurableSet_none

end Option

/-- Identifiers are strings. -/
abbrev Ident : Type _ := String

/-- The data needed to perform the cylinder construction on syntax. -/
class MeasurableSyntax (Syntax : Type _) (Gen : outParam (Type _)) where
  /-- The generators that count as measurable. -/
  base : Set Gen
  /-- The set of syntax trees that a generator describes. -/
  flatten : Gen → Set Syntax

variable {Syntax Gen : Type _} {R Z B : Type _}

/-- The cylinder sets: the flattenings of the measurable generators. -/
def MeasurableSyntax.cylinder [I : MeasurableSyntax Syntax Gen] : Set (Set Syntax) :=
  I.flatten '' I.base

instance MeasurableSyntax.instMeasurableSpace [MeasurableSyntax Syntax Gen]
    : MeasurableSpace Syntax :=
  .generateFrom cylinder

/-- Literal syntax, with the type of reals, integers and booleans as parameters. -/
@[uncurriedProjections, constructors]
inductive LitSyntax (R Z B : Type _) where
| real (r : R)
| int (z : Z)
| bool (b : B)

-- TODO: derive the higher-kinded functor `LitSyntax R Z B → LitSyntax R' Z' B'`.

/-- The set of literals that a literal of sets describes. -/
def LitSyntax.flatten : LitSyntax (Set R) (Set Z) (Set B) → Set (LitSyntax R Z B)
| .real S => real.ι '' S
| .int S => int.ι '' S
| .bool S => bool.ι '' S

/-- The literals of sets whose underlying set is measurable. -/
def LitSyntax.base [MeasurableSpace R] [MeasurableSpace Z] [MeasurableSpace B] :
  Set (LitSyntax (Set R) (Set Z) (Set B))
| .real S => MeasurableSet S
| .int S => MeasurableSet S
| .bool S => MeasurableSet S

instance [MeasurableSpace R] [MeasurableSpace Z] [MeasurableSpace B] :
    MeasurableSyntax (LitSyntax R Z B) (LitSyntax (Set R) (Set Z) (Set B)) where
  base := LitSyntax.base
  flatten := LitSyntax.flatten

-- Does the construction work when we take measurable sets of the intermediate stages
-- (ie. LitSyntax)
-- instead of combining the trees? That would make a lot of the metaprogrammable: we'd require that
-- every field of every constructor be recursive or measurable.
-- This way there's only one step to unfold.
-- Perhaps we can generate the shape inductives then?

/-- Expression syntax, with the type of reals, integers and booleans as parameters. -/
@[uncurriedProjections, constructors]
inductive ExprSyntax (R Z B : Type _) where
| rand
| lit (l : LitSyntax R Z B)
| var (x : Ident)
| app (rator rand : ExprSyntax R Z B)
| lam (x : Ident) (body : ExprSyntax R Z B)

/-- The set of expressions that an expression of sets describes. -/
def ExprSyntax.flatten : ExprSyntax (Set R) (Set Z) (Set B) → Set (ExprSyntax R Z B)
| rand => rand.ι '' { () }
| lit l => lit.ι '' (LitSyntax.flatten l)
| var x => var.ι '' { x }
| app fn arg => app.ι '' prod (flatten fn) (flatten arg)
| lam x body => lam.ι '' prod { x } (flatten body)

/-- The expressions of sets whose literals are all measurable. -/
def ExprSyntax.base [MeasurableSpace R] [MeasurableSpace Z] [MeasurableSpace B] :
  Set (ExprSyntax (Set R) (Set Z) (Set B))
| rand => True
| lit S => MeasurableSyntax.base (LitSyntax R Z B) S
| var _ => True
| app fn arg => base fn ∧ base arg
| lam _ body => base body

instance [MeasurableSpace R] [MeasurableSpace Z] [MeasurableSpace B] :
    MeasurableSyntax (ExprSyntax R Z B) (ExprSyntax (Set R) (Set Z) (Set B)) where
  base := ExprSyntax.base
  flatten := ExprSyntax.flatten

open ExprSyntax
example (ident_body : Ident × ExprSyntax R Z B) : lam.π (lam.ι ident_body) = some ident_body := rfl
example (ident_body : Ident × ExprSyntax R Z B) : app.π (lam.ι ident_body) = none := rfl
