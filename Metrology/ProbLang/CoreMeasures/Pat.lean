module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.BaseLit
public import Metrology.ProbLang.CoreMeasures.Cylinders

meta import Metrology.Meta

@[expose] public section

/-## ProbLang Measure theory -/

noncomputable section ProbLangMeasures

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

/-# Measure space on patterns.

Closely parallels the `BaseLit` construction above. `Pat` has:
- one nullary constructor (`wildcard`)
- one data-leaf constructor (`lit (b : BaseLit rT)`)
- three purely-recursive constructors (`pair`, `inl`, `inr`).
-/

namespace ProbLang.Pat

/-! ### Cylinder definitions

`<ctor>.ι.inj`, `Cylinder`, `Shape`, `Cylinder.flatten`, `Cylinder.HasMeasurableLeaves`, the
σ-algebra instance, the shape maps, `Cylinder.inter?`, `cover.<ctor>`, `decompCell(_param)`,
`singletonCyl`, `Shape.cylinder_hasMeasurableLeaves`, `flatten_measurable` and the
`measurability` aesop rules, generated from the constructors by `cylinder_defs`
(`Metrology/Meta/CylinderGen.lean`). -/

cylinder_defs Pat

/-! ### Synthetic smoke-test battery -/

/-- Test 1: discrete codomain (`tagDepth : Pat rT → Nat`). -/
@[simp] def tagDepth : Pat rT → Nat
  | .wildcard   => 0
  | .lit _      => 0
  | .pair p1 p2 => max (tagDepth p1) (tagDepth p2) + 1
  | .inl p      => tagDepth p + 1
  | .inr p      => tagDepth p + 1

theorem tagDepth.measurable [MeasurableSpace rT] :
    Measurable (tagDepth : Pat rT → Nat) := by
  apply measurable_struct_rec (f := tagDepth)
    (c_wildcard := 0)
    (c_lit := fun _ => 0)
    (c_pair := fun n1 n2 => max n1 n2 + 1)
    (c_inl := (· + 1))
    (c_inr := (· + 1))
  all_goals first | (intros; rfl) | fun_prop

/-- Test 2: data-leaf dependent (`countLeaves : Pat rT → Nat`). -/
@[simp] def countLeaves : Pat rT → Nat
  | .wildcard   => 0
  | .lit _      => 1
  | .pair p1 p2 => countLeaves p1 + countLeaves p2
  | .inl p      => countLeaves p
  | .inr p      => countLeaves p

theorem countLeaves.measurable [MeasurableSpace rT] :
    Measurable (countLeaves : Pat rT → Nat) := by
  apply measurable_struct_rec (f := countLeaves)
    (c_wildcard := 0)
    (c_lit := fun _ => 1)
    (c_pair := (· + ·))
    (c_inl := id)
    (c_inr := id)
  all_goals first | (intros; rfl) | fun_prop

/-- Test 3: endo-map (`Pat rT → Pat rT`, non-discrete codomain). -/
@[simp] def endoMap : Pat rT → Pat rT
  | .wildcard   => .wildcard
  | .lit b      => .lit b
  | .pair p1 p2 => .pair (endoMap p1) (endoMap p2)
  | .inl p      => .inl (.inl (endoMap p))
  | .inr p      => .inr (.inr (endoMap p))

theorem endoMap.measurable [MeasurableSpace rT] :
    Measurable (endoMap : Pat rT → Pat rT) := by
  apply measurable_struct_rec (f := endoMap)
    (c_wildcard := .wildcard)
    (c_lit := Pat.lit)
    (c_pair := fun p1 p2 => .pair p1 p2)
    (c_inl := fun p => .inl (.inl p))
    (c_inr := fun p => .inr (.inr p))
  all_goals first | (intros; rfl) | fun_prop

/-- Test 4: param-threaded (`addAcc : Nat → Pat rT → Nat`, the `β` is the running
accumulator threaded unchanged into every recursive call). -/
@[simp] def addAcc : Nat → Pat rT → Nat
  | acc, .wildcard   => acc
  | acc, .lit _      => acc
  | acc, .pair p1 p2 => addAcc acc p1 + addAcc acc p2
  | acc, .inl p      => addAcc acc p
  | acc, .inr p      => addAcc acc p

theorem addAcc.measurable [MeasurableSpace rT] :
    Measurable (Function.uncurry (addAcc : Nat → Pat rT → Nat)) := by
  apply measurable_struct_rec_param (g := addAcc)
    (c_wildcard := fun acc => acc)
    (c_lit := fun acc _ => acc)
    (c_pair := fun _ n1 n2 => n1 + n2)
    (c_inl := fun _ n => n)
    (c_inr := fun _ n => n)
  all_goals first | (intros; rfl) | fun_prop

end Pat
end ProbLang
end ProbLangMeasures
