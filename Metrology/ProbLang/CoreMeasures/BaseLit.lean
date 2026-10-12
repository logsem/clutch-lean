module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.Discrete
public import Metrology.ProbLang.CoreMeasures.Cylinders

meta import Metrology.Meta
meta import Metrology.ProbLang.CoreMeasures.CylinderGen

@[expose] public section

noncomputable section ProbLangMeasures

/-# Measure space on base lits -/

namespace ProbLang.BaseLit

/-! ### Cylinder definitions

`<ctor>.ι.inj`, `Cylinder`, `Shape`, `Cylinder.flatten`, `Cylinder.HasMeasurableLeaves`, the
σ-algebra instance, the shape maps, `Cylinder.inter?`, `cover.<ctor>`, `decompCell(_param)`,
`singletonCyl`, `Shape.cylinder_hasMeasurableLeaves`, `flatten_measurable` and the
`measurability` aesop rules, generated from the constructors by `cylinder_defs`
(`Metrology/ProbLang/CoreMeasures/CylinderGen.lean`). -/

cylinder_defs BaseLit

/-! ### Cylinder intersection.

`Cylinder.inter? c c'` returns `some c''` when `flatten c'' = flatten c ∩ flatten c'`, and
`none` when the structural intersection is empty (different top constructors or mismatched
discrete leaves). The cylinder type is closed under intersection because every cylinder has
a top constructor and the recursive structure matches up. -/

/-! Three generic helper lemmas next for provving measurability of a cover -/

/-! ### The cylinder flatten family is a π-system that spans `BaseLit rT`. -/

/-! ### Measurability of the per-constructor covers. -/

/-! ### Measurable constructors. One `BaseLit.<ctor>.ι.measurable` per constructor. -/

/-! ### Raw-constructor `fun_prop` lemmas. -/

/-! ### Uncurried-projection measurability. One `BaseLit.<ctor>.π.measurable` per
field-carrying constructor (`unit` is nullary, so has no projection). Each is the
generic `Cylinders.proj_measurable` instantiated at that constructor's embedding. -/

/-! ### Synthetic smoke-test battery

`BaseLit` is non-recursive, so there is no struct-rec keystone; the battery is
phrased through the `casesOn` keystones `measurable_rec` / `measurable_rec_param`.
Each test exercises every constructor slot. -/

/-- Test 1: discrete codomain (`tagDepth : BaseLit rT → Nat`, one tag per constructor;
ignores all payloads, so `f_real` is constant). -/
@[simp] def tagDepth : BaseLit rT → Nat
  | .int _  => 0
  | .bool _ => 1
  | .unit   => 2
  | .loc _  => 3
  | .lbl _  => 4
  | .real _ => 5

theorem tagDepth.measurable [MeasurableSpace rT] [Inhabited rT] :
    Measurable (tagDepth : BaseLit rT → Nat) := by
  have heq : (tagDepth : BaseLit rT → Nat)
    = (fun b : BaseLit rT =>
        BaseLit.casesOn (motive := fun _ => Nat) b
          (fun _ => 0) (fun _ => 1) 2 (fun _ => 3) (fun _ => 4) (fun _ => 5)) := by
    funext b; cases b <;> rfl
  rw [heq]
  apply measurable_rec
    (f_int := fun _ => 0) (f_bool := fun _ => 1)
    (f_unit := fun _ => 2) (f_loc := fun _ => 3) (f_lbl := fun _ => 4)
    (f_real := fun _ => 5)
  fun_prop

/-- Test 2: data-leaf dependent (`countLeaves g`, the `real` payload is mapped through a
measurable `g : rT → Int`; all other constructors return discrete tags). This is the
named equivalent of the original anonymous `measurable_rec` smoke test. -/
@[simp] def countLeaves (g : rT → Int) : BaseLit rT → Int
  | .real r => g r
  | .int n  => n
  | _       => 0

theorem countLeaves.measurable [MeasurableSpace rT] [Inhabited rT] (g : rT → Int)
    (hg : Measurable g) :
    Measurable (countLeaves g : BaseLit rT → Int) := by
  have heq : (countLeaves g : BaseLit rT → Int)
    = (fun b : BaseLit rT =>
        BaseLit.casesOn (motive := fun _ => Int) b
          (fun n => n) (fun _ => 0) 0 (fun _ => 0) (fun _ => 0) g) := by
    funext b; cases b <;> rfl
  rw [heq]
  apply measurable_rec
    (f_int := fun n => n) (f_bool := fun _ => 0)
    (f_unit := fun _ => 0) (f_loc := fun _ => 0) (f_lbl := fun _ => 0)
    (f_real := g)
  exact hg

/-- Test 3: endo-map (`endoMap : BaseLit rT → BaseLit rT`, non-discrete codomain). Since
`BaseLit` is non-recursive this is just a per-constructor relabel via `casesOn`; the
`real` leaf is carried unchanged so the obligation closes through the `real` embedding. -/
@[simp] def endoMap : BaseLit rT → BaseLit rT
  | .int z  => .int z
  | .bool b => .bool b
  | .unit   => .unit
  | .loc l  => .loc l
  | .lbl l  => .lbl l
  | .real r => .real r

theorem endoMap.measurable [MeasurableSpace rT] [Inhabited rT] :
    Measurable (endoMap : BaseLit rT → BaseLit rT) := by
  have heq : (endoMap : BaseLit rT → BaseLit rT)
    = (fun b : BaseLit rT =>
        BaseLit.casesOn (motive := fun _ => BaseLit rT) b
          BaseLit.int BaseLit.bool BaseLit.unit BaseLit.loc BaseLit.lbl BaseLit.real) := by
    funext b; cases b <;> rfl
  rw [heq]
  apply measurable_rec
    (f_int := BaseLit.int) (f_bool := BaseLit.bool)
    (f_unit := fun _ => BaseLit.unit) (f_loc := BaseLit.loc) (f_lbl := BaseLit.lbl)
    (f_real := BaseLit.real)
  exact real.measurable

/-- Test 4: param-threaded (`addAcc : Int → BaseLit rT → Int`, an `Int` accumulator
carried alongside via `measurable_rec_param`; the `int` leaf actually uses both the
payload and the accumulator). -/
@[simp] def addAcc : Int → BaseLit rT → Int
  | acc, .int n  => acc + n
  | acc, _       => acc

theorem addAcc.measurable [MeasurableSpace rT] [Inhabited rT] :
    Measurable (fun p : BaseLit rT × Int => addAcc p.2 p.1) := by
  have heq : (fun p : BaseLit rT × Int => addAcc p.2 p.1)
    = (fun p : BaseLit rT × Int =>
        BaseLit.casesOn (motive := fun _ => Int) p.1
          (fun z => (fun q : Int × Int => q.1 + q.2) (p.2, z))
          (fun b => (fun q : Int × Bool => q.1) (p.2, b))
          ((fun q : Int × Unit => q.1) (p.2, ()))
          (fun l => (fun q : Int × Loc => q.1) (p.2, l))
          (fun l => (fun q : Int × Lbl => q.1) (p.2, l))
          (fun r => (fun q : Int × rT => q.1) (p.2, r))) := by
    funext p; obtain ⟨b, x⟩ := p; cases b <;> rfl
  rw [heq]
  apply measurable_rec_param
    (c_int := fun q : Int × Int => q.1 + q.2)
    (c_bool := fun q : Int × Bool => q.1)
    (c_unit := fun q : Int × Unit => q.1)
    (c_loc := fun q : Int × Loc => q.1)
    (c_lbl := fun q : Int × Lbl => q.1)
    (c_real := fun q : Int × rT => q.1)
  all_goals fun_prop

end BaseLit
end ProbLang
end ProbLangMeasures
