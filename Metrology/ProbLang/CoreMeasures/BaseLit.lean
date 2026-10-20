module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.Discrete
public import Metrology.ProbLang.CoreMeasures.Shapes

meta import Metrology.Meta
meta import Metrology.ProbLang.CoreMeasures.CylinderGen

@[expose] public section

noncomputable section ProbLangMeasures

/-! # Measure space on base lits -/

namespace ProbLang.BaseLit

/-! Deriving `MeasurableSpace` (`CylinderGen.lean`) generates the cylinder σ-algebra, the
constructor embeddings and projections, their measurability lemmas, and the `casesOn` keystones
`measurable_casesOn` / `measurable_casesOn_param`. -/

deriving instance MeasurableSpace for BaseLit

/-! ## Smoke tests: each one exercises every constructor slot of a keystone. -/

/-- The index of the constructor. -/
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
  apply measurable_casesOn
    (c_int := fun _ => 0) (c_bool := fun _ => 1)
    (c_unit := fun _ => 2) (c_loc := fun _ => 3) (c_lbl := fun _ => 4)
    (c_real := fun _ => 5)
  fun_prop

/-- Depends on the `int` and `real` payloads. -/
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
  apply measurable_casesOn
    (c_int := fun n => n) (c_bool := fun _ => 0)
    (c_unit := fun _ => 0) (c_loc := fun _ => 0) (c_lbl := fun _ => 0)
    (c_real := g)
  exact hg

/-- Non-discrete codomain. -/
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
  apply measurable_casesOn
    (c_int := BaseLit.int) (c_bool := BaseLit.bool)
    (c_unit := fun _ => BaseLit.unit) (c_loc := BaseLit.loc) (c_lbl := BaseLit.lbl)
    (c_real := BaseLit.real)
  exact real.measurable

/-- Threads an accumulator through `measurable_casesOn_param`. -/
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
          ((fun q : Int => q) p.2)
          (fun l => (fun q : Int × Loc => q.1) (p.2, l))
          (fun l => (fun q : Int × Lbl => q.1) (p.2, l))
          (fun r => (fun q : Int × rT => q.1) (p.2, r))) := by
    funext p; obtain ⟨b, x⟩ := p; cases b <;> rfl
  rw [heq]
  apply measurable_casesOn_param
    (c_int := fun q : Int × Int => q.1 + q.2)
    (c_bool := fun q : Int × Bool => q.1)
    (c_unit := fun q : Int => q)
    (c_loc := fun q : Int × Loc => q.1)
    (c_lbl := fun q : Int × Lbl => q.1)
    (c_real := fun q : Int × rT => q.1)
  all_goals fun_prop

end BaseLit
end ProbLang
end ProbLangMeasures
