module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.BaseLit
public import Metrology.ProbLang.CoreMeasures.Shapes

meta import Metrology.Meta
meta import Metrology.ProbLang.CoreMeasures.CylinderGen

@[expose] public section

/-! # `ProbeTest`: smoke tests for the `MeasurableSpace` deriving handler

`Probe rT` has a constructor of every shape the handler supports. -/

noncomputable section ProbLangMeasures

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

namespace ProbLang.ProbeTest

/-- A tree type with one constructor of every shape, used to test the deriving handler. -/
@[uncurriedProjections, constructors]
inductive Probe (rT : Type _)
  | nil
  | tag  (n : Nat)
  | dat  (b : BaseLit rT)
  | box  (p : Probe rT)
  | pr   (p1 p2 : Probe rT)
  | tri  (p1 p2 p3 : Probe rT)
  | mix  (op : UnOp) (p : Probe rT)
  | scr  (p : Probe rT) (b : BaseLit rT)
  | quad (p1 p2 p3 p4 : Probe rT)
  deriving Inhabited

/-! ### The generated measurable space -/

deriving instance MeasurableSpace for Probe

variable {rT : Type _}

/-! ### Functions by structural recursion -/

/-- Test 1: discrete codomain. -/
@[simp] def tagDepth : Probe rT → Nat
  | .nil          => 0
  | .tag _        => 0
  | .dat _        => 0
  | .box p        => tagDepth p + 1
  | .pr p1 p2     => max (tagDepth p1) (tagDepth p2) + 1
  | .tri p1 p2 p3 => max (max (tagDepth p1) (tagDepth p2)) (tagDepth p3) + 1
  | .mix _ p      => tagDepth p + 1
  | .scr p _      => tagDepth p + 1
  | .quad p1 p2 p3 p4 =>
      max (max (tagDepth p1) (tagDepth p2)) (max (tagDepth p3) (tagDepth p4)) + 1

/-- Test 2: depends on data leaves. -/
@[simp] def countLeaves : Probe rT → Nat
  | .nil          => 0
  | .tag _        => 0
  | .dat _        => 1
  | .box p        => countLeaves p
  | .pr p1 p2     => countLeaves p1 + countLeaves p2
  | .tri p1 p2 p3 => countLeaves p1 + countLeaves p2 + countLeaves p3
  | .mix _ p      => countLeaves p
  | .scr p _      => countLeaves p + 1
  | .quad p1 p2 p3 p4 => countLeaves p1 + countLeaves p2 + countLeaves p3 + countLeaves p4

/-- Test 3: endo-map, non-discrete codomain. -/
@[simp] def endoMap : Probe rT → Probe rT
  | .nil          => .nil
  | .tag n        => .tag n
  | .dat b        => .dat b
  | .box p        => .box (.box (endoMap p))
  | .pr p1 p2     => .pr (endoMap p1) (endoMap p2)
  | .tri p1 p2 p3 => .tri (endoMap p1) (endoMap p2) (endoMap p3)
  | .mix u p      => .mix u (endoMap p)
  | .scr p b      => .scr (endoMap p) b
  | .quad p1 p2 p3 p4 => .quad (endoMap p1) (endoMap p2) (endoMap p3) (endoMap p4)

/-- Test 4: a parameter threaded unchanged into every recursive call. -/
@[simp] def addAcc : Nat → Probe rT → Nat
  | acc, .nil          => acc
  | acc, .tag n        => acc + n
  | acc, .dat _        => acc
  | acc, .box p        => addAcc acc p
  | acc, .pr p1 p2     => addAcc acc p1 + addAcc acc p2
  | acc, .tri p1 p2 p3 => addAcc acc p1 + addAcc acc p2 + addAcc acc p3
  | acc, .mix _ p      => addAcc acc p
  | acc, .scr p _      => addAcc acc p
  | acc, .quad p1 p2 p3 p4 => addAcc acc p1 + addAcc acc p2 + addAcc acc p3 + addAcc acc p4

variable [MeasurableSpace rT]

/-- `tagDepth` is a measurable function. -/
theorem tagDepth.measurable :
    Measurable (tagDepth : Probe rT → Nat) := by
  apply Probe.measurable_struct_rec
    (c_nil := 0) (c_tag := fun _ => 0) (c_dat := fun _ => 0)
    (c_box := (· + 1)) (c_pr := fun n1 n2 => max n1 n2 + 1)
    (c_tri := fun n1 n2 n3 => max (max n1 n2) n3 + 1)
    (c_mix := fun _ n => n + 1) (c_scr := fun n _ => n + 1)
    (c_quad := fun n1 n2 n3 n4 => max (max n1 n2) (max n3 n4) + 1)
  all_goals first | (intros; rfl) | fun_prop

/-- `countLeaves` is a measurable function. -/
theorem countLeaves.measurable :
    Measurable (countLeaves : Probe rT → Nat) := by
  apply Probe.measurable_struct_rec
    (c_nil := 0) (c_tag := fun _ => 0) (c_dat := fun _ => 1)
    (c_box := id) (c_pr := (· + ·))
    (c_tri := fun n1 n2 n3 => n1 + n2 + n3)
    (c_mix := fun _ n => n) (c_scr := fun n _ => n + 1)
    (c_quad := fun n1 n2 n3 n4 => n1 + n2 + n3 + n4)
  all_goals first | (intros; rfl) | fun_prop

/-- `endoMap` is a measurable function. -/
theorem endoMap.measurable :
    Measurable (endoMap : Probe rT → Probe rT) := by
  apply Probe.measurable_struct_rec
    (c_nil := .nil) (c_tag := Probe.tag) (c_dat := Probe.dat)
    (c_box := fun p => .box (.box p)) (c_pr := fun p1 p2 => .pr p1 p2)
    (c_tri := fun p1 p2 p3 => .tri p1 p2 p3)
    (c_mix := fun u p => .mix u p) (c_scr := fun p b => .scr p b)
    (c_quad := fun p1 p2 p3 p4 => .quad p1 p2 p3 p4)
  all_goals first | (intros; rfl) | fun_prop

/-- `addAcc` is a measurable function. -/
theorem addAcc.measurable :
    Measurable (Function.uncurry (addAcc : Nat → Probe rT → Nat)) := by
  apply Probe.measurable_struct_rec_param
    (c_nil := fun acc => acc) (c_tag := fun acc n => acc + n) (c_dat := fun acc _ => acc)
    (c_box := fun _ n => n) (c_pr := fun _ n1 n2 => n1 + n2)
    (c_tri := fun _ n1 n2 n3 => n1 + n2 + n3)
    (c_mix := fun _ _ n => n) (c_scr := fun _ n _ => n)
    (c_quad := fun _ n1 n2 n3 n4 => n1 + n2 + n3 + n4)
  all_goals first | (intros; rfl) | fun_prop

end ProbeTest
end ProbLang
end ProbLangMeasures
