module

@[expose] public section

/-! # Evaluator computations as data

The interpreter runs a `Comp` in `IO` (`Interp.drive`) and the proofs read the same tree as a
measure (`Comp.interpM`).
-/

namespace ProbLang

/-- An evaluator step, with recursive calls in `C` and results in `R`. -/
inductive Comp (rT : Type u) (C R : Type u) where
  | ret (r : R)
  | bind (c : Comp rT C R) (k : R → Comp rT C R)
  /-- A recursive call of the evaluator. -/
  | call (c : C)
  /-- Get stuck, or `fail`. -/
  | stuck (msg : String)
  /-- Sample an integer uniformly from `[0, z)`, or return `-1` when `z ≤ 0`. -/
  | sample (z : Int) (k : Int → Comp rT C R)
  /-- Sample a real from `LawfulProbLangℝ.unifUnit`. -/
  | sampleReal (k : rT → Comp rT C R)

end ProbLang
