module

public import Metrology.ProbLang.Exec

/-! # Bounded and limit execution for an explicit program kernel -/

@[expose] public section

noncomputable section

namespace ProbLang

open MeasureTheory MeasureTheory.Measure

variable {rT : Type} [MeasurableSpace rT]

/-- Terminated configurations reached within the fuel bound under a specified kernel. -/
def execNFor (step : Cfg rT → Measure (Cfg rT)) : Nat → Cfg rT → Measure (Cfg rT)
  | 0, _ => 0
  | n + 1, ρ => if ρ.expr.isValue then dirac ρ else (step ρ).bind (execNFor step n)

/-- The terminal configuration measure obtained as the supremum of bounded executions. -/
def limExecFor (step : Cfg rT → Measure (Cfg rT)) (ρ : Cfg rT) : Measure (Cfg rT) :=
  ⨆ n, execNFor step n ρ

/-- Forget the final state in the explicit-kernel execution measure. -/
def limExecVFor (step : Cfg rT → Measure (Cfg rT)) (ρ : Cfg rT) : Measure (Exp rT) :=
  asExpr (limExecFor step ρ)

variable {step : Cfg rT → Measure (Cfg rT)}

section MeasurableKernel

variable (hstep : Measurable step)
include hstep

/-- A measurable transition kernel has measurable bounded execution. -/
@[fun_prop]
theorem execNFor_measurable (n : Nat) : Measurable (execNFor step n) := by
  induction n with
  | zero => simp [execNFor]
  | succ n ih =>
    exact .ite (by measurability) (by measurability) (by measurability)

/-- Each bounded execution has total mass at most one. -/
theorem execNFor_univ_le_one (hbound : ∀ ρ, step ρ Set.univ ≤ 1) (n : Nat) (ρ : Cfg rT) :
    execNFor step n ρ Set.univ ≤ 1 := by
  induction n generalizing ρ with
  | zero => simp [execNFor]
  | succ n ih =>
    unfold execNFor
    by_cases hv : ρ.expr.isValue
    · simp [hv]
    · simp only [hv, ↓reduceIte]
      rw [bind_apply (by measurability) (execNFor_measurable hstep n).aemeasurable]
      calc ∫⁻ a, execNFor step n a Set.univ ∂step ρ
        _ ≤ ∫⁻ _, 1 ∂step ρ := lintegral_mono fun a => ih a
        _ = step ρ Set.univ := by simp
        _ ≤ 1 := hbound ρ

/-- Additional execution fuel preserves all already terminated runs. -/
theorem execNFor_le_succ (n : Nat) (ρ : Cfg rT) :
    execNFor step n ρ ≤ execNFor step (n + 1) ρ := by
  induction n generalizing ρ with
  | zero => exact bot_le
  | succ n ih =>
    rw [execNFor, execNFor]
    split
    · exact le_rfl
    · exact bind_mono_right' _ _ _ (execNFor_measurable hstep n)
        (execNFor_measurable hstep (n + 1)) ih

/-- Bounded explicit-kernel execution is monotone in the fuel. -/
theorem execNFor_monotone (ρ : Cfg rT) : Monotone fun n => execNFor step n ρ := by
  apply monotone_nat_of_le_succ
  exact fun n => execNFor_le_succ hstep n ρ

/-- The explicit-kernel limit measure is evaluated setwise on measurable events. -/
theorem limExecFor_apply (ρ : Cfg rT) {S : Set (Cfg rT)} (hS : MeasurableSet S) :
    limExecFor step ρ S = ⨆ n, execNFor step n ρ S :=
  iSup_measure_apply (execNFor_monotone hstep ρ) hS

/-- Limit execution retains the subprobability bound of the kernel. -/
theorem limExecFor_univ_le_one (hbound : ∀ ρ, step ρ Set.univ ≤ 1) (ρ : Cfg rT) :
    limExecFor step ρ Set.univ ≤ 1 := by
  rw [limExecFor_apply hstep ρ MeasurableSet.univ]
  exact iSup_le fun n => execNFor_univ_le_one hstep hbound n ρ

/-- A finite run of total mass one is the entire limit execution. -/
theorem limExecFor_term (hbound : ∀ ρ, step ρ Set.univ ≤ 1) {n : Nat} {ρ : Cfg rT}
    (hterm : execNFor step n ρ Set.univ = 1) :
    limExecFor step ρ = execNFor step n ρ := by
  let : IsSubProbabilityMeasure (execNFor step n ρ) := ⟨execNFor_univ_le_one hstep hbound n ρ⟩
  let : IsSubProbabilityMeasure (limExecFor step ρ) := ⟨limExecFor_univ_le_one hstep hbound ρ⟩
  have hle : execNFor step n ρ ≤ limExecFor step ρ := le_iSup (execNFor step · ρ) n
  exact (eq_of_le_of_measure_univ_eq hle
    (le_antisymm (hle _) (hterm ▸ IsSubProbabilityMeasure.measure_le_one _))).symm

end MeasurableKernel

variable [LawfulProbLangℝ rT]

/-- The explicit-kernel definition specializes exactly to the original bounded semantics. -/
theorem execNFor_primStep (n : Nat) (ρ : Cfg rT) : execNFor primStep n ρ = execN n ρ := by
  induction n generalizing ρ with
  | zero => rfl
  | succ n ih =>
    simp only [execNFor, execN]
    rw [funext ih]

/-- The explicit-kernel limit specializes exactly to the original execution semantics. -/
theorem limExecFor_primStep (ρ : Cfg rT) : limExecFor primStep ρ = limExec ρ := by
  simp only [limExecFor, limExec, execNFor_primStep]

end ProbLang
