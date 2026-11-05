module

public import Metrology.ProbLang.Exec
public import Metrology.ProbLang.DetStep

/-! # Bounded and limit execution for an explicit program kernel -/

@[expose] public section

noncomputable section

namespace ProbLang

open MeasureTheory MeasureTheory.Measure Set Exp

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

/-- A returned value is observed as soon as positive fuel remains. -/
theorem execNFor_succ_isValue {ρ : Cfg rT} (hv : ρ.expr.isValue) (n : Nat) :
    execNFor step (n + 1) ρ = dirac ρ := by simp [execNFor, hv]

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

/-- A known deterministic nonvalue transition consumes exactly one unit of execution fuel. -/
theorem execNFor_succ_of_step {ρ next : Cfg rT} (hv : ¬ρ.expr.isValue)
    (hdet : step ρ = dirac next) (n : Nat) :
    execNFor step (n + 1) ρ = execNFor step n next := by
  rw [execNFor, ite_eq_right hv, hdet, dirac_bind (execNFor_measurable hstep n)]

/-- Each bounded execution has total mass at most one. -/
theorem execNFor_univ_le_one (hbound : ∀ ρ, step ρ univ ≤ 1) (n : Nat) (ρ : Cfg rT) :
    execNFor step n ρ univ ≤ 1 := by
  induction n generalizing ρ with
  | zero => simp [execNFor]
  | succ n ih =>
    unfold execNFor
    by_cases hv : ρ.expr.isValue
    · simp [hv]
    · simp only [hv, ↓reduceIte]
      rw [bind_apply (by measurability) (execNFor_measurable hstep n).aemeasurable]
      calc ∫⁻ a, execNFor step n a univ ∂step ρ
        _ ≤ ∫⁻ _, 1 ∂step ρ := lintegral_mono fun a => ih a
        _ = step ρ univ := by simp
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
theorem limExecFor_univ_le_one (hbound : ∀ ρ, step ρ univ ≤ 1) (ρ : Cfg rT) :
    limExecFor step ρ univ ≤ 1 := by
  rw [limExecFor_apply hstep ρ MeasurableSet.univ]
  exact iSup_le fun n => execNFor_univ_le_one hstep hbound n ρ

/-- A finite run of total mass one is the entire limit execution. -/
theorem limExecFor_term (hbound : ∀ ρ, step ρ univ ≤ 1) {n : Nat} {ρ : Cfg rT}
    (hterm : execNFor step n ρ univ = 1) :
    limExecFor step ρ = execNFor step n ρ := by
  let : IsSubProbabilityMeasure (execNFor step n ρ) := ⟨execNFor_univ_le_one hstep hbound n ρ⟩
  let : IsSubProbabilityMeasure (limExecFor step ρ) := ⟨limExecFor_univ_le_one hstep hbound ρ⟩
  have hle : execNFor step n ρ ≤ limExecFor step ρ := le_iSup (execNFor step · ρ) n
  exact (eq_of_le_of_measure_univ_eq hle
    (le_antisymm (hle _) (hterm ▸ IsSubProbabilityMeasure.measure_le_one _))).symm

end MeasurableKernel

variable [LawfulProbLangℝ rT] [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]

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

/-- A deterministic step consumes one unit of fuel. -/
theorem execN_succ_of_step {ρ next : Cfg rT} (hv : ¬ρ.expr.isValue)
    (hdet : primStep ρ = dirac next) (n : ℕ) : execN (n + 1) ρ = execN n next := by
  simpa only [execNFor_primStep] using execNFor_succ_of_step primStep.measurable hv hdet n

/-- Pure steps consume one unit of fuel each. -/
theorem execN_pure_steps {e₁ e₂ : Exp rT} {k : ℕ} (h : nsteps PureStep k e₁ e₂) (fuel : ℕ)
    (σ : State rT) : execN (k + fuel) ⟨e₁, σ⟩ = execN fuel ⟨e₂, σ⟩ := by
  induction k generalizing e₁ with
  | zero =>
    cases h
    simp only [Nat.zero_add]
  | succ k ih =>
    obtain ⟨e, hpure, hrest⟩ := h
    rw [Nat.succ_add, execN_succ_of_step (val_stuck (hpure.safe σ)) (hpure.det σ)]
    exact ih hrest

/-- Storing into an allocated cell steps to unit. -/
theorem primStep_store (σ : State rT) (l : Loc) (old value : Val rT)
    (hlookup : σ.heap[l]? = some old) :
    primStep ⟨.store (.lit (.loc l)) (ofVal value), σ⟩ =
      dirac ⟨.lit .unit, σ.updateHeap (·.insert l value)⟩ := by
  have hd : (store (.lit (.loc l)) (ofVal value)).decompItem = none := by
    simp only [decompItem, toVal?_ofVal]
    rfl
  rw [primStep_eq_headStep hd]
  simp [headStep, asValM, toVal?_ofVal, hlookup]

/-- Allocation steps to a fresh location. -/
theorem primStep_alloc (σ : State rT) (value : Val rT) :
    primStep ⟨.alloc (ofVal value), σ⟩ =
      dirac ⟨.lit (.loc σ.heap.fresh), σ.updateHeap (·.insert σ.heap.fresh value)⟩ := by
  have hd : (alloc (ofVal value)).decompItem = none := by
    simp [decompItem, toVal?_ofVal]
  rw [primStep_eq_headStep hd]
  simp [headStep, asValM, toVal?_ofVal]

/-- A foreign step on a value is the step of the foreign code. -/
theorem primStep_ffi {e : Exp rT} {v : Val rT} (hv : e.toVal? = some v) (σ : State rT)
    {r : FFIOutcome rT × LocHeap (Val rT)} (h : ProbLangFFI.ffi (v, σ.heap) = some r) :
    primStep ⟨.ffi e, σ⟩ = dirac (Cfg.ofFFI σ r) := by
  have hd : (ffi e).decompItem = none := by simp [decompItem, hv]
  rw [primStep_eq_headStep hd]
  simp [headStep, asValM, hv, Cfg.ffi, h, Option.unwrapM]

end ProbLang
