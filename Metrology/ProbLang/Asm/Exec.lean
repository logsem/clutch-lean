module

public import Metrology.ProbLang.KernelExec
public import Metrology.ProbLang.Asm.Measurable
public import Metrology.ProbLang.Asm.Ordinary

/-! # Actual bounded and limit execution of assembly-calling programs -/

@[expose] public section

noncomputable section

namespace ProbLang.Asm

open MeasureTheory

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

/-- Bounded execution uses the same foreign-call kernel as the guarded assembly WP. -/
abbrev execNWith (env : FfiEnv rT) : Nat → Cfg rT → Measure (Cfg rT) :=
  execNFor (primStepWith env)

/-- The entire terminal configuration distribution of an assembly-calling program. -/
abbrev limExecWith (env : FfiEnv rT) : Cfg rT → Measure (Cfg rT) :=
  limExecFor (primStepWith env)

/-- The output distribution after forgetting the assembly-calling program's final private state. -/
abbrev limExecVWith (env : FfiEnv rT) : Cfg rT → Measure (Exp rT) :=
  limExecVFor (primStepWith env)

/-- A deterministic actual FFI-kernel transition consumes one unit of bounded-execution fuel. -/
theorem execNWith_succ_of_step (env : FfiEnv rT) {ρ next : Cfg rT}
    (hv : ¬ρ.expr.isValue) (hdet : primStepWith env ρ = Measure.dirac next) (n : Nat) :
    execNWith env (n + 1) ρ = execNWith env n next :=
  execNFor_succ_of_step (measurable_primStepWith env) hv hdet n

/-- Base-language pure execution composes with the actual explicit-kernel bounded semantics. -/
theorem execNWith_pure_steps (env : FfiEnv rT) {e₁ e₂ : Exp rT} {k : Nat}
    (h : nsteps PureStep k e₁ e₂) (fuel : Nat) (σ : State rT) :
    execNWith env (k + fuel) ⟨e₁, σ⟩ = execNWith env fuel ⟨e₂, σ⟩ := by
  show execNFor (primStepWith env) (k + fuel) ⟨e₁, σ⟩ = execNFor (primStepWith env) fuel ⟨e₂, σ⟩
  induction k generalizing e₁ with
  | zero =>
    cases h
    simp only [Nat.zero_add]
  | succ k ih =>
    obtain ⟨e, hpure, hrest⟩ := h
    rw [Nat.succ_add, execNFor_succ_of_step (measurable_primStepWith env)
      (val_stuck (hpure.safe σ)) (pureStep_with env hpure σ)]
    exact ih hrest

/-- A finite full-mass foreign execution determines the complete execution distribution. -/
theorem limExecWith_term (env : FfiEnv rT) {n : Nat} {ρ : Cfg rT}
    (hterm : execNWith env n ρ Set.univ = 1) : limExecWith env ρ = execNWith env n ρ :=
  limExecFor_term (measurable_primStepWith env) (primStepWith_univ_le_one env) hterm

end ProbLang.Asm
