module

public import Metrology.ProbLang.KernelExec
public import Metrology.ProbLang.Asm.Measurable

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

/-- A finite full-mass foreign execution determines the complete execution distribution. -/
theorem limExecWith_term (env : FfiEnv rT) {n : Nat} {ρ : Cfg rT}
    (hterm : execNWith env n ρ Set.univ = 1) : limExecWith env ρ = execNWith env n ρ :=
  limExecFor_term (measurable_primStepWith env) (primStepWith_univ_le_one env) hterm

end ProbLang.Asm
