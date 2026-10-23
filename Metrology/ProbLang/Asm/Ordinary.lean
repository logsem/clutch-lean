module

public import Metrology.ProbLang.Asm.Step
public import Metrology.ProbLang.DetStep

/-! # Ordinary program transitions under the foreign-call kernel -/

@[expose] public section

namespace ProbLang.Asm

open MeasureTheory MeasureTheory.Measure

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

/-- Every enabled base-language transition has exactly the same foreign-kernel distribution. -/
theorem primStepWith_eq_primStep_of_nonzero (env : FfiEnv rT) (ρ : Cfg rT)
    (hne : primStep ρ ≠ 0) : primStepWith env ρ = primStep ρ := by
  unfold primStepWith primStep
  cases hd : ρ.expr.decomp with
  | mk K redex =>
    cases redex <;> try rfl
    all_goals
      exfalso
      apply hne
      simp [primStep, hd, headStep]

/-- A base-language pure step remains the same pure transition under a foreign-call environment. -/
theorem pureStep_with (env : FfiEnv rT) {e₁ e₂ : Exp rT} (h : PureStep e₁ e₂) (σ : State rT) :
    primStepWith env ⟨e₁, σ⟩ = dirac ⟨e₂, σ⟩ := by
  rw [primStepWith_eq_primStep_of_nonzero env _ (h.safe σ), h.det σ]

end ProbLang.Asm
