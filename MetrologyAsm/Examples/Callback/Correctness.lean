import MetrologyAsm.Examples.Callback.Evaluation
import MetrologyAsm.Examples.Callback.Micrometer

/-! # The verified Sail-to-ProbLang callback round trip -/

namespace MetrologyAsm

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.Asm MicrometerWpGS GradedLifting

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B] [OrderTop B]
  {L : GradedLifting.{0} B} {GF : BundledGFunctors}
  [MicrometerGS rT hlc GF] [BudgetGS B GF] [L.IsLawful] [L.IsTopAbsorbing]
  {E : CoPset} {Φ : Val rT → IProp GF}

local bi IProp GF

/-- The assembled Sail code invokes the ordinary ProbLang callback and returns its value. -/
theorem wp_importToy : iprop%
    ▷ ▷ ▷ Φ (.int 7) ⊢ wpFor (primStepWith importToyEnv) L E importToyExpression Φ := by
  apply wp_importToy_of_eval (next := importToyNext)
  · simpa only [importToyTree_eq] using importToy_eval
  · exact importToyNext_valid _ _ importToy_response_ok

/-- The actual assembled callback fragment returns seven under the shared weakest precondition. -/
theorem wp_importToy_spec : iprop%
    ⊢ wpFor (primStepWith importToyEnv) L E importToyExpression
      (fun v => iprop(⌜v = .int 7⌝)) := by
  iapply wp_importToy
  iintro !> !> !>
  ipureintro
  rfl

end MetrologyAsm
