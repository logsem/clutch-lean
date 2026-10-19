module

public import Metrology.Micrometer.Soundness
public import Metrology.Micrometer.Examples.RandomizedResponse.Dp

@[expose] public section

/-! # Randomized response stays private inside a boolean context

`rr_refines` lifts through any linear context, here `if [·] then false else true`; linear
because the credit `↯b` is spent once, and a hole run twice would spend it twice. -/

open Iris Iris.BI Iris.ProofMode GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang
namespace RandomizedResponse

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

/-- The context `if [·] then false else true`. -/
def negCtx : Ctx rT := [.ifL (.lit (.bool false)) (.lit (.bool true))]

/-- Every result of the negated report is at most three times as likely under one private bit as
under the other. -/
theorem rr_negCtx_le (b b' c : Bool) (σ σ' : State rT) :
    limExec ⟨negCtx.fill (rr b), σ⟩ (finalBool c) ≤
      3 * limExec ⟨negCtx.fill (rr b'), σ'⟩ (finalBool c) := by
  simpa [expBudget_log_three] using refines_ctx_dp (GF := MicrometerFunctor rT (ℝ≥0∞ × ℝ≥0∞))
    ENNReal.ofReal_ne_top (rr b) (rr b') .bool (fun _ _ _ ↦ rr_refines b b') negCtx σ σ' c
    (.cons (.ifL .lit_bool .lit_bool) .nil) ⟨trivial, trivial⟩

end RandomizedResponse
end ProbLang
