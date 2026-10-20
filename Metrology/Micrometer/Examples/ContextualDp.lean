module

public import Metrology.Micrometer.Soundness
public import Metrology.Micrometer.Examples.RandomizedResponse.Dp

@[expose] public section

/-! # Randomized response stays private inside a boolean context

Main result `rr_negCtx_le`: `rr_refines` lifts through the linear context
`if [·] then false else true` by `refines_ctx_dp`. Linear, because the credit `↯b` is spent once
and a hole run twice would spend it twice. -/

open Iris Iris.BI Iris.ProofMode GradedLifting GradedDivergence
open scoped ENNReal

namespace ProbLang
namespace RandomizedResponse

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

/-- The context `if [·] then false else true`. -/
def negCtx : Ctx rT := [.ifL (.lit (.bool false)) (.lit (.bool true))]

/-- The negated randomized-response report is `(ln 3, 0)`-DP: every result is at most three times as
likely under one private bit as under the other. -/
theorem rr_negCtx_le (b b' c : Bool) (σ σ' : State rT) :
    limExec ⟨negCtx.fill (rr b), σ⟩ (finalBool c) ≤
      3 * limExec ⟨negCtx.fill (rr b'), σ'⟩ (finalBool c) := by
  simpa [expBudget_log_three] using refines_ctx_dp (GF := MicrometerFunctor rT (ℝ≥0∞ × ℝ≥0∞))
    ENNReal.ofReal_ne_top (rr b) (rr b') .bool (fun _ _ _ ↦ rr_refines b b') negCtx σ σ' c
    -- `negCtx` is typed bool → bool
    (.cons (.ifL .lit_bool .lit_bool) .nil)
    -- and linear (its hole runs once)
    ⟨trivial, trivial⟩

end RandomizedResponse
end ProbLang
