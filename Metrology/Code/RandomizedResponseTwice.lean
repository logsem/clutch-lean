module

public import Metrology.Code.RandomizedResponse
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Randomized response on two bits

Proved zCDP and DP in `Micrometer/Examples/RandomizedResponse/Twice`. -/

namespace ProbLang
namespace RandomizedResponse

variable {rT : Type _}

/-- Randomize the two bits `b₁` and `b₂` independently and report both. -/
def rr2 (b₁ b₂ : Bool) : Exp rT :=
  pl% let x := &(rr b₁); let y := &(rr b₂); (x, y)

end RandomizedResponse
end ProbLang
