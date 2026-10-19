module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Randomized response

Proved differentially private in `Micrometer/Examples/RandomizedResponse/Dp`. -/

namespace ProbLang
namespace RandomizedResponse

variable {rT : Type _}

/-- Report the bit `b` truthfully with probability `3/4`, else flip it
(clutch-dp's `randomized_response.v`). -/
def rr (b : Bool) : Exp rT := pl%
  let r := rand(#4, #.unit); if r < #3 then #(.bool b) else ~#(.bool b)

end RandomizedResponse
end ProbLang
