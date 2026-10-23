module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Randomized response

The one-round program `rr` (the loop is in `RandomizedResponseLoop`; proofs are in
`Micrometer/Examples/RandomizedResponse/`). -/

namespace ProbLang
namespace RandomizedResponse

variable {rT : Type _}

/-- Report the bit `b` truthfully with probability `3/4`, else flip it
(clutch-dp's `randomized_response.v`). -/
def rr (b : Bool) : Exp rT := pl%
  let r := rand(#4, #()); if r < #3 then #b else ~#b

end RandomizedResponse
end ProbLang
