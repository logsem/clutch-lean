module

public import Metrology.Code.RandomizedResponse
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # A public coin choosing between two mechanisms

Proved differentially private by the DP choice law, paying only the larger branch cost, in
`Micrometer/Examples/PublicChoice`. -/

namespace ProbLang
namespace PublicChoice

variable {rT : Type _}

/-- Flip a public coin: on `0` run randomized response on `b`, on `1` answer `true`. -/
def choice (b : Bool) : Exp rT :=
  pl% if rand(#2, #()) = #0 then &(RandomizedResponse.rr b) else #true

end PublicChoice
end ProbLang
