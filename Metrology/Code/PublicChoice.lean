module

public import Metrology.Code.RandomizedResponse
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # A public coin choosing between two mechanisms

The program `choice b`: a public coin picks randomized response or the constant `true`.
Its DP choice law (the proof pays the larger cost) is in `Micrometer/Examples/PublicChoice`. -/

namespace ProbLang
namespace PublicChoice

variable {rT : Type _}

/-- Flip a public coin: on `0` run randomized response on `b`, on `1` answer `true`. -/
def choice (b : Bool) : Exp rT :=
  pl% if rand(#2, #.unit) = #0 then &(RandomizedResponse.rr b) else #(.bool true)

end PublicChoice
end ProbLang
