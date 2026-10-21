module

public import Metrology.Code.RandomizedResponse
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Randomized response that leaks its input with probability `1/N`

The program `leakyRR`; its `(ln 3, 1/N)`-DP proof `leakyRR_DP` is in
`Micrometer/Examples/LeakyRR`. -/

namespace ProbLang
namespace LeakyRR

variable {rT : Type _}

/-- Randomized response on `b` that releases `b` outright when a uniform draw from
`{0, …, N-1}` is `0`, i.e. with probability `1/N`. -/
def leakyRR (N : Int) (b : Bool) : Exp rT :=
  pl% let x := rand(#N, #()); if x = #0 then #b else &(RandomizedResponse.rr b)

end LeakyRR
end ProbLang
