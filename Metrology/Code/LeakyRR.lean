module

public import Metrology.Code.RandomizedResponse
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Randomized response that leaks its input with probability `1/N`

Proved `(ln 3, 1/N)`-differentially private in `Micrometer/Examples/LeakyRR`. -/

namespace ProbLang
namespace LeakyRR

variable {rT : Type _}

/-- Draw uniformly from `{0, …, N-1}`: on `0` report `b` itself, otherwise run randomized
response on `b`. -/
def leakyRR (N : Int) (b : Bool) : Exp rT :=
  pl% let x := rand(#(.int N), #.unit); if x = #0 then #(.bool b) else &(RandomizedResponse.rr b)

end LeakyRR
end ProbLang
