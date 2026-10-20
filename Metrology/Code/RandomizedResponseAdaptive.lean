module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Adaptive randomized response

The programs `rr3` (a 2/3-biased round) and `rrAdaptive` (second round only after a `true` report).
Their Rényi-2 bound `log (19/12)`, below the naive `log (9/4)`, is proved in
`Micrometer/Examples/RandomizedResponse/Adaptive`. -/

namespace ProbLang
namespace RandomizedResponse

variable {rT : Type _}

/-- Report the bit `b` truthfully with probability `2/3`, else flip it. -/
def rr3 (b : Bool) : Exp rT :=
  pl% let r := rand(#3, #.unit); if r < #2 then #(.bool b) else ~#(.bool b)

/-- Randomize `b` with `rr3`; after a reported `true`, randomize it again; report both bits
(`AdaptiveRenyi.adaptive` as a program). -/
def rrAdaptive (b : Bool) : Exp rT :=
  pl% let x := &(rr3 b); if x then (x, &(rr3 b)) else (x, #(.bool false))

end RandomizedResponse
end ProbLang
