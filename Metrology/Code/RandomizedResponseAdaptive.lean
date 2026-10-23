module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Adaptive randomized response

Proved Rényi-2 private in `Micrometer/Examples/RandomizedResponse/Adaptive`. -/

namespace ProbLang
namespace RandomizedResponse

variable {rT : Type _}

/-- Report the bit `b` truthfully with probability `2/3`, else flip it. -/
def rr3 (b : Bool) : Exp rT :=
  pl% let r := rand(#3, #()); if r < #2 then #b else ~#b

/-- Randomize `b` with `rr3`; after a reported `true`, randomize it again; report both bits
(`AdaptiveRenyi.adaptive` as a program). -/
def rrAdaptive (b : Bool) : Exp rT :=
  pl% let x := &(rr3 b); if x then (x, &(rr3 b)) else (x, #false)

end RandomizedResponse
end ProbLang
