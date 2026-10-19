module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Flip a coin until heads

Proved to return `0` almost surely in `Micrometer/Examples/Retry`. -/

namespace ProbLang
namespace Retry

variable {rT : Type _}

/-- Flip a fair coin until it shows `0`, then return `0`. -/
@[pl_fold]
def retryLoop : Exp rT :=
  pl% rec loop u := if rand(#2, #.unit) = #0 then #0 else loop u

/-- Run `retryLoop`. -/
def retry : Exp rT :=
  pl% &retryLoop #.unit

end Retry
end ProbLang
