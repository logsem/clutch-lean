module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # One-time pad over the unit interval

Refined in `Micrometer/Examples/ContinuousOTP`. -/

namespace ProbLang
namespace ContinuousOTP

variable {rT : Type _}

/-- The LHS program: sample a uniform key `k`, output `frac (m + k)`. -/
def otp_enc (m : rT) : Exp rT :=
  pl% let k := urand; frac(#(.real m) + k)

/-- The RHS program: just sample uniformly. -/
def otp_ideal : Exp rT := pl% urand

end ContinuousOTP
end ProbLang
