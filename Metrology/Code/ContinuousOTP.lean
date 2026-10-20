module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # One-time pad over the unit interval

The continuous analogue of `Code/OTP`: the encryption program `otp_enc` and the ideal sampler
`otp_ideal`. The proof that they refine each other is in `Micrometer/Examples/ContinuousOTP`. -/

namespace ProbLang
namespace ContinuousOTP

variable {rT : Type _}

/-- The encryption program: sample a uniform key `k` and output the fractional part of `m + k`. -/
def otp_enc (m : rT) : Exp rT :=
  pl% let k := urand; frac(#(.real m) + k)

/-- The ideal sampler: draw uniformly from the unit interval. -/
def otp_ideal : Exp rT := pl% urand

end ContinuousOTP
end ProbLang
