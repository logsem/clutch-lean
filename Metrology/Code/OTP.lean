module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # One-time pad over `{0, …, N-1}`

The proof that `otp_enc` and `otp_ideal` refine each other is in `Micrometer/Examples/OTP`. -/

namespace ProbLang
namespace OTP

variable {rT : Type _}

/-- One-time pad: draw a uniform key `k` below `N` and return `(m + k) mod N`. -/
def otp_enc (m N : Int) : Exp rT :=
  pl% let k := rand(#N, #()); (#m + k) % #N

/-- The ideal sampler: draw uniformly from `{0, …, N-1}`. -/
def otp_ideal (N : Int) : Exp rT :=
  pl% rand(#N, #())

end OTP
end ProbLang
