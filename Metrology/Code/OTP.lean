module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # One-time pad over `{0, …, N-1}`

Refined in `Micrometer/Examples/OTP`. -/

namespace ProbLang
namespace OTP

variable {rT : Type _}

/-- The LHS program: sample a key, then output `(m + k) mod N`. -/
def otp_enc (m N : Int) : Exp rT :=
  pl% let k := rand(#(.int N), #(.unit)); (#(.int m) + k) % #(.int N)

/-- The RHS program: just sample uniformly. -/
def otp_ideal (N : Int) : Exp rT :=
  pl% rand(#(.int N), #(.unit))

end OTP
end ProbLang
