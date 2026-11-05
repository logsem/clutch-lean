module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # The geometric sampler

Specified in `TotalEris/Examples/GeometricTotal`. -/

namespace ProbLang
namespace TotalEris
namespace Examples

/-- A geometric sampler that counts failed fair-coin trials. -/
@[pl_names]
def geometric {rT : Type _} : Exp rT :=
  pl% rec geo n := if rand(#2, #()) = #0 then #0 else (geo n) + #1

end Examples
end TotalEris
end ProbLang
