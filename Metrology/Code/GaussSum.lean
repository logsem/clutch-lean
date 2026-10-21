module

public import Metrology.Code.Samplers
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

namespace ProbLang
namespace TotalEris
namespace Examples

@[pl_fold]
def gaussSum {rT : Type _} [ProbLangℝ rT] : Exp rT := pl%
  rec go n :=
    if n = #0 then toReal(#0) else (let y := &Gauss #(); y + go (n - #1))

end Examples
end TotalEris
end ProbLang
