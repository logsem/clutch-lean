module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

namespace ProbLang
namespace TotalEris
namespace Examples

@[pl_fold]
def heads {rT : Type _} : Exp rT := pl%
  rec flips n :=
    if n = #0 then #0 else (let x := rand(#2, #()); x + flips (n - #1))

end Examples
end TotalEris
end ProbLang
