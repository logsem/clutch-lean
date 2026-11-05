module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

/-! # Coin flips

The recursive coin-flipping program used by the Total Eris examples. -/

@[expose] public section

namespace ProbLang
namespace TotalEris
namespace Examples

/-- The number of heads in a sequence of fair coin flips. -/
@[pl_fold]
def heads {rT : Type _} : Exp rT := pl%
  rec flips n := if n = #0 then #0 else (let x := rand(#2, #()); x + flips (n - #1))

end Examples
end TotalEris
end ProbLang
