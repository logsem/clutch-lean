module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # A uniform draw that never reports `0`

Proved within `1/N` of a uniform draw in `Micrometer/Examples/SkipZero`. -/

namespace ProbLang
namespace SkipZero

variable {rT : Type _}

/-- Draw uniformly from `{0, …, N-1}`. -/
def unif (N : Int) : Exp rT :=
  pl% rand(#(.int N), #.unit)

/-- Draw uniformly from `{0, …, N-1}`, but report `1` instead of `0`. -/
def skipZero (N : Int) : Exp rT :=
  pl% let x := rand(#(.int N), #.unit); if x = #0 then #1 else x

end SkipZero
end ProbLang
