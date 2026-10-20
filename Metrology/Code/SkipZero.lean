module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Uniform draw with `0` reported as `1`

The programs `unif` and `skipZero`; `Micrometer/Examples/SkipZero` shows they are
within `1/N` in tv. -/

namespace ProbLang
namespace SkipZero

variable {rT : Type _}

/-- A uniform draw from `{0, …, N-1}`. -/
def unif (N : Int) : Exp rT :=
  pl% rand(#(.int N), #.unit)

/-- A uniform draw from `{0, …, N-1}` that reports `1` whenever it draws `0`. -/
def skipZero (N : Int) : Exp rT :=
  pl% let x := rand(#(.int N), #.unit); if x = #0 then #1 else x

end SkipZero
end ProbLang
