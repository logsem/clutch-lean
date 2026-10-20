module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Two labelled draws, in either order

Proved, event by event, at most as likely as the reverse order in
`Micrometer/Examples/Presample`. -/

namespace ProbLang
namespace Presample

variable {rT : Type _}

/-- Allocate tapes `α` and `β`, draw from `α`, then from `β`. -/
def drawAB (N : Int) : Exp rT :=
  pl% let α := tape(#(.int N)); let β := tape(#(.int N));
    let x := rand(#(.int N), α); let y := rand(#(.int N), β); (x, y)

/-- Allocate tapes `α` and `β`, draw from `β`, then from `α`. -/
def drawBA (N : Int) : Exp rT :=
  pl% let α := tape(#(.int N)); let β := tape(#(.int N));
    let y := rand(#(.int N), β); let x := rand(#(.int N), α); (x, y)

/-- Draw from a fresh tape. -/
def drawTape (N : Int) : Exp rT :=
  pl% let α := tape(#(.int N)); rand(#(.int N), α)

/-- Draw without a tape. -/
def draw (N : Int) : Exp rT :=
  pl% rand(#(.int N), #.unit)

end Presample
end ProbLang
