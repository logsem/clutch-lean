module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Presample programs: two tape draws in either order

`Micrometer/Examples/Presample` proves `drawAB` refines `drawBA` (`drawAB_refines_drawBA`), hence
is at most as likely on every event (`drawAB_le_drawBA`). -/

namespace ProbLang
namespace Presample

variable {rT : Type _}

/-- Allocate tapes `α`, `β`, draw from `α` then `β`, and return the pair. -/
def drawAB (N : Int) : Exp rT :=
  pl% let α := tape(#(.int N)); let β := tape(#(.int N));
    let x := rand(#(.int N), α); let y := rand(#(.int N), β); (x, y)

/-- Allocate tapes `α`, `β`, draw from `β` then `α`, and return the pair. -/
def drawBA (N : Int) : Exp rT :=
  pl% let α := tape(#(.int N)); let β := tape(#(.int N));
    let y := rand(#(.int N), β); let x := rand(#(.int N), α); (x, y)

/-- Draw uniformly from `{0,…,N-1}`, reading a fresh tape. -/
def drawTape (N : Int) : Exp rT :=
  pl% let α := tape(#(.int N)); rand(#(.int N), α)

/-- Draw uniformly from `{0,…,N-1}`, sampling at this step (no tape). -/
def draw (N : Int) : Exp rT :=
  pl% rand(#(.int N), #.unit)

end Presample
end ProbLang
