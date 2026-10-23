module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Presample programs: two tape draws in either order

`Micrometer/Examples/Presample` proves that `drawAB` refines `drawBA`. -/

namespace ProbLang
namespace Presample

variable {rT : Type _} (N : Int)

/-- Allocate tapes `α`, `β`, draw from `α` then `β`, and return the pair. -/
def drawAB : Exp rT :=
  pl% let α := tape(#N); let β := tape(#N); let x := rand(#N, α); let y := rand(#N, β); (x, y)

/-- Allocate tapes `α`, `β`, draw from `β` then `α`, and return the pair. -/
def drawBA : Exp rT :=
  pl% let α := tape(#N); let β := tape(#N); let y := rand(#N, β); let x := rand(#N, α); (x, y)

/-- Draw uniformly from `{0,…,N-1}`, reading a fresh tape. -/
def drawTape : Exp rT :=
  pl% let α := tape(#N); rand(#N, α)

/-- Draw uniformly from `{0,…,N-1}`, sampling at this step (no tape). -/
def draw : Exp rT :=
  pl% rand(#N, #())

end Presample
end ProbLang
