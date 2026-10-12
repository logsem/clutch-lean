module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # The uniform 1D random walk

Specified in `TotalEris/Examples/RandomWalk`, whose docstring explains why
`rand 1` makes this walk degenerate. -/

namespace ProbLang
namespace TotalEris
namespace Examples

variable {rT : Type _}

def unifRw1dRec : Exp rT :=
  pl% rec f n α :=
        if n < #1 then #.unit
        else
          let x := rand(#1, α);
          if x < #1
            then f (n - #1) α
            else f (n + #1) α

def unifRw1d : Exp rT :=
  pl% let α := alloc(#1); &unifRw1dRec #1 α

@[pl_fold]
def biasedWalk (u m : ℕ) (a : ℤ) : Exp rT := pl%
  rec walk n x :=
    if x = #(.int a) then #true
    else if n = #0 then #false
    else
      (let r := rand(#(.int m), #.unit);
        if r < #(.int u) then walk (n - #1) (x + #1) else walk (n - #1) (x - #1))

end Examples
end TotalEris
end ProbLang
