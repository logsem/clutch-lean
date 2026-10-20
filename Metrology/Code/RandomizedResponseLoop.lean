module

public import Metrology.Code.RandomizedResponse
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Randomized response in a loop

Proved private in any lifting by `rrCount_isPrivate` in
`Micrometer/Examples/RandomizedResponse/Basic`; DP, zCDP, tCDP, Rényi and χ² instances in its
sibling files. -/

namespace ProbLang
namespace RandomizedResponse

variable {rT : Type _}

/-- Randomize the bit `b` once per iteration, `n` times, and count the `true` reports. -/
@[pl_fold]
def rrLoop (b : Bool) : Exp rT := pl%
  rec loop n := if n = #0 then #0 else (if &(rr b) then #1 else #0) + loop (n - #1)

/-- The loop `rrLoop b` run for `k` iterations: the count of `true` reports. -/
def rrCount (b : Bool) (k : Int) : Exp rT := pl% &(rrLoop b) #(.int k)

end RandomizedResponse
end ProbLang
