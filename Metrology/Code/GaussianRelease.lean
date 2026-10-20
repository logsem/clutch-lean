module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Repeated Gaussian release

The program `release g a k` draws `k` times from a sampler `g` at input `a` and returns all draws.
Its zero-concentrated DP proof is in `Micrometer/Examples/GaussianZcdp`. -/

namespace ProbLang
namespace GaussianRelease

variable {rT : Type _}

/-- Release one draw of the sampler `g` at the input `a` per iteration, as nested pairs ending
in `()`. The sampler `g` is passed as an argument rather than spliced in, so `releaseLoop a`
contains no opaque `Val` and steps by computation. -/
def releaseLoop (a : rT) : Exp rT :=
  pl% rec loop g n := if n = #0 then #.unit else (g #(.real a), loop g (n - #1))

/-- Release `k` draws of the sampler `g` at the input `a`. -/
def release (g : Val rT) (a : rT) (k : ℕ) : Exp rT :=
  pl% &(releaseLoop a) {Exp.ofVal g} #(.int k)

end GaussianRelease
end ProbLang
