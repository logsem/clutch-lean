module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Repeated Gaussian release

Proved zero-concentrated differentially private in `Micrometer/Examples/GaussianZcdp`. -/

namespace ProbLang
namespace GaussianRelease

variable {rT : Type _}

/-- Release `k` draws of the sampler `g` at the input `a`, as nested pairs ending in `()`. -/
def release (g : Val rT) (a : rT) : ℕ → Exp rT
  | 0 => pl% #.unit
  | k + 1 => pl% ({Exp.ofVal g} #(.real a), &(release g a k))

end GaussianRelease
end ProbLang
