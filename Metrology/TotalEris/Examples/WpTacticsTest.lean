module

public import Metrology.TotalEris
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Smoke tests for the `twp_*` tactics -/

open Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS

namespace ProbLang
namespace TotalEris

variable {rT : Type _} [LawfulProbLangℝ rT] [Countable rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi IProp GF

/-- `twp_bind` discovers the context `K = [.fst]`; `hcont` pins the refocused goal. -/
example (E : CoPset) (Φ : Val rT → IProp GF)
    (hcont : ⊢ tglWp E pl(alloc(#1))
      (fun w => tglWp E pl(fst({Exp.ofVal w})) Φ)) :
    ⊢ tglWp E pl(fst(alloc(#1))) Φ := by
  twp_bind pl(alloc(#1))
  exact hcont

/-- `twp_pure` β-reduces at the top level (`K = []`). -/
example (E : CoPset) (Φ : Val rT → IProp GF)
    (hcont : ⊢ tglWp E pl(#1) Φ) :
    ⊢ tglWp E pl((fun x, x) #1) Φ := by
  twp_pure pl((fun x, x) #1)
  exact hcont

example (E : CoPset) :
    ⊢ tglWp E pl(fst(((fun x, x) #1, #2)))
      (fun w : Val rT => iprop(⌜w = .int 1⌝)) := by
  twp_pures
  twp_value
  itrivial

example (E : CoPset) :
    ⊢ tglWp E pl(#1 + #2)
      (fun w : Val rT => iprop(⌜w = .int 3⌝)) := by
  twp_pure pl(#1 + #2)
  twp_value
  itrivial

end TotalEris
end ProbLang
