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

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT] [ProbLangDist rT] [ProbLangFFI rT]
  [ProbLangObs rT] [Countable rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)
variable (E : CoPset) (Φ : Val rT → IProp GF)

/-- `twp_bind` discovers the context `K = [.fst]`; `hcont` pins the refocused goal. -/
example
    (hcont : ⊢ tglWp E pl(alloc(#1)) (fun w => tglWp E pl(fst({Exp.ofVal w})) Φ)) :
    ⊢ tglWp E pl(fst(alloc(#1))) Φ := by
  twp_bind pl(alloc(#1))
  exact hcont

/-- `twp_pure` β-reduces at the top level (`K = []`). -/
example
    (hcont : ⊢ tglWp E pl(#1) Φ) :
    ⊢ tglWp E pl((fun x, x) #1) Φ := by
  twp_pure pl((fun x, x) #1)
  exact hcont

example :
    ⊢ tglWp E pl(fst(((fun x, x) #1, #2)))
      (fun w : Val rT => iprop(⌜w = .int 1⌝)) := by
  twp_pures
  twp_value
  itrivial

example :
    ⊢ tglWp E pl(#1 + #2) (fun w : Val rT => iprop(⌜w = .int 3⌝)) := by
  twp_pure pl(#1 + #2)
  twp_value
  itrivial

/-- `twp_pure` steps inside the family argument of a `sample`. -/
example
    (hcont : ⊢ tglWp E (.sample 0 pl(#3) pl(#())) Φ) :
    ⊢ tglWp E (.sample 0 pl(#1 + #2) pl(#())) Φ := by
  twp_pure pl(#1 + #2)
  exact hcont

/-- `twp_pures` steps inside both arguments of an `allocN`, right to left. -/
example
    (hcont : ⊢ tglWp E (.allocN pl(#2) pl(#3)) Φ) :
    ⊢ tglWp E (.allocN pl(#1 + #1) pl(#1 + #2)) Φ := by
  twp_pures
  exact hcont

/-- `twp_pure` steps inside a tape allocation used as a sample label. -/
example
    (hcont : ⊢ tglWp E (.sample 0 pl(#()) (.dtape 0 pl(#3))) Φ) :
    ⊢ tglWp E (.sample 0 pl(#()) (.dtape 0 pl(#1 + #2))) Φ := by
  twp_pure pl(#1 + #2)
  exact hcont

open ProbLangℝ in
/-- `twp_pures` steps the real operators: arithmetic, `floor`, the elementary functions and `π`. -/
example (r : rT) :
    ⊢ tglWp E pl(floor(log(#real r) - sqrt(#real r) * exp(#real r) / sin(cos(atan(#pi)))))
      (fun w : Val rT => iprop(⌜w = .int (realFloor (realAdd (realLog r) (realNeg (realDiv
        (realMul (realSqrt r) (realExp r)) (realSin (realCos (realAtan realPi)))))))⌝)) := by
  twp_pures
  twp_value
  itrivial

end TotalEris
end ProbLang
