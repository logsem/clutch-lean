import MetrologyAsm.Examples.Callback.EvaluationRules
import MetrologyAsm.Examples.Callback.Specification
import MetrologyAsm.Examples.Callback.Witness

/-! # The unique interaction of the actual Sail callback fragment -/

namespace MetrologyAsm

open ProbLang ProbLang.Asm

/-- Universal Sail correctness and genuine compatible entry select the canonical callback tree. -/
theorem importToy_eval : rv.eval importToyCode [] ∅ ∅ = some importToyTree :=
  importToy_eval_of_spec importToy_rvspec importToy_compat_exists

end MetrologyAsm
