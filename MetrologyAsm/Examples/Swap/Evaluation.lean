import MetrologyAsm.Examples.Swap.Specification
import MetrologyAsm.Examples.Swap.Witness

/-! # The unique Sail-backed evaluation of the exchange source -/

namespace MetrologyAsm

open ProbLang ProbLang.Asm

/-- Compatible-state nonvacuity and the universal Sail specification select the exchange result. -/
theorem swap_eval (l k : Loc) (old : Loc → Int) (hne : l ≠ k)
    (hl : inRange true 64 (old l) = true) (hk : inRange true 64 (old k) = true) :
    rv.eval swapCode [.loc l, .loc k] (callFootprint swapCode [.loc l, .loc k])
      (integerHeap {l, k} old) = some (.ret .unit (integerHeap {l, k} (swapValues old l k))) := by
  exact rv_eval_ret swapCode [.loc l, .loc k] _ _ .unit
    (swap_compat_exists l k old hne hl hk) (swap_rvspec l k old hne hl hk)

end MetrologyAsm
