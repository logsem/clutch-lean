module

public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.Exp

@[expose] public section

/-! # Measurable space on values

The σ-algebra on `Val α` (the pullback along `Val.fst`), with measurability of `Val.fst`, `Val.mk`
and `Exp.ofVal`, and measurable singletons.
-/

noncomputable section ProbLangMeasures

open MeasurableSpace (comap measurableSet_comap measurableSet_iInf measurableSet_top)
open Set (mem_singleton_iff mem_preimage)

namespace ProbLang

variable {α : Type _}

/-- Proofs that `e` is a value carry the discrete σ-algebra. -/
instance instMeasurableSpaceIsVal {e : Exp α} : MeasurableSpace (IsVal e) := ⊤

variable [MeasurableSpace α]

namespace Val

-- A `Sigma` instance would be `⊤` here (since `IsVal e` is `⊤`), breaking measurability of
-- `Exp.toVal?`; the high priority keeps this one.
/-- The σ-algebra on values: the pullback along `Val.fst`. -/
instance (priority := 10000) instMeasurableSpaceVal : MeasurableSpace (Val α) :=
  comap fst inferInstance

/-- `Val.fst` is measurable. -/
@[fun_prop]
theorem fst.measurable : Measurable (fst : Val α → Exp α) :=
  fun _ hS => measurableSet_comap.mpr ⟨_, hS, rfl⟩

/-- `Exp.ofVal` is measurable. -/
@[fun_prop]
theorem _root_.ProbLang.Exp.ofVal.measurable : Measurable (Exp.ofVal : Val α → Exp α) :=
  fst.measurable

/-- `Val.mk` is measurable on `Σ e, IsVal e`. -/
@[fun_prop]
theorem mk.measurable : Measurable (fun p : Σ e : Exp α, IsVal e => mk p.1 p.2 p.2.lc) := by
  intro T hT
  obtain ⟨U, -, rfl⟩ := measurableSet_comap.mp hT
  exact measurableSet_iInf.mpr fun _ => measurableSet_top

/-- `Val α` has measurable singletons if `α` does. -/
instance instMeasurableSingletonClass [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Val α) where
  measurableSet_singleton v := by
    have heq : ({v} : Set (Val α)) = fst ⁻¹' {v.fst} := by
      ext v'
      simp only [mem_singleton_iff, mem_preimage]
      exact ⟨fun h => by rw [h], ext⟩
    rw [heq]
    exact fst.measurable (MeasurableSet.singleton v.fst)

end Val
end ProbLang
end ProbLangMeasures
