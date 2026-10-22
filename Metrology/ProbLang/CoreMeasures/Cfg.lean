module

public import Metrology.ProbLang.CoreMeasures.Exp
public import Metrology.ProbLang.CoreMeasures.Val
public import Metrology.ProbLang.CoreMeasures.State

@[expose] public section

/-! # σ-algebras on tapes, states and configurations

Tapes are discrete; `State` and `Cfg` are pullbacks of the product σ-algebra of their fields,
with measurability criteria and constructors (`measurable_iff`, `measurable_mk`) for each. -/

noncomputable section
open MeasureTheory

namespace ProbLang

/-! ## Tapes -/

/-- Tapes carry the discrete σ-algebra (they are countable). -/
instance instMeasurableSpaceTape : MeasurableSpace Tape := ⊤

/-- Singletons of tapes are measurable. -/
instance instMeasurableSingletonClassTape : MeasurableSingletonClass Tape :=
  ⟨fun _ => trivial⟩

variable {α : Type _} [MeasurableSpace α] {X : Type _} [MeasurableSpace X]

/-! ## States -/

/-- The σ-algebra of a state: that of its heap and tapes. -/
instance instMeasurableSpaceState : MeasurableSpace (State α) :=
  MeasurableSpace.comap (fun σ : State α => (σ.heap, σ.tapes)) inferInstance

namespace State

@[fun_prop]
theorem measurable_heap : Measurable (fun σ : State α => σ.heap) :=
  measurable_fst.comp (Measurable.of_comap_le le_rfl)

@[fun_prop]
theorem measurable_tapes : Measurable (fun σ : State α => σ.tapes) :=
  measurable_snd.comp (Measurable.of_comap_le le_rfl)

theorem measurable_iff {f : X → State α} :
    Measurable f ↔ Measurable (fun x => (f x).heap) ∧ Measurable (fun x => (f x).tapes) :=
  ⟨fun hf => ⟨measurable_heap.comp hf, measurable_tapes.comp hf⟩,
   fun ⟨h₁, h₂⟩ => measurable_comap_iff.mpr (h₁.prodMk h₂)⟩

@[fun_prop]
theorem measurable_mk :
    Measurable (fun (p : LocHeap (Val α) × LocHeap Tape) => mk p.1 p.2) :=
  measurable_iff.mpr ⟨measurable_fst, measurable_snd⟩

@[fun_prop]
theorem measurable_mk_param {γ : Type _} [MeasurableSpace γ]
    {fh : γ → LocHeap (Val α)} (hh : Measurable fh)
    {ft : γ → LocHeap Tape} (ht : Measurable ft) :
    Measurable (fun q : γ => mk (fh q) (ft q)) :=
  measurable_iff.mpr ⟨hh, ht⟩

end State

/-! ## Configurations -/

/-- The σ-algebra of a configuration: that of its expression and state. -/
instance instMeasurableSpaceCfg : MeasurableSpace (Cfg α) :=
  MeasurableSpace.comap (fun c : Cfg α => (c.expr, c.state)) inferInstance

namespace Cfg

@[fun_prop]
theorem measurable_expr : Measurable (fun c : Cfg α => c.expr) :=
  measurable_fst.comp (Measurable.of_comap_le le_rfl)

@[fun_prop]
theorem measurable_state : Measurable (fun c : Cfg α => c.state) :=
  measurable_snd.comp (Measurable.of_comap_le le_rfl)

theorem measurable_iff {f : X → Cfg α} :
    Measurable f ↔ Measurable (fun x => (f x).expr) ∧ Measurable (fun x => (f x).state) :=
  ⟨fun hf => ⟨measurable_expr.comp hf, measurable_state.comp hf⟩,
   fun ⟨h₁, h₂⟩ => measurable_comap_iff.mpr (h₁.prodMk h₂)⟩

@[fun_prop]
theorem measurable_mk : Measurable (fun (p : Exp α × State α) => mk p.1 p.2) :=
  measurable_iff.mpr ⟨measurable_fst, measurable_snd⟩

end Cfg

end ProbLang
