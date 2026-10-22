module

public import Metrology.ProbLang.CoreMeasures.Exp
public import Metrology.ProbLang.CoreMeasures.Val
public import Metrology.ProbLang.CoreMeasures.State

@[expose] public section

/-! # σ-algebras on tapes, states and configurations

Tapes are discrete; `State` and `Cfg` are pullbacks of the product σ-algebra of their fields,
with measurability criteria and constructors (`measurable_iff`, `measurable_mk`) for each. -/

noncomputable section
open Classical MeasureTheory

namespace ProbLang

/-! ## Tapes -/

/-- Tapes are countable (a bound and a list of integers), so they carry the discrete σ-algebra. -/
instance instMeasurableSpaceTape : MeasurableSpace Tape := ⊤

instance instMeasurableSingletonClassTape : MeasurableSingletonClass Tape :=
  ⟨fun _ => trivial⟩

variable {α : Type _} [MeasurableSpace α]

/-! ## States -/

/-- The σ-algebra of a state: that of its heap and tapes. -/
instance instMeasurableSpaceState : MeasurableSpace (State α) :=
  MeasurableSpace.comap (fun σ : State α => (σ.heap, σ.tapes)) inferInstance

@[fun_prop]
theorem State.measurable_heap : Measurable (fun σ : State α => σ.heap) :=
  measurable_fst.comp (Measurable.of_comap_le le_rfl)

@[fun_prop]
theorem State.measurable_tapes : Measurable (fun σ : State α => σ.tapes) :=
  measurable_snd.comp (Measurable.of_comap_le le_rfl)

theorem State.measurable_iff {X : Type _} [MeasurableSpace X] {f : X → State α} :
    Measurable f ↔
      Measurable (fun x => (f x).heap) ∧ Measurable (fun x => (f x).tapes) :=
  ⟨fun hf => ⟨State.measurable_heap.comp hf, State.measurable_tapes.comp hf⟩,
   fun ⟨h₁, h₂⟩ => measurable_comap_iff.mpr (h₁.prodMk h₂)⟩

@[fun_prop]
theorem State.measurable_mk :
    Measurable (fun (p : LocHeap (Val α) × LocHeap Tape) => State.mk p.1 p.2) :=
  State.measurable_iff.mpr ⟨measurable_fst, measurable_snd⟩

@[fun_prop]
theorem State.measurable_mk_param {γ : Type _} [MeasurableSpace γ]
    {fh : γ → LocHeap (Val α)} (hh : Measurable fh)
    {ft : γ → LocHeap Tape} (ht : Measurable ft) :
    Measurable (fun q : γ => State.mk (fh q) (ft q)) :=
  State.measurable_iff.mpr ⟨hh, ht⟩

/-! ## Configurations -/

/-- The σ-algebra of a configuration: that of its expression and state. -/
instance instMeasurableSpaceCfg : MeasurableSpace (Cfg α) :=
  MeasurableSpace.comap (fun c : Cfg α => (c.expr, c.state)) inferInstance

@[fun_prop]
theorem Cfg.measurable_expr : Measurable (fun c : Cfg α => c.expr) :=
  measurable_fst.comp (Measurable.of_comap_le le_rfl)

@[fun_prop]
theorem Cfg.measurable_state : Measurable (fun c : Cfg α => c.state) :=
  measurable_snd.comp (Measurable.of_comap_le le_rfl)

theorem Cfg.measurable_iff {X : Type _} [MeasurableSpace X] {f : X → Cfg α} :
    Measurable f ↔
      Measurable (fun x => (f x).expr) ∧ Measurable (fun x => (f x).state) :=
  ⟨fun hf => ⟨Cfg.measurable_expr.comp hf, Cfg.measurable_state.comp hf⟩,
   fun ⟨h₁, h₂⟩ => measurable_comap_iff.mpr (h₁.prodMk h₂)⟩

@[fun_prop]
theorem Cfg.measurable_mk : Measurable (fun (p : Exp α × State α) => Cfg.mk p.1 p.2) :=
  Cfg.measurable_iff.mpr ⟨measurable_fst, measurable_snd⟩

end ProbLang
