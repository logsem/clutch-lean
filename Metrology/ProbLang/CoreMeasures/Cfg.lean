module

public import Metrology.ProbLang.CoreMeasures.Exp
public import Metrology.ProbLang.CoreMeasures.Val
public import Metrology.ProbLang.CoreMeasures.Recurrences
public import Metrology.ProbLang.CoreMeasures.State

@[expose] public section

/-! # σ-algebras on tapes, states and configurations

Tapes are discrete; `State` and `Cfg` carry the pullback of the product σ-algebra of their
fields. -/

noncomputable section
open MeasureTheory Measurable

namespace ProbLang

open Val

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

/-- The heap of a state is measurable. -/
@[fun_prop]
theorem measurable_heap : Measurable (fun σ : State α => σ.heap) :=
  measurable_fst.comp (of_comap_le le_rfl)

/-- The tapes of a state are measurable. -/
@[fun_prop]
theorem measurable_tapes : Measurable (fun σ : State α => σ.tapes) :=
  measurable_snd.comp (of_comap_le le_rfl)

/-- A map into states is measurable iff its heaps and tapes are. -/
theorem measurable_iff {f : X → State α} :
    Measurable f ↔ Measurable (fun x => (f x).heap) ∧ Measurable (fun x => (f x).tapes) :=
  ⟨fun hf => ⟨measurable_heap.comp hf, measurable_tapes.comp hf⟩,
   fun ⟨h₁, h₂⟩ => measurable_comap_iff.mpr (h₁.prodMk h₂)⟩

/-- The state constructor is measurable in its heap and tape parts. -/
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

/-- The expression of a configuration is measurable. -/
@[fun_prop]
theorem measurable_expr : Measurable (fun c : Cfg α => c.expr) :=
  measurable_fst.comp (of_comap_le le_rfl)

/-- The state of a configuration is measurable. -/
@[fun_prop]
theorem measurable_state : Measurable (fun c : Cfg α => c.state) :=
  measurable_snd.comp (of_comap_le le_rfl)

/-- A map into configurations is measurable iff its expressions and states are. -/
theorem measurable_iff {f : X → Cfg α} :
    Measurable f ↔ Measurable (fun x => (f x).expr) ∧ Measurable (fun x => (f x).state) :=
  ⟨fun hf => ⟨measurable_expr.comp hf, measurable_state.comp hf⟩,
   fun ⟨h₁, h₂⟩ => measurable_comap_iff.mpr (h₁.prodMk h₂)⟩

/-- The configuration constructor is measurable in its expression and state. -/
@[fun_prop]
theorem measurable_mk : Measurable (fun (p : Exp α × State α) => mk p.1 p.2) :=
  measurable_iff.mpr ⟨measurable_fst, measurable_snd⟩

end Cfg

/-! ## Values inside expressions and configurations -/

/-- `Exp.ofVal` is a measurable embedding of values into expressions. -/
theorem measurableEmbedding_ofVal {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT] :
    MeasurableEmbedding (Exp.ofVal : Val rT → Exp rT) := by
  refine ⟨fun a b h => Val.ext h, Exp.ofVal.measurable, fun s hs => ?_⟩
  obtain ⟨U, hU, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have hrange : Set.range (fst : Val rT → Exp rT) = {e : Exp rT | e.isValue} := by
    ext e
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨v, rfl⟩; exact Val.isValue v
    · intro h; exact ⟨Val.mk e h.some h.some.lc, rfl⟩
  show MeasurableSet (fst '' (fst ⁻¹' U))
  rw [Set.image_preimage_eq_inter_range, hrange]
  have hsplit : {e : Exp rT | e.isValue} = {e | e.isValueR} ∩ {e | Exp.lcb 0 e = true} := by
    ext e; simp [Exp.isValue_iff_isValueR, Set.mem_inter_iff]
  rw [hsplit]
  exact hU.inter (Exp.isValueR.measurable.setOf.inter Exp.lcb_zero.measurableSet)

/-- The set of expressions that are values satisfying `φ` is measurable. -/
theorem measurableSet_ofValSet {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
    {φ : Val rT → Prop}
    (hφ : MeasurableSet {v : Val rT | φ v}) :
    MeasurableSet {e : Exp rT | ∃ v, e = Exp.ofVal v ∧ φ v} := by
  have heq : {e : Exp rT | ∃ v, e = Exp.ofVal v ∧ φ v} = Exp.ofVal '' {v | φ v} := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    exact ⟨fun ⟨v, he, hv⟩ => ⟨v, hv, he.symm⟩, fun ⟨v, hv, he⟩ => ⟨v, he.symm, hv⟩⟩
  rw [heq]
  exact measurableEmbedding_ofVal.measurableSet_image' hφ

/-- The set of configurations whose expression is a value satisfying `φ` is measurable. -/
theorem measurableSet_TglCfgSet {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
    {φ : Val rT → Prop}
    (hφ : MeasurableSet {v : Val rT | φ v}) :
    MeasurableSet {ρ : Cfg rT | ∃ v, ρ.expr = Exp.ofVal v ∧ φ v} :=
  (measurableSet_ofValSet hφ).preimage Cfg.measurable_expr

end ProbLang
