module

public import Metrology.ProbLang.CoreMeasures.Exp
public import Metrology.ProbLang.CoreMeasures.Val
public import Metrology.ProbLang.CoreMeasures.Recurrences
public import Metrology.ProbLang.CoreMeasures.State

@[expose] public section

/-! # σ-algebras on tapes, random variables, states and configurations

Each type carries the product σ-algebra of its fields; a tape's contents carry the product
σ-algebra over their positions. -/

noncomputable section
open MeasureTheory Measurable

namespace ProbLang

open Val

variable {α X : Type _}

/-! ## Tapes -/

namespace Tape

/-- The fields of a tape, as a tuple. -/
def toTuple (t : Tape α) : ℕ × Val α × (ℕ → Option (Val α)) :=
  (t.name, t.arg, t.presamples)

/-- A tape is determined by its fields. -/
theorem toTuple_injective : Function.Injective (toTuple : Tape α → _) := by
  rintro ⟨n, v, f⟩ ⟨n', v', f'⟩ h
  simp only [toTuple, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  rfl

end Tape

variable [MeasurableSpace α] [MeasurableSpace X]

/-- A tape carries the product σ-algebra of its family and contents. -/
instance instMeasurableSpaceTape : MeasurableSpace (Tape α) :=
  MeasurableSpace.comap Tape.toTuple inferInstance

namespace Tape

/-- The fields of a tape are jointly measurable. -/
@[fun_prop]
theorem measurable_toTuple : Measurable (toTuple : Tape α → _) :=
  of_comap_le le_rfl

/-- The family name of a tape is measurable. -/
@[fun_prop]
theorem measurable_name : Measurable (fun t : Tape α => t.name) :=
  measurable_fst.comp measurable_toTuple

/-- The family argument of a tape is measurable. -/
@[fun_prop]
theorem measurable_arg : Measurable (fun t : Tape α => t.arg) :=
  measurable_fst.comp (measurable_snd.comp measurable_toTuple)

/-- The contents of a tape are measurable. -/
@[fun_prop]
theorem measurable_presamples : Measurable (fun t : Tape α => t.presamples) :=
  measurable_snd.comp (measurable_snd.comp measurable_toTuple)

/-- Each position of a tape is measurable. -/
@[fun_prop]
theorem measurable_presamples_apply (k : ℕ) :
    Measurable (fun t : Tape α => t.presamples k) :=
  (measurable_pi_apply k).comp measurable_presamples

/-- The first position of a tape is measurable. -/
@[fun_prop]
theorem measurable_head? : Measurable (head? : Tape α → Option (Val α)) :=
  measurable_presamples_apply 0

/-- A map into tapes is measurable iff each field is. -/
theorem measurable_iff {f : X → Tape α} :
    Measurable f ↔ Measurable (fun x => (f x).name) ∧ Measurable (fun x => (f x).arg) ∧
      Measurable (fun x => (f x).presamples) :=
  ⟨fun hf => ⟨measurable_name.comp hf, measurable_arg.comp hf, measurable_presamples.comp hf⟩,
   fun ⟨h₁, h₂, h₃⟩ => measurable_comap_iff.mpr (h₁.prodMk (h₂.prodMk h₃))⟩

/-- The tape constructor is measurable in its fields. -/
@[fun_prop]
theorem measurable_mk_param {fn : X → ℕ} (hn : Measurable fn) {fa : X → Val α}
    (ha : Measurable fa) {fp : X → ℕ → Option (Val α)} (hp : Measurable fp) :
    Measurable (fun x => mk (fn x) (fa x) (fp x)) :=
  measurable_iff.mpr ⟨hn, ha, hp⟩

/-- Empty-tape construction is jointly measurable in the family. -/
@[fun_prop]
theorem measurable_empty : Measurable (fun p : ℕ × Val α => empty p.1 p.2) :=
  measurable_iff.mpr ⟨measurable_fst, measurable_snd, measurable_const⟩

/-- Consuming the first position of a tape is measurable. -/
@[fun_prop]
theorem measurable_shift : Measurable (shift : Tape α → Tape α) :=
  measurable_iff.mpr ⟨measurable_name, measurable_arg,
    Measurable.of_eval fun k => measurable_presamples_apply (k + 1)⟩

/-- Filling a fixed position is jointly measurable in the tape and value. -/
@[fun_prop]
theorem measurable_fillAt (k : ℕ) :
    Measurable (fun p : Tape α × Val α => p.1.fillAt k p.2) := by
  refine (measurable_iff (f := fun p : Tape α × Val α => p.1.fillAt k p.2)).mpr
    ⟨?_, ?_, ?_⟩
  · change Measurable fun p : Tape α × Val α => p.1.name
    exact measurable_name.comp measurable_fst
  · change Measurable fun p : Tape α × Val α => p.1.arg
    exact measurable_arg.comp measurable_fst
  · change Measurable fun p : Tape α × Val α =>
      Function.update p.1.presamples k (some ((p.1.presamples k).getD p.2))
    exact measurable_update'.comp ((measurable_presamples.comp measurable_fst).prodMk
      (measurable_some.comp (Option.measurable_getD_uncurry.comp
        ((measurable_presamples_apply k |>.comp measurable_fst).prodMk measurable_snd))))

/-- Filling every empty position is jointly measurable in the tape and filling stream. -/
@[fun_prop]
theorem measurable_fillAll :
    Measurable (fun p : Tape α × (ℕ → Val α) => p.1.fillAll p.2) := by
  refine (measurable_iff (f := fun p : Tape α × (ℕ → Val α) => p.1.fillAll p.2)).mpr
    ⟨?_, ?_, ?_⟩
  · change Measurable fun p : Tape α × (ℕ → Val α) => p.1.name
    exact measurable_name.comp measurable_fst
  · change Measurable fun p : Tape α × (ℕ → Val α) => p.1.arg
    exact measurable_arg.comp measurable_fst
  · change Measurable fun p : Tape α × (ℕ → Val α) => Presamples.fillAll p.1.presamples p.2
    apply Measurable.of_eval
    intro k
    exact measurable_some.comp (Option.measurable_getD_uncurry.comp
      ((measurable_presamples_apply k |>.comp measurable_fst).prodMk
        (measurable_pi_apply k |>.comp measurable_snd)))

end Tape

/-! ## Random variables -/

namespace RvCell

/-- The fields of a random variable, as a tuple. -/
def toTuple (c : RvCell α) : ℕ × Val α × List (ℕ × Val α × Int) × Option (Val α) :=
  (c.prior, c.arg, c.obs, c.world)

/-- A random variable carries the σ-algebra of its fields. -/
instance instMeasurableSpace : MeasurableSpace (RvCell α) :=
  MeasurableSpace.comap toTuple inferInstance

/-- `toTuple` is measurable. -/
@[fun_prop]
theorem measurable_toTuple : Measurable (toTuple : RvCell α → _) :=
  of_comap_le le_rfl

/-- The prior name of a random variable is measurable. -/
@[fun_prop]
theorem measurable_prior : Measurable (fun c : RvCell α => c.prior) :=
  measurable_fst.comp measurable_toTuple

/-- The prior argument of a random variable is measurable. -/
@[fun_prop]
theorem measurable_arg : Measurable (fun c : RvCell α => c.arg) :=
  measurable_fst.comp (measurable_snd.comp measurable_toTuple)

/-- The observations of a random variable are measurable. -/
@[fun_prop]
theorem measurable_obs : Measurable (fun c : RvCell α => c.obs) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_toTuple))

/-- The resolved value of a random variable is measurable. -/
@[fun_prop]
theorem measurable_world : Measurable (fun c : RvCell α => c.world) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_toTuple))

/-- A map into random variables is measurable iff each of its fields is. -/
theorem measurable_iff {f : X → RvCell α} :
    Measurable f ↔ Measurable (fun x => (f x).prior) ∧ Measurable (fun x => (f x).arg) ∧
      Measurable (fun x => (f x).obs) ∧ Measurable (fun x => (f x).world) :=
  ⟨fun hf => ⟨measurable_prior.comp hf, measurable_arg.comp hf, measurable_obs.comp hf,
      measurable_world.comp hf⟩,
    fun ⟨h₁, h₂, h₃, h₄⟩ => measurable_comap_iff.mpr (h₁.prodMk (h₂.prodMk (h₃.prodMk h₄)))⟩

/-- Resolving to a value is measurable in the value. -/
theorem measurable_resolveTo (c : RvCell α) : Measurable c.resolveTo :=
  measurable_iff.mpr ⟨measurable_const, measurable_const, measurable_const,
    MeasurableEmbedding.some_mk.measurable⟩

/-- Observing is measurable in the observed value. -/
theorem measurable_observe (c : RvCell α) (k : ℕ) (a : Val α) :
    Measurable (fun y : Int => c.observe k a y) :=
  .of_discrete

/-- A fresh random variable is measurable in its prior name and argument. -/
theorem measurable_fresh : Measurable (fun p : ℕ × Val α => RvCell.fresh p.1 p.2) := by
  refine measurable_iff.mpr ⟨?_, ?_, measurable_const, measurable_const⟩
  · exact measurable_fst
  · exact measurable_snd

/-- Resolving is jointly measurable in the random variable and the value. -/
theorem measurable_resolveTo_uncurry :
    Measurable (fun p : RvCell α × Val α => p.1.resolveTo p.2) := by
  refine measurable_iff.mpr ⟨?_, ?_, ?_, ?_⟩
  · show Measurable fun p : RvCell α × Val α => p.1.prior
    exact measurable_prior.comp measurable_fst
  · show Measurable fun p : RvCell α × Val α => p.1.arg
    exact measurable_arg.comp measurable_fst
  · show Measurable fun p : RvCell α × Val α => p.1.obs
    exact measurable_obs.comp measurable_fst
  · show Measurable fun p : RvCell α × Val α => some p.2
    exact MeasurableEmbedding.some_mk.measurable.comp measurable_snd

/-- Observing is jointly measurable in the random variable and the observation. -/
theorem measurable_observe_uncurry :
    Measurable (fun p : RvCell α × (ℕ × Val α × Int) => p.1.observe p.2.1 p.2.2.1 p.2.2.2) := by
  refine measurable_iff.mpr ⟨?_, ?_, ?_, ?_⟩
  · show Measurable fun p : RvCell α × (ℕ × Val α × Int) => p.1.prior
    exact measurable_prior.comp measurable_fst
  · show Measurable fun p : RvCell α × (ℕ × Val α × Int) => p.1.arg
    exact measurable_arg.comp measurable_fst
  · show Measurable fun p : RvCell α × (ℕ × Val α × Int) => p.1.obs ++ [p.2]
    exact List.measurable_append_singleton.comp ((measurable_obs.comp measurable_fst).prodMk
      measurable_snd)
  · show Measurable fun p : RvCell α × (ℕ × Val α × Int) => p.1.world
    exact measurable_world.comp measurable_fst

end RvCell

/-! ## States -/

/-- The σ-algebra of a state is the product σ-algebra of its fields. -/
instance instMeasurableSpaceState : MeasurableSpace (State α) :=
  MeasurableSpace.comap (fun σ : State α => (σ.heap, σ.tapes, σ.rvs)) inferInstance

namespace State

/-- The heap of a state is measurable. -/
@[fun_prop]
theorem measurable_heap : Measurable (fun σ : State α => σ.heap) :=
  measurable_fst.comp (of_comap_le le_rfl)

/-- The tapes of a state are measurable. -/
@[fun_prop]
theorem measurable_tapes : Measurable (fun σ : State α => σ.tapes) :=
  measurable_fst.comp (measurable_snd.comp (of_comap_le le_rfl))

/-- The random variables of a state are measurable. -/
@[fun_prop]
theorem measurable_rvs : Measurable (fun σ : State α => σ.rvs) :=
  measurable_snd.comp (measurable_snd.comp (of_comap_le le_rfl))

/-- A map into states is measurable iff its heaps, tapes and random variables are. -/
theorem measurable_iff {f : X → State α} :
    Measurable f ↔ Measurable (fun x => (f x).heap) ∧ Measurable (fun x => (f x).tapes) ∧
      Measurable (fun x => (f x).rvs) :=
  ⟨fun hf => ⟨measurable_heap.comp hf, measurable_tapes.comp hf, measurable_rvs.comp hf⟩,
    fun ⟨h₁, h₂, h₃⟩ => measurable_comap_iff.mpr (h₁.prodMk (h₂.prodMk h₃))⟩

/-- The state constructor is measurable in its three parts. -/
@[fun_prop]
theorem measurable_mk :
    Measurable (fun (p : LocHeap (Val α) × LocHeap (Tape α) × LocHeap (RvCell α)) =>
      mk p.1 p.2.1 p.2.2) :=
  measurable_iff.mpr ⟨measurable_fst, measurable_fst.comp measurable_snd,
    measurable_snd.comp measurable_snd⟩

@[fun_prop]
theorem measurable_mk_param {γ : Type _} [MeasurableSpace γ]
    {fh : γ → LocHeap (Val α)} (hh : Measurable fh)
    {ft : γ → LocHeap (Tape α)} (ht : Measurable ft)
    {fr : γ → LocHeap (RvCell α)} (hr : Measurable fr := by fun_prop) :
    Measurable (fun q : γ => mk (fh q) (ft q) (fr q)) :=
  measurable_iff.mpr ⟨hh, ht, hr⟩

/-- Writing a fixed tape at a fixed label is measurable. -/
@[fun_prop]
theorem measurable_updateTapes_insert (ℓ : Loc) (t : Tape α) :
    Measurable (fun σ : State α => σ.updateTapes (·.insert ℓ t)) :=
  measurable_mk_param measurable_heap
    ((Measurable.locHeap_insert ℓ).comp (measurable_tapes.prodMk measurable_const))
    measurable_rvs

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

/-- Applying a measurable map to the state of a configuration is measurable. -/
@[fun_prop]
theorem measurable_mapState {f : State α → State α} (hf : Measurable f) :
    Measurable (fun ρ : Cfg α => (⟨ρ.expr, f ρ.state⟩ : Cfg α)) :=
  measurable_iff.mpr ⟨measurable_expr, hf.comp measurable_state⟩

end Cfg

/-! ## Values inside expressions and configurations -/

/-- `Exp.ofVal` is a measurable embedding of values into expressions. -/
theorem measurableEmbedding_ofVal {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT] :
    MeasurableEmbedding (Exp.ofVal : Val rT → Exp rT) := by
  refine ⟨fun a b h => ext h, Exp.ofVal.measurable, fun s hs => ?_⟩
  obtain ⟨U, hU, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have hrange : Set.range (fst : Val rT → Exp rT) = {e : Exp rT | e.isValue} := by
    ext e
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨v, rfl⟩; exact isValue v
    · intro h; exact ⟨mk e h.some h.some.lc, rfl⟩
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
