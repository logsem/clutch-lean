module

public meta import Metrology.Meta.Discrete
public import Metrology.ProbLang.HeadStep
import Metrology.ProbLang.Syntax.Notation
public import Metrology.ProbLang.CtxStep

@[expose] public section

/-! # Atomic expressions

`Atomic e` says one step of `e` lands on a value; `Discrete.Atomic` is its pointwise form. -/

namespace ProbLang

open Exp (toVal?_ofVal decomp_snd_of_decompItem_none)
open IsVal (lit)

/-! ## The two notions -/

variable {rT : Type _} (z : Int) (l : Loc) (v : Val rT)

/-- The decomposition of a store of a value is `none`. -/
private theorem store_decompItem :
    (Exp.store pl(#loc l) v.1).decompItem = none := by
  have hv : v.1.toVal? = some v := toVal?_ofVal v
  show (v.1.toVal?.casesOn _ _ : Option _) = none
  rw [hv]
  rfl

/-- The decomposition of an allocation of a value is `none`. -/
private theorem alloc_decompItem : (Exp.alloc v.1).decompItem = none := by
  have hv : v.1.toVal? = some v := toVal?_ofVal v
  show (v.1.toVal?.casesOn _ _ : Option _) = none
  rw [hv]

/-- Block allocation of a value has no evaluation-context hole. -/
private theorem allocN_decompItem : (Exp.allocN pl(#z) v.1).decompItem = none := by
  have hv : v.1.toVal? = some v := toVal?_ofVal v
  show (v.1.toVal?.casesOn _ _ : Option _) = none
  rw [hv]
  rfl

variable [MeasurableSpace rT] [LawfulProbLangℝ rT]

/-- The step measure is concentrated on value configurations, which also covers `urand`. -/
def Atomic (e : Exp rT) : Prop :=
  ∀ σ, Concentrated (primStep ⟨e, σ⟩) { ρ | ρ.1.isValue }

/-- Pointwise form of `Atomic`: every successor of positive mass is a value. -/
@[discrete]
def Discrete.Atomic (e : Exp rT) : Prop :=
  ∀ σ e' σ', 0 < primStep ⟨e, σ⟩ {⟨e', σ'⟩} → e'.isValue

namespace Discrete.Atomic

/-- `Discrete.Atomic` implies `Atomic` for redexes that are not `urand`; the side condition holds
by computation at concrete redexes. -/
@[discrete]
theorem toAtomic {e : Exp rT} (h : Discrete.Atomic e) (hne : e.decomp.2 ≠ .urand) :
    _root_.ProbLang.Atomic e := by
  intro σ
  refine Concentrated.mono ?_ (primStep_atomic e σ hne).concentrated_atoms
  rintro ⟨e', σ'⟩ hpos
  exact h σ e' σ' hpos

/-- To show `Discrete.Atomic` for a head redex, check every `HeadStepSupport` successor is a
value. -/
@[discrete]
private theorem of_headStepSupport {e : Exp rT} (hd : e.decompItem = none)
    (h : ∀ σ e' σ', HeadStepSupport ⟨e, σ⟩ ⟨e', σ'⟩ → e'.isValue) : Discrete.Atomic e := by
  intro σ e' σ' hpos
  rw [primStep_eq_headStep hd] at hpos
  exact h σ e' σ' (Possible.headStepSupport (possible_iff_pos.mpr hpos))

/-! ## `Discrete.Atomic` for heap and sampling redexes -/

/-- A load is discretely atomic. -/
@[discrete]
theorem load : Discrete.Atomic (rT := rT) pl(!#loc l) :=
  of_headStepSupport rfl fun _ _ _ h => by
    cases h with
    | LoadS _ he' =>
      rename_i v _
      subst he'
      exact v.2.toIsValue

/-- A store of a value is discretely atomic. -/
@[discrete]
theorem store :
    Discrete.Atomic (.store pl(#loc l) v.1) :=
  of_headStepSupport (store_decompItem l v) fun _ _ _ h => by
    cases h with
    | StoreS _ _ _ => exact lit.toIsValue

/-- An allocation of a value is discretely atomic. -/
@[discrete]
theorem alloc : Discrete.Atomic (.alloc v.1) :=
  of_headStepSupport (alloc_decompItem v) fun _ _ _ h => by
    cases h with
    | AllocS _ _ _ => exact lit.toIsValue

/-- Block allocation of a value is discretely atomic. -/
@[discrete]
theorem allocN : Discrete.Atomic (.allocN pl(#z) v.1) :=
  of_headStepSupport (allocN_decompItem z v) fun _ _ _ h => by
    cases h with
    | AllocNS _ _ _ _ => exact lit.toIsValue

/-- `rand` on the empty tape (`#()`) is discretely atomic. -/
@[discrete]
theorem rand_unit : Discrete.Atomic (rT := rT) pl(rand(#z, #())) :=
  of_headStepSupport rfl fun _ _ _ h => by
    cases h with
    | RandNoTapeS _ _ _ => exact lit.toIsValue
    | RandNonposS _ => exact lit.toIsValue

/-- `rand` on a labelled tape is discretely atomic. -/
@[discrete]
theorem rand_lbl :
    Discrete.Atomic (rT := rT) pl(rand(#z, #lbl l)) :=
  of_headStepSupport rfl fun _ _ _ h => by
    cases h <;> exact lit.toIsValue

end Discrete.Atomic

namespace Atomic

/-! ## `Atomic` for the redexes the program logic opens invariants around

`decomp.2 ≠ .urand` reduces because each redex is a concrete constructor. -/

section
-- these lemmas go through the discrete forms but state the non-discrete `Atomic`
set_option linter.discrete false

/-- A load is atomic. -/
theorem load : Atomic (rT := rT) pl(!#loc l) :=
  (Discrete.Atomic.load l).toAtomic (by rw [decomp_snd_of_decompItem_none rfl]; nofun)

/-- A store of a value is atomic. -/
theorem store : Atomic (.store pl(#loc l) v.1) :=
  (Discrete.Atomic.store l v).toAtomic
    (by rw [decomp_snd_of_decompItem_none (store_decompItem l v)]; nofun)

/-- An allocation of a value is atomic. -/
theorem alloc : Atomic (.alloc v.1) :=
  (Discrete.Atomic.alloc v).toAtomic
    (by rw [decomp_snd_of_decompItem_none (alloc_decompItem v)]; nofun)

/-- Block allocation of a value is atomic. -/
theorem allocN : Atomic (.allocN pl(#z) v.1) :=
  (Discrete.Atomic.allocN z v).toAtomic
    (by rw [decomp_snd_of_decompItem_none (allocN_decompItem z v)]; nofun)

/-- `rand` on the empty tape (`#()`) is atomic. -/
theorem rand_unit : Atomic (rT := rT) pl(rand(#z, #())) :=
  (Discrete.Atomic.rand_unit z).toAtomic (by rw [decomp_snd_of_decompItem_none rfl]; nofun)

/-- `rand` on a labelled tape is atomic. -/
theorem rand_lbl :
    Atomic (rT := rT) pl(rand(#z, #lbl l)) :=
  (Discrete.Atomic.rand_lbl z l).toAtomic (by rw [decomp_snd_of_decompItem_none rfl]; nofun)

end

/-- `urand` steps to a value almost surely: the preimage of a non-value under the uniform draw is
empty. -/
theorem «urand» : Atomic (rT := rT) .urand := by
  intro σ
  have hd : (pl(urand) : Exp rT).decompItem = none := rfl
  rw [primStep_eq_headStep hd]
  show (Cfg.uniformReal σ) {ρ : Cfg rT | ρ.1.isValue}ᶜ = 0
  rw [Cfg.uniformReal,
    MeasureTheory.Measure.map_apply (by fun_prop) Cfg.isValue_measurableSet.compl]
  convert MeasureTheory.measure_empty (μ := LawfulProbLangℝ.unifUnit)
  ext r
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
    iff_false, not_not]
  exact lit.toIsValue

end Atomic

end ProbLang
