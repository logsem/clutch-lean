module

public meta import Metrology.Meta.Discrete
public import Metrology.ProbLang.HeadStep
import Metrology.ProbLang.Syntax.Notation
public import Metrology.ProbLang.CtxStep

@[expose] public section

/-! # Atomic expressions

`Atomic` says a redex's one step lands on a value, so the program logic may open invariants
around it (`Micrometer.OpenInv.of_atomic`); proved here for the heap, `rand` and `urand` redexes.
`Discrete.Atomic` is the pointwise form, which says nothing about `urand`. -/

namespace ProbLang

/-! ## The two notions -/

variable {rT : Type _} [LawfulProbLangℝ rT]

/-- The step measure is concentrated on value configurations: the form the program logic
consumes (`Micrometer.OpenInv.of_atomic`), which also covers `urand`. -/
def Atomic (e : Exp rT) : Prop :=
  ∀ σ, Concentrated (primStep ⟨e, σ⟩) { ρ | ρ.1.isValue }

/-- Pointwise form of `Atomic`: every successor of positive mass is a value. -/
@[discrete]
def Discrete.Atomic (e : Exp rT) : Prop :=
  ∀ σ e' σ', 0 < primStep ⟨e, σ⟩ {⟨e', σ'⟩} → e'.isValue

omit [LawfulProbLangℝ rT] in
private theorem store_decompItem (l : Loc) (v : Val rT) :
    (Exp.store pl(#(.loc l)) v.1).decompItem = none := by
  have hv : v.1.toVal? = some v := Exp.toVal?_ofVal v
  show (v.1.toVal?.casesOn _ _ : Option _) = none
  rw [hv]
  rfl

omit [LawfulProbLangℝ rT] in
private theorem alloc_decompItem (v : Val rT) : (Exp.alloc v.1).decompItem = none := by
  have hv : v.1.toVal? = some v := Exp.toVal?_ofVal v
  show (v.1.toVal?.casesOn _ _ : Option _) = none
  rw [hv]

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

@[discrete]
theorem load (l : Loc) : Discrete.Atomic (rT := rT) pl(!#(.loc l)) :=
  of_headStepSupport rfl fun _ _ _ h => by
    cases h with
    | LoadS _ he' =>
      rename_i v _
      subst he'
      exact v.2.toIsValue

@[discrete]
theorem store (l : Loc) (v : Val rT) :
    Discrete.Atomic (.store pl(#(.loc l)) v.1) :=
  of_headStepSupport (store_decompItem l v) fun _ _ _ h => by
    cases h with
    | StoreS _ _ _ => exact IsVal.lit.toIsValue

@[discrete]
theorem alloc (v : Val rT) : Discrete.Atomic (.alloc v.1) :=
  of_headStepSupport (alloc_decompItem v) fun _ _ _ h => by
    cases h with
    | AllocS _ _ _ => exact IsVal.lit.toIsValue

/-- `rand` on the empty tape (`#()`) is atomic. -/
@[discrete]
theorem rand_unit (z : Int) : Discrete.Atomic (rT := rT) pl(rand(#(.int z), #(.unit))) :=
  of_headStepSupport rfl fun _ _ _ h => by
    cases h with
    | RandNoTapeS _ _ _ => exact IsVal.lit.toIsValue
    | RandNonposS _ => exact IsVal.lit.toIsValue

@[discrete]
theorem rand_lbl (z : Int) (l : Loc) :
    Discrete.Atomic (rT := rT) pl(rand(#(.int z), #(.lbl l))) :=
  of_headStepSupport rfl fun _ _ _ h => by
    cases h <;> exact IsVal.lit.toIsValue

end Discrete.Atomic

namespace Atomic

/-! ## `Atomic` for the redexes the program logic opens invariants around

`decomp.2 ≠ .urand` reduces because each redex is a concrete constructor. -/

section
-- these lemmas go through the discrete forms but state the non-discrete `Atomic`
set_option linter.discrete false

theorem load (l : Loc) : Atomic (rT := rT) pl(!#(.loc l)) :=
  (Discrete.Atomic.load l).toAtomic (by rw [Exp.decomp_snd_of_decompItem_none rfl]; nofun)

theorem store (l : Loc) (v : Val rT) : Atomic (.store pl(#(.loc l)) v.1) :=
  (Discrete.Atomic.store l v).toAtomic
    (by rw [Exp.decomp_snd_of_decompItem_none (store_decompItem l v)]; nofun)

theorem alloc (v : Val rT) : Atomic (.alloc v.1) :=
  (Discrete.Atomic.alloc v).toAtomic
    (by rw [Exp.decomp_snd_of_decompItem_none (alloc_decompItem v)]; nofun)

theorem rand_unit (z : Int) : Atomic (rT := rT) pl(rand(#(.int z), #(.unit))) :=
  (Discrete.Atomic.rand_unit z).toAtomic (by rw [Exp.decomp_snd_of_decompItem_none rfl]; nofun)

theorem rand_lbl (z : Int) (l : Loc) :
    Atomic (rT := rT) pl(rand(#(.int z), #(.lbl l))) :=
  (Discrete.Atomic.rand_lbl z l).toAtomic (by rw [Exp.decomp_snd_of_decompItem_none rfl]; nofun)

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
  exact IsVal.lit.toIsValue

end Atomic

end ProbLang
