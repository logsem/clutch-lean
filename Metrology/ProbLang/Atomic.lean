module

public import Metrology.ProbLang.HeadStep
import Metrology.ProbLang.Syntax.Notation
public import Metrology.ProbLang.CtxStep

@[expose] public section

/-! # Atomic expressions

Redexes whose single step lands on a value, so the program logic may open invariants around them
(`Micrometer.OpenInv.of_atomic`). -/

namespace ProbLang

variable {rT : Type _} [LawfulProbLangℝ rT]

/-- Every atom of the step measure is a value (vacuous for `urand`; the logic uses `Atomic'`). -/
def Atomic (e : Exp rT) : Prop :=
  ∀ σ e' σ', 0 < primStep ⟨e, σ⟩ {⟨e', σ'⟩} → e'.isValue

/-- The step measure is concentrated on value configurations. This is the form the program
logic consumes (`Micrometer.OpenInv.of_atomic`). -/
def Atomic' (e : Exp rT) : Prop :=
  ∀ σ, Concentrated (primStep ⟨e, σ⟩) { ρ | ρ.1.isValue }

namespace Atomic

theorem primStep_eq_headStep_of_decomp_nil
    {e : Exp rT} (hd : e.decompItem = none) (σ : State rT) :
    primStep ⟨e, σ⟩ = headStep ⟨e, σ⟩ := by
  have hde : e.decomp = ([], e) := by
    rw [Exp.decomp_unfold, hd]
  simp only [primStep, hde, Ectx.fillCfg_empty, MeasureTheory.Measure.map_id]

/-- `Atomic` implies `Atomic'` for redexes that are not `urand`; the side condition is discharged
at concrete redexes, where `decomp` reduces, not threaded through the program logic. -/
theorem toAtomic' {e : Exp rT} (h : Atomic e) (hne : e.decomp.2 ≠ .urand) :
    Atomic' e := by
  intro σ
  refine Concentrated.mono ?_ (primStep_atomic e σ hne).concentrated_atoms
  rintro ⟨e', σ'⟩ hpos
  exact h σ e' σ' hpos

private theorem of_headStepSupport {e : Exp rT} (hd : e.decompItem = none)
    (h : ∀ σ e' σ', HeadStepSupport ⟨e, σ⟩ ⟨e', σ'⟩ → e'.isValue) : Atomic e := by
  intro σ e' σ' hpos
  rw [primStep_eq_headStep_of_decomp_nil hd] at hpos
  exact h σ e' σ' (Possible.headStepSupport (possible_iff_pos.mpr hpos))

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

/-! ## `Atomic` for heap and sampling redexes -/

theorem load (l : Loc) : Atomic (rT := rT) pl(!#(.loc l)) :=
  of_headStepSupport rfl fun _ _ _ h => by
    cases h with
    | LoadS _ he' =>
      rename_i v _
      subst he'
      exact v.2.toIsValue

theorem store (l : Loc) (v : Val rT) :
    Atomic (.store pl(#(.loc l)) v.1) :=
  of_headStepSupport (store_decompItem l v) fun _ _ _ h => by
    cases h with
    | StoreS _ _ _ => exact IsVal.lit.toIsValue

theorem alloc (v : Val rT) : Atomic (.alloc v.1) :=
  of_headStepSupport (alloc_decompItem v) fun _ _ _ h => by
    cases h with
    | AllocS _ _ _ => exact IsVal.lit.toIsValue

theorem rand_unit (z : Int) : Atomic (rT := rT) pl(rand(#(.int z), #(.unit))) :=
  of_headStepSupport rfl fun _ _ _ h => by
    cases h with
    | RandNoTapeS _ _ _ => exact IsVal.lit.toIsValue
    | RandNonposS _ => exact IsVal.lit.toIsValue

theorem rand_lbl (z : Int) (l : Loc) :
    Atomic (rT := rT) pl(rand(#(.int z), #(.lbl l))) :=
  of_headStepSupport rfl fun _ _ _ h => by
    cases h <;> exact IsVal.lit.toIsValue

/-! ## `Atomic'` for the redexes the program logic opens invariants around

`decomp.2 ≠ .urand` reduces because each redex is a concrete constructor. -/

theorem load' (l : Loc) : Atomic' (rT := rT) pl(!#(.loc l)) :=
  toAtomic' (load l) (by rw [Exp.decomp_snd_of_decompItem_none rfl]; nofun)

theorem store' (l : Loc) (v : Val rT) : Atomic' (.store pl(#(.loc l)) v.1) :=
  toAtomic' (store l v) (by rw [Exp.decomp_snd_of_decompItem_none (store_decompItem l v)]; nofun)

theorem alloc' (v : Val rT) : Atomic' (.alloc v.1) :=
  toAtomic' (alloc v) (by rw [Exp.decomp_snd_of_decompItem_none (alloc_decompItem v)]; nofun)

theorem rand_unit' (z : Int) : Atomic' (rT := rT) pl(rand(#(.int z), #(.unit))) :=
  toAtomic' (rand_unit z) (by rw [Exp.decomp_snd_of_decompItem_none rfl]; nofun)

theorem rand_lbl' (z : Int) (l : Loc) :
    Atomic' (rT := rT) pl(rand(#(.int z), #(.lbl l))) :=
  toAtomic' (rand_lbl z l) (by rw [Exp.decomp_snd_of_decompItem_none rfl]; nofun)

/-- `urand` steps to a value configuration almost surely. -/
theorem urand' : Atomic' (rT := rT) .urand := by
  intro σ
  have hd : (pl(urand) : Exp rT).decompItem = none := rfl
  rw [primStep_eq_headStep_of_decomp_nil hd]
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
