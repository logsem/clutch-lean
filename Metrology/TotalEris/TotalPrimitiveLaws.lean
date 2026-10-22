module

public import Metrology.TotalEris.ErisGS
import Metrology.ProbLang.Syntax.Notation
public import Metrology.TotalEris.TotalLifting

@[expose] public section

/-!
# Total-correctness primitive WP laws
-/

open Iris Iris.Std Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS

namespace ProbLang

variable {rT : Type _}

macro "solve_not_value" : term =>
  `(Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w)

namespace TotalEris

section Lifting

variable {hlc : HasLC} {GF : BundledGFunctors} [LawfulProbLangℝ rT] [ErisGS rT hlc GF]

/-! ## Heap operations -/

theorem twp_alloc {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    iprop(∀ l, appHeapFrag l v -∗ Φ (.loc l))
      ⊢ tglWp E (.alloc (.ofVal v)) Φ := by
  iintro HΦ
  iapply twp_lift_atomic_head_step solve_not_value (by is_lc)
  iintro %σ₁ Hσ !>
  have hred : HeadReducible (.alloc (.ofVal v)) σ₁ :=
    (HeadStepSupport.AllocS (Exp.toVal?_ofVal v) rfl rfl).ne_zero
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases Possible.headStepSupport Hstep with
  | AllocS hvd hl hσ =>
    rw [Exp.toVal?_ofVal] at hvd
    cases hvd
    subst hl hσ
    imod app_state_heap_alloc v $$ Hσ with ⟨Hσ', Hl⟩
    imodintro
    isimp only [erisWpGS_stateInterp_eq, Std.ExtTreeMap.insert_eq_PartialMap_insert, Exp.toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ %σ₁.heap.fresh Hl

theorem twp_load {E : CoPset} {l : Loc} {v : Val rT} {Φ : Val rT → IProp GF} :
    iprop(l ↦ v ∗ (l ↦ v -∗ Φ v)) ⊢ tglWp E pl(!#loc l) Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply twp_lift_atomic_head_step solve_not_value (by is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_heap $$ Hσ Hl
  have hred : HeadReducible pl(!#loc l) σ₁ :=
    (HeadStepSupport.LoadS hlook rfl).ne_zero
  imodintro
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases Possible.headStepSupport Hstep with
  | LoadS hlook' hofv =>
    rw [hlook] at hlook'
    cases hlook'
    subst hofv
    imodintro
    isimp only [erisWpGS_stateInterp_eq, Exp.toVal?_ofVal]
    iframe Hσ
    iapply HΦ $$ Hl

theorem twp_store {E : CoPset} {l : Loc} {v v' : Val rT} {Φ : Val rT → IProp GF} :
    iprop(l ↦ v' ∗ (l ↦ v -∗ Φ .unit))
      ⊢ tglWp E (.store pl(#loc l) (.ofVal v)) Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply twp_lift_atomic_head_step solve_not_value (by is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_heap $$ Hσ Hl
  have hred : HeadReducible (.store pl(#loc l) (.ofVal v)) σ₁ :=
    (HeadStepSupport.StoreS (Exp.toVal?_ofVal v)
      (by rw [hlook]; exact Option.isSome_some) rfl).ne_zero
  imodintro
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases Possible.headStepSupport Hstep with
  | StoreS hvd _ hσ =>
    rw [Exp.toVal?_ofVal] at hvd
    cases hvd
    subst hσ
    imod app_state_update_heap $$ Hσ Hl with ⟨Hσ', Hl'⟩
    imodintro
    isimp only [erisWpGS_stateInterp_eq, Std.ExtTreeMap.insert_eq_PartialMap_insert, Exp.toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ Hl'

/-! ## Tape operations -/

theorem twp_alloctape {E : CoPset} {z : Int} {Φ : Val rT → IProp GF} :
    iprop(∀ l, l ↪ₐ Tape.empty z -∗ Φ (.lbl l))
      ⊢ tglWp E pl(tape(#z)) Φ := by
  iintro HΦ
  iapply twp_lift_atomic_head_step solve_not_value (by is_lc)
  iintro %σ₁ Hσ !>
  have hred : HeadReducible pl(tape(#z)) σ₁ :=
    (HeadStepSupport.TapeS (ℓ := σ₁.tapes.fresh) rfl rfl).ne_zero
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases Possible.headStepSupport Hstep with
  | TapeS hl hσ =>
    subst hl hσ
    imod app_state_tape_alloc (Tape.empty z) $$ Hσ with ⟨Hσ', Hl⟩
    imodintro
    isimp only [erisWpGS_stateInterp_eq, Std.ExtTreeMap.insert_eq_PartialMap_insert, Exp.toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ %σ₁.tapes.fresh Hl

/-! ## Random sampling -/

theorem twp_rand {E : CoPset} {z : Int} {Φ : Val rT → IProp GF} (Hz : 0 < z) :
    iprop(∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n))
      ⊢ tglWp E pl(rand(#z, #())) Φ := by
  iintro HΦ
  iapply twp_lift_atomic_head_step solve_not_value (by is_lc)
  iintro %σ₁ Hσ !>
  have hred : HeadReducible pl(rand(#z, #())) σ₁ :=
    (HeadStepSupport.RandNoTapeS Hz (le_refl _) Hz).ne_zero
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases Possible.headStepSupport Hstep with
  | RandNoTapeS _ Hv0 Hvz =>
    imodintro
    isimp only [erisWpGS_stateInterp_eq, Exp.toVal?_lit]
    iframe Hσ
    iapply HΦ
    ipureintro; exact ⟨Hv0, Hvz⟩
  | RandNonposS hnz => exact absurd Hz hnz

theorem twp_rand_tape {E : CoPset} {l : Loc} {z : Int} {n : { z' : Int // 0 ≤ z' ∧ z' < z }}
    {ns : List { z' : Int // 0 ≤ z' ∧ z' < z }} {Φ : Val rT → IProp GF} :
    iprop(l ↪ₐ ⟨z, n :: ns⟩ ∗ (l ↪ₐ ⟨z, ns⟩ -∗ Φ (.int n.val)))
      ⊢ tglWp E pl(rand(#z, #lbl l)) Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply twp_lift_atomic_head_step solve_not_value (by is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape $$ Hσ Hl
  have Hzpos : 0 < z := lt_of_le_of_lt n.2.1 n.2.2
  have hred : HeadReducible pl(rand(#z, #lbl l)) σ₁ :=
    (HeadStepSupport.RandTapeS hlook rfl rfl rfl).ne_zero
  imodintro
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases Possible.headStepSupport Hstep with
  | RandTapeS hlook' _ hv hσ =>
    rw [hlook] at hlook'
    cases hlook'
    subst hσ hv
    imod app_state_update_tape $$ Hσ Hl with ⟨Hσ', Hl'⟩
    imodintro
    isimp only [erisWpGS_stateInterp_eq, Std.ExtTreeMap.insert_eq_PartialMap_insert, Exp.toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ Hl'
  | RandTapeEmptyS _ hlook' _ _ _ _ => rw [hlook] at hlook'; cases hlook'
  | RandTapeOtherS _ hlook' hne _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd rfl hne
  | RandTapeNonposEmptyS hnz _ _ => exact absurd Hzpos hnz
  | RandTapeNonposOtherS hnz _ _ => exact absurd Hzpos hnz

theorem twp_rand_tape_empty {E : CoPset} {l : Loc} {z : Int}
    {Φ : Val rT → IProp GF} (Hz : 0 < z) :
    iprop(l ↪ₐ ⟨z, []⟩ ∗ (∀ n, l ↪ₐ ⟨z, []⟩ -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)))
      ⊢ tglWp E pl(rand(#z, #lbl l)) Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply twp_lift_atomic_head_step solve_not_value (by is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape $$ Hσ Hl
  have hred : HeadReducible pl(rand(#z, #lbl l)) σ₁ :=
    (HeadStepSupport.RandTapeEmptyS Hz hlook rfl (le_refl _) Hz rfl).ne_zero
  imodintro
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases Possible.headStepSupport Hstep with
  | RandTapeS hlook' _ _ _ => rw [hlook] at hlook'; cases hlook'
  | RandTapeEmptyS _ _ _ Hv0 Hvz hσ =>
    subst hσ
    imodintro
    isimp only [erisWpGS_stateInterp_eq, Exp.toVal?_lit]
    iframe Hσ
    iapply HΦ $$ Hl
    ipureintro; exact ⟨Hv0, Hvz⟩
  | RandTapeOtherS _ hlook' hne _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd rfl hne
  | RandTapeNonposEmptyS hnz _ _ => exact absurd Hz hnz
  | RandTapeNonposOtherS hnz _ _ => exact absurd Hz hnz

end Lifting

end TotalEris
end ProbLang
