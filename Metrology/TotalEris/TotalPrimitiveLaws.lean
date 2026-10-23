module

public import Metrology.TotalEris.ErisGS
import Metrology.ProbLang.Syntax.Notation
public import Metrology.TotalEris.TotalLifting

/-!
# Total-correctness primitive WP laws
-/

@[expose] public section

open Iris Iris.Std Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS Possible
open scoped AppGS

namespace ProbLang

variable {rT : Type _}

namespace TotalEris

section Lifting

variable {hlc : HasLC} {GF : BundledGFunctors} [LawfulProbLangℝ rT] [ErisGS rT hlc GF]
variable {E : CoPset} {Φ : Val rT → IProp GF} {l : Loc} {z : Int}

/-! ## Heap operations -/

/-- Total weakest precondition of `ref v` (Eris `wp_alloc`). -/
theorem twp_alloc {v : Val rT} :
    iprop(∀ l, appHeapFrag l v -∗ Φ (.loc l)) ⊢ tglWp E (.alloc (.ofVal v)) Φ := by
  iintro HΦ
  iapply twp_lift_atomic_head_step solve_not_value (by is_lc)
  iintro %σ₁ Hσ !>
  have hred : HeadReducible (.alloc (.ofVal v)) σ₁ :=
    (HeadStepSupport.AllocS (Exp.toVal?_ofVal v) rfl rfl).ne_zero
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases headStepSupport Hstep with
  | AllocS hvd hl hσ =>
    rw [Exp.toVal?_ofVal] at hvd
    cases hvd
    subst hl hσ
    imod app_state_heap_alloc v $$ Hσ with ⟨Hσ', Hl⟩
    imodintro
    isimp only [erisWpGS_stateInterp_eq, Std.ExtTreeMap.insert_eq_PartialMap_insert, Exp.toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ %σ₁.heap.fresh Hl

/-- Total weakest precondition of `!l` (Eris `wp_load`). -/
theorem twp_load {v : Val rT} :
    iprop(l ↦ v ∗ (l ↦ v -∗ Φ v)) ⊢ tglWp E pl(!#loc l) Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply twp_lift_atomic_head_step solve_not_value (by is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_heap $$ Hσ Hl
  have hred : HeadReducible pl(!#loc l) σ₁ := (HeadStepSupport.LoadS hlook rfl).ne_zero
  imodintro
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases headStepSupport Hstep with
  | LoadS hlook' hofv =>
    rw [hlook] at hlook'
    cases hlook'
    subst hofv
    imodintro
    isimp only [erisWpGS_stateInterp_eq, Exp.toVal?_ofVal]
    iframe Hσ
    iapply HΦ $$ Hl

/-- Total weakest precondition of `l ← v` (Eris `wp_store`). -/
theorem twp_store {v v' : Val rT} :
    iprop(l ↦ v' ∗ (l ↦ v -∗ Φ .unit)) ⊢ tglWp E (.store pl(#loc l) (.ofVal v)) Φ := by
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
  cases headStepSupport Hstep with
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

/-- Total weakest precondition of `alloc_tape z` (Eris `wp_alloc_tape`). -/
theorem twp_alloctape :
    iprop(∀ l, l ↪ₐ Tape.empty z -∗ Φ (.lbl l)) ⊢ tglWp E pl(tape(#z)) Φ := by
  iintro HΦ
  iapply twp_lift_atomic_head_step solve_not_value (by is_lc)
  iintro %σ₁ Hσ !>
  have hred : HeadReducible pl(tape(#z)) σ₁ :=
    (HeadStepSupport.TapeS rfl rfl).ne_zero
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases headStepSupport Hstep with
  | TapeS hl hσ =>
    subst hl hσ
    imod app_state_tape_alloc (Tape.empty z) $$ Hσ with ⟨Hσ', Hl⟩
    imodintro
    isimp only [erisWpGS_stateInterp_eq, Std.ExtTreeMap.insert_eq_PartialMap_insert, Exp.toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ %σ₁.tapes.fresh Hl

/-! ## Random sampling -/

/-- Total weakest precondition of `rand z` without a tape (Eris `wp_rand`). -/
theorem twp_rand (Hz : 0 < z) :
    iprop(∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢ tglWp E pl(rand(#z, #())) Φ := by
  iintro HΦ
  iapply twp_lift_atomic_head_step solve_not_value (by is_lc)
  iintro %σ₁ Hσ !>
  have hred : HeadReducible pl(rand(#z, #())) σ₁ :=
    (HeadStepSupport.RandNoTapeS Hz (le_refl _) Hz).ne_zero
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases headStepSupport Hstep with
  | RandNoTapeS _ Hv0 Hvz =>
    imodintro
    isimp only [erisWpGS_stateInterp_eq, Exp.toVal?_lit]
    iframe Hσ
    iapply HΦ
    ipureintro; exact ⟨Hv0, Hvz⟩
  | RandNonposS hnz => exact absurd Hz hnz

/-- Total weakest precondition of `rand(l) z` on a tape with head `n` (Eris `wp_rand_tape`). -/
theorem twp_rand_tape {n : { z' : Int // 0 ≤ z' ∧ z' < z }}
    {ns : List { z' : Int // 0 ≤ z' ∧ z' < z }} :
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
  cases headStepSupport Hstep with
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

/-- Total weakest precondition of `rand(l) z` on an empty tape (Eris `wp_rand_tape_empty`). -/
theorem twp_rand_tape_empty
    (Hz : 0 < z) :
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
  cases headStepSupport Hstep with
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
