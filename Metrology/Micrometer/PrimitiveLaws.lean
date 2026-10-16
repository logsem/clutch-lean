module

public import Metrology.Micrometer.AppWeakestpre
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Iris.AppProgram
public import Metrology.Iris.SpecProgram
public import Metrology.Iris.SpecUpdate
public import Metrology.Iris.SpecRules
public import Metrology.Iris.BudgetCredits

/-! # Primitive Laws -/

@[expose] public section

set_option linter.discrete false

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting
open scoped AppGS

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

/-! ## Bundled ghost-state class -/

/-- The Micrometer ghost-state components. The lifting and the budget camera are not part of this
class: the lifting is the explicit first argument of `wp`, the budget is a `BudgetGS B GF`. -/
class MicrometerGS (rT : Type) [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
    (hlc : outParam HasLC) (GF : BundledGFunctors) where
  appGS : AppGS rT GF
  specGS : SpecGS rT GF
  invGS : InvGS_gen hlc GF

attribute [reducible, instance] MicrometerGS.appGS MicrometerGS.specGS MicrometerGS.invGS

/-! ## `MicrometerWpGS` instance synthesis -/

section MicrometerInstance

variable {hlc : HasLC} {GF : BundledGFunctors} [MicrometerGS rT hlc GF]

@[reducible]
noncomputable instance micrometerWpGS_of_components : MicrometerWpGS (rT := rT) GF where
  hlc := hlc
  invGS := inferInstance
  stateInterp σ := appStateAuth σ

/-! ### `stateInterp` unfolding lemmas -/

@[simp] theorem micrometerWpGS_stateInterp_eq :
    (MicrometerWpGS.stateInterp : State rT → IProp GF) = appStateAuth := rfl

@[simp] theorem micrometerWpGS_specInterp_eq :
    (SpecUpdateGS.specInterp : Cfg rT → IProp GF) = Cfg.specAuth := rfl

end MicrometerInstance

/-! ### `ExtTreeMap.insert` ↔ `PartialMap.insert` bridge -/

attribute [simp] ExtTreeMap.insert_eq_PartialMap_insert

/-! ## Primitive WP laws -/

omit [MeasurableSingletonClass rT] in
/-- A non-positive bound on an empty tape steps to `-1`, whether or not it matches the tape's. -/
theorem HeadStepSupport.rand_lbl_nonpos {σ : State rT} {l : Loc} {z N : Int} (Hz : ¬ 0 < z)
    (hlook : σ.tapes[l]? = some ⟨N, []⟩) :
    HeadStepSupport ⟨pl(rand(#(.int z), #(.lbl l))), σ⟩ ⟨pl(#(.int (-1))), σ⟩ := by
  obtain rfl | hN := eq_or_ne N z
  · exact .RandTapeNonposEmptyS Hz hlook rfl
  · exact .RandTapeNonposOtherS Hz hlook hN.symm

section Lifting

variable {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B]
  [CanonicallyOrderedAdd B] [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors}
  [MicrometerGS rT hlc GF] [BudgetGS B GF] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing]

theorem wp_alloc {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    iprop% (∀ l, appHeapFrag l v -∗ Φ (.loc l)) ⊢ wp L E (.alloc (.ofVal v)) Φ := by
  iintro HΦ
  iapply wp_lift_atomic_head_step Exp.alloc_toVal?_eq_none (by is_lc)
  iintro %σ₁ Hσ !>
  isplitr; · ipureintro; exact ⟨_, (HeadStepSupport.AllocS (Exp.toVal?_ofVal v) rfl rfl).pos⟩
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | AllocS hvd hl hσ =>
    rw [Exp.toVal?_ofVal] at hvd; cases hvd; subst hl hσ
    imod app_state_heap_alloc v $$ Hσ with ⟨Hσ', Hl⟩
    imodintro
    simp only [micrometerWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert,
      Exp.toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ %σ₁.heap.fresh Hl

theorem wp_load {E : CoPset} {l : Loc} {v : Val rT} {Φ : Val rT → IProp GF} :
    iprop% appHeapFrag l v ∗ (appHeapFrag l v -∗ Φ v) ⊢ wp L E pl(!#(.loc l)) Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply wp_lift_atomic_head_step Exp.load_toVal?_eq_none (by is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_heap $$ Hσ Hl
  imodintro
  isplitr; · ipureintro; exact ⟨_, (HeadStepSupport.LoadS hlook rfl).pos⟩
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | LoadS hlook' hofv =>
    rw [hlook] at hlook'; cases hlook'; subst hofv
    imodintro
    simp only [micrometerWpGS_stateInterp_eq, Exp.toVal?_ofVal]
    iframe Hσ
    iapply HΦ $$ Hl

theorem wp_store {E : CoPset} {l : Loc} {v v' : Val rT} {Φ : Val rT → IProp GF} : iprop%
    appHeapFrag l v' ∗ (appHeapFrag l v -∗ Φ .unit) ⊢
    wp L E (.store pl(#(.loc l)) (.ofVal v)) Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply wp_lift_atomic_head_step Exp.store_toVal?_eq_none (by is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_heap $$ Hσ Hl
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, (HeadStepSupport.StoreS (Exp.toVal?_ofVal v)
        (by rw [hlook]; exact Option.isSome_some) rfl).pos⟩
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | StoreS hvd _ hσ =>
    rw [Exp.toVal?_ofVal] at hvd; cases hvd; subst hσ
    imod app_state_update_heap $$ Hσ Hl with ⟨Hσ', Hl'⟩
    imodintro
    simp only [micrometerWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert,
      Exp.toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ Hl'

theorem wp_alloctape {E : CoPset} {z : Int} {Φ : Val rT → IProp GF} :
    iprop% (∀ l, appTapesFrag l (Tape.empty z) -∗ Φ (.lbl l)) ⊢ wp L E pl(tape(#(.int z))) Φ := by
  iintro HΦ
  iapply wp_lift_atomic_head_step Exp.tape_toVal?_eq_none (by is_lc)
  iintro %σ₁ Hσ !>
  isplitr; · ipureintro; exact ⟨_, (HeadStepSupport.TapeS rfl rfl).pos⟩
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | TapeS hl hσ =>
    subst hl hσ
    imod app_state_tape_alloc (Tape.empty z) $$ Hσ with ⟨Hσ', Hl⟩
    imodintro
    simp only [micrometerWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert,
      Exp.toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ %σ₁.tapes.fresh Hl

theorem wp_rand {E : CoPset} {z : Int} {Φ : Val rT → IProp GF} (Hz : 0 < z) : iprop%
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢ wp L E pl(rand(#(.int z), #(.unit))) Φ := by
  iintro HΦ
  iapply wp_lift_atomic_head_step Exp.rand_toVal?_eq_none (by is_lc)
  iintro %σ₁ Hσ !>
  isplitr; · ipureintro; exact ⟨_, (HeadStepSupport.RandNoTapeS Hz le_rfl Hz).pos⟩
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | RandNoTapeS _ Hv0 Hvz =>
    imodintro
    simp only [micrometerWpGS_stateInterp_eq, Exp.toVal?_lit]
    iframe Hσ
    iapply HΦ $$ %_ %⟨Hv0, Hvz⟩
  | RandNonposS hnz => exact absurd Hz hnz

theorem wp_rand_nonpos {E : CoPset} {z : Int} {Φ : Val rT → IProp GF} (Hz : ¬ 0 < z) :
    Φ (.int (-1)) ⊢ wp L E pl(rand(#(.int z), #(.unit))) Φ := by
  iintro HΦ
  iapply wp_lift_atomic_head_step Exp.rand_toVal?_eq_none (by is_lc)
  iintro %σ₁ Hσ !>
  isplitr; · ipureintro; exact ⟨_, (HeadStepSupport.RandNonposS Hz).pos⟩
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | RandNoTapeS hpos _ _ => exact absurd hpos Hz
  | RandNonposS _ =>
    imodintro
    simp only [micrometerWpGS_stateInterp_eq, Exp.toVal?_lit]
    iframe Hσ
    iexact HΦ

theorem wp_rand_tape {E : CoPset} {l : Loc} {z n : Int} {ns : List Int}
    {Φ : Val rT → IProp GF} : iprop%
    appNatTape l z (n :: ns) ∗ (appNatTape l z ns -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int z), #(.lbl l))) Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply wp_lift_atomic_head_step Exp.rand_toVal?_eq_none (by is_lc)
  iintro %σ₁ Hσ
  icases app_read_natTape_head $$ Hl with ⟨%x, %xs, Hback, %hxv, HHandback⟩
  ihave %hlook := app_state_lookup_tape $$ Hσ Hback
  have hz : 0 < z := by have := x.2; omega
  imodintro
  isplitr; · ipureintro; exact ⟨_, (HeadStepSupport.RandTapeS hlook rfl rfl rfl).pos⟩
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | RandTapeS hlook' _ hv hσ =>
    rw [hlook] at hlook'; cases hlook'
    subst hσ hv hxv
    imod app_state_update_tape $$ Hσ Hback with ⟨Hσ', Hl'⟩
    imodintro
    simp only [micrometerWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert,
      Exp.toVal?_lit]
    iframe Hσ'
    ihave HlNew := HHandback $$ Hl'
    iapply HΦ $$ HlNew %(x.2)
  | RandTapeEmptyS _ hlook' _ _ _ _ =>
    rw [hlook] at hlook'; cases hlook'
  | RandTapeOtherS _ hlook' hne _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd rfl hne
  | RandTapeNonposEmptyS hnz _ _ | RandTapeNonposOtherS hnz _ _ => exact absurd hz hnz

theorem wp_rand_tape_empty {E : CoPset} {l : Loc} {z : Int} {Φ : Val rT → IProp GF}
    (Hz : 0 < z) : iprop%
    appNatTape l z [] ∗ (∀ n, appNatTape l z [] -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int z), #(.lbl l))) Φ := by
  iintro ⟨Hl, HΦ⟩
  ihave HlBack := app_natTape_to_empty $$ Hl
  iapply wp_lift_atomic_head_step Exp.rand_toVal?_eq_none (by is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape $$ Hσ HlBack
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, (HeadStepSupport.RandTapeEmptyS Hz hlook rfl le_rfl Hz rfl).pos⟩
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | RandTapeS hlook' _ _ _ =>
    rw [hlook] at hlook'; cases hlook'
  | RandTapeEmptyS _ _ _ Hv0 Hvz hσ =>
    subst hσ
    imodintro
    simp only [micrometerWpGS_stateInterp_eq, Exp.toVal?_lit]
    iframe Hσ
    ihave HlNat := app_empty_to_natTape $$ HlBack
    iapply HΦ $$ HlNat %⟨Hv0, Hvz⟩
  | RandTapeOtherS _ hlook' hne _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd rfl hne
  | RandTapeNonposEmptyS hnz _ _ | RandTapeNonposOtherS hnz _ _ => exact absurd Hz hnz

theorem wp_rand_tape_wrong_bound {E : CoPset} {l : Loc} {z M : Int} {ns : List Int}
    {Φ : Val rT → IProp GF} (Hz : 0 < z) (HneM : z ≠ M) : iprop%
    appNatTape l M ns ∗ (∀ n, appNatTape l M ns -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int z), #(.lbl l))) Φ := by
  iintro ⟨Hl, HΦ⟩
  iunfold appNatTape at Hl
  icases Hl with ⟨%fs, %hmap, HlBack⟩
  iapply wp_lift_atomic_head_step Exp.rand_toVal?_eq_none (by is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape $$ Hσ HlBack
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, (HeadStepSupport.RandTapeOtherS Hz hlook HneM le_rfl Hz rfl).pos⟩
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | RandTapeS hlook' heq _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd heq HneM
  | RandTapeEmptyS _ hlook' heq _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd heq HneM
  | RandTapeNonposEmptyS hnz _ _ | RandTapeNonposOtherS hnz _ _ => exact absurd Hz hnz
  | RandTapeOtherS _ _ _ Hv0 Hvz hσ =>
    subst hσ
    imodintro
    simp only [micrometerWpGS_stateInterp_eq, Exp.toVal?_lit]
    iframe Hσ
    ihave HlNat : appNatTape l M ns $$ [HlBack]
    · iunfold appNatTape; iexists fs; iframe %hmap HlBack
    iapply HΦ $$ HlNat %⟨Hv0, Hvz⟩

/-! ### Spec-side `_r` WPs -/

theorem wp_rand_r {E : CoPset} (K : Ectx rT) {z : Int} {e : Exp rT} {Φ : Val rT → IProp GF}
    (Hz : 0 < z) : iprop%
    ⤇ K.fill pl(rand(#(.int z), #(.unit))) ∗
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ ⤇ K.fill pl(#(.int n)) -∗ wp L E e Φ) ⊢
    wp L E e Φ := by
  iintro ⟨Hj, Hwp⟩
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  have Hwitness : HeadStepSupport ⟨pl(rand(#(.int z), #(.unit))), σ₁'⟩
      ⟨pl(#(.int 0)), σ₁'⟩ := .RandNoTapeS Hz le_rfl Hz
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  iapply specCoupl_step (.of_headStepSupport_fill K Hwitness (by is_lc))
  iintro %e₂' %σ₂' %Hstep
  obtain ⟨e', rfl, Hstep'⟩ := HeadStepSupport.of_primStep_fill Hwitness (by is_lc) Hstep
  cases Hstep' with
  | RandNoTapeS _ Hv0 Hvz =>
    imodintro
    iapply specCoupl_ret
    imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
    imod Hclose
    imodintro
    iframe Hσ Hs' Hb
    iapply Hwp $$ %_ %⟨Hv0, Hvz⟩ Hj'
  | RandNonposS hnz => exact absurd Hz hnz

theorem wp_rand_lbl_nonpos {E : CoPset} {l : Loc} {z N : Int} {Φ : Val rT → IProp GF}
    (Hz : ¬ 0 < z) : iprop%
    appTapesFrag l ⟨N, []⟩ ∗ (appTapesFrag l ⟨N, []⟩ -∗ Φ (.int (-1))) ⊢
    wp L E pl(rand(#(.int z), #(.lbl l))) Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply wp_lift_atomic_head_step Exp.rand_toVal?_eq_none (by is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape $$ Hσ Hl
  imodintro
  isplitr; · ipureintro; exact ⟨_, (HeadStepSupport.rand_lbl_nonpos Hz hlook).pos⟩
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | RandTapeS hlook' _ _ _ =>
    rw [hlook] at hlook'; cases hlook'
  | RandTapeEmptyS hpos _ _ _ _ _ | RandTapeOtherS hpos _ _ _ _ _ => exact absurd hpos Hz
  | RandTapeNonposEmptyS _ _ _ | RandTapeNonposOtherS _ _ _ =>
    imodintro
    simp only [micrometerWpGS_stateInterp_eq, Exp.toVal?_lit]
    iframe Hσ
    iapply HΦ $$ Hl

theorem wp_rand_nonpos_r {E : CoPset} (K : Ectx rT) {z : Int} {e : Exp rT}
    {Φ : Val rT → IProp GF} (Hz : ¬ 0 < z) : iprop%
    ⤇ K.fill pl(rand(#(.int z), #(.unit))) ∗ (⤇ K.fill pl(#(.int (-1))) -∗ wp L E e Φ) ⊢
    wp L E e Φ := by
  iintro ⟨Hj, Hwp⟩
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  have Hwitness : HeadStepSupport ⟨pl(rand(#(.int z), #(.unit))), σ₁'⟩
      ⟨pl(#(.int (-1))), σ₁'⟩ := .RandNonposS Hz
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  iapply specCoupl_step (.of_headStepSupport_fill K Hwitness (by is_lc))
  iintro %e₂' %σ₂' %Hstep
  obtain ⟨e', rfl, Hstep'⟩ := HeadStepSupport.of_primStep_fill Hwitness (by is_lc) Hstep
  cases Hstep' with
  | RandNoTapeS hpos _ _ => exact absurd hpos Hz
  | RandNonposS _ =>
    imodintro
    iapply specCoupl_ret
    imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
    imod Hclose
    imodintro
    iframe Hσ Hs' Hb
    iapply Hwp $$ Hj'

theorem wp_rand_tape_empty_r {E : CoPset} (K : Ectx rT) {l : Loc} {z : Int} {e : Exp rT}
    {Φ : Val rT → IProp GF} (Hz : 0 < z) : iprop%
    ⤇ K.fill pl(rand(#(.int z), #(.lbl l))) ∗ specNatTape l z [] ∗
    (∀ n, specNatTape l z [] -∗ ⤇ K.fill pl(#(.int n)) -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ wp L E e Φ) ⊢
    wp L E e Φ := by
  iintro ⟨Hj, Hα, Hwp⟩
  ihave HαB := spec_natTape_to_empty $$ Hα
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  ihave %hlook := spec_auth_lookup_tape $$ Hs HαB
  have Hwitness : HeadStepSupport ⟨pl(rand(#(.int z), #(.lbl l))), σ₁'⟩
      ⟨pl(#(.int 0)), σ₁'⟩ := .RandTapeEmptyS Hz hlook rfl le_rfl Hz rfl
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  iapply specCoupl_step (.of_headStepSupport_fill K Hwitness (by is_lc))
  iintro %e₂' %σ₂' %Hstep
  obtain ⟨e', rfl, Hstep'⟩ := HeadStepSupport.of_primStep_fill Hwitness (by is_lc) Hstep
  cases Hstep' with
  | RandTapeS hlook' _ _ _ =>
    rw [hlook] at hlook'; cases hlook'
  | RandTapeEmptyS _ _ _ Hv0 Hvz hσ =>
    subst hσ
    imodintro
    iapply specCoupl_ret
    imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
    imod Hclose
    imodintro
    iframe Hσ Hs' Hb
    ihave HαNat := spec_empty_to_natTape $$ HαB
    iapply Hwp $$ HαNat Hj' %⟨Hv0, Hvz⟩
  | RandTapeOtherS _ hlook' hne _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd rfl hne
  | RandTapeNonposEmptyS hnz _ _ | RandTapeNonposOtherS hnz _ _ => exact absurd Hz hnz

theorem wp_rand_lbl_nonpos_r {E : CoPset} (K : Ectx rT) {l : Loc} {z N : Int} {e : Exp rT}
    {Φ : Val rT → IProp GF} (Hz : ¬ 0 < z) : iprop%
    ⤇ K.fill pl(rand(#(.int z), #(.lbl l))) ∗ specTapesFrag l ⟨N, []⟩ ∗
    (specTapesFrag l ⟨N, []⟩ -∗ ⤇ K.fill pl(#(.int (-1))) -∗ wp L E e Φ) ⊢
    wp L E e Φ := by
  iintro ⟨Hj, Hl, Hwp⟩
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  ihave %hlook := spec_auth_lookup_tape $$ Hs Hl
  have Hwitness : HeadStepSupport ⟨pl(rand(#(.int z), #(.lbl l))), σ₁'⟩
      ⟨pl(#(.int (-1))), σ₁'⟩ := .rand_lbl_nonpos Hz hlook
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  iapply specCoupl_step (.of_headStepSupport_fill K Hwitness (by is_lc))
  iintro %e₂' %σ₂' %Hstep
  obtain ⟨e', rfl, Hstep'⟩ := HeadStepSupport.of_primStep_fill Hwitness (by is_lc) Hstep
  cases Hstep' with
  | RandTapeS hlook' _ _ _ =>
    rw [hlook] at hlook'; cases hlook'
  | RandTapeEmptyS hpos _ _ _ _ _ | RandTapeOtherS hpos _ _ _ _ _ => exact absurd hpos Hz
  | RandTapeNonposEmptyS _ _ _ | RandTapeNonposOtherS _ _ _ =>
    imodintro
    iapply specCoupl_ret
    imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
    imod Hclose
    imodintro
    iframe Hσ Hs' Hb
    iapply Hwp $$ Hl Hj'

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] in
theorem wp_alloc_tape_r {E : CoPset} (K : Ectx rT) {z : Int} {e : Exp rT}
    {Φ : Val rT → IProp GF} : iprop%
    ⤇ K.fill pl(tape(#(.int z))) ∗
      (∀ (l : Loc), ⤇ K.fill pl(#(.lbl l)) -∗ specNatTape l z [] -∗ wp L E e Φ) ⊢
    wp L E e Φ := by
  iintro ⟨Hj, Hwp⟩
  imod step_alloctape K z $$ Hj with ⟨%l, Hj', Hl⟩
  isimp only [Tape.empty] at Hl
  ihave HlNat := spec_empty_to_natTape $$ Hl
  iapply Hwp $$ %l Hj' HlNat

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] in
theorem wp_rand_tape_r {E : CoPset} (K : Ectx rT) {z : Int} {l : Loc} {n : Int} {ns : List Int}
    {e : Exp rT} {Φ : Val rT → IProp GF} : iprop%
    ⤇ K.fill pl(rand(#(.int z), #(.lbl l))) ∗ specNatTape l z (n :: ns) ∗
    (⤇ K.fill pl(#(.int n)) -∗ specNatTape l z ns -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ wp L E e Φ) ⊢
    wp L E e Φ := by
  iintro ⟨Hj, Hl, Hwp⟩
  icases spec_read_natTape_head $$ Hl with ⟨%x, %xs, Hback, %hxv, HHandback⟩
  imod step_rand K l x xs $$ [$] with ⟨Hj', Hback'⟩
  subst hxv
  ihave HlNew := HHandback $$ Hback'
  iapply Hwp $$ Hj' HlNew %(x.2)

theorem wp_rand_empty_r {E : CoPset} (K : Ectx rT) {z : Int} {l : Loc} {e : Exp rT}
    {Φ : Val rT → IProp GF} (Hz : 0 < z) : iprop%
    ⤇ K.fill pl(rand(#(.int z), #(.lbl l))) ∗ specNatTape l z [] ∗
    (∀ n, specNatTape l z [] ∗ ⤇ K.fill pl(#(.int n)) -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ wp L E e Φ) ⊢
    wp L E e Φ := by
  iintro ⟨Hj, Hα, Hwp⟩
  ihave Hαb := spec_natTape_to_empty $$ Hα
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  ihave %hlook := spec_auth_lookup_tape $$ Hs Hαb
  have Hwitness : HeadStepSupport ⟨pl(rand(#(.int z), #(.lbl l))), σ₁'⟩
      ⟨pl(#(.int 0)), σ₁'⟩ := .RandTapeEmptyS Hz hlook rfl le_rfl Hz rfl
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  iapply specCoupl_step (.of_headStepSupport_fill K Hwitness (by is_lc))
  iintro %e₂' %σ₂' %Hstep
  obtain ⟨e', rfl, Hstep'⟩ := HeadStepSupport.of_primStep_fill Hwitness (by is_lc) Hstep
  cases Hstep' with
  | RandTapeS hlook' _ _ _ =>
    rw [hlook] at hlook'; cases hlook'
  | RandTapeEmptyS _ _ _ Hv0 Hvz hσ =>
    subst hσ
    imodintro
    iapply specCoupl_ret
    imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
    imod Hclose
    imodintro
    iframe Hσ Hs' Hb
    ihave HαNat := spec_empty_to_natTape $$ Hαb
    iapply Hwp $$ [$HαNat $Hj'] %⟨Hv0, Hvz⟩
  | RandTapeOtherS _ hlook' hne _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd rfl hne
  | RandTapeNonposEmptyS hnz _ _ | RandTapeNonposOtherS hnz _ _ => exact absurd Hz hnz

theorem wp_rand_wrong_tape_r {E : CoPset} (K : Ectx rT) {z M : Int} {l : Loc} {ns : List Int}
    {e : Exp rT} {Φ : Val rT → IProp GF} (Hz : 0 < z) (HneM : z ≠ M) : iprop%
    ⤇ K.fill pl(rand(#(.int z), #(.lbl l))) ∗ specNatTape l M ns ∗
    (∀ n, specNatTape l M ns ∗ ⤇ K.fill pl(#(.int n)) -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ wp L E e Φ) ⊢
    wp L E e Φ := by
  iintro ⟨Hj, Hα, Hwp⟩
  iunfold specNatTape at Hα
  icases Hα with ⟨%fs, %hmap, Hαb⟩
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  ihave %hlook := spec_auth_lookup_tape $$ Hs Hαb
  have Hwitness : HeadStepSupport ⟨pl(rand(#(.int z), #(.lbl l))), σ₁'⟩
      ⟨pl(#(.int 0)), σ₁'⟩ := .RandTapeOtherS Hz hlook HneM le_rfl Hz rfl
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  iapply specCoupl_step (.of_headStepSupport_fill K Hwitness (by is_lc))
  iintro %e₂' %σ₂' %Hstep
  obtain ⟨e', rfl, Hstep'⟩ := HeadStepSupport.of_primStep_fill Hwitness (by is_lc) Hstep
  cases Hstep' with
  | RandTapeS hlook' heq _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd heq HneM
  | RandTapeEmptyS _ hlook' heq _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd heq HneM
  | RandTapeNonposEmptyS hnz _ _ | RandTapeNonposOtherS hnz _ _ => exact absurd Hz hnz
  | RandTapeOtherS _ _ _ Hv0 Hvz hσ =>
    subst hσ
    imodintro
    iapply specCoupl_ret
    imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
    imod Hclose
    imodintro
    iframe Hσ Hs' Hb
    ihave HαNat : specNatTape l M ns $$ [Hαb]
    · iunfold specNatTape; iexists fs; iframe %hmap Hαb
    iapply Hwp $$ [$HαNat $Hj'] %⟨Hv0, Hvz⟩

end Lifting

end ProbLang
