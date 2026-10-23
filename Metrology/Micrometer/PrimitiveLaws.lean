module

public import Metrology.Micrometer.AppWeakestpre
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Iris.AppProgram
public import Metrology.Iris.SpecProgram
public import Metrology.Iris.SpecUpdate
public import Metrology.Iris.SpecRules
public import Metrology.Iris.BudgetCredits
import Metrology.Iris.LocalBI

/-! # Primitive Laws

The ghost-state bundle `MicrometerGS` and its `MicrometerWpGS` instance, then the `wp` rules for
heap, tape and `rand` steps on the program side and the spec side (`_r`). -/

@[expose] public section

-- these rules use the @[discrete] lifting lemmas without being discrete themselves
set_option linter.discrete false

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang.MicrometerWpGS GradedLifting
open ProbLang.Possible (headStepSupport)
open scoped AppGS

namespace ProbLang
open HeadStepSupport

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

open Exp (alloc_toVal?_eq_none load_toVal?_eq_none rand_toVal?_eq_none store_toVal?_eq_none
  tape_toVal?_eq_none toVal?_lit toVal?_ofVal)
open ExtTreeMap (insert_eq_PartialMap_insert)
open Cfg (specAuth)

/-! ## Ghost state -/

/-- The Micrometer ghost-state components, excluding budget (`BudgetGS B GF`) -/
class MicrometerGS (rT : outParam Type) [MeasurableSpace rT] [LawfulProbLangℝ rT]
    (hlc : outParam HasLC) (GF : BundledGFunctors) where
  /-- The program-side ghost state. -/
  appGS : AppGS rT GF
  /-- The spec-side ghost state. -/
  specGS : SpecGS rT GF
  /-- The invariant ghost state. -/
  invGS : InvGS_gen hlc GF

attribute [reducible, instance] MicrometerGS.appGS MicrometerGS.specGS

/-- `MicrometerGS.invGS`, with the measurable space and language read off the instance, not
searched for first. -/
@[reducible]
instance MicrometerGS.instInvGS {R : Type} {M : MeasurableSpace R} {P : LawfulProbLangℝ R}
    {hlc : HasLC} {GF : BundledGFunctors} [MicrometerGS R hlc GF] : InvGS_gen hlc GF :=
  MicrometerGS.invGS

section MicrometerInstance

variable {hlc : HasLC} {GF : BundledGFunctors}
  [MicrometerGS rT hlc GF]

open MicrometerWpGS SpecUpdateGS

@[reducible]
noncomputable instance micrometerWpGS_of_components : MicrometerWpGS (rT := rT) GF where
  hlc := hlc
  invGS := inferInstance
  stateInterp σ := appStateAuth σ

/-- The `wp` state interpretation is the program-side state authority. -/
@[simp]
theorem micrometerWpGS_stateInterp_eq : (stateInterp : _ → IProp GF) = appStateAuth := rfl

/-- The `wp` spec interpretation is the spec-side authority. -/
@[simp]
theorem micrometerWpGS_specInterp_eq : (specInterp : _ → IProp GF) = specAuth := rfl

end MicrometerInstance

attribute [simp] insert_eq_PartialMap_insert

/-! ## Head-step facts -/

/-- A non-positive bound on an empty tape steps to `-1`, whether or not it matches the tape's. -/
theorem HeadStepSupport.rand_lbl_nonpos {σ : State rT} {l : Loc} {z N : Int} (Hz : ¬ 0 < z)
    (hlook : σ.tapes[l]? = some ⟨N, []⟩) :
    HeadStepSupport ⟨pl(rand(#z, #lbl l)), σ⟩ ⟨pl(#(-1)), σ⟩ := by
  obtain rfl | hN := eq_or_ne N z
  · exact .RandTapeNonposEmptyS Hz hlook rfl
  · exact .RandTapeNonposOtherS Hz hlook hN.symm

/-! ## Program-side laws

Each proof lifts one atomic head step (`wp_lift_atomic_head_step`): it exhibits one possible step,
then inverts `HeadStepSupport` on every possible result and updates the state interpretation. -/

section PrimitiveLaws

variable {hlc : HasLC} {B : Type} [AddCommMonoid B]
  [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors}
  [MicrometerGS rT hlc GF] [BudgetGS B GF] [L.IsLawful] [L.IsTopAbsorbing] {E : CoPset}
  {Φ : Val rT → IProp GF} {e : Exp rT} {l : Loc} {z : Int} (K : Ectx rT)
local bi IProp GF
open BIFUpdate

section HeadSteps
variable [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] [L.HasBind]

/-! ### Heap -/

variable {v : Val rT}

/-- Allocating `v` returns a fresh location `l` that points to `v`. -/
theorem wp_alloc : iprop% (∀ l, appHeapFrag l v -∗ Φ (.loc l)) ⊢ wp L E (.alloc (.ofVal v)) Φ := by
  iintro HΦ
  iapply wp_lift_atomic_head_step alloc_toVal?_eq_none (by is_lc)
  iintro %σ₁ Hσ !>
  isplitr
  · ipureintro; exact ⟨_, (AllocS (toVal?_ofVal v) rfl rfl).pos⟩
  iintro !> %e₂ %σ₂ %hstep
  replace hstep := headStepSupport (possible_iff_pos.mpr hstep)
  cases hstep with
  | AllocS hvd hl hσ =>
    rw [toVal?_ofVal] at hvd
    cases hvd
    subst hl hσ
    imod app_state_heap_alloc v $$ Hσ with ⟨Hσ', Hl⟩
    imodintro
    simp only [micrometerWpGS_stateInterp_eq, insert_eq_PartialMap_insert, toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ %σ₁.heap.fresh Hl

/-- Loading from `l` returns the value `l` points to. -/
theorem wp_load : iprop% appHeapFrag l v ∗ (appHeapFrag l v -∗ Φ v) ⊢ wp L E pl(!#loc l) Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply wp_lift_atomic_head_step load_toVal?_eq_none (by is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_heap $$ Hσ Hl
  imodintro
  isplitr
  · ipureintro; exact ⟨_, (LoadS hlook rfl).pos⟩
  iintro !> %e₂ %σ₂ %hstep
  replace hstep := headStepSupport (possible_iff_pos.mpr hstep)
  cases hstep with
  | LoadS hlook' hofv =>
    rw [hlook] at hlook'
    cases hlook'
    subst hofv
    imodintro
    simp only [micrometerWpGS_stateInterp_eq, toVal?_ofVal]
    iframe Hσ
    iapply HΦ $$ Hl

/-- Storing `v` at `l` overwrites its value and returns unit. -/
theorem wp_store {v v' : Val rT} : iprop%
    appHeapFrag l v' ∗ (appHeapFrag l v -∗ Φ .unit) ⊢ wp L E (.store pl(#loc l) (.ofVal v)) Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply wp_lift_atomic_head_step store_toVal?_eq_none (by is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_heap $$ Hσ Hl
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, (StoreS (toVal?_ofVal v)
        (by rw [hlook]; exact Option.isSome_some) rfl).pos⟩
  iintro !> %e₂ %σ₂ %hstep
  replace hstep := headStepSupport (possible_iff_pos.mpr hstep)
  cases hstep with
  | StoreS hvd _ hσ =>
    rw [toVal?_ofVal] at hvd
    cases hvd
    subst hσ
    imod app_state_update_heap $$ Hσ Hl with ⟨Hσ', Hl'⟩
    imodintro
    simp only [micrometerWpGS_stateInterp_eq, insert_eq_PartialMap_insert, toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ Hl'

/-! ### Tapes and `rand` -/

/-- Allocating a tape with bound `z` returns a fresh label for an empty tape. -/
theorem wp_alloctape : iprop%
    (∀ l, appTapesFrag l (Tape.empty z) -∗ Φ (.lbl l)) ⊢ wp L E pl(tape(#z)) Φ := by
  iintro HΦ
  iapply wp_lift_atomic_head_step tape_toVal?_eq_none (by is_lc)
  iintro %σ₁ Hσ !>
  isplitr
  · ipureintro; exact ⟨_, (TapeS rfl rfl).pos⟩
  iintro !> %e₂ %σ₂ %hstep
  replace hstep := headStepSupport (possible_iff_pos.mpr hstep)
  cases hstep with
  | TapeS hl hσ =>
    subst hl hσ
    imod app_state_tape_alloc (Tape.empty z) $$ Hσ with ⟨Hσ', Hl⟩
    imodintro
    simp only [micrometerWpGS_stateInterp_eq, insert_eq_PartialMap_insert, toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ %σ₁.tapes.fresh Hl

variable {ns : List Int}

/-- A labeled `rand z` on a tape with bound `z` pops the tape's head. -/
theorem wp_rand_tape {n : Int} : iprop%
    appNatTape l z (n :: ns) ∗ (appNatTape l z ns -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
      wp L E pl(rand(#z, #lbl l)) Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply wp_lift_atomic_head_step rand_toVal?_eq_none (by is_lc)
  iintro %σ₁ Hσ
  icases app_read_natTape_head $$ Hl with ⟨%x, %xs, Hback, %hxv, HHandback⟩
  ihave %hlook := app_state_lookup_tape $$ Hσ Hback
  have hz : 0 < z := by have := x.2; omega
  imodintro
  isplitr
  · ipureintro; exact ⟨_, (RandTapeS hlook rfl rfl rfl).pos⟩
  iintro !> %e₂ %σ₂ %hstep
  replace hstep := headStepSupport (possible_iff_pos.mpr hstep)
  cases hstep with
  | RandTapeS hlook' _ hv hσ =>
    rw [hlook] at hlook'
    cases hlook'
    subst hσ hv hxv
    imod app_state_update_tape $$ Hσ Hback with ⟨Hσ', Hl'⟩
    imodintro
    simp only [micrometerWpGS_stateInterp_eq, insert_eq_PartialMap_insert, toVal?_lit]
    iframe Hσ'
    ihave HlNew := HHandback $$ Hl'
    iapply HΦ $$ HlNew %(x.2)
  | RandTapeEmptyS _ hlook' _ _ _ _ =>
    rw [hlook] at hlook'; cases hlook'
  | RandTapeOtherS _ hlook' hne _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd rfl hne
  | RandTapeNonposEmptyS hnz _ _ | RandTapeNonposOtherS hnz _ _ => exact absurd hz hnz

section
variable (Hz : 0 < z)
include Hz

/-- An unlabeled `rand z` with `0 < z` returns some `n` in `[0, z)`. -/
theorem wp_rand : iprop%
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢ wp L E pl(rand(#z, #())) Φ := by
  iintro HΦ
  iapply wp_lift_atomic_head_step rand_toVal?_eq_none (by is_lc)
  iintro %σ₁ Hσ !>
  isplitr
  · ipureintro; exact ⟨_, (RandNoTapeS Hz le_rfl Hz).pos⟩
  iintro !> %e₂ %σ₂ %hstep
  replace hstep := headStepSupport (possible_iff_pos.mpr hstep)
  cases hstep with
  | RandNoTapeS _ hv0 hvz =>
    imodintro
    simp only [micrometerWpGS_stateInterp_eq, toVal?_lit]
    iframe Hσ
    iapply HΦ $$ %_ %⟨hv0, hvz⟩
  | RandNonposS hnz => exact absurd Hz hnz

/-- A labeled `rand z` on an empty tape with bound `z` draws a fresh `n` in `[0, z)`. -/
theorem wp_rand_tape_empty : iprop%
    appNatTape l z [] ∗ (∀ n, appNatTape l z [] -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
      wp L E pl(rand(#z, #lbl l)) Φ := by
  iintro ⟨Hl, HΦ⟩
  ihave HlBack := app_natTape_to_empty $$ Hl
  iapply wp_lift_atomic_head_step rand_toVal?_eq_none (by is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape $$ Hσ HlBack
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, (RandTapeEmptyS Hz hlook rfl le_rfl Hz rfl).pos⟩
  iintro !> %e₂ %σ₂ %hstep
  replace hstep := headStepSupport (possible_iff_pos.mpr hstep)
  cases hstep with
  | RandTapeS hlook' _ _ _ =>
    rw [hlook] at hlook'; cases hlook'
  | RandTapeEmptyS _ _ _ hv0 hvz hσ =>
    subst hσ
    imodintro
    simp only [micrometerWpGS_stateInterp_eq, toVal?_lit]
    iframe Hσ
    ihave HlNat := app_empty_to_natTape $$ HlBack
    iapply HΦ $$ HlNat %⟨hv0, hvz⟩
  | RandTapeOtherS _ hlook' hne _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd rfl hne
  | RandTapeNonposEmptyS hnz _ _ | RandTapeNonposOtherS hnz _ _ => exact absurd Hz hnz

/-- A labeled `rand z` on a tape with another bound draws a fresh `n` and keeps the tape. -/
theorem wp_rand_tape_wrong_bound {M : Int} (HneM : z ≠ M) : iprop%
    appNatTape l M ns ∗ (∀ n, appNatTape l M ns -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
      wp L E pl(rand(#z, #lbl l)) Φ := by
  iintro ⟨Hl, HΦ⟩
  iunfold appNatTape at Hl
  icases Hl with ⟨%fs, %hmap, HlBack⟩
  iapply wp_lift_atomic_head_step rand_toVal?_eq_none (by is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape $$ Hσ HlBack
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, (RandTapeOtherS Hz hlook HneM le_rfl Hz rfl).pos⟩
  iintro !> %e₂ %σ₂ %hstep
  replace hstep := headStepSupport (possible_iff_pos.mpr hstep)
  cases hstep with
  | RandTapeS hlook' heq _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd heq HneM
  | RandTapeEmptyS _ hlook' heq _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd heq HneM
  | RandTapeNonposEmptyS hnz _ _ | RandTapeNonposOtherS hnz _ _ => exact absurd Hz hnz
  | RandTapeOtherS _ _ _ hv0 hvz hσ =>
    subst hσ
    imodintro
    simp only [micrometerWpGS_stateInterp_eq, toVal?_lit]
    iframe Hσ
    ihave HlNat : appNatTape l M ns $$ [HlBack]
    · iunfold appNatTape; iexists fs; iframe %hmap HlBack
    iapply HΦ $$ HlNat %⟨hv0, hvz⟩

end

variable {N : Int}

section
variable (Hz : ¬ 0 < z)
include Hz

/-- An unlabeled `rand z` with `z ≤ 0` returns `-1`. -/
theorem wp_rand_nonpos : Φ (.int (-1)) ⊢ wp L E pl(rand(#z, #())) Φ := by
  iintro HΦ
  iapply wp_lift_atomic_head_step rand_toVal?_eq_none (by is_lc)
  iintro %σ₁ Hσ !>
  isplitr
  · ipureintro; exact ⟨_, (RandNonposS Hz).pos⟩
  iintro !> %e₂ %σ₂ %hstep
  replace hstep := headStepSupport (possible_iff_pos.mpr hstep)
  cases hstep with
  | RandNoTapeS hpos _ _ => exact absurd hpos Hz
  | RandNonposS _ =>
    imodintro
    simp only [micrometerWpGS_stateInterp_eq, toVal?_lit]
    iframe Hσ
    iexact HΦ

/-- A labeled `rand z` with `z ≤ 0` on an empty tape returns `-1`. -/
theorem wp_rand_lbl_nonpos : iprop%
    appTapesFrag l ⟨N, []⟩ ∗ (appTapesFrag l ⟨N, []⟩ -∗ Φ (.int (-1))) ⊢
      wp L E pl(rand(#z, #lbl l)) Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply wp_lift_atomic_head_step rand_toVal?_eq_none (by is_lc)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape $$ Hσ Hl
  imodintro
  isplitr
  · ipureintro; exact ⟨_, (rand_lbl_nonpos Hz hlook).pos⟩
  iintro !> %e₂ %σ₂ %hstep
  replace hstep := headStepSupport (possible_iff_pos.mpr hstep)
  cases hstep with
  | RandTapeS hlook' _ _ _ =>
    rw [hlook] at hlook'; cases hlook'
  | RandTapeEmptyS hpos _ _ _ _ _ | RandTapeOtherS hpos _ _ _ _ _ => exact absurd hpos Hz
  | RandTapeNonposEmptyS _ _ _ | RandTapeNonposOtherS _ _ _ =>
    imodintro
    simp only [micrometerWpGS_stateInterp_eq, toVal?_lit]
    iframe Hσ
    iapply HΦ $$ Hl

end

/-! ## Spec-side `_r` laws

Random spec steps go through `wp_rand_step_r` (one spec coupling round); deterministic ones
(`wp_alloc_tape_r`, `wp_rand_tape_r`) are spec updates and need no coupling instances. -/

/-! ### Spec draws through one coupling round -/

/-- A spec-side `rand` steps to some `#n` with `Q n` and keeps the state, in every spec state
where the resource `R` gives `C`. -/
theorem wp_rand_step_r {x : BaseLit rT} {R : _} {C : State rT → Prop}
    (Q : Int → Prop)
    (hC : ∀ e' σ, ⊢ specAuth ⟨e', σ⟩ -∗ R -∗ ⌜C σ⌝)
    (hwit : ∀ σ, C σ → ∃ ρ, HeadStepSupport ⟨pl(rand(#z, #x)), σ⟩ ρ)
    (hstep : ∀ σ e' σ', C σ → HeadStepSupport ⟨pl(rand(#z, #x)), σ⟩ ⟨e', σ'⟩ →
      σ' = σ ∧ ∃ n, e' = pl(#int n) ∧ Q n) : iprop%
    ⤇ K.fill pl(rand(#z, #x)) ∗ R ∗
      (∀ n, ⌜Q n⌝ -∗ R -∗ ⤇ K.fill pl(#int n) -∗ wp L E e Φ) ⊢
      wp L E e Φ := by
  iintro ⟨Hj, HR, Hwp⟩
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %b₁ ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  ihave %hC := hC _ σ₁' $$ Hs HR
  obtain ⟨⟨e₀, σ₀⟩, Hwitness⟩ := hwit σ₁' hC
  imod subset LawfulSet.empty_subset with Hclose
  imodintro
  iapply specCoupl_step (.of_headStepSupport_fill K Hwitness (by is_lc))
  iintro %e₂' %σ₂' %Hstep
  obtain ⟨e', rfl, Hstep'⟩ := of_primStep_fill Hwitness (by is_lc) Hstep
  obtain ⟨rfl, n, rfl, hn⟩ := hstep _ _ _ hC Hstep'
  imodintro
  iapply specCoupl_ret
  imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  iframe Hσ Hs' Hb
  iapply Hwp $$ %n %hn HR Hj'

section
variable (Hz : 0 < z)
include Hz

/-- A spec-side unlabeled `rand z` with `0 < z` steps to some `#n` with `n` in `[0, z)`. -/
theorem wp_rand_r : iprop%
    ⤇ K.fill pl(rand(#z, #())) ∗
      (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ ⤇ K.fill pl(#int n) -∗ wp L E e Φ) ⊢
      wp L E e Φ := by
  iintro ⟨Hj, Hwp⟩
  iapply wp_rand_step_r K (fun n => 0 ≤ n ∧ n < z) (R := emp) (C := fun _ => True)
    (fun _ _ => by iintro - - !%; trivial) (fun _ _ => ⟨_, .RandNoTapeS Hz le_rfl Hz⟩)
    fun _ _ _ _ h => by
      cases h with
      | RandNoTapeS _ hv0 hvz => exact ⟨rfl, _, rfl, hv0, hvz⟩
      | RandNonposS hnz => exact absurd Hz hnz
  iframe Hj
  isplitr
  · iempintro
  iintro %n %hn - Hj'
  iapply Hwp $$ %n %hn Hj'

/-- A spec-side labeled `rand z` on an empty tape with bound `z` draws a fresh `n` in `[0, z)`. -/
theorem wp_rand_tape_empty_r : iprop%
    ⤇ K.fill pl(rand(#z, #lbl l)) ∗ specNatTape l z [] ∗
      (∀ n, specNatTape l z [] -∗ ⤇ K.fill pl(#int n) -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ wp L E e Φ) ⊢
      wp L E e Φ := by
  iintro ⟨Hj, Hα, Hwp⟩
  ihave HαB := spec_natTape_to_empty $$ Hα
  iapply wp_rand_step_r K (fun n => 0 ≤ n ∧ n < z) (fun _ _ => spec_auth_lookup_tape)
    (fun _ hlook => ⟨_, .RandTapeEmptyS Hz hlook rfl le_rfl Hz rfl⟩) fun _ _ _ hlook h => by
      cases h with
      | RandTapeS hlook' _ _ _ =>
        rw [hlook] at hlook'; cases hlook'
      | RandTapeEmptyS _ _ _ hv0 hvz hσ => exact ⟨hσ, _, rfl, hv0, hvz⟩
      | RandTapeOtherS _ hlook' hne _ _ _ =>
        rw [hlook] at hlook'; cases hlook'; exact absurd rfl hne
      | RandTapeNonposEmptyS hnz _ _ | RandTapeNonposOtherS hnz _ _ => exact absurd Hz hnz
  iframe Hj HαB
  iintro %n %hn HαB Hj'
  ihave HαNat := spec_empty_to_natTape $$ HαB
  iapply Hwp $$ HαNat Hj' %hn

/-- `wp_rand_tape_empty_r` with the tape and spec resources handed back as one `∗` (Rocq form). -/
theorem wp_rand_empty_r : iprop%
    ⤇ K.fill pl(rand(#z, #lbl l)) ∗ specNatTape l z [] ∗
      (∀ n, specNatTape l z [] ∗ ⤇ K.fill pl(#int n) -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ wp L E e Φ) ⊢
      wp L E e Φ := by
  iintro ⟨Hj, Hα, Hwp⟩
  iapply wp_rand_tape_empty_r K Hz
  iframe Hj Hα
  iintro %n Hα Hj'
  iapply Hwp $$ [$Hα $Hj']

/-- A spec-side labeled `rand z` on a tape with another bound draws a fresh `n`, tape kept. -/
theorem wp_rand_wrong_tape_r {M : Int} {ns : List Int} (HneM : z ≠ M) : iprop%
    ⤇ K.fill pl(rand(#z, #lbl l)) ∗ specNatTape l M ns ∗
      (∀ n, specNatTape l M ns ∗ ⤇ K.fill pl(#int n) -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ wp L E e Φ) ⊢
      wp L E e Φ := by
  iintro ⟨Hj, Hα, Hwp⟩
  iunfold specNatTape at Hα
  icases Hα with ⟨%fs, %hmap, Hαb⟩
  iapply wp_rand_step_r K (fun n => 0 ≤ n ∧ n < z) (R := specTapesFrag l ⟨M, fs⟩)
    (fun _ _ => spec_auth_lookup_tape)
    (fun _ hlook => ⟨_, .RandTapeOtherS Hz hlook HneM le_rfl Hz rfl⟩) fun _ _ _ hlook h => by
      cases h with
      | RandTapeS hlook' heq _ _ =>
        rw [hlook] at hlook'; cases hlook'; exact absurd heq HneM
      | RandTapeEmptyS _ hlook' heq _ _ _ =>
        rw [hlook] at hlook'; cases hlook'; exact absurd heq HneM
      | RandTapeNonposEmptyS hnz _ _ | RandTapeNonposOtherS hnz _ _ => exact absurd Hz hnz
      | RandTapeOtherS _ _ _ hv0 hvz hσ => exact ⟨hσ, _, rfl, hv0, hvz⟩
  iframe Hj Hαb
  iintro %n %hn Hαb Hj'
  ihave HαNat : specNatTape l M ns $$ [Hαb]
  · iunfold specNatTape; iexists fs; iframe %hmap Hαb
  iapply Hwp $$ [$HαNat $Hj'] %hn

end

section
variable (Hz : ¬ 0 < z)
include Hz

/-- A spec-side unlabeled `rand z` with `z ≤ 0` steps to `#(-1)`. -/
theorem wp_rand_nonpos_r : iprop%
    ⤇ K.fill pl(rand(#z, #())) ∗ (⤇ K.fill pl(#(-1)) -∗ wp L E e Φ) ⊢ wp L E e Φ := by
  iintro ⟨Hj, Hwp⟩
  iapply wp_rand_step_r K (· = -1) (R := emp) (C := fun _ => True)
    (fun _ _ => by iintro - - !%; trivial) (fun _ _ => ⟨_, .RandNonposS Hz⟩)
    fun _ _ _ _ h => by
      cases h with
      | RandNoTapeS hpos _ _ => exact absurd hpos Hz
      | RandNonposS _ => exact ⟨rfl, _, rfl, rfl⟩
  iframe Hj
  isplitr
  · iempintro
  iintro %_ %rfl - Hj'
  iapply Hwp $$ Hj'

/-- A spec-side labeled `rand z` with `z ≤ 0` on an empty tape steps to `#(-1)`. -/
theorem wp_rand_lbl_nonpos_r : iprop%
    ⤇ K.fill pl(rand(#z, #lbl l)) ∗ specTapesFrag l ⟨N, []⟩ ∗
      (specTapesFrag l ⟨N, []⟩ -∗ ⤇ K.fill pl(#(-1)) -∗ wp L E e Φ) ⊢
      wp L E e Φ := by
  iintro ⟨Hj, Hl, Hwp⟩
  iapply wp_rand_step_r K (· = -1) (fun _ _ => spec_auth_lookup_tape)
    (fun _ hlook => ⟨_, .rand_lbl_nonpos Hz hlook⟩) fun _ _ _ hlook h => by
      cases h with
      | RandTapeS hlook' _ _ _ =>
        rw [hlook] at hlook'; cases hlook'
      | RandTapeEmptyS hpos _ _ _ _ _ | RandTapeOtherS hpos _ _ _ _ _ => exact absurd hpos Hz
      | RandTapeNonposEmptyS _ _ _ | RandTapeNonposOtherS _ _ _ => exact ⟨rfl, _, rfl, rfl⟩
  iframe Hj Hl
  iintro %_ %rfl Hl Hj'
  iapply Hwp $$ Hl Hj'

end

end HeadSteps

/-! ### Spec updates -/

/-- A spec-side `tape z` steps to a fresh label for an empty tape. -/
theorem wp_alloc_tape_r : iprop%
    ⤇ K.fill pl(tape(#z)) ∗
      (∀ l, ⤇ K.fill pl(#lbl l) -∗ specNatTape l z [] -∗ wp L E e Φ) ⊢
      wp L E e Φ := by
  iintro ⟨Hj, Hwp⟩
  imod step_alloctape K z $$ Hj with ⟨%l, Hj', Hl⟩
  isimp only [Tape.empty] at Hl
  ihave HlNat := spec_empty_to_natTape $$ Hl
  iapply Hwp $$ %l Hj' HlNat

/-- A spec-side labeled `rand z` on a tape with bound `z` pops the tape's head. -/
theorem wp_rand_tape_r {n : Int} {ns : List Int} : iprop%
    ⤇ K.fill pl(rand(#z, #lbl l)) ∗ specNatTape l z (n :: ns) ∗
      (⤇ K.fill pl(#int n) -∗ specNatTape l z ns -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ wp L E e Φ) ⊢
      wp L E e Φ := by
  iintro ⟨Hj, Hl, Hwp⟩
  icases spec_read_natTape_head $$ Hl with ⟨%x, %xs, Hback, %hxv, HHandback⟩
  imod step_rand K l x xs $$ [$] with ⟨Hj', Hback'⟩
  subst hxv
  ihave HlNew := HHandback $$ Hback'
  iapply Hwp $$ Hj' HlNew %(x.2)

end PrimitiveLaws

end ProbLang
