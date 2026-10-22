module

public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.Couplings.Divergences.Tv
public import Metrology.Micrometer.WpTactics
public import Metrology.Code.Switching
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Lists and association-list maps: specifications

`PureSteps` facts for the list recursions of `Metrology/Code/Switching.lean`, and `wp` rules
(program side `wp_X`, spec side `wp_X_r`) for `initMap`, `getMap`, `setMap`. -/

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.MicrometerWpGS GradedLifting GradedDivergence
open scoped AppGS ENNReal
open PureSteps (fill)
open Ectx (fill)

namespace ProbLang
namespace Switching

open ProbLang.Val (option isVal_ofVal)
open ProbLang.Exp (ofVal alloc store toVal?_ofVal)
open List (length_cons getElem_cons_zero eraseIdx_cons_zero getElem_cons_succ eraseIdx_cons_succ)
open Nat (cast_succ)

variable {rT : Type} [LawfulProbLangℝ rT]

/-! ## The meta-level model of maps -/

/-- Association-list lookup (leftmost binding wins), mirroring `findList`. -/
def alookup (k : Int) : List (Int × Int) → Option Int
  | [] => none
  | (k', y) :: m => if k' = k then some y else alookup k m

/-- The value of an optional integer result (`NONE` / `SOME #y`). -/
def optIntVal (o : Option Int) : Val rT := option (o.map .int)

/-- A key is absent from the map iff it is not among the keys. -/
theorem alookup_eq_none_iff {k : Int} {m : List (Int × Int)} :
    alookup k m = none ↔ k ∉ m.map Prod.fst := by
  induction m with
  | nil => simp [alookup]
  | cons hd tl ih =>
    obtain ⟨k', y⟩ := hd
    by_cases hk : k' = k
    · simp [alookup, hk]
    · simp [alookup, hk, ih, Ne.symm hk]

/-! ## Pure recursions -/

section Recursions

/-- `findList` computes association-list lookup. -/
theorem findList_steps (m : List (Int × Int)) (k : Int) :
    PureSteps (pl% &findList {ofVal (assocVal m)} #k)
      (ofVal (optIntVal (alookup k m) : Val rT)) := by
  induction m with
  | nil =>
    simp only [assocVal, alookup]
    pure_steps
  | cons hd tl ih =>
    obtain ⟨k', y⟩ := hd
    by_cases hk : k' = k
    · subst hk
      simp only [assocVal, alookup, ↓reduceIte]
      pure_steps
    · simp only [assocVal, alookup, hk, ↓reduceIte]
      pure_steps
      simp only [beq_false_of_ne hk]
      pure_step
      pure_step
      exact ih

variable (l : List Int)

/-- `listLength` computes list length. -/
theorem listLength_steps :
    PureSteps (pl% &listLength {ofVal (intListVal l)}) (ofVal (.int l.length : Val rT)) := by
  induction l with
  | nil =>
    simp only [intListVal]
    pure_steps
  | cons n l ih =>
    simp only [intListVal]
    pure_step 5
    refine (fill [.binopR .plus _] ih).trans ?_
    pure_steps
    rw [length_cons, cast_succ, add_comm]
    exact ProbLang.PureSteps.refl _

/-- `listRemoveNth` removes the `i`-th element, returning `SOME (lᵢ, l \ i)`. -/
theorem listRemoveNth_steps (i : Nat) (hlen : i < l.length) :
    PureSteps (pl% &listRemoveNth {ofVal (intListVal l)} #int i)
      (ofVal (.inr (.pair (.int l[i]) (intListVal (l.eraseIdx i))) : Val rT)) := by
  induction l generalizing i with
  | nil => simp at hlen
  | cons n l ih =>
    cases i with
    | zero =>
      simp only [intListVal, getElem_cons_zero, eraseIdx_cons_zero]
      pure_steps
    | succ j =>
      have hj : j < l.length := by simpa using hlen
      simp only [intListVal, getElem_cons_succ, eraseIdx_cons_succ]
      pure_step 9
      rw [cast_succ, add_sub_cancel_right]
      refine (fill [.case _ _] (ih j hj)).trans ?_
      pure_steps

end Recursions

/-! ## Map operations: `wp` specifications

Rocq source: clutch's `wp_init_map`, `wp_get`, `wp_set` and their `spec_` versions. -/

section MapOps

variable {hlc : HasLC} {GF : BundledGFunctors}
  [MicrometerGS rT hlc GF] [BudgetCreditGS ℝ≥0∞ GF] {E : CoPset} {Φ : Val rT → _} (K : Ectx rT)
  {e : Exp rT}
local bi IProp GF

/-- `initMap ()` allocates a location holding the empty map. -/
theorem wp_initMap : iprop%
    (∀ ℓ : Loc, (ℓ ↦ assocVal []) -∗ Φ (.loc ℓ)) ⊢
      WP[codensity tv] (pl% &initMap #()) @ E {{ Φ }} := by
  iintro HΦ
  wp_pures
  -- restate the literal as `ofVal` of the map value so `wp_alloc` applies
  rw [show alloc (.inl (.lit .unit)) = .alloc (ofVal (assocVal [])) from rfl]
  iapply wp_alloc
  iexact HΦ

/-- Spec-side `wp_initMap`. -/
theorem wp_initMap_r : iprop%
    ⤇ K.fill (pl% &initMap #()) ∗
      (∀ ℓ : Loc, ⤇ K.fill pl(#loc ℓ) -∗ (ℓ ↦ₛ assocVal []) -∗
        WP[codensity tv] e @ E {{ Φ }}) ⊢
      WP[codensity tv] e @ E {{ Φ }} := by
  iintro ⟨Hj, Hcnt⟩
  tp_pures
  ihave Hj := specProgFrag_reshape (e₁ := fill K (alloc (.inl (.lit .unit))))
    (e₂ := K.fill (alloc (ofVal (assocVal [])))) rfl $$ Hj
  imod step_alloc_at K (isVal_ofVal _) (vv := assocVal []) rfl $$ Hj with ⟨%ℓ, Hj, Hl⟩
  iapply Hcnt $$ %ℓ Hj Hl

variable (ℓ : Loc) (m : List (Int × Int)) (k y : Int)

/-- `getMap ℓ k` returns the lookup of `k` and leaves the map unchanged. -/
theorem wp_getMap : iprop%
    (ℓ ↦ assocVal m) ∗
      ((ℓ ↦ assocVal m) -∗ Φ (optIntVal (alookup k m))) ⊢
      WP[codensity tv] (pl% &getMap #loc ℓ #k) @ E {{ Φ }} := by
  iintro ⟨Hl, HΦ⟩
  wp_pures
  wp_bind (pl% !#loc ℓ)
  iapply wp_load
  iframe Hl
  iintro Hl
  wp_steps findList_steps m k
  wp_value
  iapply HΦ $$ Hl

/-- Spec-side `wp_getMap`. -/
theorem wp_getMap_r : iprop%
    ⤇ K.fill (pl% &getMap #loc ℓ #k) ∗ (ℓ ↦ₛ assocVal m) ∗
      (⤇ K.fill (ofVal (optIntVal (alookup k m))) -∗ (ℓ ↦ₛ assocVal m) -∗
        WP[codensity tv] e @ E {{ Φ }}) ⊢
      WP[codensity tv] e @ E {{ Φ }} := by
  iintro ⟨Hj, Hl, Hcnt⟩
  tp_pures
  tp_bind (pl% !#loc ℓ)
  imod step_load $$ [$Hj $Hl] with ⟨Hj, Hl⟩
  tp_bind (pl% &findList {ofVal (assocVal m)} #k)
  imod (step_pure_steps_at _ rfl rfl (findList_steps m k)) $$ Hj with Hj
  iapply Hcnt $$ Hj Hl

/-- `setMap ℓ k y` conses the binding `(k, y)` onto the stored map. -/
theorem wp_setMap : iprop%
    (ℓ ↦ assocVal m) ∗
      ((ℓ ↦ assocVal ((k, y) :: m)) -∗ Φ .unit) ⊢
      WP[codensity tv] (pl% &setMap #loc ℓ #k #y) @ E {{ Φ }} := by
  iintro ⟨Hl, HΦ⟩
  wp_pures
  wp_bind (pl% !#loc ℓ)
  iapply wp_load
  iframe Hl
  iintro Hl
  -- restate the stored literal as `ofVal` of the map value so `wp_store` applies
  rw [show store pl(#loc ℓ) (.inr (.pair (.pair pl(#k) pl(#y)) (ofVal (assocVal m)))) =
    .store pl(#loc ℓ) (ofVal (assocVal ((k, y) :: m))) from rfl]
  iapply wp_store
  iframe Hl
  iexact HΦ

/-- Spec-side `wp_setMap`. -/
theorem wp_setMap_r : iprop%
    ⤇ K.fill (pl% &setMap #loc ℓ #k #y) ∗ (ℓ ↦ₛ assocVal m) ∗
      (⤇ K.fill pl(#()) -∗ (ℓ ↦ₛ assocVal ((k, y) :: m)) -∗
        WP[codensity tv] e @ E {{ Φ }}) ⊢
      WP[codensity tv] e @ E {{ Φ }} := by
  iintro ⟨Hj, Hl, Hcnt⟩
  tp_pures
  tp_bind (pl% !#loc ℓ)
  imod step_load $$ [$Hj $Hl] with ⟨Hj, Hl⟩
  tp_bind (store pl(#loc ℓ) (ofVal (assocVal ((k, y) :: m))))
  imod step_store _ (toVal?_ofVal _) $$ [$Hj $Hl] with ⟨Hj, Hl⟩
  iapply Hcnt $$ Hj Hl

end MapOps

end Switching
end ProbLang
