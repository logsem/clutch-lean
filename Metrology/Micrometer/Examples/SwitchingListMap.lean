module

public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.Couplings.Divergences.Tv
public import Metrology.Micrometer.WpTactics
public import Metrology.Code.Switching
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Lists and association-list maps: specifications

The `PureSteps` facts for the pure list recursions of `Metrology/Code/Switching.lean`,
and `wp`-level specifications (program side and spec side) for the map operations. -/

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.MicrometerWpGS GradedLifting GradedDivergence
open scoped AppGS ENNReal

namespace ProbLang
namespace Switching

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

/-! ## The meta-level model of maps -/

/-- Association-list lookup (leftmost binding wins), mirroring `findList`. -/
def alookup (k : Int) : List (Int × Int) → Option Int
  | [] => none
  | (k', y) :: m => if k' = k then some y else alookup k m

/-- The value of an optional integer result (`NONE` / `SOME #y`). -/
def optIntVal (o : Option Int) : Val rT := Val.option (o.map Val.int)

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

omit [MeasurableSingletonClass rT] in
/-- `findList` computes association-list lookup. -/
theorem findList_steps (m : List (Int × Int)) (k : Int) :
    PureSteps (pl% &findList {Exp.ofVal (assocVal m)} #(.int k))
      (Exp.ofVal (optIntVal (alookup k m) : Val rT)) := by
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
      simp only [beq_self_eq_true]
      pure_steps
    · simp only [assocVal, alookup, hk, ↓reduceIte]
      pure_steps
      have hkl : (BaseLit.int k' == BaseLit.int (rT := rT) k) = false :=
        beq_eq_false_iff_ne.mpr (by simp [hk])
      simp only [hkl]
      pure_step
      pure_step
      exact ih

omit [MeasurableSingletonClass rT] in
/-- `listLength` computes list length. -/
theorem listLength_steps (l : List Int) :
    PureSteps (pl% &listLength {Exp.ofVal (intListVal l)})
      (Exp.ofVal (Val.int l.length : Val rT)) := by
  induction l with
  | nil =>
    simp only [intListVal]
    pure_steps
  | cons n l ih =>
    simp only [intListVal]
    pure_step 5
    refine (PureSteps.fill [EctxItem.binopR .plus _] ih).trans ?_
    pure_steps
    rw [List.length_cons, Nat.cast_succ, add_comm]
    exact PureSteps.refl _

omit [MeasurableSingletonClass rT] in
/-- `listRemoveNth` removes the `i`-th element, returning `SOME (lᵢ, l \ i)`. -/
theorem listRemoveNth_steps (l : List Int) (i : Nat) (hlen : i < l.length) :
    PureSteps (pl% &listRemoveNth {Exp.ofVal (intListVal l)} #(.int i))
      (Exp.ofVal (Val.inr (Val.pair (Val.int l[i]) (intListVal (l.eraseIdx i))) : Val rT)) := by
  induction l generalizing i with
  | nil => simp at hlen
  | cons n l ih =>
    cases i with
    | zero =>
      simp only [intListVal, List.getElem_cons_zero, List.eraseIdx_cons_zero]
      pure_steps
    | succ j =>
      have hj : j < l.length := by simpa using hlen
      simp only [intListVal, List.getElem_cons_succ, List.eraseIdx_cons_succ]
      pure_step 9
      rw [Nat.cast_succ, add_sub_cancel_right]
      refine (PureSteps.fill [EctxItem.case _ _] (ih j hj)).trans ?_
      pure_steps

/-! ## Map operations: `wp` specifications

Rocq source: clutch's `wp_init_map`, `wp_get`, `wp_set` and their `spec_` versions. -/

section MapOps

variable {hlc : HasLC} {GF : BundledGFunctors} [MicrometerGS rT hlc GF] [BudgetCreditGS ℝ≥0∞ GF]

theorem wp_initMap {E : CoPset} {Φ : Val rT → IProp GF} : iprop%
    (∀ ℓ : Loc, (ℓ ↦ (assocVal [] : Val rT)) -∗ Φ (.loc ℓ)) ⊢
    WP[codensity tv] (pl% &initMap #.unit) @ E {{ Φ }} := by
  iintro HΦ
  wp_pures
  rw [show (Exp.alloc (.inl (.lit .unit)) : Exp rT) =
    .alloc (Exp.ofVal (assocVal [])) from rfl]
  iapply wp_alloc
  iexact HΦ

theorem wp_initMap_r {E : CoPset} (K : Ectx rT) {e : Exp rT} {Φ : Val rT → IProp GF} : iprop%
    ⤇ K.fill (pl% &initMap #.unit) ∗
    (∀ ℓ : Loc, ⤇ K.fill pl(#(.loc ℓ)) -∗ (ℓ ↦ₛ (assocVal [] : Val rT)) -∗
      WP[codensity tv] e @ E {{ Φ }}) ⊢
    WP[codensity tv] e @ E {{ Φ }} := by
  iintro ⟨Hj, Hcnt⟩
  tp_pures
  ihave Hj := specProgFrag_reshape
    (e₁ := Ectx.fill K (Exp.alloc (.inl (.lit .unit))))
    (e₂ := K.fill (Exp.alloc (Exp.ofVal (assocVal [])))) rfl $$ Hj
  imod step_alloc_at K (Val.isVal_ofVal _) (vv := assocVal []) rfl $$ Hj with ⟨%ℓ, Hj, Hl⟩
  iapply Hcnt $$ %ℓ Hj Hl

theorem wp_getMap {E : CoPset} (ℓ : Loc) (m : List (Int × Int)) (k : Int)
    {Φ : Val rT → IProp GF} : iprop%
    (ℓ ↦ (assocVal m : Val rT)) ∗
    ((ℓ ↦ (assocVal m : Val rT)) -∗ Φ (optIntVal (alookup k m))) ⊢
    WP[codensity tv] (pl% &getMap #(.loc ℓ) #(.int k)) @ E {{ Φ }} := by
  iintro ⟨Hl, HΦ⟩
  wp_pures
  wp_bind (pl% !#(.loc ℓ))
  iapply wp_load
  iframe Hl
  iintro Hl
  wp_steps findList_steps m k
  wp_value
  iapply HΦ $$ Hl

theorem wp_getMap_r {E : CoPset} (K : Ectx rT) (ℓ : Loc) (m : List (Int × Int)) (k : Int)
    {e : Exp rT} {Φ : Val rT → IProp GF} : iprop%
    ⤇ K.fill (pl% &getMap #(.loc ℓ) #(.int k)) ∗ (ℓ ↦ₛ (assocVal m : Val rT)) ∗
    (⤇ K.fill (Exp.ofVal (optIntVal (alookup k m))) -∗ (ℓ ↦ₛ (assocVal m : Val rT)) -∗
      WP[codensity tv] e @ E {{ Φ }}) ⊢
    WP[codensity tv] e @ E {{ Φ }} := by
  iintro ⟨Hj, Hl, Hcnt⟩
  tp_pures
  tp_bind (pl% !#(.loc ℓ))
  imod step_load $$ [$Hj $Hl] with ⟨Hj, Hl⟩
  tp_bind (pl% &findList {Exp.ofVal (assocVal m)} #(.int k))
  imod (step_pure_steps_at _ rfl rfl (findList_steps m k)) $$ Hj with Hj
  iapply Hcnt $$ Hj Hl

theorem wp_setMap {E : CoPset} (ℓ : Loc) (m : List (Int × Int)) (k y : Int)
    {Φ : Val rT → IProp GF} : iprop%
    (ℓ ↦ (assocVal m : Val rT)) ∗
    ((ℓ ↦ (assocVal ((k, y) :: m) : Val rT)) -∗ Φ .unit) ⊢
    WP[codensity tv] (pl% &setMap #(.loc ℓ) #(.int k) #(.int y)) @ E {{ Φ }} := by
  iintro ⟨Hl, HΦ⟩
  wp_pures
  wp_bind (pl% !#(.loc ℓ))
  iapply wp_load
  iframe Hl
  iintro Hl
  rw [show (Exp.store pl(#(.loc ℓ))
      (.inr (.pair (.pair pl(#(.int k)) pl(#(.int y))) (Exp.ofVal (assocVal m)))) : Exp rT) =
    .store pl(#(.loc ℓ)) (Exp.ofVal (assocVal ((k, y) :: m))) from rfl]
  iapply wp_store
  iframe Hl
  iexact HΦ

theorem wp_setMap_r {E : CoPset} (K : Ectx rT) (ℓ : Loc) (m : List (Int × Int)) (k y : Int)
    {e : Exp rT} {Φ : Val rT → IProp GF} : iprop%
    ⤇ K.fill (pl% &setMap #(.loc ℓ) #(.int k) #(.int y)) ∗
      (ℓ ↦ₛ (assocVal m : Val rT)) ∗
    (⤇ K.fill pl(#(.unit)) -∗ (ℓ ↦ₛ (assocVal ((k, y) :: m) : Val rT)) -∗
      WP[codensity tv] e @ E {{ Φ }}) ⊢
    WP[codensity tv] e @ E {{ Φ }} := by
  iintro ⟨Hj, Hl, Hcnt⟩
  tp_pures
  tp_bind (pl% !#(.loc ℓ))
  imod step_load $$ [$Hj $Hl] with ⟨Hj, Hl⟩
  tp_bind (Exp.store pl(#(.loc ℓ)) (Exp.ofVal (assocVal ((k, y) :: m))))
  imod step_store _ (Val.isVal_ofVal _) (Exp.toVal?_ofVal _) $$ [$Hj $Hl] with ⟨Hj, Hl⟩
  iapply Hcnt $$ Hj Hl

end MapOps

end Switching
end ProbLang
