module

public import Metrology.Micrometer.Examples.SwitchingListMap
public import Metrology.Micrometer.CouplingRules
import Metrology.ProbLang.Syntax.Notation
import Mathlib.Data.List.GetD

@[expose] public section

/-! # Specifications of the random function and random permutation

Specs of `Code/Switching`: representation predicates, creation, queries, and the fresh-query
coupling `wp_rfQuery_prpQuery_fresh` that costs `m.length / N`. Rocq source:
clutch's `is_random_function`/`is_prp` and their query lemmas
(`theories/approxis/examples/{prf,prp}.v`). -/

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.MicrometerWpGS GradedLifting GradedDivergence
open scoped AppGS ENNReal

namespace ProbLang
namespace Switching

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

/-! ## Closure values -/

/-- The random-function query closure, as a value. -/
def rfQueryV (N : Int) (ℓ : Loc) : Val rT :=
  ⟨rfQuery N ℓ, .lam (by is_lc), by is_lc⟩

/-- The random-permutation query closure, as a value. -/
def prpQueryV (ℓm ℓfv : Loc) : Val rT :=
  ⟨prpQuery ℓm ℓfv, .lam (by is_lc), by is_lc⟩

section PRP

variable {hlc : HasLC} {GF : BundledGFunctors} [MicrometerGS rT hlc GF] [BudgetCreditGS ℝ≥0∞ GF]

/-! ## Representation predicates -/

/-- `f` is an idealised random function with output space `[0, N)` and memo table `m`
(program side). -/
def isRandomFunction (N : Int) (f : Val rT) (m : List (Int × Int)) : IProp GF := iprop%
  ∃ ℓ : Loc, ⌜f = rfQueryV N ℓ⌝ ∗ (ℓ ↦ (assocVal m : Val rT))

/-- Spec-side `isRandomFunction`. -/
def isSRandomFunction (N : Int) (f : Val rT) (m : List (Int × Int)) : IProp GF := iprop%
  ∃ ℓ : Loc, ⌜f = rfQueryV N ℓ⌝ ∗ (ℓ ↦ₛ (assocVal m : Val rT))

/-- The pure permutation invariant: the sampled values `m.map (·.2)` together with the
fresh list `r` are a permutation of `[0, N)`. -/
def prpPerm (N : Int) (m : List (Int × Int)) (r : List Int) : Prop :=
  (m.map Prod.snd ++ r).Perm ((List.range N.toNat).map Int.ofNat)

/-- `f` is an idealised random permutation of `[0, N)` with memo table `m` and fresh
list `r` (program side). -/
def isPRP (N : Int) (f : Val rT) (m : List (Int × Int)) (r : List Int) : IProp GF := iprop%
  ∃ (ℓm ℓfv : Loc), ⌜f = prpQueryV ℓm ℓfv⌝ ∗ ⌜prpPerm N m r⌝ ∗
    (ℓm ↦ (assocVal m : Val rT)) ∗ (ℓfv ↦ (intListVal r : Val rT))

/-- Spec-side `isPRP`. -/
def isSPRP (N : Int) (f : Val rT) (m : List (Int × Int)) (r : List Int) : IProp GF := iprop%
  ∃ (ℓm ℓfv : Loc), ⌜f = prpQueryV ℓm ℓfv⌝ ∗ ⌜prpPerm N m r⌝ ∗
    (ℓm ↦ₛ (assocVal m : Val rT)) ∗ (ℓfv ↦ₛ (intListVal r : Val rT))

/-! ## Creation -/

/-- Creating a random function (program side). -/
theorem wp_randomFunction {E : CoPset} (N : Int) {Φ : Val rT → IProp GF} : iprop%
    (∀ f, isRandomFunction N f [] -∗ Φ f) ⊢
    WP[codensity tv] (randomFunction N) @ E {{ Φ }} := by
  iintro HΦ
  wp_bind (pl% &initMap #.unit)
  iapply wp_initMap
  iintro %ℓ Hl
  wp_pures
  wp_value_at (rfQueryV N ℓ)
  iapply HΦ
  iunfold isRandomFunction
  iexists ℓ
  iframe Hl
  ipureintro
  rfl

/-- Creating a random permutation (program side). -/
theorem wp_randomPermutation {E : CoPset} (N : Int) {Φ : Val rT → IProp GF} : iprop%
    (∀ f, isPRP N f [] ((List.range N.toNat).map Int.ofNat) -∗ Φ f) ⊢
    WP[codensity tv] (randomPermutation N) @ E {{ Φ }} := by
  iintro HΦ
  wp_bind (Exp.alloc (Exp.ofVal (intListVal ((List.range N.toNat).map Int.ofNat))))
  wp_alloc_at (intListVal ((List.range N.toNat).map Int.ofNat))
  iintro %ℓfv Hfv
  wp_pures
  wp_bind (pl% alloc(inl(#.unit)))
  wp_alloc_at (assocVal [])
  iintro %ℓm Hm
  wp_pures
  wp_value_at (prpQueryV ℓm ℓfv)
  iapply HΦ
  iunfold isPRP
  iexists ℓm, ℓfv
  iframe Hm Hfv
  ipureintro
  exact ⟨rfl, List.Perm.refl _⟩

/-- Creating a random function (spec side). -/
theorem wp_randomFunction_r {E : CoPset} (K : Ectx rT) (N : Int) {e : Exp rT}
    {Φ : Val rT → IProp GF} : iprop%
    ⤇ K.fill (randomFunction N) ∗
    (∀ f, ⤇ K.fill (Exp.ofVal f) -∗ isSRandomFunction N f [] -∗ WP[codensity tv] e @ E {{ Φ }}) ⊢
    WP[codensity tv] e @ E {{ Φ }} := by
  iintro ⟨Hj, Hcnt⟩
  tp_bind (pl% &initMap #.unit)
  iapply wp_initMap_r
  iframe Hj
  iintro %ℓ Hj Hl
  tp_pures
  tp_bind (Exp.ofVal (rfQueryV N ℓ))
  iapply Hcnt $$ %(rfQueryV N ℓ) Hj
  iunfold isSRandomFunction
  iexists ℓ
  iframe Hl
  ipureintro
  rfl

/-- Creating a random permutation (spec side). -/
theorem wp_randomPermutation_r {E : CoPset} (K : Ectx rT) (N : Int) {e : Exp rT}
    {Φ : Val rT → IProp GF} : iprop%
    ⤇ K.fill (randomPermutation N) ∗
    (∀ f, ⤇ K.fill (Exp.ofVal f) -∗
      isSPRP N f [] ((List.range N.toNat).map Int.ofNat) -∗ WP[codensity tv] e @ E {{ Φ }}) ⊢
    WP[codensity tv] e @ E {{ Φ }} := by
  iintro ⟨Hj, Hcnt⟩
  tp_bind (Exp.alloc (Exp.ofVal (intListVal ((List.range N.toNat).map Int.ofNat))))
  imod step_alloc_at _ (Val.isVal_ofVal _)
    (vv := intListVal ((List.range N.toNat).map Int.ofNat)) rfl $$ Hj with ⟨%ℓfv, Hj, Hfv⟩
  tp_pures
  tp_bind (Exp.alloc (Exp.ofVal (assocVal [])))
  imod step_alloc_at _ (Val.isVal_ofVal _) (vv := assocVal []) rfl $$ Hj with ⟨%ℓm, Hj, Hm⟩
  tp_pures
  tp_bind (Exp.ofVal (prpQueryV ℓm ℓfv))
  iapply Hcnt $$ %(prpQueryV ℓm ℓfv) Hj
  iunfold isSPRP
  iexists ℓm, ℓfv
  iframe Hm Hfv
  ipureintro
  exact ⟨rfl, List.Perm.refl _⟩

/-! ## Queries at known inputs -/

/-- Query a random function at a previously-queried input (program side). -/
theorem wp_rfQuery_prev {E : CoPset} (N : Int) (ℓ : Loc) (m : List (Int × Int))
    (n y : Int) (hlk : alookup n m = some y) {Φ : Val rT → IProp GF} : iprop%
    (ℓ ↦ (assocVal m : Val rT)) ∗ ((ℓ ↦ (assocVal m : Val rT)) -∗ Φ (.int y)) ⊢
    WP[codensity tv] (pl% {rfQuery N ℓ} #(.int n)) @ E {{ Φ }} := by
  iintro ⟨Hl, HΦ⟩
  wp_pure 1
  wp_bind (pl% &getMap #(.loc ℓ) #(.int n))
  iapply wp_getMap
  iframe Hl
  iintro Hl
  simp only [hlk, optIntVal, Option.map]
  wp_pures
  wp_value
  iapply HΦ $$ Hl

/-- Query a random function at a previously-queried input (spec side). -/
theorem wp_rfQuery_prev_r {E : CoPset} (K : Ectx rT) (N : Int) (ℓ : Loc)
    (m : List (Int × Int)) (n y : Int) (hlk : alookup n m = some y)
    {e : Exp rT} {Φ : Val rT → IProp GF} : iprop%
    ⤇ K.fill (pl% {rfQuery N ℓ} #(.int n)) ∗ (ℓ ↦ₛ (assocVal m : Val rT)) ∗
    (⤇ K.fill pl(#(.int y)) -∗ (ℓ ↦ₛ (assocVal m : Val rT)) -∗ WP[codensity tv] e @ E {{ Φ }}) ⊢
    WP[codensity tv] e @ E {{ Φ }} := by
  iintro ⟨Hj, Hl, Hcnt⟩
  tp_pure
  tp_bind (pl% &getMap #(.loc ℓ) #(.int n))
  iapply wp_getMap_r
  iframe Hj Hl
  simp only [hlk, optIntVal, Option.map]
  iintro Hj Hl
  tp_pures
  iapply Hcnt $$ Hj Hl

/-- Query a random permutation at a previously-queried input (program side). -/
theorem wp_prpQuery_prev {E : CoPset} (ℓm ℓfv : Loc) (m : List (Int × Int))
    (n y : Int) (hlk : alookup n m = some y) {Φ : Val rT → IProp GF} : iprop%
    (ℓm ↦ (assocVal m : Val rT)) ∗
    ((ℓm ↦ (assocVal m : Val rT)) -∗ Φ (.int y)) ⊢
    WP[codensity tv] (pl% {prpQuery ℓm ℓfv} #(.int n)) @ E {{ Φ }} := by
  iintro ⟨Hl, HΦ⟩
  wp_pure 1
  wp_bind (pl% &getMap #(.loc ℓm) #(.int n))
  iapply wp_getMap
  iframe Hl
  iintro Hl
  simp only [hlk, optIntVal, Option.map]
  wp_pures
  wp_value
  iapply HΦ $$ Hl

/-- Query a random permutation at a previously-queried input (spec side). -/
theorem wp_prpQuery_prev_r {E : CoPset} (K : Ectx rT) (ℓm ℓfv : Loc)
    (m : List (Int × Int)) (n y : Int) (hlk : alookup n m = some y)
    {e : Exp rT} {Φ : Val rT → IProp GF} : iprop%
    ⤇ K.fill (pl% {prpQuery ℓm ℓfv} #(.int n)) ∗ (ℓm ↦ₛ (assocVal m : Val rT)) ∗
    (⤇ K.fill pl(#(.int y)) -∗ (ℓm ↦ₛ (assocVal m : Val rT)) -∗ WP[codensity tv] e @ E {{ Φ }}) ⊢
    WP[codensity tv] e @ E {{ Φ }} := by
  iintro ⟨Hj, Hl, Hcnt⟩
  tp_pure
  tp_bind (pl% &getMap #(.loc ℓm) #(.int n))
  iapply wp_getMap_r
  iframe Hj Hl
  simp only [hlk, optIntVal, Option.map]
  iintro Hj Hl
  tp_pures
  iapply Hcnt $$ Hj Hl

/-! ## Pure bookkeeping for the fresh-query coupling -/

/-- The fresh list has no duplicates. -/
theorem prpPerm_nodup {N : Int} {m : List (Int × Int)} {r : List Int}
    (h : prpPerm N m r) : r.Nodup :=
  (h.nodup_iff.mpr (List.nodup_range.map fun _ _ hab => Int.ofNat.inj hab)).of_append_right

/-- Every element of the fresh list lies in `[0, N)`. -/
theorem prpPerm_mem_range {N : Int} {m : List (Int × Int)} {r : List Int}
    (h : prpPerm N m r) {y : Int} (hy : y ∈ r) : 0 ≤ y ∧ y < N := by
  have hy' : y ∈ (List.range N.toNat).map Int.ofNat :=
    h.mem_iff.mp (List.mem_append_right _ hy)
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy'
  have := List.mem_range.mp hj
  simp only [Int.ofNat_eq_natCast]
  omega

/-- Map size and fresh-list size add up to `N`. -/
theorem prpPerm_length {N : Int} {m : List (Int × Int)} {r : List Int}
    (h : prpPerm N m r) : m.length + r.length = N.toNat := by
  simpa using h.length_eq

/-- The fresh list is nonempty at a fresh in-range query: the map's keys are distinct
and in `[0, N)`, so they cannot already cover all of `[0, N)`. -/
theorem prpPerm_fresh_nonempty {N : Int} {m : List (Int × Int)} {r : List Int}
    (h : prpPerm N m r) (n : Int) (hn : 0 ≤ n ∧ n < N)
    (hkeys : ∀ k ∈ m.map Prod.fst, 0 ≤ k ∧ k < N) (hnodup : (m.map Prod.fst).Nodup)
    (hfresh : n ∉ m.map Prod.fst) : 0 < r.length := by
  by_contra hr
  have hlenm : m.length = N.toNat := by have := prpPerm_length h; omega
  have hsub : (n :: m.map Prod.fst) ⊆ (List.range N.toNat).map Int.ofNat := fun k hk => by
    have : 0 ≤ k ∧ k < N := (List.mem_cons.mp hk).elim (· ▸ hn) (hkeys k)
    exact List.mem_map.mpr ⟨k.toNat, List.mem_range.mpr (by omega),
      by simp only [Int.ofNat_eq_natCast]; omega⟩
  have hnd : (n :: m.map Prod.fst).Nodup := List.nodup_cons.mpr ⟨hfresh, hnodup⟩
  have hle := (List.subperm_of_subset hnd hsub).length_le
  simp [hlenm] at hle

/-- Memoising a sampled fresh value preserves the permutation invariant. -/
theorem prpPerm_insert {N : Int} {m : List (Int × Int)} {r : List Int}
    (h : prpPerm N m r) (n : Int) {y : Int} (hy : y ∈ r) :
    prpPerm N ((n, y) :: m) (r.erase y) := by
  refine List.Perm.trans ?_ h
  simp only [List.map_cons, List.cons_append]
  exact List.perm_middle.symm.trans
    (List.Perm.append_left _ (List.perm_cons_erase hy).symm)

/-- The side conditions of the injective `rand`/`rand` coupling along `i ↦ r[i]`. -/
theorem prpPerm_coupling_conds {N n : Int} {m : List (Int × Int)} {r : List Int}
    {ε : ENNReal} (hn : 0 ≤ n ∧ n < N) (hfresh : alookup n m = none) (hperm : prpPerm N m r)
    (hkeys : ∀ k ∈ m.map Prod.fst, 0 ≤ k ∧ k < N) (hnodup : (m.map Prod.fst).Nodup)
    (hε : (m.length : ENNReal) / (N.toNat : ENNReal) ≤ ε) :
    (0 : Int) < (r.length : Int) ∧ (r.length : Int) ≤ N ∧
    (∀ i, 0 ≤ i → i < (r.length : Int) → 0 ≤ r.getD i.toNat 0 ∧ r.getD i.toNat 0 < N) ∧
    (∀ i₁ i₂, 0 ≤ i₁ → i₁ < (r.length : Int) → 0 ≤ i₂ → i₂ < (r.length : Int) →
      r.getD i₁.toNat 0 = r.getD i₂.toNat 0 → i₁ = i₂) ∧
    ((N - (r.length : Int)).toNat : ENNReal) / (N.toNat : ENNReal) ≤ ε := by
  have hrpos := prpPerm_fresh_nonempty hperm n hn hkeys hnodup (alookup_eq_none_iff.mp hfresh)
  have hlen := prpPerm_length hperm
  refine ⟨by exact_mod_cast hrpos, by omega, fun i _ hlt => ?_, fun i₁ i₂ _ h₁ _ h₂ heq => ?_, ?_⟩
  · have hi : i.toNat < r.length := by omega
    rw [List.getD_eq_getElem r 0 hi]
    exact prpPerm_mem_range hperm (r.getElem_mem hi)
  · have hi₁ : i₁.toNat < r.length := by omega
    have hi₂ : i₂.toNat < r.length := by omega
    rw [List.getD_eq_getElem r 0 hi₁, List.getD_eq_getElem r 0 hi₂] at heq
    have := ((prpPerm_nodup hperm).getElem_inj_iff).mp heq
    omega
  · rwa [show (N - (r.length : Int)).toNat = m.length by omega]

/-! ## The coupled fresh query

At a fresh input, the random function's `rand N` draw is coupled with the permutation's
`rand r.length` draw along `i ↦ r[i]`, for `m.length / N` credits. Port of the fresh-query case
of clutch's `wp_prf_prp_couple_eq_err`. -/

/-- A fresh query to the random function against the random permutation costs `m.length / N`. -/
theorem wp_rfQuery_prpQuery_fresh {E : CoPset} (K : Ectx rT) (N : Int) (ℓ ℓm ℓfv : Loc)
    (m : List (Int × Int)) (r : List Int) (n : Int) (ε : ENNReal)
    (hn : 0 ≤ n ∧ n < N) (hfresh : alookup n m = none) (hperm : prpPerm N m r)
    (hkeys : ∀ k ∈ m.map Prod.fst, 0 ≤ k ∧ k < N) (hnodup : (m.map Prod.fst).Nodup)
    (hε : (m.length : ENNReal) / (N.toNat : ENNReal) ≤ ε)
    {Φ : Val rT → IProp GF} : iprop%
    ⤇ K.fill (pl% {prpQuery ℓm ℓfv} #(.int n)) ∗ ↯b ε ∗
    (ℓ ↦ (assocVal m : Val rT)) ∗ (ℓm ↦ₛ (assocVal m : Val rT)) ∗
    (ℓfv ↦ₛ (intListVal r : Val rT)) ∗
    (∀ y, ⌜y ∈ r⌝ -∗ ⤇ K.fill pl(#(.int y)) -∗
      (ℓ ↦ (assocVal ((n, y) :: m) : Val rT)) -∗
      (ℓm ↦ₛ (assocVal ((n, y) :: m) : Val rT)) -∗
      (ℓfv ↦ₛ (intListVal (r.erase y) : Val rT)) -∗ Φ (.int y)) ⊢
    WP[codensity tv] (pl% {rfQuery N ℓ} #(.int n)) @ E {{ Φ }} := by
  obtain ⟨hrlen, hRle, hdom, hinj, hεle⟩ :=
    prpPerm_coupling_conds hn hfresh hperm hkeys hnodup hε
  iintro ⟨Hj, Herr, Hl, Hm, Hfv, Hcnt⟩
  -- program side: fresh lookup
  wp_pure 1
  wp_bind (pl% &getMap #(.loc ℓ) #(.int n))
  iapply wp_getMap
  iframe Hl
  iintro Hl
  simp only [hfresh, optIntVal, Option.map]
  wp_pures
  -- spec side: fresh lookup and fresh-list length
  tp_pure
  tp_bind (pl% &getMap #(.loc ℓm) #(.int n))
  iapply wp_getMap_r
  iframe Hj Hm
  simp only [hfresh, optIntVal, Option.map]
  iintro Hj Hm
  tp_pures
  tp_bind (pl% !#(.loc ℓfv))
  imod step_load $$ [$Hj $Hfv] with ⟨Hj, Hfv⟩
  tp_bind (pl% &listLength {Exp.ofVal (intListVal r)})
  imod (step_pure_steps_at _ rfl rfl (listLength_steps r)) $$ Hj with Hj
  tp_pures
  wp_bind (pl% rand(#(.int N), #.unit))
  tp_bind (pl% rand(#(.int (r.length : Int)), #.unit))
  iapply wp_couple_rand_rand_rev_inj_tv N (r.length : Int) (fun i => r.getD i.toNat 0) ε
    hdom hinj hrlen hRle hεle
  iframe Hj Herr
  iintro %i ⟨%hi0, %hiR⟩ Hj
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hi0
  have hjN : j < r.length := by omega
  rw [show r.getD (j : Int).toNat 0 = r[j] by simp [hjN]]
  -- spec side: pop the sampled index and memoise it
  tp_pures
  tp_bind (pl% !#(.loc ℓfv))
  imod step_load $$ [$Hj $Hfv] with ⟨Hj, Hfv⟩
  tp_bind (pl% &listRemoveNth {Exp.ofVal (intListVal r)} #(.int j))
  imod (step_pure_steps_at _ rfl rfl (listRemoveNth_steps r j hjN)) $$ Hj with Hj
  tp_pures
  tp_bind (pl% !#(.loc ℓm))
  imod step_load $$ [$Hj $Hm] with ⟨Hj, Hm⟩
  tp_bind (Exp.store pl(#(.loc ℓm)) (Exp.ofVal (assocVal ((n, r[j]) :: m))))
  imod step_store _ (Val.isVal_ofVal _) (Exp.toVal?_ofVal _) $$ [$Hj $Hm] with ⟨Hj, Hm⟩
  tp_pures
  tp_bind (Exp.store pl(#(.loc ℓfv)) (Exp.ofVal (intListVal (r.eraseIdx j))))
  imod step_store _ (Val.isVal_ofVal _) (Exp.toVal?_ofVal _) $$ [$Hj $Hfv] with ⟨Hj, Hfv⟩
  tp_pures
  -- program side: memoise and return
  wp_pure 1
  wp_bind (pl% &setMap #(.loc ℓ) #(.int n) #(.int r[j]))
  iapply wp_setMap
  iframe Hl
  iintro Hl
  wp_pures
  wp_value
  rw [← (prpPerm_nodup hperm).erase_getElem j hjN]
  iapply Hcnt $$ %(r[j]) %(r.getElem_mem hjN) Hj Hl Hm Hfv

/-- The mirror of `wp_rfQuery_prpQuery_fresh`: the random permutation on the program
side against the random function on the spec side, coupling the permutation's index
draw with `rand N` along `i ↦ r[i]`. -/
theorem wp_prpQuery_rfQuery_fresh {E : CoPset} (K : Ectx rT) (N : Int) (ℓ ℓm ℓfv : Loc)
    (m : List (Int × Int)) (r : List Int) (n : Int) (ε : ENNReal)
    (hn : 0 ≤ n ∧ n < N) (hfresh : alookup n m = none) (hperm : prpPerm N m r)
    (hkeys : ∀ k ∈ m.map Prod.fst, 0 ≤ k ∧ k < N) (hnodup : (m.map Prod.fst).Nodup)
    (hε : (m.length : ENNReal) / (N.toNat : ENNReal) ≤ ε)
    {Φ : Val rT → IProp GF} : iprop%
    ⤇ K.fill (pl% {rfQuery N ℓ} #(.int n)) ∗ ↯b ε ∗
    (ℓm ↦ (assocVal m : Val rT)) ∗ (ℓfv ↦ (intListVal r : Val rT)) ∗
    (ℓ ↦ₛ (assocVal m : Val rT)) ∗
    (∀ y, ⌜y ∈ r⌝ -∗ ⤇ K.fill pl(#(.int y)) -∗
      (ℓm ↦ (assocVal ((n, y) :: m) : Val rT)) -∗
      (ℓfv ↦ (intListVal (r.erase y) : Val rT)) -∗
      (ℓ ↦ₛ (assocVal ((n, y) :: m) : Val rT)) -∗ Φ (.int y)) ⊢
    WP[codensity tv] (pl% {prpQuery ℓm ℓfv} #(.int n)) @ E {{ Φ }} := by
  obtain ⟨hrlen, hRle, hdom, hinj, hεle⟩ :=
    prpPerm_coupling_conds hn hfresh hperm hkeys hnodup hε
  iintro ⟨Hj, Herr, Hm, Hfv, Hl, Hcnt⟩
  -- program side: fresh lookup and fresh-list length
  wp_pure 1
  wp_bind (pl% &getMap #(.loc ℓm) #(.int n))
  iapply wp_getMap
  iframe Hm
  iintro Hm
  simp only [hfresh, optIntVal, Option.map]
  wp_pures
  wp_bind (pl% !#(.loc ℓfv))
  iapply wp_load
  iframe Hfv
  iintro Hfv
  wp_bind (pl% &listLength {Exp.ofVal (intListVal r)})
  wp_steps (listLength_steps r)
  wp_value
  wp_pures
  -- spec side: fresh lookup
  tp_pure
  tp_bind (pl% &getMap #(.loc ℓ) #(.int n))
  iapply wp_getMap_r
  iframe Hj Hl
  simp only [hfresh, optIntVal, Option.map]
  iintro Hj Hl
  tp_pures
  wp_bind (pl% rand(#(.int (r.length : Int)), #.unit))
  tp_bind (pl% rand(#(.int N), #.unit))
  iapply wp_couple_rand_rand_inj_tv (r.length : Int) N (fun i => r.getD i.toNat 0) ε
    hdom hinj hrlen hRle hεle
  iframe Hj Herr
  iintro %i ⟨%hi0, %hiR⟩ Hj
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hi0
  have hjN : j < r.length := by omega
  rw [show r.getD (j : Int).toNat 0 = r[j] by simp [hjN]]
  -- spec side: memoise
  tp_pures
  tp_bind (pl% !#(.loc ℓ))
  imod step_load $$ [$Hj $Hl] with ⟨Hj, Hl⟩
  tp_bind (Exp.store pl(#(.loc ℓ)) (Exp.ofVal (assocVal ((n, r[j]) :: m))))
  imod step_store _ (Val.isVal_ofVal _) (Exp.toVal?_ofVal _) $$ [$Hj $Hl] with ⟨Hj, Hl⟩
  tp_pures
  -- program side: pop the sampled index and memoise it
  wp_pures
  wp_bind (pl% !#(.loc ℓfv))
  iapply wp_load
  iframe Hfv
  iintro Hfv
  wp_bind (pl% &listRemoveNth {Exp.ofVal (intListVal r)} #(.int j))
  wp_steps (listRemoveNth_steps r j hjN)
  wp_value
  wp_pure 3
  wp_bind (pl% &setMap #(.loc ℓm) #(.int n) #(.int r[j]))
  iapply wp_setMap
  iframe Hm
  iintro Hm
  wp_pures
  wp_bind (Exp.store pl(#(.loc ℓfv)) (Exp.ofVal (intListVal (r.eraseIdx j))))
  iapply wp_store
  iframe Hfv
  iintro Hfv
  wp_pures
  wp_value
  rw [← (prpPerm_nodup hperm).erase_getElem j hjN]
  iapply Hcnt $$ %(r[j]) %(r.getElem_mem hjN) Hj Hm Hfv Hl

end PRP
end Switching
end ProbLang
