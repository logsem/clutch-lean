module

public import Metrology.Micrometer.Examples.SwitchingPRP
public import Metrology.Micrometer.Adequacy
public import Metrology.Micrometer.AdequacyRel
public import Metrology.Couplings.Divergences.Tv
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

@[expose] public section

/-! # The weak PRF/PRP switching lemma (clutch `approxis/examples/prp_prf_weak.v`)

`Q` uniform queries to a lazy random function and to a lazy random permutation over `[0, N)` are
indistinguishable up to the birthday bound `Q (Q - 1) / (2 N)` (`weak_switching_lemma`). -/

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.MicrometerWpGS GradedLifting GradedDivergence
open scoped AppGS ENNReal

namespace ProbLang
namespace Switching

open ProbLang.Exp (ofVal alloc store toVal?_ofVal)
open ProbLang.Val (isVal_ofVal)
open Finset (range sum_le_sum_of_subset range_mono sum_range_succ' sum_congr sum_range_id)
open Nat (cast_sum cast_succ cast_zero le_succ div_mul_le_self)
open Prod (fst)
open ENNReal (div_le_div_right le_div_iff_mul_le)
open List (length_cons length_nil mem_cons nodup_cons)
open BudgetCredit (weaken split)
open _root_.Int (toNat_of_nonneg)

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

/-! ## The error budget -/

section
variable (N : Int)

/-- Total error of `q` coupled rounds from `c` memoised entries: `∑_{i<q} (c + i) / N`, since
round `i` meets a collision with probability `(c + i) / N`. -/
noncomputable def loopErr (c q : Nat) : ENNReal :=
  (∑ i ∈ range q, ((c + i : Nat) : ENNReal)) / (N.toNat : ENNReal)

theorem loopErr_mono (c : Nat) {q q' : Nat} (h : q ≤ q') : loopErr N c q ≤ loopErr N c q' :=
  div_le_div_right (sum_le_sum_of_subset (range_mono h)) _

/-- The first round costs `c / N` and the remaining rounds start from `c + 1` entries. -/
theorem loopErr_succ (c q : Nat) :
    loopErr N c (q + 1) = (c : ENNReal) / (N.toNat : ENNReal) + loopErr N (c + 1) q := by
  simp only [loopErr, sum_range_succ', ← ENNReal.add_div]
  rw [add_comm]
  congr 2
  exact sum_congr rfl fun i _ => by rw [← add_assoc, add_right_comm]

/-- The loop error is at most the birthday bound `q (q - 1) / (2 N)`. -/
theorem loopErr_zero_le_birthday (q : Nat) :
    loopErr N 0 q ≤ ((q * (q - 1) : ℕ) : ENNReal) / (2 * (N.toNat : ENNReal)) := by
  simp only [loopErr, Nat.zero_add]
  rw [← cast_sum, sum_range_id]
  calc ((q * (q - 1) / 2 : ℕ) : ENNReal) / (N.toNat : ENNReal)
      ≤ (((q * (q - 1) : ℕ) : ENNReal) / 2) / (N.toNat : ENNReal) := by
        gcongr
        rw [le_div_iff_mul_le (.inl (by norm_num)) (.inl (by norm_num))]
        exact_mod_cast div_mul_le_self _ 2
    _ = ((q * (q - 1) : ℕ) : ENNReal) / (2 * (N.toNat : ENNReal)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
        ENNReal.mul_inv (.inl (by norm_num)) (.inl (by norm_num)), mul_assoc]

end

/-! ## The coupled games -/

section Games

variable {hlc : HasLC} {GF : BundledGFunctors} [MicrometerGS rT hlc GF] [BudgetCreditGS ℝ≥0∞ GF]
  {E : CoPset} {Φ : Val rT → _} (K : Ectx rT) (N : Int)
local bi IProp GF

/-! ### One round: recording the answer -/

/-- The tail of a round: record `(n, y)` in both result lists, then run the next round.
`hloop` matches the goal's unfolded `loop` against `wLoop N` by `rfl`, so callers just `iapply`. -/
theorem wp_wLoop_record {K : Ectx rT} {N : Int} {loop : Exp rT} {fL fS : Val rT} {resL resS : Loc}
    {q : Nat} {n y : Int} {acc : List (Int × Int)} (hloop : loop = wLoop N := by rfl) : iprop%
    ⤇ K.fill (pl% (#loc resS ← inr(((#n, #y), !#loc resS));
      {loop} {fS.fst} #loc resS (#int (↑(q + 1)) - #1))) ∗
    (resL ↦ assocVal acc) ∗ (resS ↦ₛ assocVal acc) ∗
    (⤇ K.fill (pl% {wLoop N} {ofVal fS} #loc resS #int q) -∗
      (resL ↦ assocVal ((n, y) :: acc)) -∗
      (resS ↦ₛ assocVal ((n, y) :: acc)) -∗
      WP[codensity tv] (pl% {wLoop N} {ofVal fL} #loc resL #int q) @ E {{ Φ }}) ⊢
    WP[codensity tv] (pl% (#loc resL ← inr(((#n, #y), !#loc resL));
      {loop} {fL.fst} #loc resL (#int (↑(q + 1)) - #1))) @ E {{ Φ }} := by
  subst hloop
  iintro ⟨Hj, HresL, HresS, Hcnt⟩
  tp_bind (pl% !#loc resS)
  imod step_load $$ [$Hj $HresS] with ⟨Hj, HresS⟩
  tp_bind (store pl(#loc resS) (ofVal (assocVal ((n, y) :: acc))))
  imod step_store _ (isVal_ofVal _) (toVal?_ofVal _) $$ [$Hj $HresS] with ⟨Hj, HresS⟩
  tp_pure
  tp_pure
  wp_bind (pl% !#loc resL)
  iapply wp_load
  iframe HresL
  iintro HresL
  wp_bind (store pl(#loc resL) (ofVal (assocVal ((n, y) :: acc))))
  iapply wp_store
  iframe HresL
  iintro HresL
  wp_pure 1
  wp_pure 1
  rw [cast_succ, add_sub_cancel_right]
  tp_bind (pl% {wLoop N} {ofVal fS} #loc resS #int q)
  wp_show (pl% {wLoop N} {ofVal fL} #loc resL #int q)
  iapply Hcnt $$ Hj HresL HresS

/-! ### The loop, random function against random permutation -/

/-- `q` coupled rounds of the loop on `rfQuery` against `prpQuery` cost `loopErr`.

Loop invariant: both maps hold the same memo table `m`, `r` lists the values the permutation has
not yet used (`prpPerm`), and the keys of `m` are distinct and in `[0, N)`. A cached input costs
nothing; a fresh one costs `|m| / N` (`wp_rfQuery_prpQuery_fresh`), so `q` rounds cost
`loopErr N |m| q`. -/
theorem wp_wLoop (ℓ ℓm ℓfv resL resS : Loc) (q : Nat) (m : List (Int × Int)) (r : List Int)
    (acc : List (Int × Int)) (hperm : prpPerm N m r) (hkeys : ∀ k ∈ m.map fst, 0 ≤ k ∧ k < N)
    (hnodup : (m.map fst).Nodup) (hN : 0 < N) : iprop%
    ⤇ K.fill (pl% {wLoop N} {ofVal (prpQueryV ℓm ℓfv)} #loc resS #int q) ∗
      ↯b (loopErr N m.length q) ∗
      (ℓ ↦ assocVal m) ∗ (ℓm ↦ₛ assocVal m) ∗
      (ℓfv ↦ₛ intListVal r) ∗
      (resL ↦ assocVal acc) ∗ (resS ↦ₛ assocVal acc) ∗
      (∀ acc' : List (Int × Int), ⤇ K.fill pl(#()) -∗
        (resL ↦ assocVal acc') -∗ (resS ↦ₛ assocVal acc') -∗
        Φ .unit) ⊢
      WP[codensity tv] (pl% {wLoop N} {ofVal (rfQueryV N ℓ)} #loc resL #int q) @ E {{ Φ }} := by
  induction q generalizing m r acc with
  | zero =>
    iintro ⟨Hj, Herr, Hl, Hm, Hfv, HresL, HresS, Hcnt⟩
    simp only [cast_zero]
    tp_pures
    wp_pures
    wp_value
    iapply Hcnt $$ %acc Hj HresL HresS
  | succ q ih =>
    iintro ⟨Hj, Herr, Hl, Hm, Hfv, HresL, HresS, Hcnt⟩
    wp_pures
    tp_pures
    wp_bind (pl% rand(#N, #()))
    tp_bind (pl% rand(#N, #()))
    iapply wp_couple_rand_rand N (fun n => n) (fun n h1 h2 => ⟨h1, h2⟩)
      (fun mm h1 h2 => ⟨mm, ⟨⟨h1, h2⟩, rfl⟩, fun y hy => hy.2⟩) hN
    iframe Hj
    iintro %n ⟨%hn0, %hnN⟩ Hj
    tp_pure
    tp_bind (pl% {prpQuery ℓm ℓfv} #n)
    wp_pure 1
    wp_bind (pl% {rfQuery N ℓ} #n)
    cases hlk : alookup n m with
    | some y =>
      -- cached input: both sides return the memoised `y`, nothing spent
      ihave Herr := weaken (loopErr_mono N m.length (le_succ q)) $$ Herr
      iapply wp_prpQuery_prev_r _ ℓm ℓfv m n y hlk
      iframe Hj Hm
      iintro Hj Hm
      iapply wp_rfQuery_prev N ℓ m n y hlk
      iframe Hl
      iintro Hl
      tp_pure
      wp_pure 1
      iapply wp_wLoop_record
      iframe Hj HresL HresS
      iintro Hj HresL HresS
      iapply ih m r ((n, y) :: acc) hperm hkeys hnodup
      iframe
    | none =>
      -- fresh input: pay `m.length / N` to couple the draw with the PRP's fresh value
      rw [loopErr_succ]
      ihave ⟨Herr, Herr'⟩ := split $$ Herr
      iapply wp_rfQuery_prpQuery_fresh _ N ℓ ℓm ℓfv m r n
        ((m.length : ENNReal) / (N.toNat : ENNReal)) ⟨hn0, hnN⟩ hlk hperm hkeys hnodup le_rfl
      iframe Hj Herr Hl Hm Hfv
      iintro %y %hyr Hj Hl Hm Hfv
      tp_pure
      wp_pure 1
      iapply wp_wLoop_record
      iframe Hj HresL HresS
      iintro Hj HresL HresS
      iapply ih ((n, y) :: m) (r.erase y) ((n, y) :: acc) (prpPerm_insert hperm n hyr)
        (fun k hk => (mem_cons.mp hk).elim (· ▸ ⟨hn0, hnN⟩) (hkeys k))
        (nodup_cons.mpr ⟨alookup_eq_none_iff.mp hlk, hnodup⟩)
      simp only [length_cons]
      iframe

/-- The program `wPRF` refines the spec `wPRP` up to the loop error. -/
theorem wp_wPRF_wPRP (Q : Int) (hN : 0 < N) (hQ : 0 ≤ Q) (ε : ENNReal)
    (hε : loopErr N 0 Q.toNat ≤ ε) : iprop%
    ⤇ K.fill (wPRP N Q) ∗ ↯b ε ∗
      (∀ v : Val rT, ⤇ K.fill (ofVal v) -∗ Φ v) ⊢
      WP[codensity tv] (wPRF N Q) @ E {{ Φ }} := by
  rw [← toNat_of_nonneg hQ]
  iintro ⟨Hj, Herr, Hcnt⟩
  ihave Herr := weaken hε $$ Herr
  wp_bind (randomFunction N)
  iapply wp_randomFunction
  simp only [isRandomFunction]
  iintro %f ⟨%ℓ, %hf, Hl⟩
  subst hf
  wp_pures
  wp_bind (pl% alloc(inl(#())))
  wp_alloc_at (assocVal ([] : List (Int × Int)))
  iintro %resL HresL
  wp_pure 1
  tp_bind (randomPermutation N)
  iapply wp_randomPermutation_r
  iframe Hj
  simp only [isSPRP]
  iintro %g Hj ⟨%ℓm, %ℓfv, %hg, %hperm, Hm, Hfv⟩
  subst hg
  tp_pures
  tp_bind (alloc (ofVal (assocVal ([] : List (Int × Int)))))
  imod step_alloc_at _ (isVal_ofVal _) (vv := assocVal []) rfl $$ Hj with ⟨%resS, Hj, HresS⟩
  tp_pure
  tp_bind (pl% {wLoop N} {ofVal (prpQueryV ℓm ℓfv)} #loc resS #int Q.toNat)
  wp_bind (pl% {wLoop N} {ofVal (rfQueryV N ℓ)} #loc resL #int Q.toNat)
  iapply wp_wLoop _ N ℓ ℓm ℓfv resL resS Q.toNat [] _ [] hperm (by simp) (by simp) hN
  simp only [length_nil]
  iframe Hj Herr Hl Hm Hfv HresL HresS
  iintro %acc Hj HresL HresS
  tp_pures
  tp_bind (pl% !#loc resS)
  imod step_load $$ [$Hj $HresS] with ⟨Hj, HresS⟩
  wp_pures
  iapply wp_load
  iframe HresL
  iintro HresL
  iapply Hcnt $$ %(assocVal acc) Hj

/-! ### The loop, random permutation against random function -/

/-- `wp_wLoop` with the roles swapped: the random permutation on the program side. -/
theorem wp_wLoop_rev (ℓ ℓm ℓfv resL resS : Loc) (q : Nat) (m : List (Int × Int)) (r : List Int)
    (acc : List (Int × Int)) (hperm : prpPerm N m r) (hkeys : ∀ k ∈ m.map fst, 0 ≤ k ∧ k < N)
    (hnodup : (m.map fst).Nodup) (hN : 0 < N) : iprop%
    ⤇ K.fill (pl% {wLoop N} {ofVal (rfQueryV N ℓ)} #loc resS #int q) ∗
      ↯b (loopErr N m.length q) ∗
      (ℓm ↦ assocVal m) ∗ (ℓfv ↦ intListVal r) ∗
      (ℓ ↦ₛ assocVal m) ∗
      (resL ↦ assocVal acc) ∗ (resS ↦ₛ assocVal acc) ∗
      (∀ acc' : List (Int × Int), ⤇ K.fill pl(#()) -∗
        (resL ↦ assocVal acc') -∗ (resS ↦ₛ assocVal acc') -∗
        Φ .unit) ⊢
      WP[codensity tv] (pl% {wLoop N} {ofVal (prpQueryV ℓm ℓfv)} #loc resL #int q) @ E {{ Φ }} := by
  induction q generalizing m r acc with
  | zero =>
    iintro ⟨Hj, Herr, Hm, Hfv, Hl, HresL, HresS, Hcnt⟩
    simp only [cast_zero]
    tp_pures
    wp_pures
    wp_value
    iapply Hcnt $$ %acc Hj HresL HresS
  | succ q ih =>
    iintro ⟨Hj, Herr, Hm, Hfv, Hl, HresL, HresS, Hcnt⟩
    wp_pures
    tp_pures
    wp_bind (pl% rand(#N, #()))
    tp_bind (pl% rand(#N, #()))
    iapply wp_couple_rand_rand N (fun n => n) (fun n h1 h2 => ⟨h1, h2⟩)
      (fun mm h1 h2 => ⟨mm, ⟨⟨h1, h2⟩, rfl⟩, fun y hy => hy.2⟩) hN
    iframe Hj
    iintro %n ⟨%hn0, %hnN⟩ Hj
    tp_pure
    tp_bind (pl% {rfQuery N ℓ} #n)
    wp_pure 1
    wp_bind (pl% {prpQuery ℓm ℓfv} #n)
    cases hlk : alookup n m with
    | some y =>
      ihave Herr := weaken (loopErr_mono N m.length (le_succ q)) $$ Herr
      iapply wp_rfQuery_prev_r _ N ℓ m n y hlk
      iframe Hj Hl
      iintro Hj Hl
      iapply wp_prpQuery_prev ℓm ℓfv m n y hlk
      iframe Hm
      iintro Hm
      tp_pure
      wp_pure 1
      iapply wp_wLoop_record
      iframe Hj HresL HresS
      iintro Hj HresL HresS
      iapply ih m r ((n, y) :: acc) hperm hkeys hnodup
      iframe
    | none =>
      rw [loopErr_succ]
      ihave ⟨Herr, Herr'⟩ := split $$ Herr
      iapply wp_prpQuery_rfQuery_fresh _ N ℓ ℓm ℓfv m r n
        ((m.length : ENNReal) / (N.toNat : ENNReal)) ⟨hn0, hnN⟩ hlk hperm hkeys hnodup le_rfl
      iframe Hj Herr Hm Hfv Hl
      iintro %y %hyr Hj Hm Hfv Hl
      tp_pure
      wp_pure 1
      iapply wp_wLoop_record
      iframe Hj HresL HresS
      iintro Hj HresL HresS
      iapply ih ((n, y) :: m) (r.erase y) ((n, y) :: acc) (prpPerm_insert hperm n hyr)
        (fun k hk => (mem_cons.mp hk).elim (· ▸ ⟨hn0, hnN⟩) (hkeys k))
        (nodup_cons.mpr ⟨alookup_eq_none_iff.mp hlk, hnodup⟩)
      simp only [length_cons]
      iframe

/-- The program `wPRP` refines the spec `wPRF` up to the loop error. -/
theorem wp_wPRP_wPRF (Q : Int) (hN : 0 < N) (hQ : 0 ≤ Q) (ε : ENNReal)
    (hε : loopErr N 0 Q.toNat ≤ ε) : iprop%
    ⤇ K.fill (wPRF N Q) ∗ ↯b ε ∗
      (∀ v : Val rT, ⤇ K.fill (ofVal v) -∗ Φ v) ⊢
      WP[codensity tv] (wPRP N Q) @ E {{ Φ }} := by
  rw [← toNat_of_nonneg hQ]
  iintro ⟨Hj, Herr, Hcnt⟩
  ihave Herr := weaken hε $$ Herr
  wp_bind (randomPermutation N)
  iapply wp_randomPermutation
  simp only [isPRP]
  iintro %f ⟨%ℓm, %ℓfv, %hf, %hperm, Hm, Hfv⟩
  subst hf
  wp_pures
  wp_bind (pl% alloc(inl(#())))
  wp_alloc_at (assocVal ([] : List (Int × Int)))
  iintro %resL HresL
  wp_pure 1
  tp_bind (randomFunction N)
  iapply wp_randomFunction_r
  iframe Hj
  simp only [isSRandomFunction]
  iintro %g Hj ⟨%ℓ, %hg, Hl⟩
  subst hg
  tp_pures
  tp_bind (alloc (ofVal (assocVal ([] : List (Int × Int)))))
  imod step_alloc_at _ (isVal_ofVal _) (vv := assocVal []) rfl $$ Hj with ⟨%resS, Hj, HresS⟩
  tp_pure
  tp_bind (pl% {wLoop N} {ofVal (rfQueryV N ℓ)} #loc resS #int Q.toNat)
  wp_bind (pl% {wLoop N} {ofVal (prpQueryV ℓm ℓfv)} #loc resL #int Q.toNat)
  iapply wp_wLoop_rev _ N ℓ ℓm ℓfv resL resS Q.toNat [] _ [] hperm (by simp) (by simp) hN
  simp only [length_nil]
  iframe Hj Herr Hm Hfv Hl HresL HresS
  iintro %acc Hj HresL HresS
  tp_pures
  tp_bind (pl% !#loc resS)
  imod step_load $$ [$Hj $HresS] with ⟨Hj, HresS⟩
  wp_pures
  iapply wp_load
  iframe HresL
  iintro HresL
  iapply Hcnt $$ %(assocVal acc) Hj

end Games

/-! ## Adequacy and the switching lemma -/

section AdequacyCor

/-- Adequacy of `wp_wPRF_wPRP`: the two games are `Rel`-close up to the birthday bound. -/
theorem wPRF_wPRP_switching (GF : BundledGFunctors) [RefinesPreGS rT ℝ≥0∞ GF] (N Q : Int)
    (hN : 0 < N) (hQ : 0 ≤ Q) (σ σ' : State rT) :
    (codensity tv).Rel (((Q.toNat * (Q.toNat - 1) : ℕ) : ENNReal) / (2 * (N.toNat : ENNReal)))
      (adequacyRel (· = ·)) (limExecV ⟨wPRF N Q, σ⟩) (limExecV ⟨wPRP N Q, σ'⟩) := by
  apply wp_adequacy_budget_lim (GF := GF)
  intro _ _ ε' hε'
  iintro Hj Herr
  iapply wp_wPRF_wPRP ([] : Ectx rT) N Q hN hQ ε'
    ((loopErr_zero_le_birthday N Q.toNat).trans hε'.le)
  rw [← spec_eq_fill_nil (wPRP N Q)]
  iframe Hj Herr
  iintro %v Hj
  iexists v
  rw [← spec_eq_fill_nil (ofVal v)]
  iframe Hj
  ipureintro
  rfl

/-- `wPRF_wPRP_switching` at the canonical functors. -/
theorem wPRF_wPRP_switching_closed (N Q : Int) (hN : 0 < N) (hQ : 0 ≤ Q) (σ σ' : State rT) :
    (codensity tv).Rel (((Q.toNat * (Q.toNat - 1) : ℕ) : ENNReal) / (2 * (N.toNat : ENNReal)))
      (adequacyRel (· = ·)) (limExecV ⟨wPRF N Q, σ⟩) (limExecV ⟨wPRP N Q, σ'⟩) :=
  wPRF_wPRP_switching (MicrometerFunctor rT ℝ≥0∞) N Q hN hQ σ σ'

/-- Adequacy of `wp_wPRP_wPRF`: the two games are `Rel`-close up to the birthday bound. -/
theorem wPRP_wPRF_switching (GF : BundledGFunctors) [RefinesPreGS rT ℝ≥0∞ GF] (N Q : Int)
    (hN : 0 < N) (hQ : 0 ≤ Q) (σ σ' : State rT) :
    (codensity tv).Rel (((Q.toNat * (Q.toNat - 1) : ℕ) : ENNReal) / (2 * (N.toNat : ENNReal)))
      (adequacyRel (· = ·)) (limExecV ⟨wPRP N Q, σ⟩) (limExecV ⟨wPRF N Q, σ'⟩) := by
  apply wp_adequacy_budget_lim (GF := GF)
  intro _ _ ε' hε'
  iintro Hj Herr
  iapply wp_wPRP_wPRF ([] : Ectx rT) N Q hN hQ ε'
    ((loopErr_zero_le_birthday N Q.toNat).trans hε'.le)
  rw [← spec_eq_fill_nil (wPRF N Q)]
  iframe Hj Herr
  iintro %v Hj
  iexists v
  rw [← spec_eq_fill_nil (ofVal v)]
  iframe Hj
  ipureintro
  rfl

/-- `wPRP_wPRF_switching` at the canonical functors. -/
theorem wPRP_wPRF_switching_closed (N Q : Int) (hN : 0 < N) (hQ : 0 ≤ Q) (σ σ' : State rT) :
    (codensity tv).Rel (((Q.toNat * (Q.toNat - 1) : ℕ) : ENNReal) / (2 * (N.toNat : ENNReal)))
      (adequacyRel (· = ·)) (limExecV ⟨wPRP N Q, σ⟩) (limExecV ⟨wPRF N Q, σ'⟩) :=
  wPRP_wPRF_switching (MicrometerFunctor rT ℝ≥0∞) N Q hN hQ σ σ'

/-- The weak PRF/PRP switching lemma: any event's probability changes by at most the
birthday bound. -/
theorem weak_switching_lemma (N Q : Int) (hN : 0 < N) (hQ : 0 ≤ Q) (σ σ' : State rT)
    {S : Set (Exp rT)} (hS : MeasurableSet S) :
    limExecV ⟨wPRF N Q, σ⟩ S ≤ limExecV ⟨wPRP N Q, σ'⟩ S +
        ((Q.toNat * (Q.toNat - 1) : ℕ) : ENNReal) / (2 * (N.toNat : ENNReal)) ∧
      limExecV ⟨wPRP N Q, σ'⟩ S ≤ limExecV ⟨wPRF N Q, σ⟩ S +
        ((Q.toNat * (Q.toNat - 1) : ℕ) : ENNReal) / (2 * (N.toNat : ENNReal)) :=
  ⟨tv_le_add_of_rel
    ((wPRF_wPRP_switching_closed N Q hN hQ σ σ').mono le_rfl adequacyRel_eq_subset) hS,
   tv_le_add_of_rel
    ((wPRP_wPRF_switching_closed N Q hN hQ σ' σ).mono le_rfl adequacyRel_eq_subset) hS⟩

end AdequacyCor

end Switching
end ProbLang
