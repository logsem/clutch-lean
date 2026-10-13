module

public import Metrology.Approxis.Examples.SwitchingPRP
public import Metrology.Approxis.Adequacy
public import Metrology.Approxis.AdequacyRel
public import Metrology.Couplings.CodensityTV
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # The weak PRF/PRP switching lemma

Port of clutch's `theories/approxis/examples/prp_prf_weak.v`: `Q` uniform queries to a random
function and to a random permutation over `[0, N)` are indistinguishable up to
`Q (Q - 1) / (2 N)`. -/

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.ApproxisWpGS
open scoped AppGS

namespace ProbLang
namespace Switching

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

/-- With `c` entries memoised and `q` rounds to go, round `i` costs `(c + i) / N`. -/
noncomputable def loopErr (N : Int) (c q : Nat) : ENNReal :=
  (∑ i ∈ Finset.range q, ((c + i : Nat) : ENNReal)) / (N.toNat : ENNReal)

theorem loopErr_mono (N : Int) (c : Nat) {q q' : Nat} (h : q ≤ q') :
    loopErr N c q ≤ loopErr N c q' :=
  ENNReal.div_le_div_right
    (Finset.sum_le_sum_of_subset fun _x hx =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) h)) _

theorem loopErr_succ (N : Int) (c q : Nat) :
    loopErr N c (q + 1) = (c : ENNReal) / (N.toNat : ENNReal) + loopErr N (c + 1) q := by
  unfold loopErr
  rw [Finset.sum_range_succ', show (∑ i ∈ Finset.range q, ((c + (i + 1) : Nat) : ENNReal)) =
      ∑ i ∈ Finset.range q, (((c + 1) + i : Nat) : ENNReal) from
    Finset.sum_congr rfl fun i _ => by push_cast; ring, ENNReal.add_div, add_comm]
  norm_num

section Games

variable {hlc : HasLC} {GF : BundledGFunctors} [ApproxisGS rT hlc TVDiv.tv GF]

theorem wp_wLoop {E : CoPset} (K : Ectx rT) (N : Int) (ℓ ℓm ℓfv resL resS : Loc)
    (q : Nat) (m : List (Int × Int)) (r : List Int) (acc : List (Int × Int))
    (hperm : prpPerm N m r) (hkeys : ∀ k ∈ m.map Prod.fst, 0 ≤ k ∧ k < N)
    (hnodup : (m.map Prod.fst).Nodup) (hN : 0 < N)
    {Φ : Val rT → IProp GF} : iprop%
    ⤇ K.fill (pl% {wLoop N} {Exp.ofVal (prpQueryV ℓm ℓfv)} #(.loc resS) #(.int q)) ∗
    ↯ (loopErr N m.length q) ∗
    (ℓ ↦ (assocVal m : Val rT)) ∗ (ℓm ↦ₛ (assocVal m : Val rT)) ∗
    (ℓfv ↦ₛ (intListVal r : Val rT)) ∗
    (resL ↦ (assocVal acc : Val rT)) ∗ (resS ↦ₛ (assocVal acc : Val rT)) ∗
    (∀ acc' : List (Int × Int), ⤇ K.fill pl(#(.unit)) -∗
       (resL ↦ (assocVal acc' : Val rT)) -∗ (resS ↦ₛ (assocVal acc' : Val rT)) -∗
       Φ .unit) ⊢
    wp E (pl% {wLoop N} {Exp.ofVal (rfQueryV N ℓ)} #(.loc resL) #(.int q)) Φ := by
  induction q generalizing m r acc with
  | zero =>
    iintro ⟨Hj, Herr, Hl, Hm, Hfv, HresL, HresS, Hcnt⟩
    simp only [Nat.cast_zero]
    tp_pures
    wp_pures
    wp_value
    iapply Hcnt $$ %acc Hj HresL HresS
  | succ q ih =>
    iintro ⟨Hj, Herr, Hl, Hm, Hfv, HresL, HresS, Hcnt⟩
    wp_pures
    tp_pures
    wp_bind (pl% rand(#(.int N), #.unit))
    tp_bind (pl% rand(#(.int N), #.unit))
    iapply wp_couple_rand_rand N (fun n => n) (fun n h1 h2 => ⟨h1, h2⟩)
      (fun mm h1 h2 => ⟨mm, ⟨⟨h1, h2⟩, rfl⟩, fun y hy => hy.2⟩) hN
    iframe Hj
    iintro %n ⟨%hn0, %hnN⟩ Hj
    tp_pure
    tp_bind (pl% {prpQuery ℓm ℓfv} #(.int n))
    wp_pure 1
    wp_bind (pl% {rfQuery N ℓ} #(.int n))
    cases hlk : alookup n m with
    | some y =>
      ihave Herr := ErrorCredit.weaken (loopErr_mono N m.length (Nat.le_succ q)) $$ Herr
      iapply wp_prpQuery_prev_r _ ℓm ℓfv m n y hlk
      iframe Hj Hm
      iintro Hj Hm
      iapply wp_rfQuery_prev N ℓ m n y hlk
      iframe Hl
      iintro Hl
      tp_pure
      tp_bind (pl% !#(.loc resS))
      imod step_load $$ [$Hj $HresS] with ⟨Hj, HresS⟩
      tp_bind (Exp.store pl(#(.loc resS)) (Exp.ofVal (assocVal ((n, y) :: acc))))
      imod step_store (hv := Val.isVal_ofVal (assocVal ((n, y) :: acc)))
        (hnew := Exp.toVal?_ofVal _) $$ [$Hj $HresS] with ⟨Hj, HresS⟩
      tp_pure
      tp_pure
      wp_pures
      wp_bind (pl% !#(.loc resL))
      iapply wp_load
      iframe HresL
      iintro HresL
      wp_bind (Exp.store pl(#(.loc resL)) (Exp.ofVal (assocVal ((n, y) :: acc))))
      iapply wp_store (v' := assocVal acc) (v := assocVal ((n, y) :: acc))
      iframe HresL
      iintro HresL
      wp_pure 1
      wp_pure 1
      rw [show ((q + 1 : Nat) : Int) - 1 = ((q : Nat) : Int) by omega]
      tp_bind (pl% {wLoop N} {Exp.ofVal (prpQueryV ℓm ℓfv)} #(.loc resS) #(.int q))
      wp_show (pl% {wLoop N} {Exp.ofVal (rfQueryV N ℓ)} #(.loc resL) #(.int q))
      iapply ih m r ((n, y) :: acc) hperm hkeys hnodup
      iframe Hj Herr Hl Hm Hfv HresL HresS
      iexact Hcnt
    | none =>
      rw [loopErr_succ]
      ihave ⟨Herr, Herr'⟩ := ErrorCredit.split $$ Herr
      iapply wp_rfQuery_prpQuery_fresh _ N ℓ ℓm ℓfv m r n
        ((m.length : ENNReal) / (N.toNat : ENNReal)) ⟨hn0, hnN⟩ hlk hperm hkeys hnodup
        le_rfl
      iframe Hj Herr Hl Hm Hfv
      iintro %y %hyr Hj Hl Hm Hfv
      tp_pure
      tp_bind (pl% !#(.loc resS))
      imod step_load $$ [$Hj $HresS] with ⟨Hj, HresS⟩
      tp_bind (Exp.store pl(#(.loc resS)) (Exp.ofVal (assocVal ((n, y) :: acc))))
      imod step_store (hv := Val.isVal_ofVal (assocVal ((n, y) :: acc)))
        (hnew := Exp.toVal?_ofVal _) $$ [$Hj $HresS] with ⟨Hj, HresS⟩
      tp_pure
      tp_pure
      wp_pures
      wp_bind (pl% !#(.loc resL))
      iapply wp_load
      iframe HresL
      iintro HresL
      wp_bind (Exp.store pl(#(.loc resL)) (Exp.ofVal (assocVal ((n, y) :: acc))))
      iapply wp_store (v' := assocVal acc) (v := assocVal ((n, y) :: acc))
      iframe HresL
      iintro HresL
      wp_pure 1
      wp_pure 1
      rw [show ((q + 1 : Nat) : Int) - 1 = ((q : Nat) : Int) by omega]
      tp_bind (pl% {wLoop N} {Exp.ofVal (prpQueryV ℓm ℓfv)} #(.loc resS) #(.int q))
      wp_show (pl% {wLoop N} {Exp.ofVal (rfQueryV N ℓ)} #(.loc resL) #(.int q))
      iapply ih ((n, y) :: m) (r.erase y) ((n, y) :: acc)
        (prpPerm_insert hperm n hyr)
        (fun k hk => (List.mem_cons.mp hk).elim (· ▸ ⟨hn0, hnN⟩) (hkeys k))
        (List.nodup_cons.mpr ⟨alookup_eq_none_iff.mp hlk, hnodup⟩)
      simp only [List.length_cons]
      iframe Hj Herr' Hl Hm Hfv HresL HresS
      iexact Hcnt

theorem wp_wPRF_wPRP {E : CoPset} (K : Ectx rT) (N Q : Int) (hN : 0 < N) (hQ : 0 ≤ Q)
    (ε : ENNReal) (hε : loopErr N 0 Q.toNat ≤ ε)
    {Φ : Val rT → IProp GF} : iprop%
    ⤇ K.fill (wPRP N Q) ∗ ↯ ε ∗
    (∀ v : Val rT, ⤇ K.fill (Exp.ofVal v) -∗ Φ v) ⊢
    wp E (wPRF N Q) Φ := by
  rw [show (Q : Int) = ((Q.toNat : Nat) : Int) by omega]
  iintro ⟨Hj, Herr, Hcnt⟩
  ihave Herr := ErrorCredit.weaken hε $$ Herr
  wp_bind (randomFunction N)
  iapply wp_randomFunction
  simp only [isRandomFunction]
  iintro %f ⟨%ℓ, %hf, Hl⟩
  subst hf
  wp_pures
  wp_bind (pl% alloc(inl(#.unit)))
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
  tp_bind (Exp.alloc (Exp.ofVal (assocVal ([] : List (Int × Int)))))
  imod step_alloc_at _ (Val.isVal_ofVal _) (vv := assocVal []) rfl
    $$ Hj with ⟨%resS, Hj, HresS⟩
  tp_pure
  tp_bind (pl% {wLoop N} {Exp.ofVal (prpQueryV ℓm ℓfv)} #(.loc resS) #(.int Q.toNat))
  wp_bind (pl% {wLoop N} {Exp.ofVal (rfQueryV N ℓ)} #(.loc resL) #(.int Q.toNat))
  iapply wp_wLoop _ N ℓ ℓm ℓfv resL resS Q.toNat [] _ [] hperm (by simp) (by simp) hN
  simp only [List.length_nil]
  iframe Hj Herr Hl Hm Hfv HresL HresS
  iintro %acc Hj HresL HresS
  tp_pures
  tp_bind (pl% !#(.loc resS))
  imod step_load $$ [$Hj $HresS] with ⟨Hj, HresS⟩
  wp_pures
  iapply wp_load
  iframe HresL
  iintro HresL
  iapply Hcnt $$ %(assocVal acc) Hj

/-! ## Adequacy: the birthday bound -/

theorem loopErr_zero_le_birthday (N : Int) (q : Nat) :
    loopErr N 0 q ≤ ((q * (q - 1) : ℕ) : ENNReal) / (2 * (N.toNat : ENNReal)) := by
  unfold loopErr
  simp only [Nat.zero_add]
  rw [show (∑ i ∈ Finset.range q, ((i : Nat) : ENNReal)) =
      ((∑ i ∈ Finset.range q, i : Nat) : ENNReal) from (Nat.cast_sum _ _).symm,
    Finset.sum_range_id]
  calc ((q * (q - 1) / 2 : ℕ) : ENNReal) / (N.toNat : ENNReal)
      ≤ (((q * (q - 1) : ℕ) : ENNReal) / 2) / (N.toNat : ENNReal) := by
        gcongr
        rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num)),
          show ((2 : ENNReal)) = ((2 : ℕ) : ENNReal) from rfl, ← Nat.cast_mul]
        exact_mod_cast Nat.div_mul_le_self _ 2
    _ = ((q * (q - 1) : ℕ) : ENNReal) / (2 * (N.toNat : ENNReal)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
          ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), mul_assoc]

theorem wp_wLoop_rev {E : CoPset} (K : Ectx rT) (N : Int) (ℓ ℓm ℓfv resL resS : Loc)
    (q : Nat) (m : List (Int × Int)) (r : List Int) (acc : List (Int × Int))
    (hperm : prpPerm N m r) (hkeys : ∀ k ∈ m.map Prod.fst, 0 ≤ k ∧ k < N)
    (hnodup : (m.map Prod.fst).Nodup) (hN : 0 < N)
    {Φ : Val rT → IProp GF} : iprop%
    ⤇ K.fill (pl% {wLoop N} {Exp.ofVal (rfQueryV N ℓ)} #(.loc resS) #(.int q)) ∗
    ↯ (loopErr N m.length q) ∗
    (ℓm ↦ (assocVal m : Val rT)) ∗ (ℓfv ↦ (intListVal r : Val rT)) ∗
    (ℓ ↦ₛ (assocVal m : Val rT)) ∗
    (resL ↦ (assocVal acc : Val rT)) ∗ (resS ↦ₛ (assocVal acc : Val rT)) ∗
    (∀ acc' : List (Int × Int), ⤇ K.fill pl(#(.unit)) -∗
       (resL ↦ (assocVal acc' : Val rT)) -∗ (resS ↦ₛ (assocVal acc' : Val rT)) -∗
       Φ .unit) ⊢
    wp E (pl% {wLoop N} {Exp.ofVal (prpQueryV ℓm ℓfv)} #(.loc resL) #(.int q)) Φ := by
  induction q generalizing m r acc with
  | zero =>
    iintro ⟨Hj, Herr, Hm, Hfv, Hl, HresL, HresS, Hcnt⟩
    simp only [Nat.cast_zero]
    tp_pures
    wp_pures
    wp_value
    iapply Hcnt $$ %acc Hj HresL HresS
  | succ q ih =>
    iintro ⟨Hj, Herr, Hm, Hfv, Hl, HresL, HresS, Hcnt⟩
    wp_pures
    tp_pures
    wp_bind (pl% rand(#(.int N), #.unit))
    tp_bind (pl% rand(#(.int N), #.unit))
    iapply wp_couple_rand_rand N (fun n => n) (fun n h1 h2 => ⟨h1, h2⟩)
      (fun mm h1 h2 => ⟨mm, ⟨⟨h1, h2⟩, rfl⟩, fun y hy => hy.2⟩) hN
    iframe Hj
    iintro %n ⟨%hn0, %hnN⟩ Hj
    tp_pure
    tp_bind (pl% {rfQuery N ℓ} #(.int n))
    wp_pure 1
    wp_bind (pl% {prpQuery ℓm ℓfv} #(.int n))
    cases hlk : alookup n m with
    | some y =>
      ihave Herr := ErrorCredit.weaken (loopErr_mono N m.length (Nat.le_succ q)) $$ Herr
      iapply wp_rfQuery_prev_r _ N ℓ m n y hlk
      iframe Hj Hl
      iintro Hj Hl
      iapply wp_prpQuery_prev ℓm ℓfv m n y hlk
      iframe Hm
      iintro Hm
      tp_pure
      tp_bind (pl% !#(.loc resS))
      imod step_load $$ [$Hj $HresS] with ⟨Hj, HresS⟩
      tp_bind (Exp.store pl(#(.loc resS)) (Exp.ofVal (assocVal ((n, y) :: acc))))
      imod step_store (hv := Val.isVal_ofVal (assocVal ((n, y) :: acc)))
        (hnew := Exp.toVal?_ofVal _) $$ [$Hj $HresS] with ⟨Hj, HresS⟩
      tp_pure
      tp_pure
      wp_pures
      wp_bind (pl% !#(.loc resL))
      iapply wp_load
      iframe HresL
      iintro HresL
      wp_bind (Exp.store pl(#(.loc resL)) (Exp.ofVal (assocVal ((n, y) :: acc))))
      iapply wp_store (v' := assocVal acc) (v := assocVal ((n, y) :: acc))
      iframe HresL
      iintro HresL
      wp_pure 1
      wp_pure 1
      rw [show ((q + 1 : Nat) : Int) - 1 = ((q : Nat) : Int) by omega]
      tp_bind (pl% {wLoop N} {Exp.ofVal (rfQueryV N ℓ)} #(.loc resS) #(.int q))
      wp_show (pl% {wLoop N} {Exp.ofVal (prpQueryV ℓm ℓfv)} #(.loc resL) #(.int q))
      iapply ih m r ((n, y) :: acc) hperm hkeys hnodup
      iframe Hj Herr Hm Hfv Hl HresL HresS
      iexact Hcnt
    | none =>
      rw [loopErr_succ]
      ihave ⟨Herr, Herr'⟩ := ErrorCredit.split $$ Herr
      iapply wp_prpQuery_rfQuery_fresh _ N ℓ ℓm ℓfv m r n
        ((m.length : ENNReal) / (N.toNat : ENNReal)) ⟨hn0, hnN⟩ hlk hperm hkeys hnodup
        le_rfl
      iframe Hj Herr Hm Hfv Hl
      iintro %y %hyr Hj Hm Hfv Hl
      tp_pure
      tp_bind (pl% !#(.loc resS))
      imod step_load $$ [$Hj $HresS] with ⟨Hj, HresS⟩
      tp_bind (Exp.store pl(#(.loc resS)) (Exp.ofVal (assocVal ((n, y) :: acc))))
      imod step_store (hv := Val.isVal_ofVal (assocVal ((n, y) :: acc)))
        (hnew := Exp.toVal?_ofVal _) $$ [$Hj $HresS] with ⟨Hj, HresS⟩
      tp_pure
      tp_pure
      wp_pures
      wp_bind (pl% !#(.loc resL))
      iapply wp_load
      iframe HresL
      iintro HresL
      wp_bind (Exp.store pl(#(.loc resL)) (Exp.ofVal (assocVal ((n, y) :: acc))))
      iapply wp_store (v' := assocVal acc) (v := assocVal ((n, y) :: acc))
      iframe HresL
      iintro HresL
      wp_pure 1
      wp_pure 1
      rw [show ((q + 1 : Nat) : Int) - 1 = ((q : Nat) : Int) by omega]
      tp_bind (pl% {wLoop N} {Exp.ofVal (rfQueryV N ℓ)} #(.loc resS) #(.int q))
      wp_show (pl% {wLoop N} {Exp.ofVal (prpQueryV ℓm ℓfv)} #(.loc resL) #(.int q))
      iapply ih ((n, y) :: m) (r.erase y) ((n, y) :: acc)
        (prpPerm_insert hperm n hyr)
        (fun k hk => (List.mem_cons.mp hk).elim (· ▸ ⟨hn0, hnN⟩) (hkeys k))
        (List.nodup_cons.mpr ⟨alookup_eq_none_iff.mp hlk, hnodup⟩)
      simp only [List.length_cons]
      iframe Hj Herr' Hm Hfv Hl HresL HresS
      iexact Hcnt

theorem wp_wPRP_wPRF {E : CoPset} (K : Ectx rT) (N Q : Int) (hN : 0 < N) (hQ : 0 ≤ Q)
    (ε : ENNReal) (hε : loopErr N 0 Q.toNat ≤ ε)
    {Φ : Val rT → IProp GF} : iprop%
    ⤇ K.fill (wPRF N Q) ∗ ↯ ε ∗
    (∀ v : Val rT, ⤇ K.fill (Exp.ofVal v) -∗ Φ v) ⊢
    wp E (wPRP N Q) Φ := by
  rw [show (Q : Int) = ((Q.toNat : Nat) : Int) by omega]
  iintro ⟨Hj, Herr, Hcnt⟩
  ihave Herr := ErrorCredit.weaken hε $$ Herr
  wp_bind (randomPermutation N)
  iapply wp_randomPermutation
  simp only [isPRP]
  iintro %f ⟨%ℓm, %ℓfv, %hf, %hperm, Hm, Hfv⟩
  subst hf
  wp_pures
  wp_bind (pl% alloc(inl(#.unit)))
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
  tp_bind (Exp.alloc (Exp.ofVal (assocVal ([] : List (Int × Int)))))
  imod step_alloc_at _ (Val.isVal_ofVal _) (vv := assocVal []) rfl
    $$ Hj with ⟨%resS, Hj, HresS⟩
  tp_pure
  tp_bind (pl% {wLoop N} {Exp.ofVal (rfQueryV N ℓ)} #(.loc resS) #(.int Q.toNat))
  wp_bind (pl% {wLoop N} {Exp.ofVal (prpQueryV ℓm ℓfv)} #(.loc resL) #(.int Q.toNat))
  iapply wp_wLoop_rev _ N ℓ ℓm ℓfv resL resS Q.toNat [] _ [] hperm (by simp) (by simp) hN
  simp only [List.length_nil]
  iframe Hj Herr Hm Hfv Hl HresL HresS
  iintro %acc Hj HresL HresS
  tp_pures
  tp_bind (pl% !#(.loc resS))
  imod step_load $$ [$Hj $HresS] with ⟨Hj, HresS⟩
  wp_pures
  iapply wp_load
  iframe HresL
  iintro HresL
  iapply Hcnt $$ %(assocVal acc) Hj

end Games

section AdequacyCor

omit [LawfulProbLangℝ rT] [MeasurableSingletonClass rT] in
theorem Exp.fst_eq_of_toVal?_eq_some {e : Exp rT} {v : Val rT} (h : e.toVal? = some v) :
    v.1 = e := by
  unfold Exp.toVal? at h
  cases hc : IsVal.check? e with
  | none => rw [hc] at h; cases h
  | some w => rw [hc] at h; cases h; rfl

omit [LawfulProbLangℝ rT] [MeasurableSingletonClass rT] in
theorem adequacyRel_eq_subset :
    adequacyRel (rT := rT) (· = ·) ⊆ {p : Exp rT × Exp rT | p.1 = p.2} := by
  rintro ⟨e1, e2⟩ ⟨v, v', hv, hv', rfl⟩
  exact (Exp.fst_eq_of_toVal?_eq_some hv).symm.trans (Exp.fst_eq_of_toVal?_eq_some hv')

set_option linter.style.haveILetI false in
theorem wPRF_wPRP_switching (GF : BundledGFunctors) [RefinesPreGS rT GF]
    (N Q : Int) (hN : 0 < N) (hQ : 0 ≤ Q) (σ σ' : State rT) :
    TVDiv.tv.{0}.Codensity 1 (((Q.toNat * (Q.toNat - 1) : ℕ) : ENNReal) / (2 * (N.toNat : ENNReal)))
      (adequacyRel (· = ·))
      (limExecV ⟨wPRF N Q, σ⟩) (limExecV ⟨wPRP N Q, σ'⟩) := by
  apply wp_adequacy_error_lim (GF := GF)
  intro IGS ε' hε'
  letI := IGS
  iintro Hj Herr
  iapply wp_wPRF_wPRP ([] : Ectx rT) N Q hN hQ ε'
    (le_of_lt (lt_of_le_of_lt (loopErr_zero_le_birthday N Q.toNat) hε'))
  rw [← spec_eq_fill_nil (wPRP N Q)]
  iframe Hj Herr
  iintro %v Hj
  iexists v
  rw [← spec_eq_fill_nil (Exp.ofVal v)]
  iframe Hj
  ipureintro
  rfl

theorem wPRF_wPRP_switching_closed (N Q : Int) (hN : 0 < N) (hQ : 0 ≤ Q)
    (σ σ' : State rT) :
    TVDiv.tv.{0}.Codensity 1 (((Q.toNat * (Q.toNat - 1) : ℕ) : ENNReal) / (2 * (N.toNat : ENNReal)))
      (adequacyRel (· = ·))
      (limExecV ⟨wPRF N Q, σ⟩) (limExecV ⟨wPRP N Q, σ'⟩) :=
  wPRF_wPRP_switching (ApproxisFunctor rT) N Q hN hQ σ σ'

set_option linter.style.haveILetI false in
theorem wPRP_wPRF_switching (GF : BundledGFunctors) [RefinesPreGS rT GF]
    (N Q : Int) (hN : 0 < N) (hQ : 0 ≤ Q) (σ σ' : State rT) :
    TVDiv.tv.{0}.Codensity 1 (((Q.toNat * (Q.toNat - 1) : ℕ) : ENNReal) / (2 * (N.toNat : ENNReal)))
      (adequacyRel (· = ·))
      (limExecV ⟨wPRP N Q, σ⟩) (limExecV ⟨wPRF N Q, σ'⟩) := by
  apply wp_adequacy_error_lim (GF := GF)
  intro IGS ε' hε'
  letI := IGS
  iintro Hj Herr
  iapply wp_wPRP_wPRF ([] : Ectx rT) N Q hN hQ ε'
    (le_of_lt (lt_of_le_of_lt (loopErr_zero_le_birthday N Q.toNat) hε'))
  rw [← spec_eq_fill_nil (wPRF N Q)]
  iframe Hj Herr
  iintro %v Hj
  iexists v
  rw [← spec_eq_fill_nil (Exp.ofVal v)]
  iframe Hj
  ipureintro
  rfl

theorem wPRP_wPRF_switching_closed (N Q : Int) (hN : 0 < N) (hQ : 0 ≤ Q)
    (σ σ' : State rT) :
    TVDiv.tv.{0}.Codensity 1 (((Q.toNat * (Q.toNat - 1) : ℕ) : ENNReal) / (2 * (N.toNat : ENNReal)))
      (adequacyRel (· = ·))
      (limExecV ⟨wPRP N Q, σ⟩) (limExecV ⟨wPRF N Q, σ'⟩) :=
  wPRP_wPRF_switching (ApproxisFunctor rT) N Q hN hQ σ σ'

theorem weak_switching_lemma (N Q : Int) (hN : 0 < N) (hQ : 0 ≤ Q) (σ σ' : State rT)
    {S : Set (Exp rT)} (hS : MeasurableSet S) :
    limExecV ⟨wPRF N Q, σ⟩ S ≤ limExecV ⟨wPRP N Q, σ'⟩ S
        + ((Q.toNat * (Q.toNat - 1) : ℕ) : ENNReal) / (2 * (N.toNat : ENNReal)) ∧
    limExecV ⟨wPRP N Q, σ'⟩ S ≤ limExecV ⟨wPRF N Q, σ⟩ S
        + ((Q.toNat * (Q.toNat - 1) : ℕ) : ENNReal) / (2 * (N.toNat : ENNReal)) :=
  ⟨GradedDivergence.Codensity.tv_le_add_of_diag
    ((wPRF_wPRP_switching_closed N Q hN hQ σ σ').mono_rel adequacyRel_eq_subset) hS,
   GradedDivergence.Codensity.tv_le_add_of_diag
    ((wPRP_wPRF_switching_closed N Q hN hQ σ' σ).mono_rel adequacyRel_eq_subset) hS⟩

end AdequacyCor

end Switching
end ProbLang
