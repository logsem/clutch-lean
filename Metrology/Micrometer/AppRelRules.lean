module

public import Metrology.Micrometer.AppRelRulesPure
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

/-! # Relational rules: left state steps and coupled draws

Left heap/tape steps, one-sided and coupled draws (`U` unlabelled, `T` tape, left first), under
`[L.IsReflexive] [L.IsSupportLocal] [L.HasBind]`; main rule `refines_couple_rands_spend`. -/

@[expose] public section

open Iris Iris.ProofMode ProbLang.MicrometerWpGS ProbLang.Ectx ProbLang.Exp
open scoped AppGS

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT]

section AppRelRules
variable {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B] [OrderTop B]
  {L : GradedLifting.{0} B} {GF : BundledGFunctors} [IR : MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF]
local bi IProp GF

variable {E : CoPset} {K K' : Ectx rT} {t e e' : Exp rT} {A : lrel rT GF} {z : Int} {l : Loc}

section Prim
variable [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind]

/-! ## Coupled draws within a budget

Every coupled-draw rule is proved the same way: unfold `refines`, merge the spec context `K2` with
`K'` (`Ectx.fill_comp`), apply the `wp` coupling rule, then split the context again for the
continuation. -/

/-- Couple `rand N ~ rand N` along `S`, given a lifting of the two uniform draws within the
cancelable budget `c`; spends `↯b c` (relational `wp_couple_rand_rand_spend`). -/
theorem refines_couple_rands_spend (N : Int) (HN : 0 < N) (S : Int → Int → Prop) (c : B)
    (hc : IsAddLeftRegular c) (Hcpl : L.Rel c S (unifInt N HN) (unifInt N HN)) : iprop%
    ↯b c ∗ (∀ r r', ⌜S r r'⌝ -∗
      refines L E (K.fill pl(#r)) (K'.fill pl(#r')) A) ⊢
    refines L E (K.fill pl(rand(#N, #())))
      (K'.fill pl(rand(#N, #()))) A := by
  unfold refines
  iintro ⟨Hc, Hcnt⟩ %K2 %b Hj Hna Herr Hpos
  isimp only [fill_comp K2 K'] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_rand_rand_spend N HN S c hc Hcpl (K2.comp K') ⊤ _
  iframe Hj Hc
  iintro %r %r' %hS HKres
  isimp only [← fill_comp K2 K'] at HKres
  rw [show ofVal (.int r : Val rT) = pl(#r) from rfl]
  iapply Hcnt $$ %r %r' %hS %K2 %b HKres Hna Herr Hpos

section Reflexive
variable [L.IsReflexive]

/-! ## Left heap steps and tape allocation -/

/-- Left allocation `ref v`: continue with a fresh location pointing to `v`. -/
theorem refines_alloc_l {v : Val rT} : iprop%
    (∀ l, l ↦ v -∗ refines L E (K.fill pl(#loc l)) t A) ⊢
    refines L E (K.fill (.alloc v.1)) t A := by
  iintro Hlog
  iapply refines_wp_l
  rw [show alloc v.1 = alloc (ofVal v) from rfl]
  iapply wp_alloc
  iintro %l Hl
  iapply Hlog $$ %l Hl

/-- Left load `!l`: read the value from the points-to. -/
theorem refines_load_l : iprop%
    (∃ v, l ↦ v ∗ (l ↦ v -∗ refines L E (K.fill v.1) t A)) ⊢
    refines L E (K.fill pl(!#loc l)) t A := by
  iintro ⟨%v, Hl, Hlog⟩
  iapply refines_wp_l
  iapply wp_load
  iframe Hl
  iintro Hl
  iapply Hlog $$ Hl

/-- Left store `l := v'`: update the points-to to `v'`. -/
theorem refines_store_l {v' : Val rT} : iprop%
    (∃ v : Val rT, l ↦ v ∗ (l ↦ v' -∗ refines L E (K.fill pl(#())) t A)) ⊢
    refines L E (K.fill (.store pl(#loc l) v'.1)) t A := by
  iintro ⟨%v, Hl, Hlog⟩
  iapply refines_wp_l
  rw [show store pl(#loc l) v'.1 = store pl(#loc l) (ofVal v') from rfl]
  iapply wp_store
  iframe Hl
  iintro Hl
  iapply Hlog $$ Hl

/-- Left tape allocation `tape z`: continue with a fresh empty tape of bound `z`. -/
theorem refines_alloctape_l : iprop%
    (∀ l, appTapesFrag l (Tape.empty z) -∗ refines L E (K.fill pl(#lbl l)) t A) ⊢
    refines L E (K.fill pl(tape(#z))) t A := by
  iintro Hlog
  iapply refines_wp_l
  iapply wp_alloctape
  iintro %l Hl
  iapply Hlog $$ %l Hl

/-- Left tape allocation, giving the fresh tape as an empty `appNatTape` (the form the tape
couplings consume). -/
theorem refines_alloctape_nat_l : iprop%
    (∀ l, appNatTape l z [] -∗ refines L E (K.fill pl(#lbl l)) t A) ⊢
    refines L E (K.fill pl(tape(#z))) t A := by
  iintro Hlog
  iapply refines_alloctape_l
  iintro %l Hl
  iapply Hlog $$ %l
  iapply appNatTape_fold (l := l) (z := z) (ns := []) (fs := []) rfl
  rw [Tape.empty] at *
  iexact Hl

/-! ## One-sided draws -/

/-- Left unlabelled draw `rand z`: continue at every outcome `0 ≤ n < z`. -/
theorem refines_randU_l (Hz : 0 < z) : iprop%
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ refines L E (K.fill pl(#n)) t A) ⊢
    refines L E (K.fill pl(rand(#z, #()))) t A := by
  iintro Hlog
  iapply refines_wp_l
  iapply wp_rand Hz
  iintro %n %Hbnds
  iapply Hlog $$ %n %Hbnds

/-- Left draw from a non-empty tape: take its head `n`. -/
theorem refines_randT_l {n : Int} {ns : List Int} : iprop%
    appNatTape l z (n :: ns) ∗
    (appNatTape l z ns -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ refines L E (K.fill pl(#n)) t A) ⊢
    refines L E (K.fill pl(rand(#z, #lbl l))) t A := by
  iintro ⟨Hl, Hlog⟩
  iapply refines_wp_l
  iapply wp_rand_tape
  iframe Hl
  iintro Hl' %Hbnds
  iapply Hlog $$ Hl' %Hbnds

/-- Left draw from an empty tape: behaves like an unlabelled draw, keeping the tape empty. -/
theorem refines_randT_empty_l (Hz : 0 < z) : iprop%
    appNatTape l z [] ∗
    (∀ n, appNatTape l z [] -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ refines L E (K.fill pl(#n)) t A) ⊢
    refines L E (K.fill pl(rand(#z, #lbl l))) t A := by
  iintro ⟨Hl, Hlog⟩
  iapply refines_wp_l
  iapply wp_rand_tape_empty Hz
  iframe Hl
  iintro %n Hl' %Hbnds
  iapply Hlog $$ %n Hl' %Hbnds

/-- Right unlabelled draw `rand z`: continue at every outcome `0 ≤ n < z`. -/
theorem refines_randU_r (Hz : 0 < z) : iprop%
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ refines L E e (K.fill pl(#n)) A) ⊢
    refines L E e (K.fill pl(rand(#z, #()))) A := by
  unfold refines
  iintro Hlog %K' %b Hj Hna Herr Hpos
  isimp only [fill_comp K' K] at Hj
  iapply wp_rand_r (K'.comp K) Hz
  iframe Hj
  iintro %n %Hbnds HKRes
  isimp only [← fill_comp K' K] at HKRes
  iapply Hlog $$ %n %Hbnds %K' %b HKRes Hna Herr Hpos

/-- Right draw from an empty spec tape: continue at every outcome, keeping the tape empty. -/
theorem refines_randT_empty_r (Hz : 0 < z) : iprop%
    specNatTape l z [] ∗
    (∀ n, specNatTape l z [] -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ refines L E e (K.fill pl(#n)) A) ⊢
    refines L E e (K.fill pl(rand(#z, #lbl l))) A := by
  unfold refines
  iintro ⟨Hα, Hlog⟩ %K' %b Hj Hna Herr Hpos
  isimp only [fill_comp K' K] at Hj
  iapply wp_rand_tape_empty_r (K'.comp K) Hz
  iframe Hj Hα
  iintro %n HαNew HKRes %Hbnds
  isimp only [← fill_comp K' K] at HKRes
  iapply Hlog $$ %n HαNew %Hbnds %K' %b HKRes Hna Herr Hpos

/-! ## Budget-free couplings along a bijection

`f` is a bijection of `{0, …, z-1}`; the right draw returns `f n` when the left returns `n`. -/

/-- Couple two unlabelled draws `rand z ~ rand z` along the bijection `f`. -/
theorem refines_couple_rands_lr (f : Int → Int) (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) (Hz : 0 < z) : iprop%
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ refines L E (K.fill pl(#n)) (K'.fill pl(#int (f n))) A) ⊢
    refines L E (K.fill pl(rand(#z, #())))
      (K'.fill pl(rand(#z, #()))) A := by
  unfold refines
  iintro Hcnt %K2 %b Hj Hna Herr Hpos
  isimp only [fill_comp K2 K'] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_rand_rand z f hdom hbij Hz (K2.comp K') ⊤ _
  iframe Hj
  iintro %n %Hn HKres
  isimp only [← fill_comp K2 K'] at HKres
  rw [show ofVal (.int n : Val rT) = pl(#n) from rfl]
  iapply Hcnt $$ %n %Hn %K2 %b HKres Hna Herr Hpos

/-- Couple a left tape draw with a right unlabelled draw along `f`. -/
theorem refines_couple_TU (α : Loc) (f : Int → Int) (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) (Hz : 0 < z) : iprop%
    ▷ appNatTape α z [] ∗ (∀ n, appNatTape α z [] -∗ ⌜0 ≤ n ∧ n < z⌝ -∗
      refines L E (K.fill pl(#n)) (K'.fill pl(#int (f n))) A) ⊢
    refines L E (K.fill pl(rand(#z, #lbl α)))
      (K'.fill pl(rand(#z, #()))) A := by
  unfold refines
  iintro ⟨Hα, Hcnt⟩ %K2 %b Hj Hna Herr Hpos
  isimp only [fill_comp K2 K'] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_tape_rand z f hdom hbij Hz (K2.comp K') ⊤ α _
  iframe Hα Hj
  iintro %n ⟨HαNew, HKres, %Hn⟩
  isimp only [← fill_comp K2 K'] at HKres
  rw [show ofVal (.int n : Val rT) = pl(#n) from rfl]
  iapply Hcnt $$ %n HαNew %Hn %K2 %b HKres Hna Herr Hpos

/-- Couple a left unlabelled draw with a right tape draw along `f`. -/
theorem refines_couple_UT (α' : Loc) (f : Int → Int) (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) (Hz : 0 < z) : iprop%
    ▷ specNatTape α' z [] ∗ (∀ n, specNatTape α' z [] -∗ ⌜0 ≤ n ∧ n < z⌝ -∗
      refines L E (K.fill pl(#n)) (K'.fill pl(#int (f n))) A) ⊢
    refines L E (K.fill pl(rand(#z, #())))
      (K'.fill pl(rand(#z, #lbl α'))) A := by
  unfold refines
  iintro ⟨Hα', Hcnt⟩ %K2 %b Hj Hna Herr Hpos
  isimp only [fill_comp K2 K'] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_rand_tape z f hdom hbij Hz (K2.comp K') ⊤ α' _
  iframe Hα' Hj
  iintro %n ⟨Hα'New, HKres, %Hn⟩
  isimp only [← fill_comp K2 K'] at HKres
  rw [show ofVal (.int n : Val rT) = pl(#n) from rfl]
  iapply Hcnt $$ %n Hα'New %Hn %K2 %b HKres Hna Herr Hpos

/-- Couple two tape draws along `f`. -/
theorem refines_couple_TT (α α' : Loc) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) (Hz : 0 < z) : iprop%
    ▷ appNatTape α z [] ∗ ▷ specNatTape α' z [] ∗
    (∀ n, appNatTape α z [] -∗ specNatTape α' z [] -∗ ⌜0 ≤ n ∧ n < z⌝ -∗
      refines L E (K.fill pl(#n)) (K'.fill pl(#int (f n))) A) ⊢
    refines L E (K.fill pl(rand(#z, #lbl α)))
      (K'.fill pl(rand(#z, #lbl α'))) A := by
  unfold refines
  iintro ⟨Hα, Hα', Hcnt⟩ %K2 %b Hj Hna Herr Hpos
  isimp only [fill_comp K2 K'] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_rand_lbl_rand_lbl z f hdom hbij Hz (K2.comp K') ⊤ α α' _
  iframe Hα Hα' Hj
  iintro %n ⟨HαNew, Hα'New, HKres, %Hn⟩
  isimp only [← fill_comp K2 K'] at HKres
  rw [show ofVal (.int n : Val rT) = pl(#n) from rfl]
  iapply Hcnt $$ %n HαNew Hα'New %Hn %K2 %b HKres Hna Herr Hpos

/-- Append coupled samples `n` and `f n` to a left and a right tape, without any program step. -/
theorem refines_couple_tapes_bij {α αₛ : Loc} {ns nsₛ : List Int} (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) (Hz : 0 < z) : iprop%
    appNatTape α z ns ∗ specNatTape αₛ z nsₛ ∗
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ appNatTape α z (ns ++ [n]) -∗ specNatTape αₛ z (nsₛ ++ [f n]) -∗
      refines L E e e' A) ⊢
    refines L E e e' A := by
  unfold refines
  iintro ⟨Hα, Hαₛ, Hcnt⟩ %K %b Hj Hna Herr Hpos
  iapply wp_couple_tapes_bij f hdom hbij Hz
  iframe Hα Hαₛ
  iintro %n %hn HA HS
  iapply Hcnt $$ %n %hn HA HS %K %b Hj Hna Herr Hpos

/-! ## Advanced couplings (tv-style) -/

/-- Couple two unlabelled draws along `f`, redistributing the credit `s ε₁` as `s (ε₂ n)`. -/
theorem refines_couple_rands_lr_adv {s : ENNReal →+o B} [L.IsExpectationAdditive s] (f : Int → Int)
    (ε₁ : ENNReal) (ε₂ : Int → ENNReal) (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) (Hz : 0 < z)
    (hamort : (∑ n ∈ Finset.Ico 0 z, ε₂ n) / z.toNat ≤ ε₁) (hc : IsAddLeftRegular (s ε₁)) : iprop%
    ↯b (s ε₁) ∗ (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ ↯b (s (ε₂ n)) -∗
      refines L E (K.fill pl(#n)) (K'.fill pl(#int (f n))) A) ⊢
    refines L E (K.fill pl(rand(#z, #())))
      (K'.fill pl(rand(#z, #()))) A := by
  unfold refines
  iintro ⟨Hε, Hcnt⟩ %K2 %b Hj Hna Herr Hpos
  isimp only [fill_comp K2 K'] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_rand_rand_adv z f ε₁ ε₂ hdom hbij Hz hamort hc (K2.comp K') ⊤ _
  iframe Hj Hε
  iintro %n %Hn - Hec HKres
  isimp only [← fill_comp K2 K'] at HKres
  rw [show ofVal (.int n : Val rT) = pl(#n) from rfl]
  iapply Hcnt $$ %n %Hn Hec %K2 %b HKres Hna Herr Hpos

/-- Couple two unlabelled draws identically, avoiding the outcome `bad` for a credit `s (1/z)`. -/
theorem refines_couple_rands_lr_avoid {s : ENNReal →+o B} [L.IsExpectationAdditive s] (bad : Int)
    (Hz : 0 < z) (habs : L.Absorbing (s 1))
    (hc : IsAddLeftRegular (s (z.toNat : ENNReal)⁻¹)) : iprop%
    ↯b (s (z.toNat : ENNReal)⁻¹) ∗ (∀ n, ⌜(0 ≤ n ∧ n < z) ∧ n ≠ bad⌝ -∗
      refines L E (K.fill pl(#n)) (K'.fill pl(#n)) A) ⊢
    refines L E (K.fill pl(rand(#z, #())))
      (K'.fill pl(rand(#z, #()))) A := by
  classical
  iintro ⟨Hε, Hcnt⟩
  iapply refines_couple_rands_lr_adv id (z.toNat : ENNReal)⁻¹ (fun n => if n = bad then 1 else 0)
    id_dom_range id_bij_range Hz (avoid_one_amort bad) hc
  iframe Hε
  iintro %n %hn Hec
  by_cases hb : n = bad
  · rw [ite_eq_left hb]
    iapply refines_of_absorbing habs $$ Hec
  · simp only [id_eq]
    iapply Hcnt $$ %n %⟨hn, hb⟩

end Reflexive

end Prim

end AppRelRules

end ProbLang
