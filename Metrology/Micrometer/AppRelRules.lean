module

public import Metrology.Micrometer.AppRelRulesPure
import Metrology.ProbLang.Syntax.Notation

/-! # Relational rules: left state steps and coupled draws

Rules needing `[L.IsReflexive] [L.IsSupportLocal] [L.HasBind]`: left heap and tape steps, draws,
and coupled draws (`U` = unlabelled draw, `T` = tape draw, left program first). The main rule is
`refines_couple_rands_spend`. -/

@[expose] public section

open Iris Iris.ProofMode ProbLang.MicrometerWpGS
open scoped AppGS

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT]

section AppRelRules
variable {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B] [OrderTop B]
  {L : GradedLifting.{0} B} {GF : BundledGFunctors} [IR : MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF]
section Prim
variable [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind]

/-! ## Left heap steps and tape allocation -/

/-- Left allocation `ref v`: continue with a fresh location pointing to `v`. -/
theorem refines_alloc_l {E : CoPset} {K : Ectx rT} {v : Val rT} {t : Exp rT} {A : lrel rT GF} :
    iprop% (∀ l, l ↦ v -∗ refines L E (K.fill pl(#(.loc l))) t A) ⊢
    refines L E (K.fill (.alloc v.1)) t A := by
  iintro Hlog
  iapply refines_wp_l
  rw [show Exp.alloc v.1 = Exp.alloc (Exp.ofVal v) from rfl]
  iapply wp_alloc
  iintro %l Hl
  iapply Hlog $$ %l Hl

/-- Left load `!l`: read the value from the points-to. -/
theorem refines_load_l {E : CoPset} {K : Ectx rT} {l : Loc} {t : Exp rT} {A : lrel rT GF} :
    iprop% (∃ v, l ↦ v ∗ (l ↦ v -∗ refines L E (K.fill v.1) t A)) ⊢
    refines L E (K.fill pl(!#(.loc l))) t A := by
  iintro ⟨%v, Hl, Hlog⟩
  iapply refines_wp_l
  iapply wp_load
  iframe Hl
  iintro Hl
  iapply Hlog $$ Hl

/-- Left store `l := v'`: update the points-to to `v'`. -/
theorem refines_store_l {E : CoPset} {K : Ectx rT} {l : Loc} {v' : Val rT} {t : Exp rT}
    {A : lrel rT GF} : iprop%
    (∃ v : Val rT, l ↦ v ∗ (l ↦ v' -∗ refines L E (K.fill pl(#(.unit))) t A)) ⊢
    refines L E (K.fill (.store pl(#(.loc l)) v'.1)) t A := by
  iintro ⟨%v, Hl, Hlog⟩
  iapply refines_wp_l
  rw [show Exp.store pl(#(.loc l)) v'.1 = Exp.store pl(#(.loc l)) (Exp.ofVal v') from rfl]
  iapply wp_store
  iframe Hl
  iintro Hl
  iapply Hlog $$ Hl

/-- Left tape allocation `tape z`: continue with a fresh empty tape of bound `z`. -/
theorem refines_alloctape_l {E : CoPset} {K : Ectx rT} {z : Int} {t : Exp rT} {A : lrel rT GF} :
    iprop% (∀ l, appTapesFrag l (Tape.empty z) -∗ refines L E (K.fill pl(#(.lbl l))) t A) ⊢
    refines L E (K.fill pl(tape(#(.int z)))) t A := by
  iintro Hlog
  iapply refines_wp_l
  iapply wp_alloctape
  iintro %l Hl
  iapply Hlog $$ %l Hl

/-- Left tape allocation, giving the fresh tape as an empty `appNatTape` (the form the tape
couplings consume). -/
theorem refines_alloctape_nat_l {E : CoPset} {K : Ectx rT} {z : Int} {t : Exp rT}
    {A : lrel rT GF} : iprop%
    (∀ l, appNatTape l z [] -∗ refines L E (K.fill pl(#(.lbl l))) t A) ⊢
    refines L E (K.fill pl(tape(#(.int z)))) t A := by
  iintro Hlog
  iapply refines_alloctape_l
  iintro %l Hl
  iapply Hlog $$ %l
  iapply appNatTape_fold (l := l) (z := z) (ns := []) (fs := []) rfl
  rw [Tape.empty] at *
  iexact Hl

/-! ## One-sided draws -/

/-- Left unlabelled draw `rand z`: continue at every outcome `0 ≤ n < z`. -/
theorem refines_randU_l {E : CoPset} {K : Ectx rT} {z : Int} {t : Exp rT} {A : lrel rT GF}
    (Hz : 0 < z) : iprop%
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ refines L E (K.fill pl(#(.int n))) t A) ⊢
    refines L E (K.fill pl(rand(#(.int z), #(.unit)))) t A := by
  iintro Hlog
  iapply refines_wp_l
  iapply wp_rand Hz
  iintro %n %Hbnds
  iapply Hlog $$ %n %Hbnds

/-- Left draw from a non-empty tape: take its head `n`. -/
theorem refines_randT_l {E : CoPset} {K : Ectx rT} {l : Loc} {z n : Int} {ns : List Int}
    {t : Exp rT} {A : lrel rT GF} : iprop%
    appNatTape l z (n :: ns) ∗
    (appNatTape l z ns -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ refines L E (K.fill pl(#(.int n))) t A) ⊢
    refines L E (K.fill pl(rand(#(.int z), #(.lbl l)))) t A := by
  iintro ⟨Hl, Hlog⟩
  iapply refines_wp_l
  iapply wp_rand_tape
  iframe Hl
  iintro Hl' %Hbnds
  iapply Hlog $$ Hl' %Hbnds

/-- Left draw from an empty tape: behaves like an unlabelled draw, keeping the tape empty. -/
theorem refines_randT_empty_l {E : CoPset} {K : Ectx rT} {l : Loc} {z : Int}
    {t : Exp rT} {A : lrel rT GF} (Hz : 0 < z) : iprop%
    appNatTape l z [] ∗
    (∀ n, appNatTape l z [] -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ refines L E (K.fill pl(#(.int n))) t A) ⊢
    refines L E (K.fill pl(rand(#(.int z), #(.lbl l)))) t A := by
  iintro ⟨Hl, Hlog⟩
  iapply refines_wp_l
  iapply wp_rand_tape_empty Hz
  iframe Hl
  iintro %n Hl' %Hbnds
  iapply Hlog $$ %n Hl' %Hbnds

/-- Right unlabelled draw `rand z`: continue at every outcome `0 ≤ n < z`. -/
theorem refines_randU_r {E : CoPset} {K : Ectx rT} {z : Int} {e : Exp rT} {A : lrel rT GF}
    (Hz : 0 < z) : iprop%
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ refines L E e (K.fill pl(#(.int n))) A) ⊢
    refines L E e (K.fill pl(rand(#(.int z), #(.unit)))) A := by
  unfold refines
  iintro Hlog %K' %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K' K] at Hj
  iapply wp_rand_r (K'.comp K) Hz
  iframe Hj
  iintro %n %Hbnds HKRes
  isimp only [← Ectx.fill_comp K' K] at HKRes
  iapply Hlog $$ %n %Hbnds %K' %b HKRes Hna Herr Hpos

/-- Right draw from an empty spec tape: continue at every outcome, keeping the tape empty. -/
theorem refines_randT_empty_r {E : CoPset} {K : Ectx rT} {l : Loc} {z : Int}
    {e : Exp rT} {A : lrel rT GF} (Hz : 0 < z) : iprop%
    specNatTape l z [] ∗
    (∀ n, specNatTape l z [] -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ refines L E e (K.fill pl(#(.int n))) A) ⊢
    refines L E e (K.fill pl(rand(#(.int z), #(.lbl l)))) A := by
  unfold refines
  iintro ⟨Hα, Hlog⟩ %K' %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K' K] at Hj
  iapply wp_rand_tape_empty_r (K'.comp K) Hz
  iframe Hj Hα
  iintro %n HαNew HKRes %Hbnds
  isimp only [← Ectx.fill_comp K' K] at HKRes
  iapply Hlog $$ %n HαNew %Hbnds %K' %b HKRes Hna Herr Hpos

/-! ## Coupled draws within a budget -/

omit [L.IsReflexive] in
/-- Couple `rand N ~ rand N` along `S`, given a lifting of the two uniform draws within the
cancelable budget `c`; spends `↯b c` (relational `wp_couple_rand_rand_spend`). -/
theorem refines_couple_rands_spend {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} (N : Int)
    (HN : 0 < N) (S : Int → Int → Prop) (c : B) (hc : IsAddLeftRegular c)
    (Hcpl : L.Rel c S (unifInt N HN) (unifInt N HN)) : iprop%
    ↯b c ∗ (∀ r r', ⌜S r r'⌝ -∗
      refines L E (K.fill pl(#(.int r))) (K'.fill pl(#(.int r'))) A) ⊢
    refines L E (K.fill pl(rand(#(.int N), #(.unit))))
      (K'.fill pl(rand(#(.int N), #(.unit)))) A := by
  unfold refines
  iintro ⟨Hc, Hcnt⟩ %K2 %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_rand_rand_spend N HN S c hc Hcpl (K2.comp K') ⊤ _
  iframe Hj Hc
  iintro %r %r' %hS HKres
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.int r : Val rT) = pl(#(.int r)) from rfl]
  iapply Hcnt $$ %r %r' %hS %K2 %b HKres Hna Herr Hpos

/-! ## Budget-free couplings along a bijection

`f` is a bijection of `{0, …, z-1}`; the right draw returns `f n` when the left returns `n`. -/

/-- Couple two unlabelled draws `rand z ~ rand z` along the bijection `f`. -/
theorem refines_couple_rands_lr {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int}
    (f : Int → Int) (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) (Hz : 0 < z) : iprop%
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ refines L E (K.fill pl(#(.int n))) (K'.fill pl(#(.int (f n)))) A) ⊢
    refines L E (K.fill pl(rand(#(.int z), #(.unit))))
      (K'.fill pl(rand(#(.int z), #(.unit)))) A := by
  -- Each coupled-draw rule: unfold `refines`, merge the spec context `K2` with `K'`, apply the
  -- unary `wp` coupling rule, then split the context again for the continuation.
  unfold refines
  iintro Hcnt %K2 %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_rand_rand z f hdom hbij Hz (K2.comp K') ⊤ _
  iframe Hj
  iintro %n %Hn HKres
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.int n : Val rT) = pl(#(.int n)) from rfl]
  iapply Hcnt $$ %n %Hn %K2 %b HKres Hna Herr Hpos

/-- Couple a left tape draw with a right unlabelled draw along `f`. -/
theorem refines_couple_TU {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int}
    (α : Loc) (f : Int → Int) (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) (Hz : 0 < z) : iprop%
    ▷ appNatTape α z [] ∗ (∀ n, appNatTape α z [] -∗ ⌜0 ≤ n ∧ n < z⌝ -∗
      refines L E (K.fill pl(#(.int n))) (K'.fill pl(#(.int (f n)))) A) ⊢
    refines L E (K.fill pl(rand(#(.int z), #(.lbl α))))
      (K'.fill pl(rand(#(.int z), #(.unit)))) A := by
  unfold refines
  iintro ⟨Hα, Hcnt⟩ %K2 %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_tape_rand z f hdom hbij Hz (K2.comp K') ⊤ α _
  iframe Hα Hj
  iintro %n ⟨HαNew, HKres, %Hn⟩
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.int n : Val rT) = pl(#(.int n)) from rfl]
  iapply Hcnt $$ %n HαNew %Hn %K2 %b HKres Hna Herr Hpos

/-- Couple a left unlabelled draw with a right tape draw along `f`. -/
theorem refines_couple_UT {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int}
    (α' : Loc) (f : Int → Int) (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) (Hz : 0 < z) : iprop%
    ▷ specNatTape α' z [] ∗ (∀ n, specNatTape α' z [] -∗ ⌜0 ≤ n ∧ n < z⌝ -∗
      refines L E (K.fill pl(#(.int n))) (K'.fill pl(#(.int (f n)))) A) ⊢
    refines L E (K.fill pl(rand(#(.int z), #(.unit))))
      (K'.fill pl(rand(#(.int z), #(.lbl α')))) A := by
  unfold refines
  iintro ⟨Hα', Hcnt⟩ %K2 %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_rand_tape z f hdom hbij Hz (K2.comp K') ⊤ α' _
  iframe Hα' Hj
  iintro %n ⟨Hα'New, HKres, %Hn⟩
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.int n : Val rT) = pl(#(.int n)) from rfl]
  iapply Hcnt $$ %n Hα'New %Hn %K2 %b HKres Hna Herr Hpos

/-- Couple two tape draws along `f`. -/
theorem refines_couple_TT {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int}
    (α α' : Loc) (f : Int → Int) (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) (Hz : 0 < z) : iprop%
    ▷ appNatTape α z [] ∗ ▷ specNatTape α' z [] ∗
    (∀ n, appNatTape α z [] -∗ specNatTape α' z [] -∗ ⌜0 ≤ n ∧ n < z⌝ -∗
      refines L E (K.fill pl(#(.int n))) (K'.fill pl(#(.int (f n)))) A) ⊢
    refines L E (K.fill pl(rand(#(.int z), #(.lbl α))))
      (K'.fill pl(rand(#(.int z), #(.lbl α')))) A := by
  unfold refines
  iintro ⟨Hα, Hα', Hcnt⟩ %K2 %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_rand_lbl_rand_lbl z f hdom hbij Hz (K2.comp K') ⊤ α α' _
  iframe Hα Hα' Hj
  iintro %n ⟨HαNew, Hα'New, HKres, %Hn⟩
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.int n : Val rT) = pl(#(.int n)) from rfl]
  iapply Hcnt $$ %n HαNew Hα'New %Hn %K2 %b HKres Hna Herr Hpos

/-- Append coupled samples `n` and `f n` to a left and a right tape, without any program step. -/
theorem refines_couple_tapes_bij {E : CoPset} {e e' : Exp rT} {A : lrel rT GF}
    {z : Int} {α αₛ : Loc} {ns nsₛ : List Int} (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) : iprop%
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

/-! ## Advanced couplings (tv-style)

Pay `↯b (s ε₁)` and receive `↯b (s (ε₂ n))` at outcome `n`, where the average of `ε₂` is at most
`ε₁`. -/

/-- Couple two unlabelled draws along `f`, redistributing the credit `s ε₁` as `s (ε₂ n)`. -/
theorem refines_couple_rands_lr_adv {s : ENNReal →+o B}
    [L.IsExpectationAdditive s] {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int}
    (f : Int → Int) (ε₁ : ENNReal) (ε₂ : Int → ENNReal)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (hamort : (∑ n ∈ Finset.Ico 0 z, ε₂ n) / z.toNat ≤ ε₁)
    (hc : IsAddLeftRegular (s ε₁)) : iprop%
    ↯b (s ε₁) ∗ (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ ↯b (s (ε₂ n)) -∗
      refines L E (K.fill pl(#(.int n))) (K'.fill pl(#(.int (f n)))) A) ⊢
    refines L E (K.fill pl(rand(#(.int z), #(.unit))))
      (K'.fill pl(rand(#(.int z), #(.unit)))) A := by
  unfold refines
  iintro ⟨Hε, Hcnt⟩ %K2 %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply MicrometerWpGS.wp_bind
  iapply wp_couple_rand_rand_adv z f ε₁ ε₂ hdom hbij Hz hamort hc (K2.comp K') ⊤ _
  iframe Hj Hε
  iintro %n %Hn - Hec HKres
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.int n : Val rT) = pl(#(.int n)) from rfl]
  iapply Hcnt $$ %n %Hn Hec %K2 %b HKres Hna Herr Hpos

/-- Couple two unlabelled draws identically, avoiding the outcome `bad` for a credit `s (1/z)`. -/
theorem refines_couple_rands_lr_avoid {s : ENNReal →+o B}
    [L.IsExpectationAdditive s] {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int}
    (bad : Int) (Hz : 0 < z) (habs : L.Absorbing (s 1))
    (hc : IsAddLeftRegular (s (z.toNat : ENNReal)⁻¹)) : iprop%
    ↯b (s (z.toNat : ENNReal)⁻¹) ∗ (∀ n, ⌜(0 ≤ n ∧ n < z) ∧ n ≠ bad⌝ -∗
      refines L E (K.fill pl(#(.int n))) (K'.fill pl(#(.int n))) A) ⊢
    refines L E (K.fill pl(rand(#(.int z), #(.unit))))
      (K'.fill pl(rand(#(.int z), #(.unit)))) A := by
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

end Prim

end AppRelRules

end ProbLang
