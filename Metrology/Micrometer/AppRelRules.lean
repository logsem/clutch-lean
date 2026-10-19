module

public import Metrology.Micrometer.AppWeakestpre
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Micrometer.Model
public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.Micrometer.CouplingRules
public import Metrology.Micrometer.OpenInv

@[expose] public section

/-! # Relational Rules -/

open Iris Iris.ProofMode ProbLang.MicrometerWpGS
open scoped AppGS

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT]

section AppRelRules
variable {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B]
  [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors} [IR : MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing]
  [L.HasBind]

/-! ## Forward reductions on the LHS -/

theorem refines_pure_l {E : CoPset} {K : Ectx rT} {e e' t : Exp rT} {A : lrel rT GF}
    {φ : Prop} {n : ℕ} [Hex : PureExec φ n e e'] (Hφ : φ) :
    iprop% ▷^[n] refines L E (K.fill e') t A ⊢ refines L E (K.fill e) t A := by
  have HexK : PureExec φ n (K.fill e) (K.fill e') := PureExec.fill K
  iunfold refines
  iintro H %K' %b HK Hna Herr Hpos
  iapply MicrometerWpGS.wp_pure_step_later' (Hex := HexK) Hφ
  inext
  iapply H $$ HK Hna Herr Hpos

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] [L.HasBind] in
theorem refines_pure_r {E : CoPset} {K : Ectx rT} {e e' t : Exp rT} {A : lrel rT GF}
    {φ : Prop} {n : ℕ} [Hex : PureExec φ n e e'] (Hφ : φ) :
    refines L E t (K.fill e') A ⊢ refines L E t (K.fill e) A := by
  iunfold refines
  iintro H %K' %b Hj Hna Herr Hpos
  rw [Ectx.fill_comp]
  ihave HStep := step_pure (K'.comp K) (Hex := Hex) Hφ $$ Hj
  iapply specUpdate_wp
  iapply specUpdate_mono
  iframe HStep
  iintro HK'
  isimp only [← Ectx.fill_comp K' K e'] at HK'
  iapply H $$ %K' %b HK' Hna Herr Hpos

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] [L.HasBind] in
theorem refines_step_r {E : CoPset} {K' : Ectx rT} {e1 e2 : Exp rT} {A : lrel rT GF} : iprop%
    (∀ (K : Ectx rT), ⤇ K.fill e2 -∗
      specUpdate rT ⊤ (∃ (v : Val rT), iprop(⤇ K.fill v.1 ∗ refines L E e1 (K'.fill v.1) A))) ⊢
    refines L E e1 (K'.fill e2) A := by
  iunfold refines
  iintro He %K'' %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K'' K' e2] at Hj
  ihave HStep := He $$ %(K''.comp K') Hj
  iapply specUpdate_wp
  iapply specUpdate_mono
  iframe HStep
  iintro ⟨%v, HK'', Hrefines⟩
  isimp only [← Ectx.fill_comp K'' K' v.1] at HK''
  iapply Hrefines $$ %K'' %b HK'' Hna Herr Hpos

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] [L.HasBind] in
theorem refines_steps_r {E : CoPset} {K' : Ectx rT} {e1 e2 e2' : Exp rT}
    {A : lrel rT GF} : iprop%
    (∀ (K : Ectx rT), ⤇ K.fill e2 -∗ specUpdate rT ⊤ (⤇ K.fill e2')) ⊢
    (|={⊤}=> refines L E e1 (K'.fill e2') A) -∗ refines L E e1 (K'.fill e2) A := by
  iunfold refines
  iintro Hupd Hlog %K'' %b Hj Hna Herr Hpos
  imod Hlog
  isimp only [Ectx.fill_comp K'' K'] at Hj
  ihave HStep := Hupd $$ %(K''.comp K') Hj
  iapply specUpdate_wp
  iapply specUpdate_mono
  iframe HStep
  iintro HKres
  isimp only [← Ectx.fill_comp K'' K' e2'] at HKres
  iapply Hlog $$ %K'' %b HKres Hna Herr Hpos

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] in
theorem refines_wp_l {E : CoPset} {K : Ectx rT} {e1 t : Exp rT} {A : lrel rT GF} :
    wp L ⊤ e1 (fun v => refines L E (K.fill v.1) t A) ⊢ refines L E (K.fill e1) t A := by
  iunfold refines
  iintro He %K' %b HK Hna Herr Hpos
  iapply MicrometerWpGS.wp_bind
  iapply MicrometerWpGS.wp_frame_wand (R := iprop(⤇ K'.fill t ∗ naOwnP E ∗ ↯b b ∗ ⌜(0 : B) < b⌝))
  iframe
  iapply MicrometerWpGS.wp_mono $$ He
  intro v
  rw [show Exp.ofVal v = v.1 from rfl]
  iintro HRefv ⟨HK, Hna, Herr, Hpos⟩
  iapply HRefv $$ %K' %b HK Hna Herr Hpos

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] in
theorem refines_atomic_l {E E' : CoPset} {K : Ectx rT} {e1 t : Exp rT} {A : lrel rT GF}
    (Hopen : OpenInv L e1) : iprop%
    (∀ (K' : Ectx rT), ⤇ K'.fill t -∗
      |={⊤, E'}=> wp L E' e1 fun v => iprop(|={E', ⊤}=> ∃ t',
        ⤇ K'.fill t' ∗ refines L E (K.fill v.1) t' A)) ⊢
    refines L E (K.fill e1) t A := by
  iunfold refines
  iintro Hlog %K' %b HK Hna Herr Hpos
  iapply MicrometerWpGS.wp_bind
  iapply wp_atomic Hopen
  imod Hlog $$ %K' HK with HW
  imodintro
  iapply MicrometerWpGS.wp_frame_wand (R := iprop(naOwnP E ∗ ↯b b ∗ ⌜(0 : B) < b⌝))
  iframe
  iapply MicrometerWpGS.wp_mono $$ HW
  intro v
  rw [show Exp.ofVal v = v.1 from rfl]
  iintro HFup ⟨Hna, Herr, Hpos⟩
  imod HFup with ⟨%t', HKt', HRef⟩
  imodintro
  iapply HRef $$ %K' %b HKt' Hna Herr Hpos

/-! ## Stateful reductions on the LHS -/

theorem refines_alloc_l {E : CoPset} {K : Ectx rT} {v : Val rT} {t : Exp rT} {A : lrel rT GF} :
    iprop% (∀ l, l ↦ v -∗ refines L E (K.fill pl(#(.loc l))) t A) ⊢
    refines L E (K.fill (.alloc v.1)) t A := by
  iintro Hlog
  iapply refines_wp_l
  rw [show Exp.alloc v.1 = Exp.alloc (Exp.ofVal v) from rfl]
  iapply wp_alloc
  iintro %l Hl
  iapply Hlog $$ %l Hl

theorem refines_load_l {E : CoPset} {K : Ectx rT} {l : Loc} {t : Exp rT} {A : lrel rT GF} :
    iprop% (∃ v, l ↦ v ∗ (l ↦ v -∗ refines L E (K.fill v.1) t A)) ⊢
    refines L E (K.fill pl(!#(.loc l))) t A := by
  iintro ⟨%v, Hl, Hlog⟩
  iapply refines_wp_l
  iapply wp_load
  iframe Hl
  iintro Hl
  iapply Hlog $$ Hl

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

/-! ## Stateful reductions on the RHS -/

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] [L.HasBind] in
theorem refines_alloc_r {E : CoPset} {K : Ectx rT} {v : Val rT} {t : Exp rT} {A : lrel rT GF} :
    iprop% (∀ l, l ↦ₛ v -∗ refines L E t (K.fill pl(#(.loc l))) A) ⊢
    refines L E t (K.fill (.alloc v.1)) A := by
  iintro Hlog
  iapply refines_step_r
  iintro %K' Hj
  iapply specUpdate_mono
  ihave HStep := step_alloc K' v.2 $$ Hj
  iframe HStep
  iintro ⟨%l, HKRes, Hl⟩
  iexists .loc l
  iframe HKRes
  iapply Hlog $$ %l Hl

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] [L.HasBind] in
theorem refines_load_r {E : CoPset} {K : Ectx rT} {l : Loc} {v : Val rT} {t : Exp rT}
    {A : lrel rT GF} : iprop%
    l ↦ₛ v ∗ (l ↦ₛ v -∗ refines L E t (K.fill v.1) A) ⊢
    refines L E t (K.fill pl(!#(.loc l))) A := by
  iintro ⟨Hl, Hlog⟩
  iapply refines_step_r
  iintro %K' Hj
  iapply specUpdate_mono
  ihave HStep := step_load K' $$ [$Hj $Hl]
  iframe HStep
  iintro ⟨HKRes, HlRes⟩
  isimp only [show Exp.ofVal v = v.1 from rfl] at HKRes
  iexists v
  iframe HKRes
  iapply Hlog $$ HlRes

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] [L.HasBind] in
theorem refines_store_r {E : CoPset} {K : Ectx rT} {l : Loc} {v v' : Val rT} {e : Exp rT}
    {A : lrel rT GF} : iprop%
    l ↦ₛ v ∗ (l ↦ₛ v' -∗ refines L E e (K.fill pl(#(.unit))) A) ⊢
    refines L E e (K.fill (.store pl(#(.loc l)) v'.1)) A := by
  iintro ⟨Hl, Hlog⟩
  iapply refines_step_r
  iintro %K' Hj
  iapply specUpdate_mono
  ihave HStep := step_store K' v'.2 (Exp.toVal?_ofVal v') $$ [$Hj $Hl]
  iframe HStep
  iintro ⟨HKRes, Hl'⟩
  iexists .unit
  iframe HKRes
  iapply Hlog $$ Hl'

/-! ## Rand directional rules -/

theorem refines_randU_l {E : CoPset} {K : Ectx rT} {z : Int} {t : Exp rT} {A : lrel rT GF}
    (Hz : 0 < z) : iprop%
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ refines L E (K.fill pl(#(.int n))) t A) ⊢
    refines L E (K.fill pl(rand(#(.int z), #(.unit)))) t A := by
  iintro Hlog
  iapply refines_wp_l
  iapply wp_rand Hz
  iintro %n %Hbnds
  iapply Hlog $$ %n %Hbnds

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

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] [L.HasBind] in
theorem refines_randT_r {E : CoPset} {K : Ectx rT} {l : Loc} {z n : Int} {ns : List Int}
    {e : Exp rT} {A : lrel rT GF} : iprop%
    specNatTape l z (n :: ns) ∗
    (specNatTape l z ns -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ refines L E e (K.fill pl(#(.int n))) A) ⊢
    refines L E e (K.fill pl(rand(#(.int z), #(.lbl l)))) A := by
  unfold refines
  iintro ⟨Hα, Hlog⟩ %K' %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K' K] at Hj
  iapply wp_rand_tape_r (K'.comp K)
  iframe Hj Hα
  iintro HKRes HαNew %Hbnds
  isimp only [← Ectx.fill_comp K' K] at HKRes
  iapply Hlog $$ HαNew %Hbnds %K' %b HKRes Hna Herr Hpos

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

theorem refines_alloctape_l {E : CoPset} {K : Ectx rT} {z : Int} {t : Exp rT} {A : lrel rT GF} :
    iprop% (∀ l, appTapesFrag l (Tape.empty z) -∗ refines L E (K.fill pl(#(.lbl l))) t A) ⊢
    refines L E (K.fill pl(tape(#(.int z)))) t A := by
  iintro Hlog
  iapply refines_wp_l
  iapply wp_alloctape
  iintro %l Hl
  iapply Hlog $$ %l Hl

/-- `refines_alloctape_l` with the fresh tape as an empty `appNatTape`, the form the tape
couplings consume. -/
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

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] [L.HasBind] in
theorem refines_alloctape_r {E : CoPset} {K : Ectx rT} {z : Int} {e : Exp rT} {A : lrel rT GF} :
    iprop% (∀ l, specNatTape l z [] -∗ refines L E e (K.fill pl(#(.lbl l))) A) ⊢
    refines L E e (K.fill pl(tape(#(.int z)))) A := by
  unfold refines
  iintro Hlog %K' %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K' K] at Hj
  iapply wp_alloc_tape_r (K'.comp K)
  iframe Hj
  iintro %l HKRes Hl
  isimp only [← Ectx.fill_comp K' K] at HKRes
  iapply Hlog $$ %l Hl %K' %b HKRes Hna Herr Hpos

/-! ## Structural rules -/

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] in
theorem refines_wand {E : CoPset} {e1 e2 : Exp rT} {A A' : lrel rT GF} : iprop%
    refines L E e1 e2 A ⊢ (∀ v1 v2, A v1 v2 ={⊤}=∗ A' v1 v2) -∗ refines L E e1 e2 A' := by
  iintro He HAA
  ihave H := refines_bind [] [] $$ He
  isimp only [Ectx.fill_nil] at H
  iapply H
  iintro %v %v' HA
  iapply refines_ret rfl rfl
  iapply HAA $$ %v %v' HA

omit [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] in
/-- `refines_bind` as an entailment from its two premises. -/
theorem refines_bind_sep (K K' : Ectx rT) {E : CoPset} {A A' : lrel rT GF} {e e' : Exp rT} : iprop%
    refines L E e e' A ∗
      (∀ v v', A v v' -∗ refines L ⊤ (K.fill v.1) (K'.fill v'.1) A') ⊢
    refines L E (K.fill e) (K'.fill e') A' := by
  iintro ⟨H, Hk⟩
  iapply refines_bind K K' $$ H Hk

omit [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind] in
theorem refines_arrow_val {v v' : Val rT} {A A' : lrel rT GF}
    (hv : v.1.isClosedEmpty ∧ v'.1.isClosedEmpty) : iprop%
    □ (∀ v1 v2, A v1 v2 -∗ refines L ⊤ (.app v.1 v1.1) (.app v'.1 v2.1) A') ⊢
    refines L ⊤ v.1 v'.1 (lrel_arr L A A') := by
  iintro #H
  iapply refines_ret rfl rfl
  imodintro
  unfold lrel_arr
  isplitr; · ipureintro; exact hv
  iintro !> %w1 %w2 HA
  iapply H $$ %w1 %w2 HA

omit [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal]
  [L.IsTopAbsorbing] [L.HasBind] in
theorem refines_arrow {v v' : Val rT} {A A' : lrel rT GF}
    (hv : v.1.isClosedEmpty ∧ v'.1.isClosedEmpty) : iprop%
    □ (∀ (v1 v2 : Val rT), □ refines L ⊤ v1.1 v2.1 A -∗
      refines L ⊤ (.app v.1 v1.1) (.app v'.1 v2.1) A') ⊢
    refines L ⊤ v.1 v'.1 (lrel_arr L A A') := by
  iintro #H
  iapply refines_arrow_val hv
  iintro !> %v1 %v2 #HA
  iapply H $$ %v1 %v2
  iintro !>
  iapply refines_ret rfl rfl
  iapply fupd_intro $$ HA

/-! ## Budget-credit rules

An absorbing credit discharges any refinement; amplification climbs from `↯b (s ε)` to the
absorbing `↯b (s 1)` along any slack map `s`. The `_of_bc` forms take the seed credit as an
argument and work for every budget (dp included, at `s = dpSlack`); the unseeded forms draw the
seed from the threaded budget, which needs every positive budget to carry slack (tv). -/

omit [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind] in
theorem refines_of_absorbing {c : B} (hc : L.Absorbing c) {E : CoPset} {e e' : Exp rT}
    {A : lrel rT GF} : ↯b c ⊢ refines L E e e' A := by
  unfold refines
  iintro Hc %K %b - - - -
  iapply wp_of_absorbing hc $$ Hc

omit [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind] in
theorem refines_get_ec (hsplit : ∀ b : B, 0 < b → ∃ b₁ b₂, 0 < b₁ ∧ 0 < b₂ ∧ b₁ + b₂ ≤ b)
    {E : CoPset} {e e' : Exp rT} {A : lrel rT GF} : iprop%
    (∀ b : B, ↯b b -∗ ⌜0 < b⌝ -∗ refines L E e e' A) ⊢ refines L E e e' A := by
  unfold refines
  iintro Hcnt %K %b Hj Hna Herr %Hpos
  obtain ⟨b₁, b₂, hb₁, hb₂, hle⟩ := hsplit b Hpos
  ihave ⟨Herr1, Herr2⟩ := (BudgetCredit.weaken hle).trans BudgetCredit.split $$ Herr
  iapply Hcnt $$ %b₁ Herr1 %hb₁ %K %b₂ Hj Hna Herr2 %hb₂

omit [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind] in
/-- A seed credit `↯b (s ε)` amplifies by `k` up to the absorbing `↯b (s 1)` (Rocq
`refines_ind_amp`, seed made explicit). -/
theorem refines_ind_amp_of_bc {s : ENNReal →+o B} {ε : ENNReal} {E : CoPset} {e e' : Exp rT}
    {A : lrel rT GF} {k : NNReal} (hε : 0 < ε) (habs : L.Absorbing (s 1)) (hk : 1 < k) : iprop%
    □ (∀ ε', ⌜0 < ε'⌝ -∗ □ (↯b (s ((k : ENNReal) * ε')) -∗ refines L E e e' A) -∗
      ↯b (s ε') -∗ refines L E e e' A) ⊢
    ↯b (s ε) -∗ refines L E e e' A := by
  iintro #Hamp Hε
  iapply BudgetCredit.amplifying hε hk $$ [] Hamp Hε
  iintro !> Hc
  iapply refines_of_absorbing habs $$ Hc

omit [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind] in
theorem refines_ind_amp {s : ENNReal →+o B} {E : CoPset} {e e' : Exp rT} {A : lrel rT GF}
    {k : NNReal} (hsplit : ∀ b : B, 0 < b → ∃ b₁ b₂, 0 < b₁ ∧ 0 < b₂ ∧ b₁ + b₂ ≤ b)
    (hslack : ∀ b : B, 0 < b → ∃ ε, 0 < ε ∧ s ε ≤ b) (habs : L.Absorbing (s 1))
    (hk : 1 < k) : iprop%
    □ (∀ ε, ⌜0 < ε⌝ -∗ □ (↯b (s ((k : ENNReal) * ε)) -∗ refines L E e e' A) -∗ ↯b (s ε) -∗
      refines L E e e' A) ⊢
    refines L E e e' A := by
  iintro #Hamp
  iapply refines_get_ec hsplit
  iintro %b Herr %hpos
  obtain ⟨ε, hε, hle⟩ := hslack b hpos
  iapply refines_ind_amp_of_bc hε habs hk $$ Hamp
  iapply BudgetCredit.weaken hle $$ Herr

omit [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind] in
/-- A seed credit `↯b (s ε)` amplifies a function body uniformly in its arguments (Rocq
`refines_arrow_val_err`, seed made explicit). -/
theorem refines_app_ind_amp_of_bc {s : ENNReal →+o B} {ε : ENNReal} {v v' : Val rT}
    {A A' : lrel rT GF} {k : NNReal} (hε : 0 < ε) (habs : L.Absorbing (s 1)) (hk : 1 < k) :
    iprop%
    □ (∀ ε', ⌜0 < ε'⌝ -∗
      □ (↯b (s ((k : ENNReal) * ε')) -∗
        ∀ v1 v2, A v1 v2 -∗ refines L ⊤ (.app v.1 v1.1) (.app v'.1 v2.1) A') -∗
      ↯b (s ε') -∗ ∀ v1 v2, A v1 v2 -∗ refines L ⊤ (.app v.1 v1.1) (.app v'.1 v2.1) A') ⊢
    ↯b (s ε) -∗ ∀ v1 v2, A v1 v2 -∗ refines L ⊤ (.app v.1 v1.1) (.app v'.1 v2.1) A' := by
  iintro #Hamp Hε
  iapply BudgetCredit.amplifying hε hk $$ [] Hamp Hε
  iintro !> Hc %w1 %w2 -
  iapply refines_of_absorbing habs $$ Hc

omit [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind] in
theorem refines_arrow_val_err {s : ENNReal →+o B} {v v' : Val rT} {A A' : lrel rT GF}
    {k : NNReal} (hsplit : ∀ b : B, 0 < b → ∃ b₁ b₂, 0 < b₁ ∧ 0 < b₂ ∧ b₁ + b₂ ≤ b)
    (hslack : ∀ b : B, 0 < b → ∃ ε, 0 < ε ∧ s ε ≤ b) (habs : L.Absorbing (s 1))
    (hk : 1 < k) (hv : v.1.isClosedEmpty ∧ v'.1.isClosedEmpty) : iprop%
    □ (∀ ε, ⌜0 < ε⌝ -∗
      □ (↯b (s ((k : ENNReal) * ε)) -∗
        ∀ v1 v2, A v1 v2 -∗ refines L ⊤ (.app v.1 v1.1) (.app v'.1 v2.1) A') -∗
      ↯b (s ε) -∗ ∀ v1 v2, A v1 v2 -∗ refines L ⊤ (.app v.1 v1.1) (.app v'.1 v2.1) A') ⊢
    refines L ⊤ v.1 v'.1 (lrel_arr L A A') := by
  iintro #Hamp
  iapply refines_arrow_val hv
  iintro !> %v1 %v2 HA
  iapply refines_get_ec hsplit
  iintro %b Herr %hpos
  obtain ⟨ε, hε, hle⟩ := hslack b hpos
  ihave Herr := BudgetCredit.weaken hle $$ Herr
  iapply refines_app_ind_amp_of_bc hε habs hk $$ Hamp Herr %v1 %v2 HA

/-! ## Coupling-driven rule -/

theorem refines_couple_rands_lr {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int}
    (f : Int → Int) (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) (Hz : 0 < z) : iprop%
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ refines L E (K.fill pl(#(.int n))) (K'.fill pl(#(.int (f n)))) A) ⊢
    refines L E (K.fill pl(rand(#(.int z), #(.unit))))
      (K'.fill pl(rand(#(.int z), #(.unit)))) A := by
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

end AppRelRules

end ProbLang
