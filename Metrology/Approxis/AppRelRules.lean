module

public import Metrology.Approxis.AppWeakestpre
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Approxis.Model
public import Metrology.Approxis.PrimitiveLaws
public import Metrology.Approxis.CouplingRules
public import Metrology.Approxis.OpenInv

@[expose] public section

/-! # Relational Rules -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS
open scoped AppGS

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT]

section AppRelRules
variable {hlc : HasLC} {ι : Type} [Monoid ι] {Δ : GradedDivergence.{0} ι}
  {GF : BundledGFunctors} [IR : ApproxisRGS rT hlc Δ GF]
  [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft]

/-! ## Forward reductions on the LHS -/

theorem refines_pure_l {E : CoPset} {K : Ectx rT} {e e' t : Exp rT} {A : lrel rT GF}
    {φ : Prop} {n : ℕ} [Hex : PureExec φ n e e'] (Hφ : φ) :
    iprop% ▷^[n] refines E (K.fill e') t A ⊢ refines E (K.fill e) t A := by
  have HexK : PureExec φ n (K.fill e) (K.fill e') := PureExec.fill K
  iunfold refines
  iintro H %K' %ε HK Hna Herr Hpos
  iapply ApproxisWpGS.wp_pure_step_later' (Hex := HexK) Hφ
  inext
  iapply H $$ HK Hna Herr Hpos

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_pure_r {E : CoPset} {K : Ectx rT} {e e' t : Exp rT} {A : lrel rT GF}
    {φ : Prop} {n : ℕ} [Hex : PureExec φ n e e'] (Hφ : φ) :
    refines E t (K.fill e') A ⊢ refines E t (K.fill e) A := by
  iunfold refines
  iintro H %K' %ε Hj Hna Herr Hpos
  rw [Ectx.fill_comp]
  ihave HStep := step_pure (K'.comp K) (Hex := Hex) Hφ $$ Hj
  iapply specUpdate_wp
  iapply specUpdate_mono
  iframe HStep
  iintro HK'
  isimp only [← Ectx.fill_comp K' K e'] at HK'
  iapply H $$ %K' %ε HK' Hna Herr Hpos

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_step_r {E : CoPset} {K' : Ectx rT} {e1 e2 : Exp rT} {A : lrel rT GF} : iprop%
    (∀ (K : Ectx rT), ⤇ K.fill e2 -∗
      specUpdate rT ⊤ (∃ (v : Val rT), iprop(⤇ K.fill v.1 ∗ refines E e1 (K'.fill v.1) A))) ⊢
    refines E e1 (K'.fill e2) A := by
  iunfold refines
  iintro He %K'' %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K'' K' e2] at Hj
  ihave HStep := He $$ %(K''.comp K') Hj
  iapply specUpdate_wp
  iapply specUpdate_mono
  iframe HStep
  iintro ⟨%v, HK'', Hrefines⟩
  isimp only [← Ectx.fill_comp K'' K' v.1] at HK''
  iapply Hrefines $$ %K'' %ε HK'' Hna Herr Hpos

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_steps_r {E : CoPset} {K' : Ectx rT} {e1 e2 e2' : Exp rT}
    {A : lrel rT GF} : iprop%
    (∀ (K : Ectx rT), ⤇ K.fill e2 -∗ specUpdate rT ⊤ (⤇ K.fill e2')) ⊢
    (|={⊤}=> refines E e1 (K'.fill e2') A) -∗ refines E e1 (K'.fill e2) A := by
  iunfold refines
  iintro Hupd Hlog %K'' %ε Hj Hna Herr Hpos
  imod Hlog
  isimp only [Ectx.fill_comp K'' K'] at Hj
  ihave HStep := Hupd $$ %(K''.comp K') Hj
  iapply specUpdate_wp
  iapply specUpdate_mono
  iframe HStep
  iintro HKres
  isimp only [← Ectx.fill_comp K'' K' e2'] at HKres
  iapply Hlog $$ %K'' %ε HKres Hna Herr Hpos

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_wp_l {E : CoPset} {K : Ectx rT} {e1 t : Exp rT} {A : lrel rT GF} :
    wp ⊤ e1 (fun v => refines E (K.fill v.1) t A) ⊢ refines E (K.fill e1) t A := by
  iintro He
  iunfold refines
  iintro %K' %ε HK Hna Herr Hpos
  iapply ApproxisWpGS.wp_bind (K := K)
  let R : IProp GF := iprop% ⤇ K'.fill t ∗ naOwnP (rT := rT) E ∗ ↯ ε ∗ ⌜0 < ε⌝
  ihave HR : R $$ [HK Hna Herr Hpos]
  · isplitl [HK]; · iassumption
    iframe
  ihave HFrame : wp ⊤ e1 (fun v => iprop(R ∗ refines E (K.fill v.1) t A)) $$ [HR He]
  · iapply ApproxisWpGS.wp_frame_l (Φ := fun v => refines E (K.fill v.1) t A)
    iframe HR He
  iapply ApproxisWpGS.wp_mono $$ HFrame
  intro v
  rw [show Exp.ofVal v = v.1 from rfl]
  iintro ⟨⟨HK, Hna, Herr, Hpos⟩, HRefv⟩
  iunfold refines at HRefv
  iapply HRefv $$ %K' %ε HK Hna Herr Hpos

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_atomic_l {E E' : CoPset} {K : Ectx rT} {e1 t : Exp rT} {A : lrel rT GF}
    (Hopen : OpenInv Δ e1) : iprop%
    (∀ (K' : Ectx rT), ⤇ K'.fill t -∗
      |={⊤, E'}=> wp E' e1 fun v => iprop(|={E', ⊤}=> ∃ t',
        ⤇ K'.fill t' ∗ refines E (K.fill v.1) t' A)) ⊢
    refines E (K.fill e1) t A := by
  iintro Hlog
  iunfold refines
  iintro %K' %ε HK Hna Herr Hpos
  iapply ApproxisWpGS.wp_bind (K := K)
  iapply wp_atomic Hopen
  imod Hlog $$ %K' HK with HW
  imodintro
  let R : IProp GF := iprop% naOwnP (rT := rT) E ∗ ↯ ε ∗ ⌜0 < ε⌝
  ihave HR : R $$ [Hna Herr Hpos]
  · isplitl [Hna]; · iassumption
    iframe
  ihave HFrame : wp E' e1 (fun v => iprop(R ∗
      (|={E', ⊤}=> ∃ t', ⤇ K'.fill t' ∗ refines E (K.fill v.1) t' A))) $$ [HR HW]
  · iapply ApproxisWpGS.wp_frame_l
      (Φ := fun v => iprop(|={E',⊤}=> ∃ t', ⤇ K'.fill t' ∗ refines E (K.fill v.1) t' A))
    iframe HR HW
  iapply ApproxisWpGS.wp_mono $$ HFrame
  intro v
  rw [show Exp.ofVal v = v.1 from rfl]
  iintro ⟨⟨Hna, Herr, Hpos⟩, HFup⟩
  imod HFup with ⟨%t', HKt', HRef⟩
  imodintro
  iunfold refines at HRef
  iapply HRef $$ %K' %ε HKt' Hna Herr Hpos

/-! ## Stateful reductions on the LHS -/

theorem refines_alloc_l {E : CoPset} {K : Ectx rT} {v : Val rT} {t : Exp rT} {A : lrel rT GF} :
    iprop% (∀ l, l ↦ v -∗ refines E (K.fill pl(#(.loc l))) t A) ⊢
    refines E (K.fill (.alloc v.1)) t A := by
  iintro Hlog
  iapply refines_wp_l
  rw [show Exp.alloc v.1 = Exp.alloc (Exp.ofVal v) from rfl]
  iapply wp_alloc
  iintro %l Hl
  iapply Hlog $$ %l Hl

theorem refines_load_l {E : CoPset} {K : Ectx rT} {l : Loc} {t : Exp rT} {A : lrel rT GF} :
    iprop% (∃ v, l ↦ v ∗ (l ↦ v -∗ refines E (K.fill v.1) t A)) ⊢
    refines E (K.fill pl(!#(.loc l))) t A := by
  iintro ⟨%v, Hl, Hlog⟩
  iapply refines_wp_l
  iapply wp_load
  iframe Hl
  iintro Hl
  iapply Hlog $$ Hl

theorem refines_store_l {E : CoPset} {K : Ectx rT} {l : Loc} {v' : Val rT} {t : Exp rT}
    {A : lrel rT GF} : iprop%
    (∃ v : Val rT, l ↦ v ∗ (l ↦ v' -∗ refines E (K.fill pl(#(.unit))) t A)) ⊢
    refines E (K.fill (.store pl(#(.loc l)) v'.1)) t A := by
  iintro ⟨%v, Hl, Hlog⟩
  iapply refines_wp_l
  rw [show Exp.store pl(#(.loc l)) v'.1 = Exp.store pl(#(.loc l)) (Exp.ofVal v') from rfl]
  iapply wp_store (v' := v)
  iframe Hl
  iintro Hl
  iapply Hlog $$ Hl

/-! ## Stateful reductions on the RHS -/

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_alloc_r {E : CoPset} {K : Ectx rT} {v : Val rT} {t : Exp rT} {A : lrel rT GF} :
    iprop% (∀ l, l ↦ₛ v -∗ refines E t (K.fill pl(#(.loc l))) A) ⊢
    refines E t (K.fill (.alloc v.1)) A := by
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

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_load_r {E : CoPset} {K : Ectx rT} {l : Loc} {v : Val rT} {t : Exp rT}
    {A : lrel rT GF} : iprop%
    l ↦ₛ v ∗ (l ↦ₛ v -∗ refines E t (K.fill v.1) A) ⊢ refines E t (K.fill pl(!#(.loc l))) A := by
  iintro ⟨Hl, Hlog⟩
  iapply refines_step_r
  iintro %K' Hj
  iapply specUpdate_mono
  ihave HStep := step_load K' (v := v) $$ [$Hj $Hl]
  iframe HStep
  iintro ⟨HKRes, HlRes⟩
  isimp only [show Exp.ofVal v = v.1 from rfl] at HKRes
  iexists v
  iframe HKRes
  iapply Hlog $$ HlRes

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_store_r {E : CoPset} {K : Ectx rT} {l : Loc} {v v' : Val rT} {e : Exp rT}
    {A : lrel rT GF} : iprop%
    l ↦ₛ v ∗ (l ↦ₛ v' -∗ refines E e (K.fill pl(#(.unit))) A) ⊢
    refines E e (K.fill (.store pl(#(.loc l)) v'.1)) A := by
  iintro ⟨Hl, Hlog⟩
  iapply refines_step_r
  iintro %K' Hj
  iapply specUpdate_mono
  ihave HStep := step_store K' (v_old := v) v'.2 (Exp.toVal?_ofVal v') $$ [$Hj $Hl]
  iframe HStep
  iintro ⟨HKRes, Hl'⟩
  iexists .unit
  iframe HKRes
  iapply Hlog $$ Hl'

/-! ## Rand directional rules -/

theorem refines_randU_l {E : CoPset} {K : Ectx rT} {z : Int} {t : Exp rT} {A : lrel rT GF}
    (Hz : 0 < z) : iprop%
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ refines E (K.fill pl(#(.int n))) t A) ⊢
    refines E (K.fill pl(rand(#(.int z), #(.unit)))) t A := by
  iintro Hlog
  iapply refines_wp_l
  iapply wp_rand Hz
  iintro %n %Hbnds
  iapply Hlog $$ %n %Hbnds

theorem refines_randT_l {E : CoPset} {K : Ectx rT} {l : Loc} {z n : Int} {ns : List Int}
    {t : Exp rT} {A : lrel rT GF} : iprop%
    appNatTape l z (n :: ns) ∗
    (appNatTape l z ns -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ refines E (K.fill pl(#(.int n))) t A) ⊢
    refines E (K.fill pl(rand(#(.int z), #(.lbl l)))) t A := by
  iintro ⟨Hl, Hlog⟩
  iapply refines_wp_l
  iapply wp_rand_tape
  iframe Hl
  iintro Hl' %Hbnds
  iapply Hlog $$ Hl' %Hbnds

theorem refines_randT_empty_l {E : CoPset} {K : Ectx rT} {l : Loc} {z : Int}
    {t : Exp rT} {A : lrel rT GF} (Hz : 0 < z) : iprop%
    appNatTape l z [] ∗
    (∀ n, appNatTape l z [] -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ refines E (K.fill pl(#(.int n))) t A) ⊢
    refines E (K.fill pl(rand(#(.int z), #(.lbl l)))) t A := by
  iintro ⟨Hl, Hlog⟩
  iapply refines_wp_l
  iapply wp_rand_tape_empty Hz
  iframe Hl
  iintro %n Hl' %Hbnds
  iapply Hlog $$ %n Hl' %Hbnds

theorem refines_randU_r {E : CoPset} {K : Ectx rT} {z : Int} {e : Exp rT} {A : lrel rT GF}
    (Hz : 0 < z) : iprop%
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ refines E e (K.fill pl(#(.int n))) A) ⊢
    refines E e (K.fill pl(rand(#(.int z), #(.unit)))) A := by
  iintro Hlog
  unfold refines
  iintro %K' %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K' K] at Hj
  iapply wp_rand_r (K'.comp K) Hz
  iframe Hj
  iintro %n %Hbnds HKRes
  isimp only [← Ectx.fill_comp K' K] at HKRes
  iapply Hlog $$ %n %Hbnds %K' %ε HKRes Hna Herr Hpos

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_randT_r {E : CoPset} {K : Ectx rT} {l : Loc} {z n : Int} {ns : List Int}
    {e : Exp rT} {A : lrel rT GF} : iprop%
    specNatTape l z (n :: ns) ∗
    (specNatTape l z ns -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ refines E e (K.fill pl(#(.int n))) A) ⊢
    refines E e (K.fill pl(rand(#(.int z), #(.lbl l)))) A := by
  iintro ⟨Hα, Hlog⟩
  unfold refines
  iintro %K' %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K' K] at Hj
  iapply wp_rand_tape_r (K'.comp K)
  iframe Hj Hα
  iintro HKRes HαNew %Hbnds
  isimp only [← Ectx.fill_comp K' K] at HKRes
  iapply Hlog $$ HαNew %Hbnds %K' %ε HKRes Hna Herr Hpos

theorem refines_randT_empty_r {E : CoPset} {K : Ectx rT} {l : Loc} {z : Int}
    {e : Exp rT} {A : lrel rT GF} (Hz : 0 < z) : iprop%
    specNatTape l z [] ∗
    (∀ n, specNatTape l z [] -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ refines E e (K.fill pl(#(.int n))) A) ⊢
    refines E e (K.fill pl(rand(#(.int z), #(.lbl l)))) A := by
  iintro ⟨Hα, Hlog⟩
  unfold refines
  iintro %K' %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K' K] at Hj
  iapply wp_rand_tape_empty_r (K'.comp K) Hz
  iframe Hj Hα
  iintro %n HαNew HKRes %Hbnds
  isimp only [← Ectx.fill_comp K' K] at HKRes
  iapply Hlog $$ %n HαNew %Hbnds %K' %ε HKRes Hna Herr Hpos

theorem refines_alloctape_l {E : CoPset} {K : Ectx rT} {z : Int} {t : Exp rT} {A : lrel rT GF} :
    iprop% (∀ l, appTapesFrag l (Tape.empty z) -∗ refines E (K.fill pl(#(.lbl l))) t A) ⊢
    refines E (K.fill pl(tape(#(.int z)))) t A := by
  iintro Hlog
  iapply refines_wp_l
  iapply wp_alloctape
  iintro %l Hl
  iapply Hlog $$ %l Hl

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_alloctape_r {E : CoPset} {K : Ectx rT} {z : Int} {e : Exp rT} {A : lrel rT GF} :
    iprop% (∀ l, specNatTape l z [] -∗ refines E e (K.fill pl(#(.lbl l))) A) ⊢
    refines E e (K.fill pl(tape(#(.int z)))) A := by
  iintro Hlog
  unfold refines
  iintro %K' %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K' K] at Hj
  iapply wp_alloc_tape_r (K'.comp K)
  iframe Hj
  iintro %l HKRes Hl
  isimp only [← Ectx.fill_comp K' K] at HKRes
  iapply Hlog $$ %l Hl %K' %ε HKRes Hna Herr Hpos

/-! ## Structural rules -/

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_wand {E : CoPset} {e1 e2 : Exp rT} {A A' : lrel rT GF} : iprop%
    refines E e1 e2 A ⊢ (∀ v1 v2, A v1 v2 ={⊤}=∗ A' v1 v2) -∗ refines E e1 e2 A' := by
  iintro He HAA
  have Hfill1 : e1 = Ectx.empty.fill e1 := rfl
  have Hfill2 : e2 = Ectx.empty.fill e2 := rfl
  rw [Hfill1, Hfill2]
  iapply refines_bind (K' := Ectx.empty) (A := A) $$ [He]
  · rw [← Hfill1, ← Hfill2]; iexact He
  iintro %v %v' HA
  rw [← show v.1 = Ectx.empty.fill v.1 from rfl, ← show v'.1 = Ectx.empty.fill v'.1 from rfl]
  iapply refines_ret (v1 := v) (v2 := v') rfl rfl
  iapply HAA $$ %v %v' HA

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_arrow_val {v v' : Val rT} {A A' : lrel rT GF}
    (hv : v.1.isClosedEmpty ∧ v'.1.isClosedEmpty) : iprop%
    □ (∀ v1 v2, A v1 v2 -∗ refines ⊤ (.app v.1 v1.1) (.app v'.1 v2.1) A') ⊢
    refines ⊤ v.1 v'.1 (lrel_arr A A') := by
  iintro #H
  iapply refines_ret (v1 := v) (v2 := v') rfl rfl
  imodintro
  unfold lrel_arr
  isplitr; · ipureintro; exact hv
  iintro !> %w1 %w2 HA
  iapply H $$ %w1 %w2 HA

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_arrow {v v' : Val rT} {A A' : lrel rT GF}
    (hv : v.1.isClosedEmpty ∧ v'.1.isClosedEmpty) : iprop%
    □ (∀ (v1 v2 : Val rT), □ refines ⊤ v1.1 v2.1 A -∗
      refines ⊤ (.app v.1 v1.1) (.app v'.1 v2.1) A') ⊢
    refines ⊤ v.1 v'.1 (lrel_arr A A') := by
  iintro #H
  iapply refines_arrow_val hv
  iintro !> %v1 %v2 #HA
  iapply H $$ %v1 %v2
  iintro !>
  iapply refines_ret rfl rfl
  imodintro
  iexact HA

/-! ## Error-credit rules -/

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_get_ec {E : CoPset} {e e' : Exp rT} {A : lrel rT GF} : iprop%
    (∀ ε, ↯ ε -∗ ⌜0 < ε⌝ -∗ refines E e e' A) ⊢ refines E e e' A := by
  iintro Hcnt
  unfold refines
  iintro %K %ε Hj Hna HerrTot %HposTot
  ihave HerrEq : ↯ (ε / 2 + ε / 2) $$ [HerrTot]
  · rw [ENNReal.add_halves]; iexact HerrTot
  ihave ⟨Herr1, Herr2⟩ := ErrorCredit.split $$ HerrEq
  have hpos2 : 0 < ε / 2 := ENNReal.half_pos HposTot.ne'
  iapply Hcnt $$ %(ε / 2) Herr1 %hpos2 %K %(ε / 2) Hj Hna Herr2 %hpos2

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_ind_amp {E : CoPset} {e e' : Exp rT} {A : lrel rT GF} {k : NNReal}
    (hk : 1 < k) : iprop%
    □ (∀ (ε : ENNReal), ⌜0 < ε⌝ -∗ □ (↯ ((k : ENNReal) * ε) -∗ refines E e e' A) -∗ ↯ ε -∗
      refines E e e' A) ⊢
    refines E e e' A := by
  iintro #Hamp
  iapply refines_get_ec
  iintro %ε Herr %hpos
  iapply ErrorCredit.Induction.amplifying hpos hk $$ [] Herr
  iintro !> %ε' %hε' #Hstep Hε'
  iapply Hamp $$ %ε' %hε' Hstep Hε'

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_arrow_val_err {v v' : Val rT} {A A' : lrel rT GF} {k : NNReal}
    (hk : 1 < k) (hv : v.1.isClosedEmpty ∧ v'.1.isClosedEmpty) : iprop%
    □ (∀ (ε : ENNReal), ⌜0 < ε⌝ -∗
      □ (↯ ((k : ENNReal) * ε) -∗
        ∀ v1 v2, A v1 v2 -∗ refines ⊤ (.app v.1 v1.1) (.app v'.1 v2.1) A') -∗
      ↯ ε -∗ ∀ v1 v2, A v1 v2 -∗ refines ⊤ (.app v.1 v1.1) (.app v'.1 v2.1) A') ⊢
    refines ⊤ v.1 v'.1 (lrel_arr A A') := by
  iintro #Hamp
  iapply refines_arrow_val hv
  iintro !> %v1 %v2 HA
  iapply refines_get_ec
  iintro %ε Herr %hpos
  ihave Hall := ErrorCredit.Induction.amplifying
      (P := iprop(∀ w1 w2, A w1 w2 -∗ refines ⊤ (.app v.1 w1.1) (.app v'.1 w2.1) A')) hpos hk
    $$ [] Herr
  · iintro !> %ε' %hε' #Hstep Hε'
    iapply Hamp $$ %ε' %hε' Hstep Hε'
  iapply Hall $$ %v1 %v2 HA

/-! ## Coupling-driven rule -/

theorem refines_couple_rands_lr {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int}
    (f : Int → Int) (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) (Hz : 0 < z) : iprop%
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ refines E (K.fill pl(#(.int n))) (K'.fill pl(#(.int (f n)))) A) ⊢
    refines E (K.fill pl(rand(#(.int z), #(.unit))))
      (K'.fill pl(rand(#(.int z), #(.unit)))) A := by
  iintro Hcnt
  unfold refines
  iintro %K2 %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply ApproxisWpGS.wp_bind (K := K)
  iapply wp_couple_rand_rand z f hdom hbij Hz (K2.comp K') ⊤ _
  iframe Hj
  iintro %n %Hn HKres
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.int n : Val rT) = pl(#(.int n)) from rfl]
  iapply Hcnt $$ %n %Hn %K2 %ε HKres Hna Herr Hpos

theorem refines_couple_rands_lr_adv {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int}
    (f : Int → Int) (ε₁ : ENNReal) (ε₂ : Int → ENNReal)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (hamort : (∑ n ∈ Finset.Ico 0 z, ε₂ n) / z.toNat ≤ ε₁) : iprop%
    ↯ ε₁ ∗ (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ ↯ ε₂ n -∗
      refines E (K.fill pl(#(.int n))) (K'.fill pl(#(.int (f n)))) A) ⊢
    refines E (K.fill pl(rand(#(.int z), #(.unit))))
      (K'.fill pl(rand(#(.int z), #(.unit)))) A := by
  iintro ⟨Hε, Hcnt⟩
  unfold refines
  iintro %K2 %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply ApproxisWpGS.wp_bind (K := K)
  iapply wp_couple_rand_rand_adv z f ε₁ ε₂ hdom hbij Hz hamort (K2.comp K') ⊤ _
  iframe Hj Hε
  iintro %n %Hn Hec HKres
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.int n : Val rT) = pl(#(.int n)) from rfl]
  iapply Hcnt $$ %n %Hn Hec %K2 %ε HKres Hna Herr Hpos

theorem refines_couple_rands_lr_avoid {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int}
    (bad : Int) (Hz : 0 < z) : iprop%
    ↯ (z.toNat : ENNReal)⁻¹ ∗ (∀ n, ⌜(0 ≤ n ∧ n < z) ∧ n ≠ bad⌝ -∗
      refines E (K.fill pl(#(.int n))) (K'.fill pl(#(.int n))) A) ⊢
    refines E (K.fill pl(rand(#(.int z), #(.unit))))
      (K'.fill pl(rand(#(.int z), #(.unit)))) A := by
  classical
  iintro ⟨Hε, Hcnt⟩
  iapply refines_couple_rands_lr_adv id (z.toNat : ENNReal)⁻¹ (fun n => if n = bad then 1 else 0)
    id_dom_range id_bij_range Hz (avoid_one_amort bad)
  iframe Hε
  iintro %n %hn Hec
  by_cases hb : n = bad
  · rw [ite_eq_left hb]
    iexfalso
    iapply ErrorCredit.contradict (_root_.le_refl 1) $$ Hec
  · simp only [id_eq]
    iapply Hcnt $$ %n %⟨hn, hb⟩

theorem refines_couple_tapes_bij {E : CoPset} {e e' : Exp rT} {A : lrel rT GF}
    {z : Int} {α αₛ : Loc} {ns nsₛ : List Int} (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) : iprop%
    appNatTape α z ns ∗ specNatTape αₛ z nsₛ ∗
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ appNatTape α z (ns ++ [n]) -∗ specNatTape αₛ z (nsₛ ++ [f n]) -∗
      refines E e e' A) ⊢
    refines E e e' A := by
  iintro ⟨Hα, Hαₛ, Hcnt⟩
  unfold refines
  iintro %K %ε Hj Hna Herr Hpos
  iapply wp_couple_tapes_bij (αₛ := αₛ) (ns := ns) (nsₛ := nsₛ) f hdom hbij Hz
  iframe Hα Hαₛ
  iintro %n %hn HA HS
  iapply Hcnt $$ %n %hn HA HS %K %ε Hj Hna Herr Hpos

theorem refines_couple_TU {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int}
    (α : Loc) (f : Int → Int) (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) (Hz : 0 < z) : iprop%
    ▷ appNatTape α z [] ∗ (∀ n, appNatTape α z [] -∗ ⌜0 ≤ n ∧ n < z⌝ -∗
      refines E (K.fill pl(#(.int n))) (K'.fill pl(#(.int (f n)))) A) ⊢
    refines E (K.fill pl(rand(#(.int z), #(.lbl α))))
      (K'.fill pl(rand(#(.int z), #(.unit)))) A := by
  iintro ⟨Hα, Hcnt⟩
  unfold refines
  iintro %K2 %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply ApproxisWpGS.wp_bind (K := K)
  iapply wp_couple_tape_rand z f hdom hbij Hz (K2.comp K') ⊤ α _
  iframe Hα Hj
  iintro %n ⟨HαNew, HKres, %Hn⟩
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.int n : Val rT) = pl(#(.int n)) from rfl]
  iapply Hcnt $$ %n HαNew %Hn %K2 %ε HKres Hna Herr Hpos

theorem refines_couple_UT {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int}
    (α' : Loc) (f : Int → Int) (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) (Hz : 0 < z) : iprop%
    ▷ specNatTape α' z [] ∗ (∀ n, specNatTape α' z [] -∗ ⌜0 ≤ n ∧ n < z⌝ -∗
      refines E (K.fill pl(#(.int n))) (K'.fill pl(#(.int (f n)))) A) ⊢
    refines E (K.fill pl(rand(#(.int z), #(.unit))))
      (K'.fill pl(rand(#(.int z), #(.lbl α')))) A := by
  iintro ⟨Hα', Hcnt⟩
  unfold refines
  iintro %K2 %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply ApproxisWpGS.wp_bind (K := K)
  iapply wp_couple_rand_tape z f hdom hbij Hz (K2.comp K') ⊤ α' _
  iframe Hα' Hj
  iintro %n ⟨Hα'New, HKres, %Hn⟩
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.int n : Val rT) = pl(#(.int n)) from rfl]
  iapply Hcnt $$ %n Hα'New %Hn %K2 %ε HKres Hna Herr Hpos

theorem refines_couple_TT {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int}
    (α α' : Loc) (f : Int → Int) (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) (Hz : 0 < z) : iprop%
    ▷ appNatTape α z [] ∗ ▷ specNatTape α' z [] ∗
    (∀ n, appNatTape α z [] -∗ specNatTape α' z [] -∗ ⌜0 ≤ n ∧ n < z⌝ -∗
      refines E (K.fill pl(#(.int n))) (K'.fill pl(#(.int (f n)))) A) ⊢
    refines E (K.fill pl(rand(#(.int z), #(.lbl α))))
      (K'.fill pl(rand(#(.int z), #(.lbl α')))) A := by
  iintro ⟨Hα, Hα', Hcnt⟩
  unfold refines
  iintro %K2 %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply ApproxisWpGS.wp_bind (K := K)
  iapply wp_couple_rand_lbl_rand_lbl z f hdom hbij Hz (K2.comp K') ⊤ α α' _
  iframe Hα Hα' Hj
  iintro %n ⟨HαNew, Hα'New, HKres, %Hn⟩
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.int n : Val rT) = pl(#(.int n)) from rfl]
  iapply Hcnt $$ %n HαNew Hα'New %Hn %K2 %ε HKres Hna Herr Hpos

end AppRelRules

end ProbLang
