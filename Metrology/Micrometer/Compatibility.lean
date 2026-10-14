module

public import Metrology.Micrometer.PrimitiveLaws
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Micrometer.Model
public import Metrology.Micrometer.RelTactics
public import Metrology.Micrometer.AppRelRules
public import Metrology.ProbLang.Syntax.LocallyClosed

@[expose] public section

set_option linter.discrete false

/-! # Compatibility Lemmas -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
open scoped AppGS

namespace ProbLang

section Compatibility
variable {rT : Type} [LawfulProbLangℝ rT]
variable {hlc : HasLC} {ι : Type} [Monoid ι] {Δ : GradedDivergence.{0} ι}
  {GF : BundledGFunctors} [IR : MicrometerRGS rT hlc GF]
  [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft]

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem lrel_arr_unfold_wand (A B : lrel rT GF) (v v' : Val rT) :
    (lrel_arr Δ A B).car v v' ⊢
    □ (∀ w1 w2, A w1 w2 -∗ refines Δ ⊤ (Exp.app v.1 w1.1) (Exp.app v'.1 w2.1) B) :=
  sep_elim_right

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_pair {e1 e2 e1' e2' : Exp rT} {A B : lrel rT GF} : iprop%
    refines Δ ⊤ e1 e1' A ⊢
    refines Δ ⊤ e2 e2' B -∗ refines Δ ⊤ (Exp.pair e1 e2) (Exp.pair e1' e2') (lrel_prod A B) := by
  show _ ⊢ refines Δ ⊤ e2 e2' B -∗ refines Δ ⊤ (Ectx.fill [EctxItem.pairR e1] e2)
    (Ectx.fill [EctxItem.pairR e1'] e2') (lrel_prod A B)
  iintro IH1 IH2
  iapply refines_bind [EctxItem.pairR e1] [EctxItem.pairR e1'] $$ IH2
  iintro %v2 %v2' HB
  rw [show Ectx.fill [EctxItem.pairR e1] v2.1 = Ectx.fill [EctxItem.pairL v2] e1 from rfl,
    show Ectx.fill [EctxItem.pairR e1'] v2'.1 = Ectx.fill [EctxItem.pairL v2'] e1' from rfl]
  iapply refines_bind [EctxItem.pairL v2] [EctxItem.pairL v2'] $$ IH1
  iintro %v1 %v1' HA
  iapply refines_ret (e1 := Ectx.fill [EctxItem.pairL v2] v1.1)
    (e2 := Ectx.fill [EctxItem.pairL v2'] v1'.1)
    (v1 := ⟨.pair v1.1 v2.1, IsVal.pair v1.2 v2.2, (IsVal.pair v1.2 v2.2).lc⟩)
    (v2 := ⟨.pair v1'.1 v2'.1, IsVal.pair v1'.2 v2'.2, (IsVal.pair v1'.2 v2'.2).lc⟩) rfl rfl
  imodintro
  unfold lrel_prod
  iexists v1, v1', v2, v2'
  iframe
  itrivial

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_injl {e e' : Exp rT} {A B : lrel rT GF} : iprop%
    refines Δ ⊤ e e' A ⊢ refines Δ ⊤ (.inl e) (.inl e') (lrel_sum A B) := by
  show _ ⊢ refines Δ ⊤ (Ectx.fill [EctxItem.inl] e) (Ectx.fill [EctxItem.inl] e') (lrel_sum A B)
  iintro IH
  iapply refines_bind [EctxItem.inl] [EctxItem.inl] $$ IH
  iintro %v %v' HA
  iapply refines_ret (e1 := Ectx.fill [EctxItem.inl] v.1) (e2 := Ectx.fill [EctxItem.inl] v'.1)
    (v1 := ⟨.inl v.1, IsVal.inl v.2, (IsVal.inl v.2).lc⟩)
    (v2 := ⟨.inl v'.1, IsVal.inl v'.2, (IsVal.inl v'.2).lc⟩) rfl rfl
  imodintro
  unfold lrel_sum
  iexists v, v'
  ileft
  iframe HA
  itrivial

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_injr {e e' : Exp rT} {A B : lrel rT GF} : iprop%
    refines Δ ⊤ e e' B ⊢ refines Δ ⊤ (.inr e) (.inr e') (lrel_sum A B) := by
  show _ ⊢ refines Δ ⊤ (Ectx.fill [EctxItem.inr] e) (Ectx.fill [EctxItem.inr] e') (lrel_sum A B)
  iintro IH
  iapply refines_bind [EctxItem.inr] [EctxItem.inr] $$ IH
  iintro %v %v' HB
  iapply refines_ret (e1 := Ectx.fill [EctxItem.inr] v.1) (e2 := Ectx.fill [EctxItem.inr] v'.1)
    (v1 := ⟨.inr v.1, IsVal.inr v.2, (IsVal.inr v.2).lc⟩)
    (v2 := ⟨.inr v'.1, IsVal.inr v'.2, (IsVal.inr v'.2).lc⟩) rfl rfl
  imodintro
  unfold lrel_sum
  iexists v, v'
  iright
  iframe HB
  itrivial

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_app {e1 e2 e1' e2' : Exp rT} {A B : lrel rT GF} : iprop%
    refines Δ ⊤ e1 e1' (lrel_arr Δ A B) ⊢
    refines Δ ⊤ e2 e2' A -∗ refines Δ ⊤ (Exp.app e1 e2) (Exp.app e1' e2') B := by
  show _ ⊢ refines Δ ⊤ e2 e2' A -∗
    refines Δ ⊤ (Ectx.fill [EctxItem.appR e1] e2) (Ectx.fill [EctxItem.appR e1'] e2') B
  iintro IH1 IH2
  iapply refines_bind [EctxItem.appR e1] [EctxItem.appR e1'] $$ IH2
  iintro %v2 %v2' HA
  rw [show Ectx.fill [EctxItem.appR e1] v2.1 = Ectx.fill [EctxItem.appL v2] e1 from rfl,
    show Ectx.fill [EctxItem.appR e1'] v2'.1 = Ectx.fill [EctxItem.appL v2'] e1' from rfl]
  iapply refines_bind [EctxItem.appL v2] [EctxItem.appL v2'] $$ IH1
  iintro %v1 %v1' #Hff
  iunfold lrel_arr at Hff
  icases Hff with ⟨-, Hff⟩
  rw [show Ectx.fill [EctxItem.appL v2] v1.1 = Exp.app v1.1 v2.1 from rfl,
    show Ectx.fill [EctxItem.appL v2'] v1'.1 = Exp.app v1'.1 v2'.1 from rfl]
  iapply Hff $$ %v2 %v2' HA

theorem refines_beta_l {b t : Exp rT} {u : Val rT} {A : lrel rT GF} (hb : b.IsLocallyClosed) :
    iprop% ▷ refines Δ ⊤ b t A ⊢ refines Δ ⊤ (.app (.lam b) u.1) t A := by
  iintro H
  rw [Ectx.eq_fill_nil (Exp.app (.lam b) u.1)]
  iapply refines_pure_l (e := .app (.lam b) u.1) (e' := Exp.open' b u.1) (n := 1)
    (φ := u.1.isValue ∧ (Exp.lam b).IsLocallyClosed) ⟨⟨u.2⟩, by is_lc⟩
  rw [show Ectx.fill [] (Exp.open' b u.1) = b from (Exp.open_lc 0 u.1 b hb).symm]
  inext
  iexact H

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_beta_r {b t : Exp rT} {u : Val rT} {A : lrel rT GF} (hb : b.IsLocallyClosed) :
    refines Δ ⊤ t b A ⊢ refines Δ ⊤ t (.app (.lam b) u.1) A := by
  iintro H
  rw [Ectx.eq_fill_nil (Exp.app (.lam b) u.1)]
  iapply refines_pure_r (e := .app (.lam b) u.1) (e' := Exp.open' b u.1) (n := 1)
    (φ := u.1.isValue ∧ (Exp.lam b).IsLocallyClosed) ⟨⟨u.2⟩, by is_lc⟩
  rw [show Ectx.fill [] (Exp.open' b u.1) = b from (Exp.open_lc 0 u.1 b hb).symm]
  iexact H

theorem refines_seq (A : lrel rT GF) {e1 e2 e1' e2' : Exp rT} {B : lrel rT GF}
    (he2 : e2.IsLocallyClosed) (he2' : e2'.IsLocallyClosed) : iprop%
    refines Δ ⊤ e1 e1' A ⊢
    refines Δ ⊤ e2 e2' B -∗ refines Δ ⊤ (.app (.lam e2) e1) (.app (.lam e2') e1') B := by
  show _ ⊢ refines Δ ⊤ e2 e2' B -∗
    refines Δ ⊤ (Ectx.fill [EctxItem.appR (.lam e2)] e1)
      (Ectx.fill [EctxItem.appR (.lam e2')] e1') B
  iintro IH1 IH2
  iapply refines_bind [EctxItem.appR (.lam e2)] [EctxItem.appR (.lam e2')] $$ IH1
  iintro %v %v' -
  rw [Ectx.fill_appR, Ectx.fill_appR]
  iapply refines_beta_l he2
  inext
  iapply refines_beta_r he2'
  iexact IH2

/-! ### Pure-step constructors -/

theorem refines_pure_step {e e' r r' : Exp rT} {φ φ' : Prop}
    [Hex : PureExec φ 1 e r] [Hex' : PureExec φ' 1 e' r'] (hφ : φ) (hφ' : φ')
    {A : lrel rT GF} : iprop% ▷ refines Δ ⊤ r r' A ⊢ refines Δ ⊤ e e' A := by
  iintro H
  rw [Ectx.eq_fill_nil e, Ectx.eq_fill_nil e']
  iapply refines_pure_l (Hex := Hex) hφ
  inext
  iapply refines_pure_r (Hex := Hex') hφ'
  simp only [Ectx.fill_nil]
  iexact H

theorem refines_pure_ret {e e' r r' : Exp rT} {φ φ' : Prop} {v v' : Val rT}
    [Hex : PureExec φ 1 e r] [Hex' : PureExec φ' 1 e' r'] (hφ : φ) (hφ' : φ')
    (hr : r = v.1) (hr' : r' = v'.1) {A : lrel rT GF} :
    A.car v v' ⊢ refines Δ ⊤ e e' A := by
  iintro HA
  iapply refines_pure_step (Hex := Hex) (Hex' := Hex') hφ hφ'
  inext
  iapply refines_ret hr hr'
  imodintro
  iexact HA

theorem refines_fst {e e' : Exp rT} {A B : lrel rT GF} : iprop%
    refines Δ ⊤ e e' (lrel_prod A B) ⊢ refines Δ ⊤ (.fst e) (.fst e') A := by
  show _ ⊢ refines Δ ⊤ (Ectx.fill [EctxItem.fst] e) (Ectx.fill [EctxItem.fst] e') A
  iintro IH
  iapply refines_bind [EctxItem.fst] [EctxItem.fst] $$ IH
  iintro %v %v' Hprod
  iunfold lrel_prod at Hprod
  icases Hprod with ⟨%a1, %a2, %b1, %b2, %hv, %hv', HA, -⟩
  rw [Ectx.fill_fst, Ectx.fill_fst, hv, hv']
  iapply refines_pure_ret (Hex := pureExec_fst_pair) (Hex' := pureExec_fst_pair)
    ⟨a1.2.toIsValue, b1.2.toIsValue⟩ ⟨a2.2.toIsValue, b2.2.toIsValue⟩ rfl rfl $$ HA

theorem refines_case {e0 e1 e2 e0' e1' e2' : Exp rT} {A B C : lrel rT GF} : iprop%
    refines Δ ⊤ e0 e0' (lrel_sum A B) ⊢
    refines Δ ⊤ e1 e1' (lrel_arr Δ A C) -∗ refines Δ ⊤ e2 e2' (lrel_arr Δ B C) -∗
    refines Δ ⊤ (.case e0 e1 e2) (.case e0' e1' e2') C := by
  show _ ⊢ refines Δ ⊤ e1 e1' (lrel_arr Δ A C) -∗ refines Δ ⊤ e2 e2' (lrel_arr Δ B C) -∗
    refines Δ ⊤ (Ectx.fill [EctxItem.case e1 e2] e0) (Ectx.fill [EctxItem.case e1' e2'] e0') C
  iintro IH0 IH1 IH2
  iapply refines_bind [EctxItem.case e1 e2] [EctxItem.case e1' e2'] $$ IH0
  iintro %v %v' Hsum
  rw [Ectx.fill_case, Ectx.fill_case]
  iunfold lrel_sum at Hsum
  icases Hsum with ⟨%w1, %w2, ⟨%hv, %hv', HA⟩ | ⟨%hv, %hv', HB⟩⟩
  · rw [hv, hv']
    iapply refines_pure_step (Hex := pureExec_case_inl) (Hex' := pureExec_case_inl)
      w1.2.toIsValue w2.2.toIsValue
    inext
    iapply refines_app $$ IH1
    iapply refines_ret (v1 := w1) (v2 := w2) rfl rfl
    imodintro
    iexact HA
  · rw [hv, hv']
    iapply refines_pure_step (Hex := pureExec_case_inr) (Hex' := pureExec_case_inr)
      w1.2.toIsValue w2.2.toIsValue
    inext
    iapply refines_app $$ IH2
    iapply refines_ret (v1 := w1) (v2 := w2) rfl rfl
    imodintro
    iexact HB

theorem refines_pure_both {e r : Exp rT} {φ : Prop} [Hex : PureExec φ 1 e r] (hφ : φ)
    (hrv : IsVal r) {A : lrel rT GF} (HA : ⊢ A ⟨r, hrv, hrv.lc⟩ ⟨r, hrv, hrv.lc⟩) :
    ⊢ refines Δ ⊤ e e A := by
  iapply refines_pure_ret (Hex := Hex) (Hex' := Hex) (v := ⟨r, hrv, hrv.lc⟩)
    (v' := ⟨r, hrv, hrv.lc⟩) hφ hφ rfl rfl
  iapply HA

theorem refines_binop_pure (op : BinOp) (v1 v2 r : Exp rT) (hv1 : IsVal v1) (hv2 : IsVal v2)
    (hrv : IsVal r) (heval : op.eval v1 v2 = some r) {A : lrel rT GF}
    (HA : ⊢ A ⟨r, hrv, hrv.lc⟩ ⟨r, hrv, hrv.lc⟩) :
    ⊢ refines Δ ⊤ (.binop op v1 v2) (.binop op v1 v2) A :=
  refines_pure_both (φ := v1.isValue ∧ v2.isValue ∧ op.eval v1 v2 = some r)
    ⟨hv1.toIsValue, hv2.toIsValue, heval⟩ hrv HA

theorem refines_unop_pure (op : UnOp) (v r : Exp rT) (hv : IsVal v) (hrv : IsVal r)
    (heval : op.eval v = some r) {A : lrel rT GF}
    (HA : ⊢ A ⟨r, hrv, hrv.lc⟩ ⟨r, hrv, hrv.lc⟩) :
    ⊢ refines Δ ⊤ (.unop op v) (.unop op v) A :=
  refines_pure_both (φ := v.isValue ∧ op.eval v = some r) ⟨hv.toIsValue, heval⟩ hrv HA

/-! ### Discrete fragment: tape allocation and bounded sampling -/

theorem refines_alloctape {e e' : Exp rT} : iprop%
    refines Δ ⊤ e e' lrel_int ⊢@{IProp GF} refines Δ ⊤ (.tape e) (.tape e') lrel_tape := by
  show _ ⊢@{IProp GF}
    refines Δ ⊤ (Ectx.fill [EctxItem.tape] e) (Ectx.fill [EctxItem.tape] e') lrel_tape
  iintro IH
  iapply refines_bind [EctxItem.tape] [EctxItem.tape] $$ IH
  iintro %v %v' Hint
  iunfold lrel_int at Hint
  icases Hint with ⟨%n, %hv, %hv'⟩
  rw [Ectx.fill_tape, Ectx.fill_tape, hv, hv']
  unfold refines
  iintro %K %ε Hj Hna Herr Hpos
  ihave HStep := step_alloctape K n $$ Hj
  iapply specUpdate_wp
  iapply specUpdate_bind Std.LawfulSet.subset_refl
  iframe HStep
  iintro ⟨%l', HKRes, Hl'frag⟩
  iapply specUpdate_ret
  iapply wp_lift_atomic_head_step (Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w)
  iintro %σ₁ Hσ !>
  isplitr; · ipureintro; exact ⟨_, (HeadStepSupport.TapeS rfl rfl).pos⟩
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | TapeS hl hσ =>
    subst hl hσ
    imod app_state_tape_alloc (Tape.empty n) $$ Hσ with ⟨Hσ', Hlfrag⟩
    set lL := σ₁.tapes.fresh
    imod Iris.inv_alloc (P := iprop(appTapesFrag lL ⟨n, []⟩ ∗ specTapesFrag l' ⟨n, []⟩))
      $$ [Hlfrag Hl'frag] with #HInv
    · rw [← show Tape.empty n = ⟨n, []⟩ from rfl]
      iintro !>; iframe Hlfrag Hl'frag
    imodintro
    simp only [micrometerWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert,
      Exp.toVal?_lit]
    iframe Hσ'
    iexists (.lbl l' : Val _), ε
    iframe HKRes Hna Herr Hpos
    unfold lrel_tape
    iexists lL, l', n
    iframe HInv
    itrivial

theorem refines_alloc {e e' : Exp rT} {A : lrel rT GF} : iprop%
    refines Δ ⊤ e e' A ⊢ refines Δ ⊤ (.alloc e) (.alloc e') (lrel_ref A) := by
  show _ ⊢ refines Δ ⊤ (Ectx.fill [EctxItem.alloc] e) (Ectx.fill [EctxItem.alloc] e') (lrel_ref A)
  iintro IH
  iapply refines_bind [EctxItem.alloc] [EctxItem.alloc] $$ IH
  iintro %v %v' #HA
  rw [Ectx.fill_alloc, Ectx.fill_alloc, Ectx.eq_fill_nil (Exp.alloc v.1),
    Ectx.eq_fill_nil (Exp.alloc v'.1)]
  iapply refines_alloc_r
  iintro %l' Hl'
  iapply refines_alloc_l
  iintro %l Hl
  imod Iris.inv_alloc (E := ⊤)
    (P := iprop(∃ w1 w2, appHeapFrag l w1 ∗ specHeapFrag l' w2 ∗ A w1 w2)) $$ [Hl Hl' HA]
    with #HInv
  · iintro !>
    iexists v, v'
    iframe Hl Hl' HA
  iapply refines_ret (e1 := Ectx.fill [] pl(#(.loc l))) (e2 := Ectx.fill [] pl(#(.loc l')))
    (v1 := .loc l) (v2 := .loc l') rfl rfl
  imodintro
  unfold lrel_ref
  iexists l, l'
  iframe HInv
  itrivial

theorem refines_if {e0 e1 e2 e0' e1' e2' : Exp rT} {A : lrel rT GF} : iprop%
    refines Δ ⊤ e0 e0' lrel_bool ⊢
    refines Δ ⊤ e1 e1' A -∗ refines Δ ⊤ e2 e2' A -∗
    refines Δ ⊤ (.cond e0 e1 e2) (.cond e0' e1' e2') A := by
  show _ ⊢ refines Δ ⊤ e1 e1' A -∗ refines Δ ⊤ e2 e2' A -∗
    refines Δ ⊤ (Ectx.fill [EctxItem.condC e1 e2] e0) (Ectx.fill [EctxItem.condC e1' e2'] e0') A
  iintro IH0 IH1 IH2
  iapply refines_bind [EctxItem.condC e1 e2] [EctxItem.condC e1' e2'] $$ IH0
  iintro %v %v' Hb
  iunfold lrel_bool at Hb
  icases Hb with ⟨%b, %hv, %hv'⟩
  rw [Ectx.fill_condC, Ectx.fill_condC, hv, hv']
  cases b with
  | true =>
    iapply refines_pure_step (Hex := pureExec_cond_true) (Hex' := pureExec_cond_true)
      trivial trivial
    inext
    iexact IH1
  | false =>
    iapply refines_pure_step (Hex := pureExec_cond_false) (Hex' := pureExec_cond_false)
      trivial trivial
    inext
    iexact IH2

theorem refines_snd {e e' : Exp rT} {A B : lrel rT GF} : iprop%
    refines Δ ⊤ e e' (lrel_prod A B) ⊢ refines Δ ⊤ (.snd e) (.snd e') B := by
  show _ ⊢ refines Δ ⊤ (Ectx.fill [EctxItem.snd] e) (Ectx.fill [EctxItem.snd] e') B
  iintro IH
  iapply refines_bind [EctxItem.snd] [EctxItem.snd] $$ IH
  iintro %v %v' Hprod
  iunfold lrel_prod at Hprod
  icases Hprod with ⟨%a1, %a2, %b1, %b2, %hv, %hv', -, HB⟩
  rw [Ectx.fill_snd, Ectx.fill_snd, hv, hv']
  iapply refines_pure_ret (Hex := pureExec_snd_pair) (Hex' := pureExec_snd_pair)
    ⟨a1.2.toIsValue, b1.2.toIsValue⟩ ⟨a2.2.toIsValue, b2.2.toIsValue⟩ rfl rfl $$ HB

omit [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem refines_pack (A : lrel rT GF) {e e' : Exp rT} {C : lrel rT GF → lrel rT GF}
    (_hC : OFE.NonExpansive C)
    (hCclosed : ∀ v v', (C A).car v v' ⊢ ⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝) :
    refines Δ ⊤ e e' (C A) ⊢ refines Δ ⊤ e e' (lrel_exists C) := by
  show _ ⊢ refines Δ ⊤ (Ectx.fill Ectx.empty e) (Ectx.fill Ectx.empty e') (lrel_exists C)
  iintro IH
  iapply refines_bind Ectx.empty Ectx.empty $$ IH
  iintro %v %v' HCA
  iapply refines_ret (e1 := Ectx.fill Ectx.empty v.1) (e2 := Ectx.fill Ectx.empty v'.1)
    (v1 := v) (v2 := v') rfl rfl
  imodintro
  ihave %hcl := hCclosed v v' $$ HCA
  iunfold lrel_exists
  isplitr; · ipureintro; exact hcl
  iexists A
  iexact HCA

theorem refines_forall {e e' : Exp rT} {C : lrel rT GF → lrel rT GF}
    (he : e.IsLocallyClosed) (he' : e'.IsLocallyClosed) (he_fv : e.fv = ∅) (he'_fv : e'.fv = ∅) :
    □ (∀ A, refines Δ ⊤ e e' (C A)) ⊢ refines Δ ⊤ (.lam e) (.lam e') (lrel_forall Δ C) := by
  iintro #H
  iapply refines_ret (v1 := ⟨.lam e, IsVal.lam (by is_lc), by is_lc⟩)
    (v2 := ⟨.lam e', IsVal.lam (by is_lc), by is_lc⟩) rfl rfl
  imodintro
  unfold lrel_forall
  iintro %A
  unfold lrel_arr
  isplitr
  · ipureintro
    exact ⟨⟨by is_lc, by simpa [Exp.fv] using he_fv⟩, ⟨by is_lc, by simpa [Exp.fv] using he'_fv⟩⟩
  iintro !> %u %u' -
  iapply refines_beta_l he
  inext
  iapply refines_beta_r he'
  iapply H

theorem refines_store {e1 e2 e1' e2' : Exp rT} {A : lrel rT GF} : iprop%
    refines Δ ⊤ e1 e1' (lrel_ref A) ⊢
    refines Δ ⊤ e2 e2' A -∗ refines Δ ⊤ (.store e1 e2) (.store e1' e2') lrel_unit := by
  show _ ⊢ refines Δ ⊤ e2 e2' A -∗
    refines Δ ⊤ (Ectx.fill [EctxItem.storeR e1] e2) (Ectx.fill [EctxItem.storeR e1'] e2') lrel_unit
  iintro IH1 IH2
  iapply refines_bind [EctxItem.storeR e1] [EctxItem.storeR e1'] $$ IH2
  iintro %w %w' #HwA
  rw [show Ectx.fill [EctxItem.storeR e1] w.1 = Ectx.fill [EctxItem.storeL w] e1 from rfl,
    show Ectx.fill [EctxItem.storeR e1'] w'.1 = Ectx.fill [EctxItem.storeL w'] e1' from rfl]
  iapply refines_bind [EctxItem.storeL w] [EctxItem.storeL w'] $$ IH1
  iintro %v %v' HRef
  iunfold lrel_ref at HRef
  icases HRef with ⟨%l, %l', %heq, %heq', #Hinv⟩
  rw [show Ectx.fill [EctxItem.storeL w] v.1 = Exp.store v.1 w.1 from rfl,
    show Ectx.fill [EctxItem.storeL w'] v'.1 = Exp.store v'.1 w'.1 from rfl, heq, heq',
    Ectx.eq_fill_nil (Exp.store pl(#(.loc l)) w.1)]
  iapply refines_atomic_l (E' := ⊤ \ ↑(logN.@ (l, l'))) (OpenInv.of_atomic (Atomic.store' l w))
  iintro %K' Hr
  iinv Hinv with ⟨%v1, %v2, >Hv1, >Hv2, -⟩ Hclose
  imodintro
  ihave HStep := step_store K' w'.2 (Exp.toVal?_ofVal w') $$ [$Hr $Hv2]
  iapply specUpdate_wp
  iapply specUpdate_bind Std.LawfulSet.subset_refl
  iframe HStep
  iintro ⟨HKRes, Hv2'⟩
  iapply specUpdate_ret
  rw [show Exp.store pl(#(.loc l)) w.1 = .store pl(#(.loc l)) (.ofVal w) from rfl]
  iapply wp_store (v' := v1)
  iframe Hv1
  iintro Hw1'
  imod Hclose $$ [Hw1' Hv2' HwA] with -
  · iintro !>
    iexists w, w'
    iframe Hw1' Hv2' HwA
  imodintro
  iexists pl(#(.unit))
  iframe HKRes
  iapply refines_ret (e1 := Ectx.fill [] pl(#(.unit))) (e2 := pl(#(.unit))) (v1 := .unit)
    (v2 := .unit) rfl rfl
  imodintro
  iapply lrel_unit_lit

theorem refines_load {e e' : Exp rT} {A : lrel rT GF} : iprop%
    refines Δ ⊤ e e' (lrel_ref A) ⊢ refines Δ ⊤ (.load e) (.load e') A := by
  show _ ⊢ refines Δ ⊤ (Ectx.fill [EctxItem.load] e) (Ectx.fill [EctxItem.load] e') A
  iintro IH
  iapply refines_bind [EctxItem.load] [EctxItem.load] $$ IH
  iintro %v %v' HRef
  iunfold lrel_ref at HRef
  icases HRef with ⟨%l, %l', %heq, %heq', #Hinv⟩
  rw [Ectx.fill_load, Ectx.fill_load, heq, heq', Ectx.eq_fill_nil (pl(!#(.loc l)) : Exp rT)]
  iapply refines_atomic_l (E' := ⊤ \ ↑(logN.@ (l, l'))) (OpenInv.of_atomic (Atomic.load' l))
  iintro %K' Hr
  iinv Hinv with ⟨%w1, %w2, >Hw1, >Hw2, #HwAL⟩ Hclose
  imodintro
  ihave HStep := step_load K' $$ [$Hr $Hw2]
  iapply specUpdate_wp
  iapply specUpdate_bind Std.LawfulSet.subset_refl
  iframe HStep
  iintro ⟨HKRes, Hw2'⟩
  iapply specUpdate_ret
  have HE : (∅ : CoPset) ⊆ ⊤ \ ↑(logN.@ (l, l')) := Std.LawfulSet.empty_subset
  iapply wp_step_fupd HE Exp.load_toVal?_eq_none
  isplitl [HwAL]
  · iapply step_fupd_intro HE $$ HwAL
  iapply wp_load
  iframe Hw1
  iintro Hw1' #HwA
  imod Hclose $$ [Hw1' Hw2' HwA] with -
  · iintro !>
    iexists w1, w2
    iframe Hw1' Hw2' HwA
  imodintro
  iexists Exp.ofVal w2
  iframe HKRes
  iapply refines_ret (e1 := Ectx.fill [] w1.1) (e2 := Exp.ofVal w2) (v1 := w1) (v2 := w2) rfl rfl
  imodintro
  iexact HwA

/-! ### Shared machinery for the `rand` compatibility rules -/

omit [Monoid ι] [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] in
theorem natTapes_empty_close {α α' : Loc} {z : Int} : iprop%
    appNatTape α z [] ∗ specNatTape α' z [] ⊢@{IProp GF}
    ▷ (appTapesFrag α ⟨z, []⟩ ∗ specTapesFrag α' ⟨z, []⟩) := by
  iintro ⟨Hα, Hα'⟩
  ihave HαE := app_natTape_to_empty $$ Hα
  ihave Hα'E := spec_natTape_to_empty $$ Hα'
  iintro !>
  iframe HαE Hα'E

theorem refines_rand_lbl_of_pos {A : lrel rT GF} {α α' : Loc} {N z : Int} (hz : 0 < z)
    (HA : ∀ m : Int, 0 ≤ m → m < z → ⊢ A.car (.int m) (.int m)) :
    Iris.inv (logN.@ (α, α')) iprop(appTapesFrag α ⟨N, []⟩ ∗ specTapesFrag α' ⟨N, []⟩) ⊢
    refines Δ ⊤ pl(rand(#(.int z), #(.lbl α))) pl(rand(#(.int z), #(.lbl α'))) A := by
  iintro #Hinv
  rw [Ectx.eq_fill_nil (pl(rand(#(.int z), #(.lbl α))) : Exp rT)]
  iapply refines_atomic_l (E' := ⊤ \ ↑(logN.@ (α, α'))) (OpenInv.of_atomic (Atomic.rand_lbl' z α))
  iintro %K' Hr
  iinv Hinv with ⟨>Hα, >Hα'⟩ Hclose
  imodintro
  ihave HαN := app_empty_to_natTape $$ Hα
  ihave Hα'N := spec_empty_to_natTape $$ Hα'
  by_cases hNz : z = N
  · subst hNz
    iapply wp_couple_rand_lbl_rand_lbl z id id_dom_range id_bij_range hz K' _ α α'
    iframe HαN Hα'N Hr
    iintro %m ⟨HαRet, Hα'Ret, HKRes, %hm⟩
    ihave HCloseArg := natTapes_empty_close $$ [$HαRet $Hα'Ret]
    imod Hclose $$ HCloseArg with -
    imodintro
    iexists pl(#(.int (id m)))
    iframe HKRes
    iapply refines_ret (e1 := Ectx.fill [] (Val.int m : Val rT).1) (e2 := pl(#(.int (id m))))
      (v1 := .int m) (v2 := .int m) rfl rfl
    imodintro
    iapply HA m hm.1 hm.2
  · iapply wp_couple_rand_lbl_rand_lbl_wrong z N id id_dom_range id_bij_range hz hNz K' _ α α'
      [] []
    iframe HαN Hα'N Hr
    iintro %m ⟨HαRet, Hα'Ret, HKRes, %hm⟩
    ihave HCloseArg := natTapes_empty_close $$ [$HαRet $Hα'Ret]
    imod Hclose $$ HCloseArg with -
    imodintro
    iexists pl(#(.int (id m)))
    iframe HKRes
    iapply refines_ret (e1 := Ectx.fill [] (Val.int m : Val rT).1) (e2 := pl(#(.int (id m))))
      (v1 := .int m) (v2 := .int m) rfl rfl
    imodintro
    iapply HA m hm.1 hm.2

theorem refines_rand_unit_of_pos {A : lrel rT GF} {z : Int} (hz : 0 < z)
    (HA : ∀ m : Int, 0 ≤ m → m < z → ⊢ A.car (.int m) (.int m)) :
    ⊢ refines Δ ⊤ pl(rand(#(.int z), #(.unit))) pl(rand(#(.int z), #(.unit))) A := by
  rw [Ectx.eq_fill_nil (pl(rand(#(.int z), #(.unit))) : Exp rT)]
  iapply refines_couple_rands_lr id id_dom_range id_bij_range hz
  iintro %m ⟨%hm0, %hmz⟩
  iapply refines_ret (e1 := Ectx.fill [] pl(#(.int m))) (e2 := Ectx.fill [] pl(#(.int (id m))))
    (v1 := .int m) (v2 := .int m) rfl rfl
  imodintro
  iapply HA m hm0 hmz

theorem refines_rand_tape {e1 e1' e2 e2' : Exp rT} : iprop%
    refines Δ ⊤ e1 e1' lrel_pos_nat ⊢@{IProp GF}
    refines Δ ⊤ e2 e2' lrel_tape -∗ refines Δ ⊤ (.rand e1 e2) (.rand e1' e2') lrel_nat := by
  show _ ⊢@{IProp GF} refines Δ ⊤ e2 e2' lrel_tape -∗
    refines Δ ⊤ (Ectx.fill [EctxItem.randR e1] e2) (Ectx.fill [EctxItem.randR e1'] e2') lrel_nat
  iintro IH1 IH2
  iapply refines_bind [EctxItem.randR e1] [EctxItem.randR e1'] $$ IH2
  iintro %w %w' HTapeRel
  iunfold lrel_tape at HTapeRel
  icases HTapeRel with ⟨%α, %α', %N, %hw, %hw', #Hinv⟩
  rw [show Ectx.fill [EctxItem.randR e1] w.1 = Ectx.fill [EctxItem.randL w] e1 from rfl,
    show Ectx.fill [EctxItem.randR e1'] w'.1 = Ectx.fill [EctxItem.randL w'] e1' from rfl]
  iapply refines_bind [EctxItem.randL w] [EctxItem.randL w'] $$ IH1
  iintro %v %v' HPosNat
  iunfold lrel_pos_nat at HPosNat
  icases HPosNat with ⟨%M, %hM, %hv, %hv'⟩
  rw [show Ectx.fill [EctxItem.randL w] v.1 = Exp.rand v.1 w.1 from rfl,
    show Ectx.fill [EctxItem.randL w'] v'.1 = Exp.rand v'.1 w'.1 from rfl, hv, hv', hw, hw']
  iapply refines_rand_lbl_of_pos (z := (M : Int)) (by exact_mod_cast hM)
    (fun m h0 _ => lrel_nat_lit h0) $$ Hinv

theorem refines_rand_unit {e e' : Exp rT} : iprop%
    refines Δ ⊤ e e' lrel_pos_nat ⊢@{IProp GF}
    refines Δ ⊤ (Ectx.fill [EctxItem.randL .unit] e) (Ectx.fill [EctxItem.randL .unit] e')
      lrel_nat := by
  iintro IH
  iapply refines_bind [EctxItem.randL .unit] [EctxItem.randL .unit] $$ IH
  iintro %v %v' HPosNat
  iunfold lrel_pos_nat at HPosNat
  icases HPosNat with ⟨%n, %hn, %hv, %hv'⟩
  rw [show Ectx.fill [EctxItem.randL .unit] v.1 = Exp.rand v.1 pl(#(.unit)) from rfl,
    show Ectx.fill [EctxItem.randL .unit] v'.1 = Exp.rand v'.1 pl(#(.unit)) from rfl, hv, hv']
  iapply refines_rand_unit_of_pos (z := (n : Int)) (by exact_mod_cast hn)
    fun m h0 _ => lrel_nat_lit h0

theorem refines_rand_tape_int {e1 e1' e2 e2' : Exp rT} : iprop%
    refines Δ ⊤ e1 e1' lrel_int ⊢@{IProp GF}
    refines Δ ⊤ e2 e2' lrel_tape -∗ refines Δ ⊤ (.rand e1 e2) (.rand e1' e2') lrel_int := by
  show _ ⊢@{IProp GF} refines Δ ⊤ e2 e2' lrel_tape -∗
    refines Δ ⊤ (Ectx.fill [EctxItem.randR e1] e2) (Ectx.fill [EctxItem.randR e1'] e2') lrel_int
  iintro IH1 IH2
  iapply refines_bind [EctxItem.randR e1] [EctxItem.randR e1'] $$ IH2
  iintro %w %w' HTapeRel
  iunfold lrel_tape at HTapeRel
  icases HTapeRel with ⟨%α, %α', %N, %hw, %hw', #Hinv⟩
  rw [show Ectx.fill [EctxItem.randR e1] w.1 = Ectx.fill [EctxItem.randL w] e1 from rfl,
    show Ectx.fill [EctxItem.randR e1'] w'.1 = Ectx.fill [EctxItem.randL w'] e1' from rfl]
  iapply refines_bind [EctxItem.randL w] [EctxItem.randL w'] $$ IH1
  iintro %v %v' HInt
  iunfold lrel_int at HInt
  icases HInt with ⟨%n, %hv, %hv'⟩
  rw [show Ectx.fill [EctxItem.randL w] v.1 = Exp.rand v.1 w.1 from rfl,
    show Ectx.fill [EctxItem.randL w'] v'.1 = Exp.rand v'.1 w'.1 from rfl, hv, hv', hw, hw']
  by_cases hnpos : 0 < n
  · iapply refines_rand_lbl_of_pos hnpos (fun m _ _ => lrel_int_lit m) $$ Hinv
  · rw [Ectx.eq_fill_nil (pl(rand(#(.int n), #(.lbl α))) : Exp rT)]
    iapply refines_atomic_l (E' := ⊤ \ ↑(logN.@ (α, α')))
      (OpenInv.of_atomic (Atomic.rand_lbl' n α))
    iintro %K' Hr
    iinv Hinv with ⟨>Hα, >Hα'⟩ Hclose
    imodintro
    iapply wp_rand_lbl_nonpos_r K' hnpos
    iframe Hr Hα'
    iintro Hα'New HKRes
    iapply wp_rand_lbl_nonpos hnpos
    iframe Hα
    iintro HαNew
    imod Hclose $$ [HαNew Hα'New] with -
    · iintro !>; iframe HαNew Hα'New
    imodintro
    iexists pl(#(.int (-1)))
    iframe HKRes
    iapply refines_ret (e1 := Ectx.fill [] pl(#(.int (-1)))) (e2 := pl(#(.int (-1))))
      (v1 := .int (-1)) (v2 := .int (-1)) rfl rfl
    imodintro
    iapply lrel_int_lit (-1)

theorem refines_rand_unit_int {e e' : Exp rT} : iprop%
    refines Δ ⊤ e e' lrel_int ⊢@{IProp GF}
    refines Δ ⊤ (Ectx.fill [EctxItem.randL .unit] e) (Ectx.fill [EctxItem.randL .unit] e')
      lrel_int := by
  iintro IH
  iapply refines_bind [EctxItem.randL .unit] [EctxItem.randL .unit] $$ IH
  iintro %v %v' HInt
  iunfold lrel_int at HInt
  icases HInt with ⟨%n, %hv, %hv'⟩
  rw [show Ectx.fill [EctxItem.randL .unit] v.1 = Exp.rand v.1 pl(#(.unit)) from rfl,
    show Ectx.fill [EctxItem.randL .unit] v'.1 = Exp.rand v'.1 pl(#(.unit)) from rfl, hv, hv']
  by_cases hnpos : 0 < n
  · iapply refines_rand_unit_of_pos hnpos fun m _ _ => lrel_int_lit m
  · unfold refines
    iintro %K %ε HK Hna Herr Hpos
    iapply wp_rand_nonpos_r K hnpos
    iframe HK
    iintro HK'
    iapply wp_rand_nonpos hnpos
    iexists (.int (-1) : Val _), ε
    iframe HK' Hna Herr Hpos
    iapply lrel_int_lit (-1)

end Compatibility

end ProbLang
