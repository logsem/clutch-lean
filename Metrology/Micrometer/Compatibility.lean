module

public import Metrology.Micrometer.PrimitiveLaws
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Micrometer.Model
public import Metrology.Micrometer.RelTactics
public import Metrology.Micrometer.AppRelRules
public import Metrology.ProbLang.Syntax.LocallyClosed

/-! Compatibility lemmas for the pure fragment. -/

@[expose] public section

-- these rules use the @[discrete] lifting lemmas without being discrete themselves
set_option linter.discrete false

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting
open scoped AppGS

namespace ProbLang

section Compatibility
variable {rT : Type} [LawfulProbLangℝ rT] {hlc : HasLC} {B : Type} [AddCommMonoid B]
  [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors}
  [IR : MicrometerRGS rT hlc GF] [BudgetCreditGS B GF]

theorem lrel_arr_unfold_wand (A B : lrel rT GF) (v v' : Val rT) :
    (lrel_arr L A B).car v v' ⊢
    □ (∀ w1 w2, A w1 w2 -∗ refines L ⊤ (Exp.app v.1 w1.1) (Exp.app v'.1 w2.1) B) :=
  sep_elim_right

section Steps
variable [L.IsLawful] [L.IsTopAbsorbing]

/-! ### Pure-step constructors -/

/-- β-step on the left for a constant function: the body `b` is locally closed, so it ignores the argument. -/
theorem refines_beta_const_l {b t : Exp rT} {u : Val rT} {A : lrel rT GF} (hb : b.IsLocallyClosed) :
    iprop% ▷ refines L ⊤ b t A ⊢ refines L ⊤ (.app (.lam b) u.1) t A := by
  iintro H
  rw [Ectx.eq_fill_nil (Exp.app (.lam b) u.1)]
  iapply refines_pure_l (e' := Exp.open' b u.1)
    (φ := u.1.isValue ∧ (Exp.lam b).IsLocallyClosed) ⟨⟨u.2⟩, by is_lc⟩
  rw [show Ectx.fill [] (Exp.open' b u.1) = b from (Exp.open_lc 0 u.1 b hb).symm]
  inext
  iexact H

/-- β-step on the right for a constant function: the body `b` is locally closed, so it ignores the argument. -/
theorem refines_beta_const_r {b t : Exp rT} {u : Val rT} {A : lrel rT GF} (hb : b.IsLocallyClosed) :
    refines L ⊤ t b A ⊢ refines L ⊤ t (.app (.lam b) u.1) A := by
  iintro H
  rw [Ectx.eq_fill_nil (Exp.app (.lam b) u.1)]
  iapply refines_pure_r (e' := Exp.open' b u.1)
    (φ := u.1.isValue ∧ (Exp.lam b).IsLocallyClosed) ⟨⟨u.2⟩, by is_lc⟩
  rw [show Ectx.fill [] (Exp.open' b u.1) = b from (Exp.open_lc 0 u.1 b hb).symm]
  iexact H

theorem refines_pure_step {e e' r r' : Exp rT} {φ φ' : Prop}
    [Hex : PureExec φ 1 e r] [Hex' : PureExec φ' 1 e' r'] (hφ : φ) (hφ' : φ')
    {A : lrel rT GF} : iprop% ▷ refines L ⊤ r r' A ⊢ refines L ⊤ e e' A := by
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
    A.car v v' ⊢ refines L ⊤ e e' A := by
  iintro HA
  iapply refines_pure_step (Hex := Hex) (Hex' := Hex') hφ hφ'
  inext
  iapply refines_ret hr hr'
  imodintro
  iexact HA

theorem refines_pure_both {e r : Exp rT} {φ : Prop} [Hex : PureExec φ 1 e r] (hφ : φ)
    (hrv : IsVal r) {A : lrel rT GF} (HA : ⊢ A ⟨r, hrv, hrv.lc⟩ ⟨r, hrv, hrv.lc⟩) :
    ⊢ refines L ⊤ e e A := by
  iapply refines_pure_ret (v := ⟨r, hrv, hrv.lc⟩) (v' := ⟨r, hrv, hrv.lc⟩) hφ hφ rfl rfl
  iapply HA

theorem refines_binop_pure (op : BinOp) (v1 v2 r : Exp rT) (hv1 : IsVal v1) (hv2 : IsVal v2)
    (hrv : IsVal r) (heval : op.eval v1 v2 = some r) {A : lrel rT GF}
    (HA : ⊢ A ⟨r, hrv, hrv.lc⟩ ⟨r, hrv, hrv.lc⟩) :
    ⊢ refines L ⊤ (.binop op v1 v2) (.binop op v1 v2) A :=
  refines_pure_both ⟨hv1.toIsValue, hv2.toIsValue, heval⟩ hrv HA

theorem refines_unop_pure (op : UnOp) (v r : Exp rT) (hv : IsVal v) (hrv : IsVal r)
    (heval : op.eval v = some r) {A : lrel rT GF}
    (HA : ⊢ A ⟨r, hrv, hrv.lc⟩ ⟨r, hrv, hrv.lc⟩) :
    ⊢ refines L ⊤ (.unop op v) (.unop op v) A :=
  refines_pure_both ⟨hv.toIsValue, heval⟩ hrv HA

/-- Type abstractions, thunks `λ_. e`, are related at `∀` when their bodies are related at every
instance. -/
theorem refines_forall {e e' : Exp rT} {C : lrel rT GF → lrel rT GF}
    (he : e.IsLocallyClosed) (he' : e'.IsLocallyClosed) (he_fv : e.fv = ∅) (he'_fv : e'.fv = ∅) :
    □ (∀ A, refines L ⊤ e e' (C A)) ⊢ refines L ⊤ (.lam e) (.lam e') (lrel_forall L C) := by
  iintro #H
  iapply refines_ret (v1 := ⟨.lam e, IsVal.lam (by is_lc), by is_lc⟩)
    (v2 := ⟨.lam e', IsVal.lam (by is_lc), by is_lc⟩) rfl rfl
  imodintro
  iunfold lrel_forall
  iintro %A
  iunfold lrel_arr
  isplitr
  · ipureintro
    exact ⟨⟨by is_lc, by simpa [Exp.fv] using he_fv⟩, ⟨by is_lc, by simpa [Exp.fv] using he'_fv⟩⟩
  iintro !> %u %u' -
  iapply refines_beta_const_l he
  inext
  iapply refines_beta_const_r he'
  iapply H

/-! ### Constructors that bind their operands -/

/-! Each proof restates the goal as `Ectx.fill [item] e` so `refines_bind` unifies, binds the right
operand first (ProbLang evaluates right to left), then re-reads the same term with the hole in the
left operand (a definitional `rw [show ... from rfl]`). -/

theorem refines_pair {e1 e2 e1' e2' : Exp rT} {A B : lrel rT GF} : iprop%
    refines L ⊤ e1 e1' A ⊢
    refines L ⊤ e2 e2' B -∗ refines L ⊤ (Exp.pair e1 e2) (Exp.pair e1' e2') (lrel_prod A B) := by
  show _ ⊢ refines L ⊤ e2 e2' B -∗ refines L ⊤ (Ectx.fill [EctxItem.pairR e1] e2)
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
  iunfold lrel_prod
  iexists v1, v1', v2, v2'
  iframe
  itrivial

theorem refines_injl {e e' : Exp rT} {A B : lrel rT GF} : iprop%
    refines L ⊤ e e' A ⊢ refines L ⊤ (.inl e) (.inl e') (lrel_sum A B) := by
  show _ ⊢ refines L ⊤ (Ectx.fill [EctxItem.inl] e) (Ectx.fill [EctxItem.inl] e') (lrel_sum A B)
  iintro IH
  iapply refines_bind [EctxItem.inl] [EctxItem.inl] $$ IH
  iintro %v %v' HA
  iapply refines_ret (e1 := Ectx.fill [EctxItem.inl] v.1) (e2 := Ectx.fill [EctxItem.inl] v'.1)
    (v1 := ⟨.inl v.1, IsVal.inl v.2, (IsVal.inl v.2).lc⟩)
    (v2 := ⟨.inl v'.1, IsVal.inl v'.2, (IsVal.inl v'.2).lc⟩) rfl rfl
  imodintro
  iunfold lrel_sum
  iexists v, v'
  ileft
  iframe HA
  itrivial

theorem refines_injr {e e' : Exp rT} {A B : lrel rT GF} : iprop%
    refines L ⊤ e e' B ⊢ refines L ⊤ (.inr e) (.inr e') (lrel_sum A B) := by
  show _ ⊢ refines L ⊤ (Ectx.fill [EctxItem.inr] e) (Ectx.fill [EctxItem.inr] e') (lrel_sum A B)
  iintro IH
  iapply refines_bind [EctxItem.inr] [EctxItem.inr] $$ IH
  iintro %v %v' HB
  iapply refines_ret (e1 := Ectx.fill [EctxItem.inr] v.1) (e2 := Ectx.fill [EctxItem.inr] v'.1)
    (v1 := ⟨.inr v.1, IsVal.inr v.2, (IsVal.inr v.2).lc⟩)
    (v2 := ⟨.inr v'.1, IsVal.inr v'.2, (IsVal.inr v'.2).lc⟩) rfl rfl
  imodintro
  iunfold lrel_sum
  iexists v, v'
  iright
  iframe HB
  itrivial

theorem refines_app {e1 e2 e1' e2' : Exp rT} {A B : lrel rT GF} : iprop%
    refines L ⊤ e1 e1' (lrel_arr L A B) ⊢
    refines L ⊤ e2 e2' A -∗ refines L ⊤ (Exp.app e1 e2) (Exp.app e1' e2') B := by
  show _ ⊢ refines L ⊤ e2 e2' A -∗
    refines L ⊤ (Ectx.fill [EctxItem.appR e1] e2) (Ectx.fill [EctxItem.appR e1'] e2') B
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

/-- Sequencing `e1; e2`, encoded as `(λ_. e2) e1` with `e2` locally closed; the result of `e1`,
related at `A`, is discarded. -/
theorem refines_seq (A : lrel rT GF) {e1 e2 e1' e2' : Exp rT} {B : lrel rT GF}
    (he2 : e2.IsLocallyClosed) (he2' : e2'.IsLocallyClosed) : iprop%
    refines L ⊤ e1 e1' A ⊢
    refines L ⊤ e2 e2' B -∗ refines L ⊤ (.app (.lam e2) e1) (.app (.lam e2') e1') B := by
  show _ ⊢ refines L ⊤ e2 e2' B -∗
    refines L ⊤ (Ectx.fill [EctxItem.appR (.lam e2)] e1)
      (Ectx.fill [EctxItem.appR (.lam e2')] e1') B
  iintro IH1 IH2
  iapply refines_bind [EctxItem.appR (.lam e2)] [EctxItem.appR (.lam e2')] $$ IH1
  iintro %v %v' -
  rw [Ectx.fill_appR, Ectx.fill_appR]
  iapply refines_beta_const_l he2
  inext
  iapply refines_beta_const_r he2'
  iexact IH2

theorem refines_fst {e e' : Exp rT} {A B : lrel rT GF} : iprop%
    refines L ⊤ e e' (lrel_prod A B) ⊢ refines L ⊤ (.fst e) (.fst e') A := by
  show _ ⊢ refines L ⊤ (Ectx.fill [EctxItem.fst] e) (Ectx.fill [EctxItem.fst] e') A
  iintro IH
  iapply refines_bind [EctxItem.fst] [EctxItem.fst] $$ IH
  iintro %v %v' Hprod
  iunfold lrel_prod at Hprod
  icases Hprod with ⟨%a1, %a2, %b1, %b2, %hv, %hv', HA, -⟩
  rw [Ectx.fill_fst, Ectx.fill_fst, hv, hv']
  iapply refines_pure_ret ⟨a1.2.toIsValue, b1.2.toIsValue⟩ ⟨a2.2.toIsValue, b2.2.toIsValue⟩
    rfl rfl $$ HA

theorem refines_snd {e e' : Exp rT} {A B : lrel rT GF} : iprop%
    refines L ⊤ e e' (lrel_prod A B) ⊢ refines L ⊤ (.snd e) (.snd e') B := by
  show _ ⊢ refines L ⊤ (Ectx.fill [EctxItem.snd] e) (Ectx.fill [EctxItem.snd] e') B
  iintro IH
  iapply refines_bind [EctxItem.snd] [EctxItem.snd] $$ IH
  iintro %v %v' Hprod
  iunfold lrel_prod at Hprod
  icases Hprod with ⟨%a1, %a2, %b1, %b2, %hv, %hv', -, HB⟩
  rw [Ectx.fill_snd, Ectx.fill_snd, hv, hv']
  iapply refines_pure_ret ⟨a1.2.toIsValue, b1.2.toIsValue⟩ ⟨a2.2.toIsValue, b2.2.toIsValue⟩
    rfl rfl $$ HB

theorem refines_case {e0 e1 e2 e0' e1' e2' : Exp rT} {A B C : lrel rT GF} : iprop%
    refines L ⊤ e0 e0' (lrel_sum A B) ⊢
    refines L ⊤ e1 e1' (lrel_arr L A C) -∗ refines L ⊤ e2 e2' (lrel_arr L B C) -∗
    refines L ⊤ (.case e0 e1 e2) (.case e0' e1' e2') C := by
  show _ ⊢ refines L ⊤ e1 e1' (lrel_arr L A C) -∗ refines L ⊤ e2 e2' (lrel_arr L B C) -∗
    refines L ⊤ (Ectx.fill [EctxItem.case e1 e2] e0) (Ectx.fill [EctxItem.case e1' e2'] e0') C
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
    iapply refines_ret rfl rfl
    imodintro
    iexact HA
  · rw [hv, hv']
    iapply refines_pure_step (Hex := pureExec_case_inr) (Hex' := pureExec_case_inr)
      w1.2.toIsValue w2.2.toIsValue
    inext
    iapply refines_app $$ IH2
    iapply refines_ret rfl rfl
    imodintro
    iexact HB

theorem refines_if {e0 e1 e2 e0' e1' e2' : Exp rT} {A : lrel rT GF} : iprop%
    refines L ⊤ e0 e0' lrel_bool ⊢
    refines L ⊤ e1 e1' A -∗ refines L ⊤ e2 e2' A -∗
    refines L ⊤ (.cond e0 e1 e2) (.cond e0' e1' e2') A := by
  show _ ⊢ refines L ⊤ e1 e1' A -∗ refines L ⊤ e2 e2' A -∗
    refines L ⊤ (Ectx.fill [EctxItem.condC e1 e2] e0) (Ectx.fill [EctxItem.condC e1' e2'] e0') A
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

theorem refines_pack (A : lrel rT GF) {e e' : Exp rT} {C : lrel rT GF → lrel rT GF} :
    refines L ⊤ e e' (C A) ⊢ refines L ⊤ e e' (lrel_exists C) := by
  iintro IH
  iapply refines_wand $$ IH
  iintro %v %v' HCA !>
  ihave %hcl := (C A).closed v v' $$ HCA
  iunfold lrel_exists
  isplitr; · ipureintro; exact hcl
  iexists A
  iexact HCA

end Steps

end Compatibility

end ProbLang
