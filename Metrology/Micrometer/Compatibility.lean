module

public import Metrology.Micrometer.PrimitiveLaws
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI
public import Metrology.Micrometer.Model
public import Metrology.Micrometer.RelTactics
public import Metrology.Micrometer.AppRelRules
public import Metrology.ProbLang.Syntax.LocallyClosed

/-! # Closed compatibility lemmas, pure fragment

One `refines_*` rule per syntactic form of the pure fragment (pairs, sums, application, `if`, `∀`,
`∃`), the closed layer that `bin_log_related_*` calls. -/

@[expose] public section

-- these rules use the @[discrete] lifting lemmas without being discrete themselves
set_option linter.discrete false

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting
open scoped AppGS
open Exp EctxItem Ectx
open Ectx (fill)

namespace ProbLang

section Compatibility
variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT] {hlc : HasLC} {B : Type}
    [AddCommMonoid B]
  [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors}
  [IR : MicrometerRGS rT hlc GF] [BudgetCreditGS B GF]

/-- A related pair of functions sends related arguments to related applications. -/
theorem lrel_arr_unfold_wand (A B : lrel rT GF) (v v' : Val rT) :
    (lrel_arr L A B).car v v' ⊢
      □ (∀ w1 w2, A w1 w2 -∗ refines L ⊤ (app v.1 w1.1) (app v'.1 w2.1) B) :=
  sep_elim_right

section Steps
variable [L.IsLawful] [L.IsTopAbsorbing]
variable {e e' : Exp rT} {A B : lrel rT GF}
local bi IProp GF

/-! ### Pure steps -/

variable {b t : Exp rT}
variable {u : Val rT}

/-- β-step on the left for a constant function: the body `b` is locally closed, so it
ignores the argument. -/
theorem refines_beta_const_l (hb : b.IsLocallyClosed) : iprop%
    ▷ refines L ⊤ b t A ⊢ refines L ⊤ (.app (.lam b) u.1) t A := by
  iintro H
  rw [eq_fill_nil (app (.lam b) u.1)]
  iapply refines_pure_l (e' := open' b u.1) ⟨⟨u.2⟩, by is_lc⟩
  rw [show fill [] (open' b u.1) = b from (open_lc 0 u.1 b hb).symm]
  inext
  iexact H

/-- β-step on the right for a constant function: the body `b` is locally closed, so it
ignores the argument. -/
theorem refines_beta_const_r (hb : b.IsLocallyClosed) :
    refines L ⊤ t b A ⊢ refines L ⊤ t (.app (.lam b) u.1) A := by
  iintro H
  rw [eq_fill_nil (app (.lam b) u.1)]
  iapply refines_pure_r (e' := open' b u.1) ⟨⟨u.2⟩, by is_lc⟩
  rw [show fill [] (open' b u.1) = b from (open_lc 0 u.1 b hb).symm]
  iexact H

section
variable {φ : Prop} (hφ : φ) {r : Exp rT} [Hex : PureExec φ 1 e r]
include hφ

variable {r' : Exp rT}
variable {φ' : Prop}
variable [Hex' : PureExec φ' 1 e' r']

/-- One pure step on each side reduces the goal to the reducts, under a later. -/
theorem refines_pure_step (hφ' : φ') : iprop% ▷ refines L ⊤ r r' A ⊢ refines L ⊤ e e' A := by
  iintro H
  rw [eq_fill_nil e, eq_fill_nil e']
  iapply refines_pure_l (Hex := Hex) hφ
  inext
  iapply refines_pure_r (Hex := Hex') hφ'
  simp only [fill_nil]
  iexact H

/-- One pure step on each side to values related at `A` closes the goal. -/
theorem refines_pure_ret {v v' : Val rT} (hφ' : φ') (hr : r = v.1) (hr' : r' = v'.1) :
    A.car v v' ⊢ refines L ⊤ e e' A := by
  iintro HA
  iapply refines_pure_step (Hex := Hex) (Hex' := Hex') hφ hφ'
  inext
  iapply refines_ret hr hr'
  imodintro
  iexact HA

/-- The same pure step on both sides, to a value related to itself at `A`. -/
theorem refines_pure_both (hrv : IsVal r) (HA : ⊢ A ⟨r, hrv, hrv.lc⟩ ⟨r, hrv, hrv.lc⟩) :
    ⊢ refines L ⊤ e e A := by
  iapply refines_pure_ret (v := ⟨r, hrv, hrv.lc⟩) (v' := ⟨r, hrv, hrv.lc⟩) hφ hφ rfl rfl
  iapply HA

end

/-- A binary operator applied to the same values on both sides, with a result related to itself. -/
theorem refines_binop_pure (op : BinOp) (v1 v2 r : Exp rT) (hv1 : IsVal v1) (hv2 : IsVal v2)
    (hrv : IsVal r) (heval : op.eval v1 v2 = some r)
    (HA : ⊢ A ⟨r, hrv, hrv.lc⟩ ⟨r, hrv, hrv.lc⟩) :
    ⊢ refines L ⊤ (.binop op v1 v2) (.binop op v1 v2) A :=
  refines_pure_both ⟨hv1.toIsValue, hv2.toIsValue, heval⟩ hrv HA

/-- A unary operator applied to the same value on both sides, with a result related to itself. -/
theorem refines_unop_pure (op : UnOp) (v r : Exp rT) (hv : IsVal v) (hrv : IsVal r)
    (heval : op.eval v = some r)
    (HA : ⊢ A ⟨r, hrv, hrv.lc⟩ ⟨r, hrv, hrv.lc⟩) :
    ⊢ refines L ⊤ (.unop op v) (.unop op v) A :=
  refines_pure_both ⟨hv.toIsValue, heval⟩ hrv HA

/-! ### Rules that bind their operands -/

section Binding
variable {e0 e0' e1 e2 e1' e2' : Exp rT}

/-! Each proof restates the goal as `Ectx.fill [item] e` so `refines_bind` unifies, binds the right
operand first (ProbLang evaluates right to left), then re-reads the same term with the hole in the
left operand (a definitional `rw [show ... from rfl]`). -/

/-- Pairs `(e1, e2)` are related at the product when the components are. -/
theorem refines_pair : iprop%
    refines L ⊤ e1 e1' A ⊢
      refines L ⊤ e2 e2' B -∗ refines L ⊤ (pair e1 e2) (pair e1' e2') (lrel_prod A B) := by
  show _ ⊢ refines L ⊤ e2 e2' B -∗ refines L ⊤ (fill [pairR e1] e2)
    (fill [pairR e1'] e2') (lrel_prod A B)
  iintro IH1 IH2
  iapply refines_bind [pairR e1] [pairR e1'] $$ IH2
  iintro %v2 %v2' HB
  rw [show fill [pairR e1] v2.1 = fill [pairL v2] e1 from rfl,
    show fill [pairR e1'] v2'.1 = fill [pairL v2'] e1' from rfl]
  iapply refines_bind [pairL v2] [pairL v2'] $$ IH1
  iintro %v1 %v1' HA
  iapply refines_ret (e1 := fill [pairL v2] v1.1) (e2 := fill [pairL v2'] v1'.1)
    (v1 := .pair v1 v2) (v2 := .pair v1' v2') rfl rfl
  imodintro
  iunfold lrel_prod
  iexists v1, v1', v2, v2'
  iframe
  itrivial

/-- Left injections are related at the sum when the payloads are related at `A`. -/
theorem refines_injl : iprop%
    refines L ⊤ e e' A ⊢ refines L ⊤ (.inl e) (.inl e') (lrel_sum A B) := by
  show _ ⊢ refines L ⊤ (fill [inl] e) (fill [inl] e') (lrel_sum A B)
  iintro IH
  iapply refines_bind [inl] [inl] $$ IH
  iintro %v %v' HA
  iapply refines_ret (e1 := fill [inl] v.1) (e2 := fill [inl] v'.1)
    (v1 := .inl v) (v2 := .inl v') rfl rfl
  imodintro
  iunfold lrel_sum
  iexists v, v'
  ileft
  iframe HA
  itrivial

/-- Right injections are related at the sum when the payloads are related at `B`. -/
theorem refines_injr : iprop%
    refines L ⊤ e e' B ⊢ refines L ⊤ (.inr e) (.inr e') (lrel_sum A B) := by
  show _ ⊢ refines L ⊤ (fill [inr] e) (fill [inr] e') (lrel_sum A B)
  iintro IH
  iapply refines_bind [inr] [inr] $$ IH
  iintro %v %v' HB
  iapply refines_ret (e1 := fill [inr] v.1) (e2 := fill [inr] v'.1)
    (v1 := .inr v) (v2 := .inr v') rfl rfl
  imodintro
  iunfold lrel_sum
  iexists v, v'
  iright
  iframe HB
  itrivial

/-- Application is related at `B` when the function is related at `A → B` and the argument at
`A`. -/
theorem refines_app : iprop%
    refines L ⊤ e1 e1' (lrel_arr L A B) ⊢
      refines L ⊤ e2 e2' A -∗ refines L ⊤ (app e1 e2) (app e1' e2') B := by
  show _ ⊢ refines L ⊤ e2 e2' A -∗
    refines L ⊤ (fill [appR e1] e2) (fill [appR e1'] e2') B
  iintro IH1 IH2
  iapply refines_bind [appR e1] [appR e1'] $$ IH2
  iintro %v2 %v2' HA
  rw [show fill [appR e1] v2.1 = fill [appL v2] e1 from rfl,
    show fill [appR e1'] v2'.1 = fill [appL v2'] e1' from rfl]
  iapply refines_bind [appL v2] [appL v2'] $$ IH1
  iintro %v1 %v1' #Hff
  iunfold lrel_arr at Hff
  icases Hff with ⟨-, Hff⟩
  rw [show fill [appL v2] v1.1 = app v1.1 v2.1 from rfl,
    show fill [appL v2'] v1'.1 = app v1'.1 v2'.1 from rfl]
  iapply Hff $$ %v2 %v2' HA

/-- Sequencing `e1; e2`, encoded as `(λ_. e2) e1` with `e2` locally closed; the result of `e1`,
related at `A`, is discarded. -/
theorem refines_seq (A : lrel rT GF) (he2 : e2.IsLocallyClosed)
    (he2' : e2'.IsLocallyClosed) : iprop%
    refines L ⊤ e1 e1' A ⊢
      refines L ⊤ e2 e2' B -∗ refines L ⊤ (.app (.lam e2) e1) (.app (.lam e2') e1') B := by
  show _ ⊢ refines L ⊤ e2 e2' B -∗
    refines L ⊤ (fill [appR (.lam e2)] e1) (fill [appR (.lam e2')] e1') B
  iintro IH1 IH2
  iapply refines_bind [appR (.lam e2)] [appR (.lam e2')] $$ IH1
  iintro %v %v' -
  rw [fill_appR, fill_appR]
  iapply refines_beta_const_l he2
  inext
  iapply refines_beta_const_r he2'
  iexact IH2

/-- First projections of related pairs are related. -/
theorem refines_fst : iprop%
    refines L ⊤ e e' (lrel_prod A B) ⊢ refines L ⊤ (.fst e) (.fst e') A := by
  show _ ⊢ refines L ⊤ (fill [fst] e) (fill [fst] e') A
  iintro IH
  iapply refines_bind [fst] [fst] $$ IH
  iintro %v %v' Hprod
  iunfold lrel_prod at Hprod
  icases Hprod with ⟨%a1, %a2, %b1, %b2, %hv, %hv', HA, -⟩
  rw [fill_fst, fill_fst, hv, hv']
  iapply refines_pure_ret ⟨a1.2.toIsValue, b1.2.toIsValue⟩ ⟨a2.2.toIsValue, b2.2.toIsValue⟩
    rfl rfl $$ HA

/-- Second projections of related pairs are related. -/
theorem refines_snd : iprop%
    refines L ⊤ e e' (lrel_prod A B) ⊢ refines L ⊤ (.snd e) (.snd e') B := by
  show _ ⊢ refines L ⊤ (fill [snd] e) (fill [snd] e') B
  iintro IH
  iapply refines_bind [snd] [snd] $$ IH
  iintro %v %v' Hprod
  iunfold lrel_prod at Hprod
  icases Hprod with ⟨%a1, %a2, %b1, %b2, %hv, %hv', -, HB⟩
  rw [fill_snd, fill_snd, hv, hv']
  iapply refines_pure_ret ⟨a1.2.toIsValue, b1.2.toIsValue⟩ ⟨a2.2.toIsValue, b2.2.toIsValue⟩
    rfl rfl $$ HB

/-- `case` on related sums is related when the branches are related functions out of each
summand. -/
theorem refines_case {C : lrel rT GF} : iprop%
    refines L ⊤ e0 e0' (lrel_sum A B) ⊢
      refines L ⊤ e1 e1' (lrel_arr L A C) -∗ refines L ⊤ e2 e2' (lrel_arr L B C) -∗
      refines L ⊤ (.case e0 e1 e2) (.case e0' e1' e2') C := by
  show _ ⊢ refines L ⊤ e1 e1' (lrel_arr L A C) -∗ refines L ⊤ e2 e2' (lrel_arr L B C) -∗
    refines L ⊤ (fill [.case e1 e2] e0) (fill [.case e1' e2'] e0') C
  iintro IH0 IH1 IH2
  iapply refines_bind [.case e1 e2] [.case e1' e2'] $$ IH0
  iintro %v %v' Hsum
  rw [fill_case, fill_case]
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

/-- `if` on related booleans is related when both branches are related. -/
theorem refines_if : iprop%
    refines L ⊤ e0 e0' lrel_bool ⊢
      refines L ⊤ e1 e1' A -∗ refines L ⊤ e2 e2' A -∗
      refines L ⊤ (.cond e0 e1 e2) (.cond e0' e1' e2') A := by
  show _ ⊢ refines L ⊤ e1 e1' A -∗ refines L ⊤ e2 e2' A -∗
    refines L ⊤ (fill [condC e1 e2] e0) (fill [condC e1' e2'] e0') A
  iintro IH0 IH1 IH2
  iapply refines_bind [condC e1 e2] [condC e1' e2'] $$ IH0
  iintro %v %v' Hb
  iunfold lrel_bool at Hb
  icases Hb with ⟨%b, %hv, %hv'⟩
  rw [fill_condC, fill_condC, hv, hv']
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

end Binding

/-! ### Quantifiers -/

variable {C : lrel rT GF → lrel rT GF}

/-- Packing a witness `A` relates `e` at `∃ C` as soon as it is related at `C A`. -/
theorem refines_pack (A : lrel rT GF) :
    refines L ⊤ e e' (C A) ⊢ refines L ⊤ e e' (lrel_exists C) := by
  iintro IH
  iapply refines_wand $$ IH
  iintro %v %v' HCA !>
  ihave %hcl := (C A).closed v v' $$ HCA
  iunfold lrel_exists
  isplitr
  · ipureintro; exact hcl
  iexists A
  iexact HCA

/-- Type abstractions, thunks `λ_. e`, are related at `∀` when their bodies are related at every
instance. -/
theorem refines_forall (he : e.IsLocallyClosed) (he' : e'.IsLocallyClosed) (he_fv : e.fv = ∅)
    (he'_fv : e'.fv = ∅) :
    □ (∀ A, refines L ⊤ e e' (C A)) ⊢ refines L ⊤ (.lam e) (.lam e') (lrel_forall L C) := by
  iintro #H
  iapply refines_ret (v1 := ⟨.lam e, .lam (by is_lc), by is_lc⟩)
    (v2 := ⟨.lam e', .lam (by is_lc), by is_lc⟩) rfl rfl
  imodintro
  iunfold lrel_forall
  iintro %A
  iunfold lrel_arr
  isplitr
  · ipureintro
    exact ⟨⟨by is_lc, by simpa [fv] using he_fv⟩, ⟨by is_lc, by simpa [fv] using he'_fv⟩⟩
  iintro !> %u %u' -
  iapply refines_beta_const_l he
  inext
  iapply refines_beta_const_r he'
  iapply H

end Steps

end Compatibility

end ProbLang
