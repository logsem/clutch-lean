module

public import Metrology.Micrometer.UnifInt
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

@[expose] public section

-- these rules use the @[discrete] lifting lemmas without being discrete themselves
set_option linter.discrete false

/-! # Coupling rules for `rand`

The `wp` rules that couple a program draw with a spec draw or tape: free rules along a bijection
(`wp_couple_rand_core`), and credit-paying rules from any lifting (`wp_couple_rand_rand_lift`). -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting
open scoped AppGS
open Cfg Exp BIFUpdate LawfulSet BudgetCredit ENNReal
open List (map_eq_nil_iff)

namespace ProbLang

variable {rT : Type} [MeasurableSpace rT] [ProbLang.LawfulProbLangℝ rT]
variable {B : Type} {L : GradedLifting.{0} B} {hlc : HasLC} {GF : BundledGFunctors}
local bi IProp GF

/-! ## Raw tapes to tape predicates -/

variable {l : Loc}
variable {z : Int}
variable {ns : List Int}

/-- A raw tape holding `fs` gives the user-level tape predicate on its values. -/
theorem appNatTape_fold [AppGS rT GF] {fs : List { z' : Int // 0 ≤ z' ∧ z' < z }}
    (hfs : fs.map (fun x => x.val) = ns) :
    l ↪ₐ ⟨z, fs⟩ ⊢ appNatTape l z ns := by
  iintro Hb
  iunfold appNatTape
  iexists fs
  iframe %hfs Hb

/-- A raw spec tape holding `fs` gives the user-level spec tape predicate on its values. -/
theorem specNatTape_fold [SpecGS rT GF] {fs : List { z' : Int // 0 ≤ z' ∧ z' < z }}
    (hfs : fs.map (fun x => x.val) = ns) :
    l ↪ₛ ⟨z, fs⟩ ⊢ specNatTape l z ns := by
  iintro Hb
  iunfold specNatTape
  iexists fs
  iframe %hfs Hb

variable [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B]
  [OrderTop B] [MicrometerGS rT hlc GF] [L.IsLawful] [L.IsSupportLocal] [L.IsTopAbsorbing]
  [L.HasBind]

/-! ## Coupling two draws along a bijection, at no cost -/

section CouplingRules

variable [BudgetGS B GF] [L.IsReflexive]

/-! ### Step premises for the core rule -/

section
variable {z : Int} (Hz : 0 < z)
include Hz

/-- A unit-label `rand` steps to the uniform distribution, in the shape of the core rule's
`HstepL`/`HstepR` premise (it needs no resource). -/
theorem randUnit_step_pure (σ : State rT) {P A : IProp GF} :
    ⊢ P -∗ A -∗ ⌜Discrete.Reducible pl(rand(#z, #())) σ ∧
      primStep ⟨pl(rand(#z, #())), σ⟩ = uniform z σ⌝ := by
  iintro - -
  ipureintro
  exact randUnit_uniform_step Hz σ

variable (α : Loc)

/-- A `rand` on an empty program tape steps to the uniform distribution. -/
theorem appNatTape_empty_rand_step (σ : State rT) :
    ⊢ appStateAuth σ -∗ appNatTape α z [] -∗
      ⌜Discrete.Reducible pl(rand(#z, #lbl α)) σ ∧
        primStep ⟨pl(rand(#z, #lbl α)), σ⟩ = uniform z σ⌝ := by
  unfold appNatTape
  iintro Hσ ⟨%fs, %hmap, Hb⟩
  obtain rfl : fs = [] := map_eq_nil_iff.mp hmap
  ihave %hlk := app_state_lookup_tape $$ Hσ Hb
  ipureintro
  exact randLbl_empty_uniform_step Hz hlk

/-- A `rand` on an empty spec tape steps to the uniform distribution. -/
theorem specNatTape_empty_rand_step (e : Exp rT) (σ : State rT) :
    ⊢ specAuth ⟨e, σ⟩ -∗ specNatTape α z [] -∗
      ⌜Discrete.Reducible pl(rand(#z, #lbl α)) σ ∧
        primStep ⟨pl(rand(#z, #lbl α)), σ⟩ = uniform z σ⌝ := by
  unfold specNatTape
  iintro Hs ⟨%fs, %hmap, Hb⟩
  obtain rfl : fs = [] := map_eq_nil_iff.mp hmap
  ihave %hlk := spec_auth_lookup_tape $$ Hs Hb
  ipureintro
  exact randLbl_empty_uniform_step Hz hlk

end

/-! ### The core rule -/

section Draw
variable (z : Int) (f : Int → Int) (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
  (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) (Hz : 0 < z) (K : Ectx rT)
  (E : CoPset)
include hdom hbij Hz

/-- Core rule: if the resource `A` shows that `eL` (program side) and `eR` (spec side) each step to
`Cfg.uniform z`, couple the two draws along the bijection `f` at budget `0` and return `A`. -/
theorem wp_couple_rand_core {eL eR : Exp rT} (A : _) [Timeless A]
    (HvL : eL.toVal? = none) (HvR : ¬ eR.isValue)
    (HstepL : ∀ σ, ⊢ appStateAuth σ -∗ A -∗
      ⌜Discrete.Reducible eL σ ∧ primStep ⟨eL, σ⟩ = uniform z σ⌝)
    (HstepR : ∀ e' σ', ⊢ specAuth ⟨e', σ'⟩ -∗ A -∗
      ⌜Discrete.Reducible eR σ' ∧ primStep ⟨eR, σ'⟩ = uniform z σ'⌝)
    (Φ : Val rT → _) : iprop%
    ▷ A ∗ ⤇ K.fill eR ∗ (∀ n, A ∗ ⤇ K.fill pl(#int (f n)) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
      wp L E eL Φ := by
  iintro ⟨HA, Hj, Hcnt⟩
  iapply wp_lift_prim_steps_coupl HvL
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  imod HA
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  ihave %hL := HstepL σ₁ $$ Hσ HA
  ihave %hR := HstepR (K.fill eR) σ₁' $$ Hs HA
  have hb : 0 + b ≤ b := (zero_add b).le
  have hredL := hL.1.toReducible
  have hredR := hR.1.toReducible.fill K
  have hcpl : L.Rel 0 (CoupledDraw z f σ₁ σ₁' K)
      (primStep ⟨eL, σ₁⟩) (primStep ⟨K.fill eR, σ₁'⟩) := by
    rw [hL.2, primStep_fill HvR, hR.2]
    exact uniform_rel_bij_fill Hz σ₁ σ₁' f K hdom hbij
  imod subset empty_subset with Hclose
  imodintro
  iexists CoupledDraw z f σ₁ σ₁' K, 0, b
  iframe %hb %hredL %hredR %hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %⟨n, hn0, hnz, heq1, heq2⟩
  obtain ⟨rfl, rfl⟩ := (mk.injEq ..).mp heq1
  obtain ⟨rfl, rfl⟩ := (mk.injEq ..).mp heq2
  iintro !> !>
  imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  iframe Hσ Hs' Hb
  iapply wp_value_of_toVal rfl
  iapply Hcnt
  iframe HA Hj'
  ipureintro; exact ⟨hn0, hnz⟩

/-! ### Instances: unit draws, labelled draws, mixed -/

/-- Couple `rand z ~ K[rand z]` along a bijection `f`. -/
theorem wp_couple_rand_rand (Φ : Val rT → _) : iprop%
    ⤇ K.fill pl(rand(#z, #())) ∗
      (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ ⤇ K.fill pl(#int (f n)) -∗ Φ (.int n)) ⊢
      wp L E pl(rand(#z, #())) Φ := by
  iintro ⟨Hj, Hcnt⟩
  iapply wp_couple_rand_core z f hdom hbij Hz K E iprop(emp) rand_toVal?_eq_none rand_not_isValue
    (fun σ => randUnit_step_pure Hz σ) (fun _ σ' => randUnit_step_pure Hz σ') Φ
  isplitr
  · iintro !>; iempintro
  iframe Hj
  iintro %n ⟨-, Hj', %hn⟩
  iapply Hcnt $$ %n %hn Hj'

/-- Couple `rand` on an empty tape with a spec `rand` on an empty tape, along `f`. -/
theorem wp_couple_rand_lbl_rand_lbl (α α' : Loc) (Φ : Val rT → _) : iprop%
    ▷ appNatTape α z [] ∗ ▷ specNatTape α' z [] ∗ ⤇ K.fill pl(rand(#z, #lbl α')) ∗
      (∀ n, appNatTape α z [] ∗ specNatTape α' z [] ∗ ⤇ K.fill pl(#int (f n)) ∗
        ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
      wp L E pl(rand(#z, #lbl α)) Φ := by
  iintro ⟨Hα, Hα', Hj, Hcnt⟩
  iapply wp_couple_rand_core z f hdom hbij Hz (eR := pl(rand(#z, #lbl α'))) K E
    iprop(appNatTape α z [] ∗ specNatTape α' z [])
    rand_toVal?_eq_none rand_not_isValue
    (fun σ => by iintro Hσ ⟨HA, -⟩; iapply (appNatTape_empty_rand_step Hz α σ) $$ Hσ HA)
    (fun e' σ' => by iintro Hs ⟨-, HS⟩; iapply (specNatTape_empty_rand_step Hz α' e' σ') $$ Hs HS)
    Φ
  isplitl [Hα Hα']
  · iintro !>; iframe
  iframe Hj
  iintro %n ⟨⟨HA, HS⟩, Hj', %hn⟩
  iapply Hcnt
  iframe HA HS Hj' %hn

/-- Couple `rand` on an empty tape with a spec `rand`, along `f`. -/
theorem wp_couple_tape_rand (α : Loc) (Φ : Val rT → _) : iprop%
    ▷ appNatTape α z [] ∗ ⤇ K.fill pl(rand(#z, #())) ∗
      (∀ n, appNatTape α z [] ∗ ⤇ K.fill pl(#int (f n)) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
      wp L E pl(rand(#z, #lbl α)) Φ :=
  wp_couple_rand_core z f hdom hbij Hz K E iprop(appNatTape α z [])
    rand_toVal?_eq_none rand_not_isValue
    (appNatTape_empty_rand_step Hz α) (fun _ σ' => randUnit_step_pure Hz σ') Φ

/-- Couple `rand` with a spec `rand` on an empty tape, along `f`. -/
theorem wp_couple_rand_tape (α' : Loc) (Φ : Val rT → _) : iprop%
    ▷ specNatTape α' z [] ∗ ⤇ K.fill pl(rand(#z, #lbl α')) ∗
      (∀ n, specNatTape α' z [] ∗ ⤇ K.fill pl(#int (f n)) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
      wp L E pl(rand(#z, #())) Φ :=
  wp_couple_rand_core z f hdom hbij Hz K E iprop(specNatTape α' z [])
    rand_toVal?_eq_none rand_not_isValue
    (fun σ => randUnit_step_pure Hz σ) (specNatTape_empty_rand_step Hz α') Φ

end Draw

/-- Couple two `rand`s whose tapes have a size `M ≠ z`, so both draw fresh, along `f`. -/
theorem wp_couple_rand_lbl_rand_lbl_wrong (z M : Int) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) (Hz : 0 < z) (HneM : z ≠ M)
    (K : Ectx rT) (E : CoPset) (α α' : Loc) (xs ys : List Int) (Φ : Val rT → _) : iprop%
    ▷ appNatTape α M xs ∗ ▷ specNatTape α' M ys ∗ ⤇ K.fill pl(rand(#z, #lbl α')) ∗
      (∀ n, appNatTape α M xs ∗ specNatTape α' M ys ∗ ⤇ K.fill pl(#int (f n)) ∗
        ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
      wp L E pl(rand(#z, #lbl α)) Φ := by
  iintro ⟨Hα, Hα', Hj, Hcnt⟩
  iapply wp_couple_rand_core z f hdom hbij Hz (eR := pl(rand(#z, #lbl α'))) K E
    iprop(appNatTape α M xs ∗ specNatTape α' M ys)
    rand_toVal?_eq_none rand_not_isValue
    (fun σ => by
      unfold appNatTape
      iintro Hσ ⟨⟨%fs, -, Hb⟩, -⟩
      ihave %hlk := app_state_lookup_tape $$ Hσ Hb
      ipureintro
      exact randLbl_wrong_uniform_step Hz HneM hlk)
    (fun _ σ' => by
      unfold specNatTape
      iintro Hs ⟨-, ⟨%fs', -, Hb'⟩⟩
      ihave %hlk := spec_auth_lookup_tape $$ Hs Hb'
      ipureintro
      exact randLbl_wrong_uniform_step Hz HneM hlk) Φ
  isplitl [Hα Hα']
  · iintro !>; iframe
  iframe Hj
  iintro %n ⟨⟨HA, HS⟩, Hj', %hn⟩
  iapply Hcnt
  iframe HA HS Hj' %hn

/-! ### Presampling onto tapes -/

/-- Presample one draw onto a program tape and one onto a spec tape, coupled along a bijection
`f`. -/
theorem wp_couple_tapes_bij {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} {z : Int}
    {α αₛ : Loc} {ns nsₛ : List Int} (f : Int → Int) (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) (Hz : 0 < z) : iprop%
    appNatTape α z ns ∗ specNatTape αₛ z nsₛ ∗
      (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ appNatTape α z (ns ++ [n]) -∗ specNatTape αₛ z (nsₛ ++ [f n]) -∗
        wp L E e Φ) ⊢
      wp L E e Φ := by
  iintro ⟨Hα, Hαₛ, Hcnt⟩
  iunfold appNatTape at Hα
  iunfold specNatTape at Hαₛ
  icases Hα with ⟨%fs, %Hfs, Hα⟩
  icases Hαₛ with ⟨%fsₛ, %Hfsₛ, Hαₛ⟩
  iapply wp_couple_erasables
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  ihave %hlk := app_state_lookup_tape $$ Hσ Hα
  ihave %hlkₛ := spec_auth_lookup_tape $$ Hs Hαₛ
  imod subset empty_subset with Hclose
  imodintro
  iexists (fun σ₂ σ₂' => ∃ n, 0 ≤ n ∧ n < z ∧
      σ₂ = σ₁.update_tapes (·.insert α ⟨z, fs ++ [tapeIdxOf Hz n]⟩) ∧
      σ₂' = σ₁'.update_tapes (·.insert αₛ ⟨z, fsₛ ++ [tapeIdxOf Hz (f n)]⟩)),
    tapePresample σ₁ α, tapePresample σ₁' αₛ
  have her := ErasableExpr.tapePresample hlk Hz
  have herₛ := ErasableExpr.tapePresample hlkₛ Hz
  have hcpl := tapePresample_rel_bij (L := L) hlk hlkₛ Hz f hdom hbij
  iframe %her %herₛ %hcpl
  iintro %σ₂ %σ₂' %⟨n, hn0, hnz, rfl, rfl⟩
  imod app_state_update_tape $$ Hσ Hα with ⟨Hσ', Hα'⟩
  imod spec_auth_update_tape $$ Hs Hαₛ with ⟨Hs', Hαₛ'⟩
  imod Hclose
  imodintro
  simp only [micrometerWpGS_stateInterp_eq, micrometerWpGS_specInterp_eq,
    ExtTreeMap.insert_eq_PartialMap_insert]
  iframe Hσ' Hs' Hb
  have hd := hdom n hn0 hnz
  ihave HnatA := appNatTape_fold (ns := ns ++ [n])
    (by simp [← Hfs, tapeIdxOf_val Hz hn0 hnz]) $$ Hα'
  ihave HnatS := specNatTape_fold (ns := nsₛ ++ [f n])
    (by simp [← Hfsₛ, tapeIdxOf_val Hz hd.1 hd.2]) $$ Hαₛ'
  iapply Hcnt $$ %n %⟨hn0, hnz⟩ HnatA HnatS

end CouplingRules

/-! ## Rules that spend budget credits -/

section CreditRules

variable [BudgetCreditGS B GF]

/-! ### The general rule: any lifting of the two uniform draws -/

/-- Couple `rand zL ~ K[rand zR]` along `S`, given a lifting of the two uniform draws within the
cancelable budget `c`; spends `↯b c`. -/
theorem wp_couple_rand_rand_lift (zL zR : Int) (HzL : 0 < zL) (HzR : 0 < zR) (S : Int → Int → Prop)
    (c : B) (hc : IsAddLeftRegular c) (Hcpl : L.Rel c S (unifInt zL HzL) (unifInt zR HzR))
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → _) : iprop%
    ⤇ K.fill pl(rand(#zR, #())) ∗ ↯b c ∗
      (∀ n m, ⌜S n m⌝ -∗ ⤇ K.fill pl(#m) -∗ Φ (.int n)) ⊢
      wp L E pl(rand(#zL, #())) Φ := by
  iintro ⟨Hj, Hc, Hcnt⟩
  iapply wp_lift_prim_steps_coupl rand_toVal?_eq_none
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  imod supply_decrease hc $$ Hb Hc with ⟨%r, %hr, Hdec⟩
  imod subset empty_subset with Hclose
  imodintro
  let S' : Cfg rT → Cfg rT → Prop := fun c₁ c₂ =>
    ∃ n m, S n m ∧ c₁ = ⟨pl(#n), σ₁⟩ ∧ c₂ = ⟨K.fill pl(#m), σ₁'⟩
  iexists S', c, r
  have hsum : c + r ≤ b := hr.ge
  have hredL := (randUnit_uniform_step HzL σ₁).1.toReducible
  have hredR := ((randUnit_uniform_step HzR σ₁').1.toReducible).fill K
  have hcpl : L.Rel c S' (primStep ⟨pl(rand(#zL, #())), σ₁⟩)
      (primStep ⟨K.fill pl(rand(#zR, #())), σ₁'⟩) := by
    rw [primStep_rand_unit HzL, primStep_fill rand_not_isValue, primStep_rand_unit HzR]
    exact uniform_rel_fill HzL HzR σ₁ σ₁' K Hcpl fun n m h => ⟨n, m, h, rfl, rfl⟩
  iframe %hsum %hredL %hredR %hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %⟨n, m, hS, heq1, heq2⟩
  obtain ⟨rfl, rfl⟩ := (mk.injEq ..).mp heq1
  obtain ⟨rfl, rfl⟩ := (mk.injEq ..).mp heq2
  iintro !> !>
  imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  iframe Hσ Hs' Hdec
  iapply wp_value_of_toVal rfl
  iapply Hcnt $$ %n %m %hS Hj'

/-- `wp_couple_rand_rand_lift` with equal bounds `N` (the shape of clutch-dp's
`hoare_couple_laplace`, for uniform draws). -/
theorem wp_couple_rand_rand_spend (N : Int) (HN : 0 < N) (S : Int → Int → Prop) (c : B)
    (hc : IsAddLeftRegular c) (Hcpl : L.Rel c S (unifInt N HN) (unifInt N HN)) (K : Ectx rT)
    (E : CoPset) (Φ : Val rT → _) : iprop%
    ⤇ K.fill pl(rand(#N, #())) ∗ ↯b c ∗
      (∀ r r', ⌜S r r'⌝ -∗ ⤇ K.fill pl(#r') -∗ Φ (.int r)) ⊢
      wp L E pl(rand(#N, #())) Φ :=
  wp_couple_rand_rand_lift N N HN HN S c hc Hcpl K E Φ

variable (zL zR : Int) (f : Int → Int) (b binj : B) (HzL : 0 < zL) (HzR : 0 < zR)

/-- Couple `rand zL ~ K[rand zR]` along `f`, given a lifting `Hcpl` of the two uniform draws at
cost `binj ≤ b`: the left draw is `n`, the right draw is `f n` (clutch's
`wp_couple_rand_rand_inj`, for any `L`). -/
theorem wp_couple_rand_rand_inj
    (Hcpl : L.Rel binj (fun n m ↦ 0 ≤ n ∧ n < zL ∧ m = f n) (unifInt zL HzL) (unifInt zR HzR))
    (hb : binj ≤ b) (hc : IsAddLeftRegular binj) (K : Ectx rT) (E : CoPset)
    (Φ : Val rT → _) : iprop%
    ⤇ K.fill pl(rand(#zR, #())) ∗ ↯b b ∗
      (∀ n, ⌜0 ≤ n ∧ n < zL⌝ -∗ ⤇ K.fill pl(#int (f n)) -∗ Φ (.int n)) ⊢
      wp L E pl(rand(#zL, #())) Φ := by
  iintro ⟨Hj, Herr, Hcnt⟩
  ihave Herr := weaken hb $$ Herr
  iapply wp_couple_rand_rand_lift zL zR HzL HzR _ binj hc Hcpl K E Φ
  iframe Hj Herr
  iintro %n %m %⟨hn0, hnz, rfl⟩ Hj'
  iapply Hcnt $$ %n %⟨hn0, hnz⟩ Hj'

/-- Couple `rand zL ~ K[rand zR]` along `f`, given a lifting `Hcpl` of the two uniform draws at
cost `binj ≤ b`: the left draw is `f m`, the right draw is `m` (clutch's
`wp_couple_rand_rand_rev_inj`, for any `L`). -/
theorem wp_couple_rand_rand_rev_inj
    (Hcpl : L.Rel binj (fun n m ↦ 0 ≤ m ∧ m < zR ∧ n = f m) (unifInt zL HzL) (unifInt zR HzR))
    (hb : binj ≤ b) (hc : IsAddLeftRegular binj) (K : Ectx rT) (E : CoPset)
    (Φ : Val rT → _) : iprop%
    ⤇ K.fill pl(rand(#zR, #())) ∗ ↯b b ∗
      (∀ m, ⌜0 ≤ m ∧ m < zR⌝ -∗ ⤇ K.fill pl(#m) -∗ Φ (.int (f m))) ⊢
      wp L E pl(rand(#zL, #())) Φ := by
  iintro ⟨Hj, Herr, Hcnt⟩
  ihave Herr := weaken hb $$ Herr
  iapply wp_couple_rand_rand_lift zL zR HzL HzR _ binj hc Hcpl K E Φ
  iframe Hj Herr
  iintro %n %m %⟨hm0, hmz, rfl⟩ Hj'
  iapply Hcnt $$ %m %⟨hm0, hmz⟩ Hj'

/-! ### Outcome-dependent credits -/

variable [L.IsReflexive]

/-- Couple `rand z ~ K[rand z]` along a bijection `f`, turning `↯b (s ε₁)` into `↯b (s (ε₂ n))` at
draw `n`, where `ε₁` bounds the average of `ε₂` (credits paid in expectation,
Eris `wp_couple_rand_adv_comp`). -/
theorem wp_couple_rand_rand_adv {s : ENNReal →+o B} [L.IsExpectationAdditive s] (z : Int)
    (f : Int → Int) (ε₁ : ENNReal) (ε₂ : Int → ENNReal)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m) (Hz : 0 < z)
    (hamort : (∑ n ∈ Finset.Ico 0 z, ε₂ n) / z.toNat ≤ ε₁) (hc : IsAddLeftRegular (s ε₁))
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → _) : iprop%
    ⤇ K.fill pl(rand(#z, #())) ∗ ↯b (s ε₁) ∗
      (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ ⌜¬ L.Absorbing (s (ε₂ n))⌝ -∗ ↯b (s (ε₂ n)) -∗
        ⤇ K.fill pl(#int (f n)) -∗ Φ (.int n)) ⊢
      wp L E pl(rand(#z, #())) Φ := by
  classical
  iintro ⟨Hj, Herr, Hcnt⟩
  iapply wp_lift_prim_steps_coupl_adv_absorbing rand_toVal?_eq_none
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  have hredL := (randUnit_uniform_step Hz σ₁).1.toReducible
  have hredR := (randUnit_uniform_step Hz σ₁').1.toReducible.fill K
  imod supply_decrease hc $$ Hb Herr with ⟨%r, %hr, Hb⟩
  imod subset empty_subset with Hclose
  have hb : s ε₁ + r ≤ b := hr.ge
  imodintro
  have hlift := uniform_lift_adv (L := L) (s := s) Hz f ε₁ ε₂ σ₁ σ₁' K hdom hbij hamort
  iexists advLeftover s z f σ₁ σ₁' K ε₂, s ε₁, r
  iframe %hb %hredL %hredR %hlift
  iintro %e₂ %σ₂ %e₂' %σ₂' !>
  -- leftover absorbing: exit left; on a coupled draw it is s (ε₂ n) + r: re-mint the credit; off
  -- the graph it is ⊤, hence absorbing (contradiction)
  by_cases habs : L.Absorbing (advLeftover s z f σ₁ σ₁' K ε₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + r)
  · imod Hclose
    imodintro
    ileft
    ipureintro
    exact habs
  by_cases hg : CoupledDraw z f σ₁ σ₁' K ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩
  · obtain ⟨n, hn0, hnz, h1, h2⟩ := hg
    obtain ⟨rfl, rfl⟩ := (mk.injEq ..).mp h1
    obtain ⟨rfl, rfl⟩ := (mk.injEq ..).mp h2
    rw [advLeftover_apply s f _ _ K ε₂ hn0 hnz] at habs ⊢
    have hna : ¬ L.Absorbing (s (ε₂ n)) := fun h => habs (h.mono le_self_add)
    imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
    imod supply_increase $$ Hb with ⟨Hb, Hfrag⟩
    imod Hclose
    imodintro
    iright
    rw [add_comm (s (ε₂ n))]
    iframe Hσ Hs' Hb
    iapply wp_value_of_toVal rfl
    iapply Hcnt $$ %n %⟨hn0, hnz⟩ %hna Hfrag Hj'
  · exfalso
    refine habs ?_
    simp only [advLeftover, hg, ↓reduceDIte]
    exact IsTopAbsorbing.absorbing_top.mono le_self_add

/-- Couple `rand z ~ K[rand z]` along the identity, avoiding the outcome `bad` for
`↯b (s (1 / z))` when `s 1` is absorbing. -/
theorem wp_couple_rand_rand_avoid {s : ENNReal →+o B} [L.IsExpectationAdditive s] (z bad : Int)
    (Hz : 0 < z) (habs : L.Absorbing (s 1)) (hc : IsAddLeftRegular (s (z.toNat : ENNReal)⁻¹))
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → _) : iprop%
    ⤇ K.fill pl(rand(#z, #())) ∗ ↯b (s (z.toNat : ENNReal)⁻¹) ∗
      (∀ n, ⌜(0 ≤ n ∧ n < z) ∧ n ≠ bad⌝ -∗ ⤇ K.fill pl(#n) -∗ Φ (.int n)) ⊢
      wp L E pl(rand(#z, #())) Φ := by
  classical
  iintro ⟨Hj, Herr, Hcnt⟩
  iapply wp_couple_rand_rand_adv z id (z.toNat : ENNReal)⁻¹ (fun n => if n = bad then 1 else 0)
    id_dom_range id_bij_range Hz (avoid_one_amort bad) hc K E Φ
  iframe Hj Herr
  iintro %n %hn %hna - Hj'
  by_cases hb : n = bad
  · simp only [hb, ↓reduceIte] at hna
    exact (hna habs).elim
  · simp only [id_eq]
    iapply Hcnt $$ %n %⟨hn, hb⟩ Hj'

end CreditRules

/-! ## Injective couplings at total variation -/

section CouplingRulesTV

open GradedDivergence

variable [BudgetCreditGS ENNReal GF]

/-- A finite ratio of naturals is cancelable, so it can be spent as a tv credit. -/
theorem isAddLeftRegular_natCast_div {a b : ℕ} (hb : b ≠ 0) :
    IsAddLeftRegular ((a : ENNReal) / b) :=
  (IsAddRegular.of_ne_top (div_ne_top (natCast_ne_top _) (Nat.cast_ne_zero.2 hb))).1

variable (zL zR : Int) (f : Int → Int) (ε : ENNReal)

/-- Couple `rand zL ~ K[rand zR]` (`zL ≤ zR`) along an injection `f : [0,zL) ↪ [0,zR)`, spending
`(zR - zL)/zR` error credits (Approxis's `wp_couple_rand_rand_inj`). -/
theorem wp_couple_rand_rand_inj_tv (hdom : ∀ n, 0 ≤ n → n < zL → 0 ≤ f n ∧ f n < zR)
    (hinj : ∀ n₁ n₂, 0 ≤ n₁ → n₁ < zL → 0 ≤ n₂ → n₂ < zL → f n₁ = f n₂ → n₁ = n₂) (HzL : 0 < zL)
    (Hle : zL ≤ zR) (hε : ((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal) ≤ ε) (K : Ectx rT)
    (E : CoPset) (Φ : Val rT → _) : iprop%
    ⤇ K.fill pl(rand(#zR, #())) ∗ ↯b ε ∗
      (∀ n, ⌜0 ≤ n ∧ n < zL⌝ -∗ ⤇ K.fill pl(#int (f n)) -∗ Φ (.int n)) ⊢
      wp tv.codensity E pl(rand(#zL, #())) Φ :=
  wp_couple_rand_rand_inj zL zR f ε _ HzL (HzL.trans_le Hle)
    (unifInt_addCoupl_inj HzL Hle f hdom hinj).codensity hε
    (isAddLeftRegular_natCast_div (by omega)) K E Φ

/-- Couple `rand zL ~ K[rand zR]` (`zR ≤ zL`) along an injection `f : [0,zR) ↪ [0,zL)`, spending
`(zL - zR)/zL` error credits (Approxis's `wp_couple_rand_rand_rev_inj`). -/
theorem wp_couple_rand_rand_rev_inj_tv (hdom : ∀ m, 0 ≤ m → m < zR → 0 ≤ f m ∧ f m < zL)
    (hinj : ∀ m₁ m₂, 0 ≤ m₁ → m₁ < zR → 0 ≤ m₂ → m₂ < zR → f m₁ = f m₂ → m₁ = m₂) (HzR : 0 < zR)
    (Hle : zR ≤ zL) (hε : ((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal) ≤ ε) (K : Ectx rT)
    (E : CoPset) (Φ : Val rT → _) : iprop%
    ⤇ K.fill pl(rand(#zR, #())) ∗ ↯b ε ∗
      (∀ m, ⌜0 ≤ m ∧ m < zR⌝ -∗ ⤇ K.fill pl(#m) -∗ Φ (.int (f m))) ⊢
      wp tv.codensity E pl(rand(#zL, #())) Φ :=
  wp_couple_rand_rand_rev_inj zL zR f ε _ (HzR.trans_le Hle) HzR
    (unifInt_addCoupl_rev_inj HzR Hle f hdom hinj).codensity hε
    (isAddLeftRegular_natCast_div (by omega)) K E Φ

end CouplingRulesTV

end ProbLang
