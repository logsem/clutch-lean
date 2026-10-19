module

public import Metrology.Micrometer.UnifInt
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

set_option linter.discrete false

/-! Coupling rules for `rand` in `wp`: draws against draws and tapes, with and without credits. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting
open scoped AppGS

namespace ProbLang

variable {rT : Type} [ProbLang.LawfulProbLangℝ rT]
variable {B : Type} {L : GradedLifting.{0} B}

/-! ## Fold/unfold bridges for the user-level tape predicates -/

section NatTapeBridges

variable {GF : BundledGFunctors}

theorem appNatTape_fold [AppGS rT GF] {l : Loc} {z : Int} {ns : List Int}
    {fs : List { z' : Int // 0 ≤ z' ∧ z' < z }} (hfs : fs.map (fun x => x.val) = ns) :
    l ↪ₐ ⟨z, fs⟩ ⊢@{IProp GF} appNatTape l z ns := by
  iintro Hb
  iunfold appNatTape
  iexists fs
  iframe %hfs Hb

theorem specNatTape_fold [SpecGS rT GF] {l : Loc} {z : Int} {ns : List Int}
    {fs : List { z' : Int // 0 ≤ z' ∧ z' < z }} (hfs : fs.map (fun x => x.val) = ns) :
    l ↪ₛ ⟨z, fs⟩ ⊢@{IProp GF} specNatTape l z ns := by
  iintro Hb
  iunfold specNatTape
  iexists fs
  iframe %hfs Hb

end NatTapeBridges

section CouplingRules

variable [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
  {hlc : HasLC} {GF : BundledGFunctors} [MeasurableSingletonClass rT] [MicrometerGS rT hlc GF]
  [BudgetGS B GF] [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] [L.IsTopAbsorbing] [L.HasBind]

theorem randUnit_step_pure {z : Int} (Hz : 0 < z) (σ : State rT) {P A : IProp GF} :
    ⊢ P -∗ A -∗ ⌜Discrete.Reducible pl(rand(#(.int z), #(.unit))) σ ∧
      primStep ⟨pl(rand(#(.int z), #(.unit))), σ⟩ = Cfg.uniform z σ⌝ := by
  iintro - -
  ipureintro
  exact randUnit_uniform_step Hz σ

theorem appNatTape_empty_rand_step {z : Int} (Hz : 0 < z) (α : Loc) (σ : State rT) :
    ⊢@{IProp GF} appStateAuth σ -∗ appNatTape α z [] -∗
      ⌜Discrete.Reducible pl(rand(#(.int z), #(.lbl α))) σ ∧
        primStep ⟨pl(rand(#(.int z), #(.lbl α))), σ⟩ = Cfg.uniform z σ⌝ := by
  unfold appNatTape
  iintro Hσ ⟨%fs, %hmap, Hb⟩
  obtain rfl : fs = [] := List.map_eq_nil_iff.mp hmap
  ihave %hlk := app_state_lookup_tape $$ Hσ Hb
  ipureintro
  exact randLbl_empty_uniform_step Hz hlk

theorem specNatTape_empty_rand_step {z : Int} (Hz : 0 < z) (α : Loc) (e : Exp rT)
    (σ : State rT) :
    ⊢@{IProp GF} Cfg.specAuth ⟨e, σ⟩ -∗ specNatTape α z [] -∗
      ⌜Discrete.Reducible pl(rand(#(.int z), #(.lbl α))) σ ∧
        primStep ⟨pl(rand(#(.int z), #(.lbl α))), σ⟩ = Cfg.uniform z σ⌝ := by
  unfold specNatTape
  iintro Hs ⟨%fs, %hmap, Hb⟩
  obtain rfl : fs = [] := List.map_eq_nil_iff.mp hmap
  ihave %hlk := spec_auth_lookup_tape $$ Hs Hb
  ipureintro
  exact randLbl_empty_uniform_step Hz hlk

theorem wp_couple_rand_core (z : Int) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) {eL eR : Exp rT} (K : Ectx rT) (E : CoPset) (A : IProp GF) [BI.Timeless A]
    (HvL : eL.toVal? = none) (HvR : ¬ eR.isValue)
    (HstepL : ∀ σ, ⊢@{IProp GF} appStateAuth σ -∗ A -∗
      ⌜Discrete.Reducible eL σ ∧ primStep ⟨eL, σ⟩ = Cfg.uniform z σ⌝)
    (HstepR : ∀ e' σ', ⊢@{IProp GF} Cfg.specAuth ⟨e', σ'⟩ -∗ A -∗
      ⌜Discrete.Reducible eR σ' ∧ primStep ⟨eR, σ'⟩ = Cfg.uniform z σ'⌝)
    (Φ : Val rT → IProp GF) : iprop%
    ▷ A ∗ ⤇ K.fill eR ∗ (∀ n, A ∗ ⤇ K.fill pl(#(.int (f n))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
    wp L E eL Φ := by
  iintro ⟨HA, Hj, Hcnt⟩
  iapply wp_lift_prim_steps_coupl HvL
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  imod HA
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  ihave %HL := HstepL σ₁ $$ Hσ HA
  ihave %HR := HstepR (K.fill eR) σ₁' $$ Hs HA
  have hb : 0 + b ≤ b := (zero_add b).le
  have hredL := HL.1.toReducible
  have hredR := HR.1.toReducible.fill K
  have hcpl : L.Rel 0 (CoupledDraw z f σ₁ σ₁' K)
      (primStep ⟨eL, σ₁⟩) (primStep ⟨K.fill eR, σ₁'⟩) := by
    rw [HL.2, primStep_fill HvR, HR.2]
    exact Cfg.uniform_codensity_bij_fill Hz σ₁ σ₁' f K hdom hbij
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  iexists CoupledDraw z f σ₁ σ₁' K, 0, b
  iframe %hb %hredL %hredR %hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %⟨n, hn0, hnz, heq1, heq2⟩
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq1
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq2
  iintro !> !>
  imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  iframe Hσ Hs' Hb
  iapply wp_value_of_toVal rfl
  iapply Hcnt
  iframe HA Hj'
  ipureintro; exact ⟨hn0, hnz⟩

theorem wp_couple_rand_rand (z : Int) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int z), #(.unit))) ∗
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ ⤇ K.fill pl(#(.int (f n))) -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int z), #(.unit))) Φ := by
  iintro ⟨Hj, Hcnt⟩
  iapply wp_couple_rand_core z f hdom hbij Hz K E iprop(emp)
    Exp.rand_toVal?_eq_none Exp.rand_not_isValue
    (fun σ => randUnit_step_pure Hz σ) (fun _ σ' => randUnit_step_pure Hz σ') Φ
  isplitr
  · iintro !>; iempintro
  iframe Hj
  iintro %n ⟨-, Hj', %hn⟩
  iapply Hcnt $$ %n %hn Hj'

theorem wp_couple_tapes_bij {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    {z : Int} {α αₛ : Loc} {ns nsₛ : List Int} (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) : iprop%
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
  ihave %hlk' := spec_auth_lookup_tape $$ Hs Hαₛ
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  iexists (fun σ₂ σ₂' => ∃ n, 0 ≤ n ∧ n < z ∧
      σ₂ = σ₁.update_tapes (·.insert α ⟨z, fs ++ [tapeIdxOf Hz n]⟩) ∧
      σ₂' = σ₁'.update_tapes (·.insert αₛ ⟨z, fsₛ ++ [tapeIdxOf Hz (f n)]⟩)),
    tapePresample σ₁ α, tapePresample σ₁' αₛ
  have her := ErasableExpr.tapePresample hlk Hz
  have her' := ErasableExpr.tapePresample hlk' Hz
  have hcpl := tapePresample_codensity_bij (L := L) hlk hlk' Hz f hdom hbij
  iframe %her %her' %hcpl
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

theorem wp_couple_rand_lbl_rand_lbl_wrong (z M : Int) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (HneM : z ≠ M) (K : Ectx rT) (E : CoPset) (α α' : Loc)
    (xs ys : List Int) (Φ : Val rT → IProp GF) : iprop%
    ▷ appNatTape α M xs ∗ ▷ specNatTape α' M ys ∗ ⤇ K.fill pl(rand(#(.int z), #(.lbl α'))) ∗
    (∀ n, appNatTape α M xs ∗ specNatTape α' M ys ∗ ⤇ K.fill pl(#(.int (f n))) ∗
      ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int z), #(.lbl α))) Φ := by
  iintro ⟨Hα, Hα', Hj, Hcnt⟩
  iapply wp_couple_rand_core z f hdom hbij Hz (eR := pl(rand(#(.int z), #(.lbl α')))) K E
    iprop(appNatTape α M xs ∗ specNatTape α' M ys)
    Exp.rand_toVal?_eq_none Exp.rand_not_isValue
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

theorem wp_couple_rand_lbl_rand_lbl (z : Int) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx rT) (E : CoPset) (α α' : Loc) (Φ : Val rT → IProp GF) : iprop%
    ▷ appNatTape α z [] ∗ ▷ specNatTape α' z [] ∗ ⤇ K.fill pl(rand(#(.int z), #(.lbl α'))) ∗
    (∀ n, appNatTape α z [] ∗ specNatTape α' z [] ∗ ⤇ K.fill pl(#(.int (f n))) ∗
      ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int z), #(.lbl α))) Φ := by
  iintro ⟨Hα, Hα', Hj, Hcnt⟩
  iapply wp_couple_rand_core z f hdom hbij Hz (eR := pl(rand(#(.int z), #(.lbl α')))) K E
    iprop(appNatTape α z [] ∗ specNatTape α' z [])
    Exp.rand_toVal?_eq_none Exp.rand_not_isValue
    (fun σ => by iintro Hσ ⟨HA, -⟩; iapply (appNatTape_empty_rand_step Hz α σ) $$ Hσ HA)
    (fun e' σ' => by iintro Hs ⟨-, HS⟩; iapply (specNatTape_empty_rand_step Hz α' e' σ') $$ Hs HS)
    Φ
  isplitl [Hα Hα']
  · iintro !>; iframe
  iframe Hj
  iintro %n ⟨⟨HA, HS⟩, Hj', %hn⟩
  iapply Hcnt
  iframe HA HS Hj' %hn

/-! ## Mixed tape-rand couplings -/

theorem wp_couple_tape_rand (z : Int) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx rT) (E : CoPset) (α : Loc) (Φ : Val rT → IProp GF) : iprop%
    ▷ appNatTape α z [] ∗ ⤇ K.fill pl(rand(#(.int z), #(.unit))) ∗
    (∀ n, appNatTape α z [] ∗ ⤇ K.fill pl(#(.int (f n))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int z), #(.lbl α))) Φ :=
  wp_couple_rand_core z f hdom hbij Hz K E iprop(appNatTape α z [])
    Exp.rand_toVal?_eq_none Exp.rand_not_isValue
    (appNatTape_empty_rand_step Hz α) (fun _ σ' => randUnit_step_pure Hz σ') Φ

theorem wp_couple_rand_tape (z : Int) (f : Int → Int)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (K : Ectx rT) (E : CoPset) (α' : Loc) (Φ : Val rT → IProp GF) : iprop%
    ▷ specNatTape α' z [] ∗ ⤇ K.fill pl(rand(#(.int z), #(.lbl α'))) ∗
    (∀ n, specNatTape α' z [] ∗ ⤇ K.fill pl(#(.int (f n))) ∗ ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int z), #(.unit))) Φ :=
  wp_couple_rand_core z f hdom hbij Hz K E iprop(specNatTape α' z [])
    Exp.rand_toVal?_eq_none Exp.rand_not_isValue
    (fun σ => randUnit_step_pure Hz σ) (specNatTape_empty_rand_step Hz α') Φ

end CouplingRules

/-! ## Rules that spend budget credits -/

section CreditRules

variable [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
  {hlc : HasLC} {GF : BundledGFunctors} [MeasurableSingletonClass rT] [MicrometerGS rT hlc GF]
  [BudgetCreditGS B GF] [L.IsLawful] [L.IsTopAbsorbing] [L.HasBind] [L.IsSupportLocal]

/-- Couple `rand z ~ K[rand z]` along a bijection `f`, paying `s (ε₂ n)` to the continuation at
the left draw `n` out of `↯b (s ε₁)`, where `ε₁` bounds the average of `ε₂`. -/
theorem wp_couple_rand_rand_adv [L.IsReflexive]
    {s : ENNReal →+o B} [L.IsExpectationAdditive s] (z : Int) (f : Int → Int) (ε₁ : ENNReal)
    (ε₂ : Int → ENNReal)
    (hdom : ∀ n, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m, 0 ≤ m → m < z → ∃! n, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) (hamort : (∑ n ∈ Finset.Ico 0 z, ε₂ n) / z.toNat ≤ ε₁)
    (hc : IsAddLeftRegular (s ε₁)) (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int z), #(.unit))) ∗ ↯b (s ε₁) ∗
    (∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ ⌜¬ L.Absorbing (s (ε₂ n))⌝ -∗ ↯b (s (ε₂ n)) -∗
      ⤇ K.fill pl(#(.int (f n))) -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int z), #(.unit))) Φ := by
  classical
  iintro ⟨Hj, Herr, Hcnt⟩
  iapply wp_lift_prim_steps_coupl_adv_absorbing Exp.rand_toVal?_eq_none
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  have hredL := (randUnit_uniform_step Hz σ₁).1.toReducible
  have hredR := (randUnit_uniform_step Hz σ₁').1.toReducible.fill K
  imod BudgetCredit.supply_decrease hc $$ Hb Herr with ⟨%r, %hr, Hb⟩
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  have hb : s ε₁ + r ≤ b := hr.ge
  imodintro
  have hlift := Cfg.uniform_lift_adv (L := L) (s := s) Hz f ε₁ ε₂ σ₁ σ₁' K hdom hbij hamort
  iexists Cfg.advLeftover s z f σ₁ σ₁' K ε₂, s ε₁, r
  iframe %hb %hredL %hredR %hlift
  iintro %e₂ %σ₂ %e₂' %σ₂' !>
  by_cases habs : L.Absorbing (Cfg.advLeftover s z f σ₁ σ₁' K ε₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + r)
  · imod Hclose
    imodintro
    ileft
    ipureintro
    exact habs
  by_cases hg : CoupledDraw z f σ₁ σ₁' K ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩
  · obtain ⟨n, hn0, hnz, h1, h2⟩ := hg
    obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp h1
    obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp h2
    rw [Cfg.advLeftover_apply s f _ _ K ε₂ hn0 hnz] at habs ⊢
    have hna : ¬ L.Absorbing (s (ε₂ n)) := fun h => habs (h.mono le_self_add)
    imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
    imod BudgetCredit.supply_increase $$ Hb with ⟨Hb, Hfrag⟩
    imod Hclose
    imodintro
    iright
    rw [add_comm (s (ε₂ n))]
    iframe Hσ Hs' Hb
    iapply wp_value_of_toVal rfl
    iapply Hcnt $$ %n %⟨hn0, hnz⟩ %hna Hfrag Hj'
  · exfalso
    refine habs ?_
    simp only [Cfg.advLeftover, hg, ↓reduceDIte]
    exact IsTopAbsorbing.absorbing_top.mono le_self_add

/-- Couple `rand z ~ K[rand z]` along the identity, avoiding the outcome `bad` for
`↯b (s (1 / z))` when `s 1` is absorbing. -/
theorem wp_couple_rand_rand_avoid [L.IsReflexive]
    {s : ENNReal →+o B} [L.IsExpectationAdditive s] (z bad : Int) (Hz : 0 < z)
    (habs : L.Absorbing (s 1))
    (hc : IsAddLeftRegular (s (z.toNat : ENNReal)⁻¹)) (K : Ectx rT) (E : CoPset)
    (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int z), #(.unit))) ∗ ↯b (s (z.toNat : ENNReal)⁻¹) ∗
    (∀ n, ⌜(0 ≤ n ∧ n < z) ∧ n ≠ bad⌝ -∗ ⤇ K.fill pl(#(.int n)) -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int z), #(.unit))) Φ := by
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

/-- Couple `rand zL ~ K[rand zR]` along `S`, given a lifting of the two uniform draws within the
cancelable budget `c`; spends `↯b c`. -/
theorem wp_couple_rand_rand_lift (zL zR : Int) (HzL : 0 < zL) (HzR : 0 < zR)
    (S : Int → Int → Prop) (c : B) (hc : IsAddLeftRegular c)
    (Hcpl : L.Rel c S (unifInt zL HzL) (unifInt zR HzR)) (K : Ectx rT) (E : CoPset)
    (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int zR), #(.unit))) ∗ ↯b c ∗
    (∀ n m, ⌜S n m⌝ -∗ ⤇ K.fill pl(#(.int m)) -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int zL), #(.unit))) Φ := by
  iintro ⟨Hj, Hc, Hcnt⟩
  iapply wp_lift_prim_steps_coupl Exp.rand_toVal?_eq_none
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  imod BudgetCredit.supply_decrease hc $$ Hb Hc with ⟨%r, %hr, Hdec⟩
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  let S' : Cfg rT → Cfg rT → Prop := fun c₁ c₂ =>
    ∃ n m, S n m ∧ c₁ = ⟨pl(#(.int n)), σ₁⟩ ∧ c₂ = ⟨K.fill pl(#(.int m)), σ₁'⟩
  iexists S', c, r
  have hsum : c + r ≤ b := hr.ge
  have hredL := (randUnit_uniform_step HzL σ₁).1.toReducible
  have hredR := ((randUnit_uniform_step HzR σ₁').1.toReducible).fill K
  have hcpl : L.Rel c S' (primStep ⟨pl(rand(#(.int zL), #(.unit))), σ₁⟩)
      (primStep ⟨K.fill pl(rand(#(.int zR), #(.unit))), σ₁'⟩) := by
    rw [primStep_rand_unit HzL, primStep_fill Exp.rand_not_isValue, primStep_rand_unit HzR]
    exact Cfg.uniform_codensity_fill HzL HzR σ₁ σ₁' K Hcpl fun n m h => ⟨n, m, h, rfl, rfl⟩
  iframe %hsum %hredL %hredR %hcpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %⟨n, m, hS, heq1, heq2⟩
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq1
  obtain ⟨rfl, rfl⟩ := (Cfg.mk.injEq ..).mp heq2
  iintro !> !>
  imod specProg_update $$ Hs Hj with ⟨Hs', Hj'⟩
  imod Hclose
  imodintro
  iframe Hσ Hs' Hdec
  iapply wp_value_of_toVal rfl
  iapply Hcnt $$ %n %m %hS Hj'

/-- Coupling `rand zL ~ rand zR` along `f`, given a coupling `Hcpl` of the two uniform draws
that costs `binj`: the left draw is `n`, the right draw is `f n` (clutch's
`wp_couple_rand_rand_inj`, for any `L`). -/
theorem wp_couple_rand_rand_inj (zL zR : Int) (f : Int → Int)
    (b binj : B) (HzL : 0 < zL) (HzR : 0 < zR)
    (Hcpl : L.Rel binj (fun n m ↦ 0 ≤ n ∧ n < zL ∧ m = f n) (unifInt zL HzL) (unifInt zR HzR))
    (hb : binj ≤ b) (hc : IsAddLeftRegular binj) (K : Ectx rT) (E : CoPset)
    (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int zR), #(.unit))) ∗ ↯b b ∗
    (∀ n, ⌜0 ≤ n ∧ n < zL⌝ -∗ ⤇ K.fill pl(#(.int (f n))) -∗ Φ (.int n)) ⊢
    wp L E pl(rand(#(.int zL), #(.unit))) Φ := by
  iintro ⟨Hj, Herr, Hcnt⟩
  ihave Herr := BudgetCredit.weaken hb $$ Herr
  iapply wp_couple_rand_rand_lift zL zR HzL HzR _ binj hc Hcpl K E Φ
  iframe Hj Herr
  iintro %n %m %⟨hn0, hnz, rfl⟩ Hj'
  iapply Hcnt $$ %n %⟨hn0, hnz⟩ Hj'

/-- Coupling `rand zL ~ rand zR` along `f`, given a coupling `Hcpl` of the two uniform draws
that costs `binj`: the left draw is `f m`, the right draw is `m` (clutch's
`wp_couple_rand_rand_rev_inj`, for any `L`). -/
theorem wp_couple_rand_rand_rev_inj (zL zR : Int) (f : Int → Int)
    (b binj : B) (HzL : 0 < zL) (HzR : 0 < zR)
    (Hcpl : L.Rel binj (fun n m ↦ 0 ≤ m ∧ m < zR ∧ n = f m) (unifInt zL HzL) (unifInt zR HzR))
    (hb : binj ≤ b) (hc : IsAddLeftRegular binj) (K : Ectx rT) (E : CoPset)
    (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int zR), #(.unit))) ∗ ↯b b ∗
    (∀ m, ⌜0 ≤ m ∧ m < zR⌝ -∗ ⤇ K.fill pl(#(.int m)) -∗ Φ (.int (f m))) ⊢
    wp L E pl(rand(#(.int zL), #(.unit))) Φ := by
  iintro ⟨Hj, Herr, Hcnt⟩
  ihave Herr := BudgetCredit.weaken hb $$ Herr
  iapply wp_couple_rand_rand_lift zL zR HzL HzR _ binj hc Hcpl K E Φ
  iframe Hj Herr
  iintro %n %m %⟨hm0, hmz, rfl⟩ Hj'
  iapply Hcnt $$ %m %⟨hm0, hmz⟩ Hj'

/-- Couple `rand N ~ K[rand N]` along `S`, given a lifting of the two uniform draws within the
cancelable budget `c`; spends `↯b c` (clutch-dp's `hoare_couple_laplace`, for any `L`). -/
theorem wp_couple_rand_rand_spend (N : Int) (HN : 0 < N) (S : Int → Int → Prop) (c : B)
    (hc : IsAddLeftRegular c) (Hcpl : L.Rel c S (unifInt N HN) (unifInt N HN))
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int N), #(.unit))) ∗ ↯b c ∗
    (∀ r r', ⌜S r r'⌝ -∗ ⤇ K.fill pl(#(.int r')) -∗ Φ (.int r)) ⊢
    wp L E pl(rand(#(.int N), #(.unit))) Φ :=
  wp_couple_rand_rand_lift N N HN HN S c hc Hcpl K E Φ

end CreditRules

/-! ## Injective couplings at total variation -/

section CouplingRulesTV

variable {hlc : HasLC} {GF : BundledGFunctors} [MeasurableSingletonClass rT]
  [MicrometerGS rT hlc GF] [BudgetCreditGS ENNReal GF]

theorem isAddLeftRegular_natCast_div {a b : ℕ} (hb : b ≠ 0) :
    IsAddLeftRegular ((a : ENNReal) / b) :=
  (IsAddRegular.of_ne_top
    (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (Nat.cast_ne_zero.2 hb))).1

/-- Coupling `rand zL ~ rand zR` (`zL ≤ zR`) along an injection `f : [0,zL) ↪ [0,zR)`,
spending `(zR - zL)/zR` error credits: the left draw is `n`, the right draw is `f n`.
Ports `wp_couple_rand_rand_inj` from `clutch/theories/approxis/coupling_rules.v`. -/
theorem wp_couple_rand_rand_inj_tv (zL zR : Int) (f : Int → Int) (ε : ENNReal)
    (hdom : ∀ n, 0 ≤ n → n < zL → 0 ≤ f n ∧ f n < zR)
    (hinj : ∀ n₁ n₂, 0 ≤ n₁ → n₁ < zL → 0 ≤ n₂ → n₂ < zL → f n₁ = f n₂ → n₁ = n₂)
    (HzL : 0 < zL) (Hle : zL ≤ zR)
    (hε : ((zR - zL).toNat : ENNReal) / (zR.toNat : ENNReal) ≤ ε)
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int zR), #(.unit))) ∗ ↯b ε ∗
    (∀ n, ⌜0 ≤ n ∧ n < zL⌝ -∗ ⤇ K.fill pl(#(.int (f n))) -∗ Φ (.int n)) ⊢
    wp GradedDivergence.tv.codensity E pl(rand(#(.int zL), #(.unit))) Φ :=
  wp_couple_rand_rand_inj zL zR f ε _ HzL (HzL.trans_le Hle)
    (unifInt_addCoupl_inj HzL Hle f hdom hinj).codensity hε
    (isAddLeftRegular_natCast_div (by omega)) K E Φ

/-- Coupling `rand zL ~ rand zR` (`zR ≤ zL`) along an injection `f : [0,zR) ↪ [0,zL)`,
spending `(zL - zR)/zL` error credits: the left draw is `f m`, the right draw is `m`.
Ports `wp_couple_rand_rand_rev_inj` from `clutch/theories/approxis/coupling_rules.v`. -/
theorem wp_couple_rand_rand_rev_inj_tv (zL zR : Int) (f : Int → Int) (ε : ENNReal)
    (hdom : ∀ m, 0 ≤ m → m < zR → 0 ≤ f m ∧ f m < zL)
    (hinj : ∀ m₁ m₂, 0 ≤ m₁ → m₁ < zR → 0 ≤ m₂ → m₂ < zR → f m₁ = f m₂ → m₁ = m₂)
    (HzR : 0 < zR) (Hle : zR ≤ zL)
    (hε : ((zL - zR).toNat : ENNReal) / (zL.toNat : ENNReal) ≤ ε)
    (K : Ectx rT) (E : CoPset) (Φ : Val rT → IProp GF) : iprop%
    ⤇ K.fill pl(rand(#(.int zR), #(.unit))) ∗ ↯b ε ∗
    (∀ m, ⌜0 ≤ m ∧ m < zR⌝ -∗ ⤇ K.fill pl(#(.int m)) -∗ Φ (.int (f m))) ⊢
    wp GradedDivergence.tv.codensity E pl(rand(#(.int zL), #(.unit))) Φ :=
  wp_couple_rand_rand_rev_inj zL zR f ε _ (HzR.trans_le Hle) HzR
    (unifInt_addCoupl_rev_inj HzR Hle f hdom hinj).codensity hε
    (isAddLeftRegular_natCast_div (by omega)) K E Φ

end CouplingRulesTV

end ProbLang
