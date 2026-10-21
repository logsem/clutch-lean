module

public import Metrology.Micrometer.AppWeakestpre
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Micrometer.Model
public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.Micrometer.CouplingRules
public import Metrology.Micrometer.OpenInv
import Metrology.Iris.LocalBI

/-! # Refinement rules without coupled draws

Pure and spec steps, embedding a left `wp`, and structural, value and budget-credit rules for
`refines`; coupled draws are in `AppRelRules`. -/

@[expose] public section

open Iris hiding wp_bind wp_mono wp_frame_wand
open Iris.ProofMode ProbLang.MicrometerWpGS
open scoped AppGS

namespace ProbLang

open Ectx (fill_comp fill_nil)
open Exp (ofVal toVal?_ofVal)
open BudgetCredit (weaken split amplifying)

variable {rT : Type} [LawfulProbLangℝ rT]

/-! ## Budget predicates -/

section Predicates
variable (B : Type) [AddCommMonoid B] [PartialOrder B]

/-- Every positive budget splits into two positive budgets (true for tv, where halving works). -/
abbrev PosSplits : Prop := ∀ b : B, 0 < b → ∃ b₁ b₂, 0 < b₁ ∧ 0 < b₂ ∧ b₁ + b₂ ≤ b

variable {B}

/-- Every positive budget is above some positive seed `s ε` (true for tv at `s = id`); unrelated to
the divergence class `GradedDivergence.HasSlack`. -/
abbrev HasSlack (s : ENNReal →+o B) : Prop := ∀ b : B, 0 < b → ∃ ε, 0 < ε ∧ s ε ≤ b

end Predicates

section AppRelRules
variable {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B] [OrderTop B]
  {L : GradedLifting.{0} B} {GF : BundledGFunctors} [IR : MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF] {E : CoPset} {K : Ectx rT} {A A' : lrel rT GF}
local bi IProp GF

section Steps
variable [L.IsLawful] [L.IsTopAbsorbing] {e e' e1 e2 e2' t : Exp rT} {K' : Ectx rT} {l : Loc}
  {v v' : Val rT}

/-! ## Pure steps and the left `wp` -/

variable {φ : Prop}
variable {n : ℕ}
/-- A pure step on the left, which earns a `▷`. -/
theorem refines_pure_l [Hex : PureExec φ n e e'] (Hφ : φ) : iprop%
    ▷^[n] refines L E (K.fill e') t A ⊢ refines L E (K.fill e) t A := by
  have HexK : PureExec φ n (K.fill e) (K.fill e') := PureExec.fill K
  iunfold refines
  iintro H %K' %b HK Hna Herr Hpos
  iapply wp_pure_step_later (Hex := HexK) Hφ
  inext
  iapply H $$ HK Hna Herr Hpos

/-- A pure step on the right; spec steps earn no `▷`. -/
theorem refines_pure_r [Hex : PureExec φ n e e'] (Hφ : φ) :
    refines L E t (K.fill e') A ⊢ refines L E t (K.fill e) A := by
  iunfold refines
  iintro H %K' %b Hj Hna Herr Hpos
  rw [fill_comp]
  ihave HStep := step_pure (K'.comp K) (Hex := Hex) Hφ $$ Hj
  iapply specUpdate_wp
  iapply specUpdate_mono
  iframe HStep
  iintro HK'
  isimp only [← fill_comp K' K e'] at HK'
  iapply H $$ %K' %b HK' Hna Herr Hpos

/-- Run the left focus by any `wp`, continuing with a refinement of the context. -/
theorem refines_wp_l :
    wp L ⊤ e1 (fun v => refines L E (K.fill v.1) t A) ⊢ refines L E (K.fill e1) t A := by
  iunfold refines
  iintro He %K' %b HK Hna Herr Hpos
  iapply wp_bind
  iapply wp_frame_wand (R := iprop(⤇ K'.fill t ∗ naOwnP E ∗ ↯b b ∗ ⌜(0 : B) < b⌝))
  iframe
  iapply wp_mono $$ He
  intro v
  rw [show ofVal v = v.1 from rfl]
  iintro HRefv ⟨HK, Hna, Herr, Hpos⟩
  iapply HRefv $$ %K' %b HK Hna Herr Hpos

/-- Open invariants around the atomic left step `e1`: given the spec thread, open masks to `E'`, run
`e1`, close them, and return the (possibly stepped) right program `t'` with a refinement of the
continuation. -/
theorem refines_atomic_l {E' : CoPset}
    (Hopen : OpenInv L e1) : iprop%
    (∀ (K' : Ectx rT), ⤇ K'.fill t -∗
      |={⊤, E'}=> wp L E' e1 fun v => iprop(|={E', ⊤}=> ∃ t',
        ⤇ K'.fill t' ∗ refines L E (K.fill v.1) t' A)) ⊢
    refines L E (K.fill e1) t A := by
  iunfold refines
  iintro Hlog %K' %b HK Hna Herr Hpos
  iapply wp_bind
  iapply wp_atomic Hopen
  imod Hlog $$ %K' HK with HW
  imodintro
  iapply wp_frame_wand (R := iprop(naOwnP E ∗ ↯b b ∗ ⌜(0 : B) < b⌝))
  iframe
  iapply wp_mono $$ HW
  intro v
  rw [show ofVal v = v.1 from rfl]
  iintro HFup ⟨Hna, Herr, Hpos⟩
  imod HFup with ⟨%t', HKt', HRef⟩
  imodintro
  iapply HRef $$ %K' %b HKt' Hna Herr Hpos

/-! ## Steps on the right (spec program) -/

/-- Run the right program by a spec update that ends in a value. -/
theorem refines_step_r : iprop%
    (∀ (K : Ectx rT), ⤇ K.fill e2 -∗
      specUpdate rT ⊤ (∃ (v : Val rT), iprop(⤇ K.fill v.1 ∗ refines L E e1 (K'.fill v.1) A))) ⊢
    refines L E e1 (K'.fill e2) A := by
  iunfold refines
  iintro He %K'' %b Hj Hna Herr Hpos
  isimp only [fill_comp K'' K' e2] at Hj
  ihave HStep := He $$ %(K''.comp K') Hj
  iapply specUpdate_wp
  iapply specUpdate_mono
  iframe HStep
  iintro ⟨%v, HK'', Hrefines⟩
  isimp only [← fill_comp K'' K' v.1] at HK''
  iapply Hrefines $$ %K'' %b HK'' Hna Herr Hpos

/-- Rewrite the right program by any spec update. -/
theorem refines_steps_r : iprop%
    (∀ (K : Ectx rT), ⤇ K.fill e2 -∗ specUpdate rT ⊤ (⤇ K.fill e2')) ⊢
    (|={⊤}=> refines L E e1 (K'.fill e2') A) -∗ refines L E e1 (K'.fill e2) A := by
  iunfold refines
  iintro Hupd Hlog %K'' %b Hj Hna Herr Hpos
  imod Hlog
  isimp only [fill_comp K'' K'] at Hj
  ihave HStep := Hupd $$ %(K''.comp K') Hj
  iapply specUpdate_wp
  iapply specUpdate_mono
  iframe HStep
  iintro HKres
  isimp only [← fill_comp K'' K' e2'] at HKres
  iapply Hlog $$ %K'' %b HKres Hna Herr Hpos

/-- Right-side `alloc`: continue with the fresh spec location. -/
theorem refines_alloc_r : iprop%
    (∀ l, l ↦ₛ v -∗ refines L E t (K.fill pl(#loc l)) A) ⊢
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

/-- Right-side load from a spec location. -/
theorem refines_load_r : iprop%
    l ↦ₛ v ∗ (l ↦ₛ v -∗ refines L E t (K.fill v.1) A) ⊢ refines L E t (K.fill pl(!#loc l)) A := by
  iintro ⟨Hl, Hlog⟩
  iapply refines_step_r
  iintro %K' Hj
  iapply specUpdate_mono
  ihave HStep := step_load K' $$ [$Hj $Hl]
  iframe HStep
  iintro ⟨HKRes, HlRes⟩
  isimp only [show ofVal v = v.1 from rfl] at HKRes
  iexists v
  iframe HKRes
  iapply Hlog $$ HlRes

/-- Right-side store to a spec location. -/
theorem refines_store_r : iprop%
    l ↦ₛ v ∗ (l ↦ₛ v' -∗ refines L E e (K.fill pl(#())) A) ⊢
    refines L E e (K.fill (.store pl(#loc l) v'.1)) A := by
  iintro ⟨Hl, Hlog⟩
  iapply refines_step_r
  iintro %K' Hj
  iapply specUpdate_mono
  ihave HStep := step_store K' v'.2 (toVal?_ofVal v') $$ [$Hj $Hl]
  iframe HStep
  iintro ⟨HKRes, Hl'⟩
  iexists .unit
  iframe HKRes
  iapply Hlog $$ Hl'

/-- Right-side draw from a spec tape, consuming its first entry. -/
theorem refines_randT_r {z n : Int} {ns : List Int} : iprop%
    specNatTape l z (n :: ns) ∗
    (specNatTape l z ns -∗ ⌜0 ≤ n ∧ n < z⌝ -∗ refines L E e (K.fill pl(#n)) A) ⊢
    refines L E e (K.fill pl(rand(#z, #lbl l))) A := by
  unfold refines
  iintro ⟨Hα, Hlog⟩ %K' %b Hj Hna Herr Hpos
  isimp only [fill_comp K' K] at Hj
  iapply wp_rand_tape_r (K'.comp K)
  iframe Hj Hα
  iintro HKRes HαNew %Hbnds
  isimp only [← fill_comp K' K] at HKRes
  iapply Hlog $$ HαNew %Hbnds %K' %b HKRes Hna Herr Hpos

/-- Right-side tape allocation: continue with a fresh empty spec tape. -/
theorem refines_alloctape_r {z : Int} : iprop%
    (∀ l, specNatTape l z [] -∗ refines L E e (K.fill pl(#lbl l)) A) ⊢
    refines L E e (K.fill pl(tape(#z))) A := by
  unfold refines
  iintro Hlog %K' %b Hj Hna Herr Hpos
  isimp only [fill_comp K' K] at Hj
  iapply wp_alloc_tape_r (K'.comp K)
  iframe Hj
  iintro %l HKRes Hl
  isimp only [← fill_comp K' K] at HKRes
  iapply Hlog $$ %l Hl %K' %b HKRes Hna Herr Hpos

/-! ## Structural rules -/

/-- Weaken the result relation of a refinement. -/
theorem refines_wand : iprop%
    refines L E e1 e2 A ⊢ (∀ v1 v2, A v1 v2 ={⊤}=∗ A' v1 v2) -∗ refines L E e1 e2 A' := by
  iintro He HAA
  ihave H := refines_bind [] [] $$ He
  isimp only [fill_nil] at H
  iapply H
  iintro %v %v' HA
  iapply refines_ret rfl rfl
  iapply HAA $$ %v %v' HA

/-- `refines_bind` as an entailment from its two premises. -/
theorem refines_bind_sep (K K' : Ectx rT) : iprop%
    refines L E e e' A ∗
      (∀ v v', A v v' -∗ refines L ⊤ (K.fill v.1) (K'.fill v'.1) A') ⊢
    refines L E (K.fill e) (K'.fill e') A' := by
  iintro ⟨H, Hk⟩
  iapply refines_bind K K' $$ H Hk

end Steps

/-! ## Value rules -/

variable {v v' : Val rT}
/-- Closures are related at `A → A'` when their applications to `A`-related values refine. -/
theorem refines_arrow_val (hv : v.1.isClosedEmpty ∧ v'.1.isClosedEmpty) : iprop%
    □ (∀ v1 v2, A v1 v2 -∗ refines L ⊤ (.app v.1 v1.1) (.app v'.1 v2.1) A') ⊢
    refines L ⊤ v.1 v'.1 (lrel_arr L A A') := by
  iintro #H
  iapply refines_ret rfl rfl
  imodintro
  unfold lrel_arr
  isplitr; · ipureintro; exact hv
  iintro !> %w1 %w2 HA
  iapply H $$ %w1 %w2 HA

/-- `refines_arrow_val` with the argument hypothesis given as a refinement. -/
theorem refines_arrow (hv : v.1.isClosedEmpty ∧ v'.1.isClosedEmpty) : iprop%
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

The `_of_bc` forms take the seed credit as an argument and work for every budget (dp included,
at `s = dpSlack`); the unseeded forms draw it from the threaded budget, which needs slack (tv). -/

section Credits
variable [CanonicallyOrderedAdd B] {e e' : Exp rT}

/-- Splits the threaded credit into two positive parts and hands one to the proof as `↯b b`; the
only way to reach the credit threaded through `refines` (`ec` is Rocq's "error credit"). -/
theorem refines_get_ec (hsplit : PosSplits B) : iprop%
    (∀ b : B, ↯b b -∗ ⌜0 < b⌝ -∗ refines L E e e' A) ⊢ refines L E e e' A := by
  unfold refines
  iintro Hcnt %K %b Hj Hna Herr %Hpos
  obtain ⟨b₁, b₂, hb₁, hb₂, hle⟩ := hsplit b Hpos
  ihave ⟨Herr1, Herr2⟩ := (weaken hle).trans split $$ Herr
  iapply Hcnt $$ %b₁ Herr1 %hb₁ %K %b₂ Hj Hna Herr2 %hb₂

section Absorbing
variable [L.IsLawful] {s : ENNReal →+o B} {ε : ENNReal} {k : NNReal} {v v' : Val rT}

/-- An absorbing credit `↯b c` discharges any refinement. -/
theorem refines_of_absorbing {c : B} (hc : L.Absorbing c) : ↯b c ⊢ refines L E e e' A := by
  unfold refines
  iintro Hc %K %b - - - -
  iapply wp_of_absorbing hc $$ Hc

/-- A seed credit `↯b (s ε)` amplifies by `k` up to the absorbing `↯b (s 1)` (Rocq
`refines_ind_amp`, seed made explicit). -/
theorem refines_ind_amp_of_bc
    (hε : 0 < ε) (habs : L.Absorbing (s 1)) (hk : 1 < k) : iprop%
    □ (∀ ε', ⌜0 < ε'⌝ -∗ □ (↯b (s ((k : ENNReal) * ε')) -∗ refines L E e e' A) -∗
      ↯b (s ε') -∗ refines L E e e' A) ⊢
    ↯b (s ε) -∗ refines L E e e' A := by
  iintro #Hamp Hε
  iapply amplifying hε hk $$ [] Hamp Hε
  iintro !> Hc
  iapply refines_of_absorbing habs $$ Hc

/-- A seed credit `↯b (s ε)` amplifies a function body uniformly in its arguments (core of
`refines_arrow_val_err`). -/
theorem refines_app_ind_amp_of_bc
    (hε : 0 < ε) (habs : L.Absorbing (s 1)) (hk : 1 < k) : iprop%
    □ (∀ ε', ⌜0 < ε'⌝ -∗
      □ (↯b (s ((k : ENNReal) * ε')) -∗
        ∀ v1 v2, A v1 v2 -∗ refines L ⊤ (.app v.1 v1.1) (.app v'.1 v2.1) A') -∗
      ↯b (s ε') -∗ ∀ v1 v2, A v1 v2 -∗ refines L ⊤ (.app v.1 v1.1) (.app v'.1 v2.1) A') ⊢
    ↯b (s ε) -∗ ∀ v1 v2, A v1 v2 -∗ refines L ⊤ (.app v.1 v1.1) (.app v'.1 v2.1) A' := by
  iintro #Hamp Hε
  iapply amplifying hε hk $$ [] Hamp Hε
  iintro !> Hc %w1 %w2 -
  iapply refines_of_absorbing habs $$ Hc

/-- Amplification rule for `refines`: seed a credit `↯b (s ε)` from the threaded budget and amplify
it by `k` (Rocq `refines_ind_amp`). -/
theorem refines_ind_amp
    (hsplit : PosSplits B) (hslack : HasSlack s) (habs : L.Absorbing (s 1)) (hk : 1 < k) : iprop%
    □ (∀ ε, ⌜0 < ε⌝ -∗ □ (↯b (s ((k : ENNReal) * ε)) -∗ refines L E e e' A) -∗ ↯b (s ε) -∗
      refines L E e e' A) ⊢
    refines L E e e' A := by
  iintro #Hamp
  iapply refines_get_ec hsplit
  iintro %b Herr %hpos
  obtain ⟨ε, hε, hle⟩ := hslack b hpos
  iapply refines_ind_amp_of_bc hε habs hk $$ Hamp
  iapply weaken hle $$ Herr

/-- Amplification for closures: the budget-seeded form of `refines_app_ind_amp_of_bc`, giving a
refinement at `A → A'` (Rocq `refines_arrow_val_err`). -/
theorem refines_arrow_val_err
    (hsplit : PosSplits B) (hslack : HasSlack s) (habs : L.Absorbing (s 1)) (hk : 1 < k)
    (hv : v.1.isClosedEmpty ∧ v'.1.isClosedEmpty) : iprop%
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
  ihave Herr := weaken hle $$ Herr
  iapply refines_app_ind_amp_of_bc hε habs hk $$ Hamp Herr %v1 %v2 HA

end Absorbing

end Credits
end AppRelRules

end ProbLang
