module

public import Metrology.Micrometer.CouplingRulesLaw
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

/-! # Presampling two tapes against a spec `rand`, by a bind law

`wp_couple_tapes_rand_law`: presample one draw onto each of two empty program tapes, and couple
the pair with a spec `rand N` step by any `HeadShift`, `SideFree` law. The head sees both draws at
once, so its cost can be a divergence of a function of the pair (the chi-squared method, ePrint
2017/537, Lemma 3). -/

@[expose] public section

-- these rules use the @[discrete] lifting lemmas without being discrete themselves
set_option linter.discrete false

open Iris Iris.Std Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting GradedDivergence
open MeasureTheory (Measure)
open scoped AppGS ENNReal

namespace ProbLang

open Cfg Ectx BudgetCredit BIFUpdate LawfulSet Exp
open BindLaw (SideFree)

variable {rT : Type} {B : Type}

/-! ## Two draws in a state, and their leftover -/

section Draws

variable (σ σ' : State rT) (α β : Loc) {z₁ z₂ : Int} (hz₁ : 0 < z₁) (hz₂ : 0 < z₂) (K : Ectx rT)

/-- `σ` with the single draw `a` on tape `α` (bound `z₁`) and `b` on tape `β` (bound `z₂`). -/
noncomputable def State.withDraws (a b : Int) : State rT :=
  (σ.update_tapes (·.insert α ⟨z₁, [tapeIdxOf hz₁ a]⟩)).update_tapes
    (·.insert β ⟨z₂, [tapeIdxOf hz₂ b]⟩)

/-- Draws in range are read back from `State.withDraws`. -/
theorem State.withDraws_inj (hαβ : α ≠ β) {a a' b b' : Int} (ha : 0 ≤ a ∧ a < z₁)
    (ha' : 0 ≤ a' ∧ a' < z₁) (hb : 0 ≤ b ∧ b < z₂) (hb' : 0 ≤ b' ∧ b' < z₂)
    (h : State.withDraws σ α β hz₁ hz₂ a b = State.withDraws σ α β hz₁ hz₂ a' b') :
    a = a' ∧ b = b' := by
  have h1 := congrArg (fun (τ : State rT) => τ.tapes[α]?) h
  have h2 := congrArg (fun (τ : State rT) => τ.tapes[β]?) h
  simp only [State.withDraws, State.update_tapes] at h1 h2
  rw [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_insert,
    Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_insert] at h1 h2
  simp [Ne.symm hαβ] at h1 h2
  exact ⟨by simpa [tapeIdxOf_val hz₁ ha.1 ha.2, tapeIdxOf_val hz₁ ha'.1 ha'.2] using
      congrArg Subtype.val h1,
    by simpa [tapeIdxOf_val hz₂ hb.1 hb.2, tapeIdxOf_val hz₂ hb'.1 hb'.2] using
      congrArg Subtype.val h2⟩

open Classical in
/-- The leftover of presampling `α`, `β` from `σ` against `K[rand N]` from `σ'`: `R a b m` at the
state with draws `a`, `b` and the configuration drawn as `m`, and `⊤` elsewhere. -/
noncomputable def presampleCost [_root_.Top B] (R : Int → Int → Int → B) (τ : State rT)
    (ρ' : Cfg rT) : B :=
  if h : ∃ a b m : Int, (0 ≤ a ∧ a < z₁) ∧ (0 ≤ b ∧ b < z₂) ∧
      τ = State.withDraws σ α β hz₁ hz₂ a b ∧ ρ' = ⟨K.fill pl(#int m), σ'⟩ then
    R h.choose h.choose_spec.choose h.choose_spec.choose_spec.choose
  else ⊤

/-- At the state with draws `a`, `b` and the configuration drawn as `m`, `presampleCost` is
`R a b m`. -/
theorem presampleCost_apply [_root_.Top B] (hαβ : α ≠ β) (R : Int → Int → Int → B) {a b : Int}
    (ha : 0 ≤ a ∧ a < z₁) (hb : 0 ≤ b ∧ b < z₂) (m : Int) :
    presampleCost σ σ' α β hz₁ hz₂ K R (State.withDraws σ α β hz₁ hz₂ a b)
      ⟨K.fill pl(#int m), σ'⟩ = R a b m := by
  rw [presampleCost, dite_eq_left_of_eq_true (eq_true ⟨a, b, m, ha, hb, rfl, rfl⟩)]
  generalize_proofs h
  obtain ⟨ha', hb', h1, h2⟩ := h.choose_spec.choose_spec.choose_spec
  obtain ⟨e1, e2⟩ := State.withDraws_inj σ α β hz₁ hz₂ hαβ ha ha' hb hb' h1
  have e3 := fill_injective K (congrArg Cfg.expr h2)
  injection e3 with e3
  injection e3 with e3
  rw [← e3, ← e2, ← e1]

/-- A finite `presampleCost` forces a state with two draws in range and a drawn configuration. -/
theorem exists_of_presampleCost_lt_top [Preorder B] [OrderTop B] {R : Int → Int → Int → B}
    {τ : State rT} {ρ' : Cfg rT} (h : presampleCost σ σ' α β hz₁ hz₂ K R τ ρ' < (⊤ : B)) :
    ∃ a b m : Int, (0 ≤ a ∧ a < z₁) ∧ (0 ≤ b ∧ b < z₂) ∧
      τ = State.withDraws σ α β hz₁ hz₂ a b ∧ ρ' = ⟨K.fill pl(#int m), σ'⟩ := by
  by_contra hne
  simp only [presampleCost, hne, dite_false, lt_self_iff_false] at h

end Draws

/-! ## Presampling two tapes -/

section Presample

variable [MeasurableSpace rT] (σ : State rT) (α β : Loc)

/-- Presample tape `α`, then tape `β`. -/
noncomputable def tapePresample₂ : Measure (State rT) :=
  (tapePresample σ α).bind fun τ ↦ tapePresample τ β

variable {z₁ z₂ : Int} (hz₁ : 0 < z₁) (hz₂ : 0 < z₂)

/-- Presampling two distinct empty tapes draws both values uniformly and independently. -/
theorem tapePresample₂_eq_bind (hαβ : α ≠ β) (h₁ : σ.tapes[α]? = some ⟨z₁, []⟩)
    (h₂ : σ.tapes[β]? = some ⟨z₂, []⟩) :
    tapePresample₂ σ α β =
      (unifInt z₁ hz₁).bind fun a ↦ (unifInt z₂ hz₂).map (State.withDraws σ α β hz₁ hz₂ a) := by
  have hβ (i : { z : Int // 0 ≤ z ∧ z < z₁ }) :
      (σ.update_tapes (·.insert α ⟨z₁, [] ++ [i]⟩)).tapes[β]? = some ⟨z₂, []⟩ := by
    rw [State.update_tapes, Std.ExtTreeMap.getElem?_insert]
    simpa [hαβ] using h₂
  rw [tapePresample₂, tapePresample_eq_map h₁,
    Measure.bind_map Measurable.of_discrete.aemeasurable tapePresample.measurable.aemeasurable,
    tapeIndexUniform_eq_map hz₁,
    Measure.bind_map Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable]
  congr 1
  funext a
  rw [tapePresample_eq_map (hβ _), tapeIndexUniform_eq_map hz₂,
    Measure.map_map Measurable.of_discrete Measurable.of_discrete]
  rfl

variable [LawfulProbLangℝ rT]

/-- Presampling two allocated tapes of positive bound leaves every expression distribution
unchanged. -/
theorem ErasableExpr.tapePresample₂ {t₁ t₂ : Tape} (h₁ : σ.tapes[α]? = some t₁)
    (hb₁ : 0 < t₁.bound) (h₂ : σ.tapes[β]? = some t₂) (hb₂ : 0 < t₂.bound) :
    ErasableExpr (tapePresample₂ σ α β) σ := by
  sorry

end Presample

/-! ## The rule -/

variable [MeasurableSpace rT] [LawfulProbLangℝ rT] {GF : BundledGFunctors}
local bi IProp GF

variable [AddCommMonoid B] [PartialOrder B] [CanonicallyOrderedAdd B] [OrderTop B]
  {L : GradedLifting.{0} B} [L.IsLawful] [L.IsTopAbsorbing] {hlc : HasLC}
  [BudgetCreditGS B GF] [MicrometerGS rT hlc GF]

/-- Presample `α` and `β` against `K[rand N]` by a step of `law`, spending `↯b c` on its head and
handing the leftover `R a b m` to the draws `a`, `b` and `m`. -/
theorem wp_couple_tapes_rand_law (law : L.BindLaw) [law.HeadShift] [law.SideFree] {α β : Loc}
    (hαβ : α ≠ β) {z₁ z₂ N : Int} (hz₁ : 0 < z₁) (hz₂ : 0 < z₂) (HN : 0 < N)
    (R : Int → Int → Int → B) (c : B) (hc : IsAddLeftRegular c) (K : Ectx rT)
    (hhead : ∀ σ σ', law.head
      ((unifInt z₁ hz₁).bind fun a ↦ (unifInt z₂ hz₂).map (State.withDraws σ α β hz₁ hz₂ a))
      ((unifInt N HN).map fun m ↦ (⟨K.fill pl(#int m), σ'⟩ : Cfg rT))
      (presampleCost σ σ' α β hz₁ hz₂ K R) c)
    (E : CoPset) (e : Exp rT) (Φ : Val rT → _) : iprop%
    appNatTape α z₁ [] ∗ appNatTape β z₂ [] ∗ ⤇ K.fill pl(rand(#N, #())) ∗ ↯b c ∗
      (∀ a b m, ⌜(0 ≤ a ∧ a < z₁) ∧ (0 ≤ b ∧ b < z₂) ∧ R a b m < (⊤ : B)⌝ -∗ ↯b (R a b m) -∗
        appNatTape α z₁ [a] -∗ appNatTape β z₂ [b] -∗ ⤇ K.fill pl(#int m) -∗ wp L E e Φ) ⊢
      wp L E e Φ := by
  iintro ⟨Hα, Hβ, Hj, Hc, Hcnt⟩
  iunfold appNatTape at Hα Hβ
  icases Hα with ⟨%fs₁, %Hfs₁, Hα⟩
  icases Hβ with ⟨%fs₂, %Hfs₂, Hβ⟩
  obtain rfl := List.map_eq_nil_iff.1 Hfs₁
  obtain rfl := List.map_eq_nil_iff.1 Hfs₂
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %b ⟨Hσ, Hs, Hb⟩
  ihave %rfl := specAuth_specFrag_agree $$ Hs Hj
  ihave %hlk₁ := app_state_lookup_tape $$ Hσ Hα
  ihave %hlk₂ := app_state_lookup_tape $$ Hσ Hβ
  imod supply_decrease hc $$ Hb Hc with ⟨%r, %hr, Hb⟩
  imod subset empty_subset with Hclose
  imodintro
  by_cases hrTop : r < (⊤ : B)
  swap
  · iapply specCoupl_absorbing
    exact IsTopAbsorbing.absorbing_top.mono (hr ▸ not_lt_top_iff.1 hrTop ▸ le_add_self)
  have Hred' : Reducible (K.fill pl(rand(#N, #()))) σ₁' :=
    (randUnit_uniform_step HN σ₁').1.toReducible.fill K
  have her := ErasableExpr.tapePresample₂ σ₁ α β hlk₁ hz₁ hlk₂ hz₂
  have := her.isProbabilityMeasure
  have := prim_step_mass Hred'
  have hν : (Measure.dirac σ₁').bind (fun σ ↦ pexecN 1 ⟨K.fill pl(rand(#N, #())), σ⟩) =
      (unifInt N HN).map fun m ↦ (⟨K.fill pl(#int m), σ₁'⟩ : Cfg rT) := by
    rw [dirac_bind_pexecN_one Hred', primStep_fill rand_not_isValue, primStep_rand_unit HN,
      uniform_eq_map HN,
      Measure.map_map (g := fun ρ : Cfg rT => (⟨K.fill ρ.expr, ρ.state⟩ : Cfg rT))
        (fillCfg.measurable K) Measurable.of_discrete]
    rfl
  have hhead' := hhead σ₁ σ₁'
  rw [← tapePresample₂_eq_bind σ₁ α β hz₁ hz₂ hαβ hlk₁ hlk₂, ← hν] at hhead'
  iapply specCoupl_couple_law law (law.mono_out (BindLaw.HeadShift.shift hrTop hhead') hr.ge)
    (.of_forall fun k₁ k₂ ↦ SideFree.side _ _ _ k₁ k₂) her (ErasableExpr.dret σ₁')
  iintro %σ₂ %e₂' %σ₂' %hR
  obtain ⟨a, b', m, ha, hb', rfl, hρ⟩ :=
    exists_of_presampleCost_lt_top _ _ _ _ _ _ _ (lt_of_le_of_lt le_self_add hR)
  obtain ⟨rfl, rfl⟩ := Cfg.mk.injEq .. ▸ hρ
  rw [presampleCost_apply _ _ _ _ _ _ _ hαβ R ha hb'] at hR ⊢
  iintro !>
  iapply specCoupl_ret
  imod specProg_update (e3 := K.fill pl(#int m)) $$ Hs Hj with ⟨Hs', Hj'⟩
  imod app_state_update_tape (s := ⟨z₁, [tapeIdxOf hz₁ a]⟩) $$ Hσ Hα with ⟨Hσ, Hα⟩
  imod app_state_update_tape (s := ⟨z₂, [tapeIdxOf hz₂ b']⟩) $$ Hσ Hβ with ⟨Hσ, Hβ⟩
  imod supply_increase (c := R a b' m) $$ Hb with ⟨Hb, Hfrag⟩
  imod Hclose
  imodintro
  rw [add_comm (R a b' m)]
  simp only [micrometerWpGS_stateInterp_eq, micrometerWpGS_specInterp_eq, State.withDraws,
    Std.ExtTreeMap.insert_eq_PartialMap_insert]
  iframe Hσ Hs' Hb
  ihave HnatA := appNatTape_fold (ns := [a]) (by simp [tapeIdxOf_val hz₁ ha.1 ha.2]) $$ Hα
  ihave HnatB := appNatTape_fold (ns := [b']) (by simp [tapeIdxOf_val hz₂ hb'.1 hb'.2]) $$ Hβ
  iapply Hcnt $$ %a %b' %m %⟨ha, hb', lt_of_le_of_lt le_self_add hR⟩ Hfrag HnatA HnatB Hj'

end ProbLang
