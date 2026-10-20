module

public import Metrology.TotalEris.ErisGS
import Metrology.ProbLang.Syntax.Notation
public import Metrology.TotalEris.TotalPrimitiveLaws

@[expose] public section

/-! # Error credit rules  -/

open Iris Iris.Std Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped ENNReal AppGS

namespace ProbLang

variable {rT : Type _} [LawfulProbLangℝ rT]

-- TODO: Move me
def Exp.asLit (default : ℝ≥0∞) (value : BaseLit rT → ℝ≥0∞) : Exp rT → ℝ≥0∞ :=
  (fun x => x.getD default) ∘ Option.map value ∘ Exp.lit.π

@[fun_prop]
theorem Exp.measurable_asLit (default : ℝ≥0∞) (value : BaseLit rT → ℝ≥0∞)
    (Hm : Measurable value) : Measurable (Exp.asLit default value) := by
  unfold Exp.asLit; fun_prop

def BaseLit.asInt (default : ℝ≥0∞) (value : Int → ℝ≥0∞) : BaseLit rT → ℝ≥0∞ :=
  (fun x => x.getD default) ∘ Option.map value ∘ BaseLit.int.π

@[fun_prop]
theorem BaseLit.measurable_asInt (default : ℝ≥0∞) (value : Int → ℝ≥0∞) :
    Measurable (BaseLit.asInt (rT := rT) default value) := by unfold asInt; fun_prop

def BaseLit.asReal (default : ℝ≥0∞) (value : rT → ℝ≥0∞) : BaseLit rT → ℝ≥0∞ :=
  (fun x => x.getD default) ∘ Option.map value ∘ BaseLit.real.π

@[fun_prop]
theorem BaseLit.measurable_asReal (default : ℝ≥0∞) (value : rT → ℝ≥0∞) (hv : Measurable value) :
    Measurable (BaseLit.asReal default value) := by unfold asReal; fun_prop

theorem measurable_litInt_elim (g : Int → ENNReal) :
    Measurable (fun e : Exp rT => match e with | .lit (.int n) => g n | _ => 0) := by
  convert_to Measurable (Exp.asLit 0 (BaseLit.asInt 0 g))
  swap; fun_prop
  ext e
  cases e <;> try rfl
  case lit b => cases b <;> rfl

theorem measurable_litReal_elim (g : rT → ENNReal) (hg : Measurable g) :
    Measurable (fun e : Exp rT => match e with | .lit (.real r) => g r | _ => 0) := by
  convert_to Measurable (Exp.asLit 0 (BaseLit.asReal 0 g))
  swap; fun_prop
  ext e
  cases e <;> try rfl
  case lit r => cases r <;> rfl

namespace TotalEris

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]

open ErrorCredit

theorem errInterp_supply_decrease {εₛ ε : ENNReal} :
    iprop(errInterp (rT := rT) εₛ ∗ ↯ε) ⊢@{IProp GF} |==> errInterp (rT := rT) (εₛ - ε) := by
  iintro ⟨Hs, Hε⟩
  iapply supply_decrease $$ Hs Hε

theorem errInterp_supply_bound {εₛ ε : ENNReal} :
    iprop(errInterp (rT := rT) εₛ ∗ ↯ε) ⊢@{IProp GF} errInterp (rT := rT) εₛ ∗ ↯ε ∗ ⌜ε ≤ εₛ⌝ := by
  iintro ⟨Hs, Hε⟩
  ihave %hLe := supply_bound $$ Hs Hε
  iframe Hs Hε %hLe

theorem errInterp_supply_increase {ε δ : ENNReal} (h : ε + δ < 1) :
    iprop(errInterp (rT := rT) ε) ⊢@{IProp GF} |==> (errInterp (rT := rT) (ε + δ) ∗ ↯δ) :=
  ErrorCredit.supply_increase h

theorem twp_err_incr {E : CoPset} {e : Exp rT} {ε : ENNReal} {Φ : Val rT → IProp GF}
    (Hnv : e.toVal? = none) :
    iprop(↯ε ∗ ∀ ε', ⌜ε < ε'⌝ -∗ ↯ε' -∗ tglWp E e Φ) ⊢ tglWp E e Φ := by
  iintro ⟨Herr, Hwp⟩
  iapply twp_lift_step_fupd_glm Hnv
  iintro %σ₁ %ε₂ ⟨Hσ₁, Hε₂⟩
  imod (BIFUpdate.subset Std.LawfulSet.empty_subset) with Hclose
  imodintro
  iapply glm'_credit_bump
  iintro %ε' %Hε'
  by_cases hlt : ε' < 1
  case neg =>
    push Not at hlt
    imodintro
    iapply execStutter_spend hlt
  case pos =>
    imod Hclose with -
    have hbnd : ε₂ + (ε' - ε₂) < 1 := by rw [add_tsub_cancel_of_le Hε'.le]; exact hlt
    conv_rhs => rw [← add_tsub_cancel_of_le Hε'.le]
    imod errInterp_supply_increase hbnd $$ Hε₂ with ⟨HsuppNew, Hfrag⟩
    icombine Herr Hfrag as Herr'
    ihave %hValid := valid $$ Herr'
    ispecialize Hwp $$ %(ε + (ε' - ε₂)) %?bound Herr'
    case bound =>
      refine ENNReal.lt_add_right ?_ ?_
      · intro hε_top; simp [hε_top] at hValid
      · rw [Ne, tsub_eq_zero_iff_le]; exact not_le.mpr Hε'
    isimp only [tglWp_unfold_step Hnv] at Hwp
    imod Hwp $$ %σ₁ %(ε₂ + (ε' - ε₂)) [$] with HGlm
    imodintro
    iapply execStutter_free
    iexact HGlm

/-- Thin-air credit rule: A client is free to assume an arbitrarily small error credit. -/
theorem twp_err_pos {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} (Hnv : e.toVal? = none) :
    iprop(∀ ε, ⌜0 < ε⌝ -∗ ↯ε -∗ tglWp E e Φ) ⊢ tglWp E e Φ := by
  iintro Hwp
  iapply fupd_tglWp
  imod zero with Herr
  imodintro
  iapply twp_err_incr Hnv
  iframe

theorem twp_err_pos_add {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} {a : ℝ≥0∞}
    (Hnv : e.toVal? = none) :
    ⊢ ↯ a -∗ (∀ ε, ⌜0 < ε⌝ -∗ ↯ (a + ε) -∗ tglWp E e Φ) -∗ tglWp E e Φ := by
  iintro Ha Hwp
  iapply twp_err_pos Hnv
  iintro %ε %Hε Hε
  icombine Ha Hε as H
  iapply Hwp $$ %ε %Hε H

/-- If a program's spec holds at every credit cost in a set, you only have to pay the infimum of
those costs. -/
theorem twp_err_biInf {ι : Type _} {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} {S : Set ι}
    {ε : ι → ℝ≥0∞} (Hnv : e.toVal? = none) :
    iprop(↯(⨅ i ∈ S, ε i) ∗ ∀ i, ⌜i ∈ S⌝ -∗ ↯(ε i) -∗ tglWp E e Φ) ⊢ tglWp E e Φ := by
  iintro ⟨Herr, Hwp⟩
  iapply twp_err_incr Hnv
  iframe Herr
  iintro %ε' %Hlt Hε'
  obtain ⟨i, hi⟩ := iInf_lt_iff.mp Hlt
  obtain ⟨hiS, hlt⟩ := iInf_lt_iff.mp hi
  iapply Hwp $$ %i %hiS
  iapply ErrorCredit.weaken hlt.le $$ Hε'

/-- If the spec holds at cost `ε i` for every `i` in some set in the filter `l`, you only have to
pay `liminf ε` along `l`. -/
theorem twp_err_liminf {ι : Type _} {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    {l : Filter ι} {S : Set ι} {ε : ι → ℝ≥0∞} (hS : S ∈ l) (Hnv : e.toVal? = none) :
    iprop(↯(Filter.liminf ε l) ∗ ∀ i, ⌜i ∈ S⌝ -∗ ↯(ε i) -∗ tglWp E e Φ) ⊢ tglWp E e Φ := by
  iintro ⟨Herr, Hwp⟩
  iapply twp_err_biInf (S := S) Hnv
  iframe Hwp
  iapply ErrorCredit.weaken (Filter.le_liminf_of_le (h := Filter.mem_of_superset hS
    fun i hi => biInf_le ε hi)) $$ Herr

/-- Spend `↯ε₁` on a primitive step whose outcomes `ρ` (all in `R`) each receive `↯(f ρ)`,
given that `f` averages to at most `ε₁`. -/
theorem twp_glm_spend {E : CoPset} {e₁ : Exp rT} {ε₁ : ENNReal}
    {Φ : Val rT → IProp GF} {R : State rT → Cfg rT → Prop} {f : Cfg rT → ENNReal}
    (hv : e₁.toVal? = none)
    (Hbd : ∀ ρ, f ρ ≤ 1)
    (Hstate : ∀ {σ₁ : State rT} {ρ : Cfg rT}, R σ₁ ρ → ρ.state = σ₁)
    (Hred : ∀ σ₁, Reducible e₁ σ₁)
    (hRmeas : ∀ σ₁, MeasurableSet {ρ : Cfg rT | R σ₁ ρ})
    (hPgl : ∀ σ₁, Pgl 0 (R σ₁) (primStep ⟨e₁, σ₁⟩))
    (HInt : ∀ σ₁, (∫⁻ ρ, f ρ ∂(primStep ⟨e₁, σ₁⟩)) ≤ ε₁) :
    iprop(↯ε₁) ⊢
      iprop((∀ σ₁ ρ, ⌜R σ₁ ρ⌝ -∗ ↯(f ρ) -∗ tglWp E ρ.expr Φ) -∗
      tglWp E e₁ Φ) := by
  iintro Herr Hcont
  iapply twp_lift_step_fupd_glm hv
  iintro %σ₁ %ε_now ⟨Hσ, Hε_now⟩
  imod (BIFUpdate.subset Std.LawfulSet.empty_subset) with Hclose
  imodintro
  ihave ⟨Hε_now, Herr, %hLe⟩ := errInterp_supply_bound $$ [$Hε_now $Herr]
  iapply glm'_prim_step
  iexists (R σ₁), 0, (fun ρ : Cfg rT => (ε_now - ε₁) + f ρ), ((ε_now - ε₁) + 1)
  specialize Hred σ₁; specialize hRmeas σ₁; specialize hPgl σ₁
  have hbnd : ∀ ρ : Cfg rT, (ε_now - ε₁) + f ρ ≤ (ε_now - ε₁) + 1 :=
    fun ρ => add_le_add_right (Hbd ρ) _
  have hexp : 0 + ∫⁻ ρ, ((ε_now - ε₁) + f ρ) ∂(primStep ⟨e₁, σ₁⟩) ≤ ε_now := by
    rw [zero_add, MeasureTheory.lintegral_add_left measurable_const,
        MeasureTheory.lintegral_const]
    calc (ε_now - ε₁) * (primStep ⟨e₁, σ₁⟩) Set.univ + ∫⁻ ρ, f ρ ∂primStep ⟨e₁, σ₁⟩
        ≤ (ε_now - ε₁) * 1 + ε₁ := by gcongr; exacts [primStep_univ_le_one _, HInt σ₁]
      _ = ε_now := by rw [mul_one]; exact tsub_add_cancel_of_le hLe
  iframe %Hred %hRmeas %hbnd %hexp %hPgl
  iintro %ρ %HRρ
  imod errInterp_supply_decrease $$ [$Hε_now $Herr] with Hε_minus
  imodintro
  by_cases hlt : (ε_now - ε₁) + f ρ < 1
  case neg => push Not at hlt; iapply execStutter_spend hlt
  case pos =>
    iapply execStutter_free
    imod errInterp_supply_increase hlt $$ Hε_minus with ⟨Hε_new, Hcr⟩
    imod Hclose with -
    imodintro
    rw [Hstate HRρ]
    iframe Hσ Hε_new
    iapply Hcont $$ %σ₁ %ρ %HRρ Hcr

/-- Use `twp_rand_exp'` instead; it drops the boundedness hypothesis. -/
theorem twp_rand_exp {E : CoPset} {z : Int} {ε₁ : ENNReal} {ε₂ : ℕ → ENNReal}
    {Φ : Val rT → IProp GF} (Hz : 0 < z) (Hbd : ∀ n, ε₂ n ≤ 1)
    (HSum : (∑ n ∈ Finset.range z.toNat, ε₂ n) / z.toNat ≤ ε₁) :
    iprop(↯ε₁) ⊢
      iprop((∀ n, ⌜0 ≤ n ∧ n < z⌝ ∗ ↯(ε₂ n.toNat) -∗
        Φ (.int n : Val rT)) -∗
      tglWp E (pl(rand(#(.int z), #(.unit)))) Φ) := by
  have Hnv : (pl(rand(#(.int z), #(.unit))) : Exp rT).toVal? = none := solve_not_value
  have hhead : ∀ σ₁ : State rT, HeadReducible (pl(rand(#(.int z), #(.unit)))) σ₁ :=
    fun σ₁ => (HeadStepSupport.RandNoTapeS Hz (le_refl _) Hz).ne_zero
  set R : State rT → Cfg rT → Prop :=
    fun σ₁ ρ => ∃ n : Int, 0 ≤ n ∧ n < z ∧ ρ = (⟨.lit (.int n), σ₁⟩ : Cfg rT)
  set f : Cfg rT → ENNReal := fun ρ => match ρ.expr with
    | .lit (.int n) => if h : 0 ≤ n ∧ n < z then ε₂ n.toNat else 0
    | _ => 0 with hf
  have hbd : ∀ ρ : Cfg rT, f ρ ≤ 1 := by
    intro ρ; simp only [hf]; split
    · split <;> first | exact Hbd _ | exact zero_le
    · exact zero_le
  have hstate : ∀ {σ₁ : State rT} {ρ : Cfg rT}, R σ₁ ρ → ρ.state = σ₁ := by
    rintro σ₁ ρ ⟨n, _, _, rfl⟩; rfl
  have hred : ∀ σ₁, Reducible (pl(rand(#(.int z), #(.unit)))) σ₁ :=
    fun σ₁ => reducible_of_headReducible (by is_lc) (hhead σ₁)
  have hrmeas : ∀ σ₁ : State rT, MeasurableSet {ρ : Cfg rT | R σ₁ ρ} := fun σ₁ => by
    apply Set.Countable.measurableSet
    apply Set.Countable.mono (s₂ := (fun n : Int => (⟨.lit (.int n), σ₁⟩ : Cfg rT)) '' Set.univ)
    · rintro ρ ⟨n, _, _, rfl⟩; exact ⟨n, trivial, rfl⟩
    · exact Set.countable_univ.image _
  have hpgl : ∀ σ₁ : State rT,
      Pgl 0 (R σ₁) (primStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ₁⟩) := fun σ₁ => by
    show (primStep ⟨pl(rand(#(.int z), #(.unit))), σ₁⟩) {ρ : Cfg rT | ¬ R σ₁ ρ} ≤ 0
    refine le_of_eq ?_
    rw [primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible (by is_lc) (hhead σ₁))]
    show (Cfg.uniform z σ₁) {ρ : Cfg rT | ¬ R σ₁ ρ} = 0
    have hg : Measurable (fun n : Int => (⟨.lit (.int n), σ₁⟩ : Cfg rT)) := Measurable.of_discrete
    have hRc : MeasurableSet {ρ : Cfg rT | ¬ R σ₁ ρ} := (hrmeas σ₁).compl
    rw [Cfg.uniform_eq_map_uniformOfFinset Hz σ₁, MeasureTheory.Measure.map_apply hg hRc,
      PMF.toMeasure_apply_eq_zero_iff _ (hg hRc), PMF.support_uniformOfFinset,
      Set.disjoint_left]
    intro n hn hcontra
    rw [Finset.mem_coe, Finset.mem_Ico] at hn
    exact hcontra ⟨n, hn.1, hn.2, rfl⟩
  have hint : ∀ σ₁ : State rT,
      (∫⁻ ρ, f ρ ∂(primStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ₁⟩)) ≤ ε₁ := fun σ₁ => by
    have hφ : Measurable f := (measurable_litInt_elim _).comp Cfg.measurable_expr
    rw [primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible (by is_lc) (hhead σ₁))]
    show (∫⁻ ρ, f ρ ∂(Cfg.uniform z σ₁)) ≤ ε₁
    rw [Cfg.lintegral_uniform' Hz σ₁ hφ, ← ENNReal.div_eq_inv_mul]
    convert HSum using 2
    refine Finset.sum_nbij' (i := fun n : Int => n.toNat) (j := (Nat.cast : ℕ → Int))
      ?_ ?_ (fun n hn => Int.toNat_of_nonneg (Finset.mem_Ico.mp hn).1)
      (fun k _ => Int.toNat_natCast k) ?_
    · intro n hn
      simp only [Finset.mem_Ico, Finset.mem_range] at hn ⊢
      omega
    · intro k hk
      simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢
      omega
    · intro n hn
      simp only [Finset.mem_Ico] at hn
      show (if h : 0 ≤ n ∧ n < z then ε₂ n.toNat else 0) = ε₂ n.toNat
      exact dite_eq_left ⟨hn.1, hn.2⟩
  iintro Herr Hcont
  iapply (twp_glm_spend Hnv hbd hstate hred hrmeas hpgl hint) $$ Herr
  iintro %σ₁ %ρ %HRρ Hcr
  obtain ⟨n, Hn₁, Hn₂, rfl⟩ := HRρ
  have hfe : f (⟨pl(#(.int n)), σ₁⟩ : Cfg rT) = ε₂ n.toNat := by
    simp only [hf]; exact dite_eq_left ⟨Hn₁, Hn₂⟩
  iapply (ErisWpGS.tglWp_value_of_toVal rfl)
  have hn : 0 ≤ n ∧ n < z := ⟨Hn₁, Hn₂⟩
  iapply Hcont $$ %n
  iframe %hn
  iapply (ErrorCredit.ext hfe) $$ Hcr

theorem twp_urand_exp {E : CoPset} {ε₁ : ENNReal}
    {ε₂ : rT → ENNReal} {Φ : Val rT → IProp GF}
    (hε₂ : Measurable ε₂) (Hbd : ∀ r, ε₂ r ≤ 1)
    (HInt : (∫⁻ r, ε₂ r ∂(LawfulProbLangℝ.unifUnit)) ≤ ε₁) :
    iprop(↯ε₁) ⊢
      iprop((∀ r, (⌜r ∈ LawfulProbLangℝ.unifUnitSupport⌝ ∗ ↯(ε₂ r)) -∗ Φ (.real r)) -∗
      tglWp E pl(urand) Φ) := by
  have Hnv : (pl(urand) : Exp rT).toVal? = none := solve_not_value
  have hhead : ∀ σ₁ : State rT, HeadReducible (pl(urand) : Exp rT) σ₁ :=
    fun σ₁ => show Cfg.uniformReal σ₁ ≠ 0 from MeasureTheory.IsProbabilityMeasure.ne_zero _
  have hps : ∀ σ₁ : State rT, primStep (⟨pl(urand), σ₁⟩ : Cfg rT)
      = (LawfulProbLangℝ.unifUnit).map (fun r : rT => (⟨.lit (.real r), σ₁⟩ : Cfg rT)) :=
    fun σ₁ => primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible (by is_lc) (hhead σ₁))
  have hg : ∀ σ₁ : State rT, Measurable (fun r : rT => (⟨.lit (.real r), σ₁⟩ : Cfg rT)) :=
    fun σ₁ => Cfg.measurable_iff.mpr
      ⟨Exp.lit.measurable.comp BaseLit.real.measurable, measurable_const⟩
  have hgemb : ∀ σ₁ : State rT,
      MeasurableEmbedding (fun r : rT => (⟨.lit (.real r), σ₁⟩ : Cfg rT)) := fun σ₁ => by
    have hcomp : (fun r : rT => (⟨.lit (.real r), σ₁⟩ : Cfg rT))
        = Cfg.measurableEquivProd.symm ∘ (fun e : Exp rT => (e, σ₁))
            ∘ Exp.lit ∘ BaseLit.real := rfl
    rw [hcomp]
    exact Cfg.measurableEquivProd.symm.measurableEmbedding.comp
      ((measurableEmbedding_prod_mk_right σ₁).comp
        (Exp.lit.measurableEmbedding.comp BaseLit.real.measurableEmbedding))
  set R : State rT → Cfg rT → Prop :=
    fun σ₁ ρ => ∃ r : rT, ρ = (⟨.lit (.real r), σ₁⟩ : Cfg rT) ∧ r ∈ LawfulProbLangℝ.unifUnitSupport
    with hR
  set f : Cfg rT → ENNReal := fun ρ => match ρ.expr with
    | .lit (.real r) => ε₂ r
    | _ => 0 with hf
  have hrange : ∀ σ₁ : State rT, {ρ : Cfg rT | R σ₁ ρ}
      = (fun r : rT => (⟨.lit (.real r), σ₁⟩ : Cfg rT)) '' LawfulProbLangℝ.unifUnitSupport := fun σ₁ => by
    ext ρ; simp only [Set.mem_image, Set.mem_ofPred_eq, hR]
    exact ⟨fun ⟨r, h, hr⟩ => ⟨r, hr, h.symm⟩, fun ⟨r, hr, h⟩ => ⟨r, h.symm, hr⟩⟩
  have hbd : ∀ ρ : Cfg rT, f ρ ≤ 1 := by
    intro ρ; simp only [hf]; split
    · exact Hbd _
    · exact zero_le
  have hstate : ∀ {σ₁ : State rT} {ρ : Cfg rT}, R σ₁ ρ → ρ.state = σ₁ := by
    rintro σ₁ ρ ⟨r, rfl, _⟩; rfl
  have hred : ∀ σ₁, Reducible (pl(urand) : Exp rT) σ₁ :=
    fun σ₁ => reducible_of_headReducible (by is_lc) (hhead σ₁)
  have hrmeas : ∀ σ₁ : State rT, MeasurableSet {ρ : Cfg rT | R σ₁ ρ} := fun σ₁ => by
    rw [hrange σ₁]
    exact (hgemb σ₁).measurableSet_image.mpr LawfulProbLangℝ.unifUnitSupportMeasurable
  have hpgl : ∀ σ₁ : State rT, Pgl 0 (R σ₁) (primStep ⟨Exp.urand, σ₁⟩) := fun σ₁ => by
    apply Pgl.of_concentrated
    rw [hps σ₁, hrange σ₁]
    exact concentratedOn_map (hg σ₁)
      ((hgemb σ₁).measurableSet_image.mpr LawfulProbLangℝ.unifUnitSupportMeasurable)
      LawfulProbLangℝ.unifUnitIsConcentrated
  have hint : ∀ σ₁ : State rT,
      (∫⁻ ρ, f ρ ∂(primStep ⟨Exp.urand, σ₁⟩)) ≤ ε₁ := fun σ₁ => by
    have hφ : Measurable f := (measurable_litReal_elim ε₂ hε₂).comp Cfg.measurable_expr
    rw [hps σ₁, MeasureTheory.lintegral_map hφ (hg σ₁)]
    exact HInt
  iintro Herr Hcont
  iapply (twp_glm_spend Hnv hbd hstate hred hrmeas hpgl hint) $$ Herr
  iintro %σ₁ %ρ %HRρ Hcr
  obtain ⟨r, rfl, hrsupp⟩ := HRρ
  have hfe : f (⟨pl(#(.real r)), σ₁⟩ : Cfg rT) = ε₂ r := by simp only [hf]
  iapply (ErisWpGS.tglWp_value_of_toVal rfl)
  iapply Hcont $$ %r
  iframe %hrsupp
  iapply (ErrorCredit.ext hfe) $$ Hcr

/-- `twp_urand_exp` without the bound, via the clamped credit `min (ε₂ r) 1`. -/
theorem twp_urand_exp' {E : CoPset} {ε₁ : ENNReal}
    {ε₂ : rT → ENNReal} {Φ : Val rT → IProp GF}
    (hε₂ : Measurable ε₂)
    (HInt : (∫⁻ r, ε₂ r ∂(LawfulProbLangℝ.unifUnit)) ≤ ε₁) :
    iprop(↯ε₁) ⊢
      iprop((∀ r, (⌜r ∈ LawfulProbLangℝ.unifUnitSupport⌝ ∗ ↯(ε₂ r)) -∗ Φ (.real r)) -∗
      tglWp E pl(urand) Φ) := by
  iintro Herr Hcont
  have hint : (∫⁻ r, min (ε₂ r) 1 ∂(LawfulProbLangℝ.unifUnit)) ≤ ε₁ :=
    (MeasureTheory.lintegral_mono fun r => min_le_left _ _).trans HInt
  iapply (twp_urand_exp (hε₂.min measurable_const)
    (fun r => min_le_right _ _) hint) $$ Herr
  iintro %r ⟨%hrsupp, Hcr⟩
  by_cases h : ε₂ r ≤ 1
  · iapply Hcont $$ %r
    iframe %hrsupp
    iapply (ErrorCredit.ext (show min (ε₂ r) 1 = ε₂ r from min_eq_left h)) $$ Hcr
  · push Not at h
    iexfalso
    iapply (ErrorCredit.contradict (le_min h.le (le_refl 1))) $$ Hcr

/-- `twp_rand_exp` without the bound, via the clamped credit `min (ε₂ n) 1`. -/
theorem twp_rand_exp' {E : CoPset} {z : Int} {ε₁ : ENNReal}
    {ε₂ : ℕ → ENNReal} {Φ : Val rT → IProp GF} (Hz : 0 < z)
    (HSum : (∑ n ∈ Finset.range z.toNat, ε₂ n) / z.toNat ≤ ε₁) :
    iprop(↯ε₁) ⊢
      iprop((∀ n, ⌜0 ≤ n ∧ n < z⌝ ∗ ↯(ε₂ n.toNat) -∗
        Φ (.int n : Val rT)) -∗
      tglWp E (pl(rand(#(.int z), #(.unit)))) Φ) := by
  iintro Herr Hcont
  have hsum : (∑ n ∈ Finset.range z.toNat, min (ε₂ n) 1) / (z.toNat : ENNReal) ≤ ε₁ :=
    (ENNReal.div_le_div_right
      (Finset.sum_le_sum fun n _ => min_le_left _ _) _).trans HSum
  iapply (twp_rand_exp Hz
    (fun n => min_le_right _ _) hsum) $$ Herr
  iintro %n ⟨%Hn, Hcr⟩
  by_cases h : ε₂ n.toNat ≤ 1
  · iapply Hcont $$ %n
    iframe %Hn
    iapply (ErrorCredit.ext (show min (ε₂ n.toNat) 1 = ε₂ n.toNat from min_eq_left h)) $$ Hcr
  · push Not at h
    iexfalso
    iapply (ErrorCredit.contradict (le_min h.le (le_refl 1))) $$ Hcr

end TotalEris
end ProbLang
