module

public import Metrology.LiveEris.PrimitiveLaws
import Metrology.ProbLang.Syntax.Notation
import Metrology.Iris.LocalBI

@[expose] public section

/-! # LiveEris credit rules

Spending error and divergence credits at random draws, thin-air rules for both, and conversion of
error credits into divergence credits.
-/

open Iris Iris.Std Iris.BI Iris.ProofMode ProbLang ProbLang.LiveEris.LiveWpGS
  ProbLang.LiveEris.CreditVec
open scoped ENNReal AppGS

namespace ProbLang
namespace LiveEris

variable {rT : Type _}

/-- The credit assigned to the outcome of `rand z`: `H n` on the integer `n` in range, else `0`. -/
def randCredit (z : Int) (H : ℕ → ℝ≥0∞) (ρ : Cfg rT) : ℝ≥0∞ :=
  match ρ.expr with
  | .lit (.int n) => if 0 ≤ n ∧ n < z then H n.toNat else 0
  | _ => 0

theorem randCredit_int {z n : Int} {H : ℕ → ℝ≥0∞} {σ : State rT} (hn : 0 ≤ n ∧ n < z) :
    randCredit z H (⟨pl(#n), σ⟩ : Cfg rT) = H n.toNat := by
  simp [randCredit, hn]

theorem randCredit_le_one {z : Int} {H : ℕ → ℝ≥0∞} (hH : ∀ n, H n ≤ 1) (ρ : Cfg rT) :
    randCredit z H ρ ≤ 1 := by
  unfold randCredit; split
  · split <;> first | exact hH _ | exact zero_le
  · exact zero_le

variable [MeasurableSpace rT]

theorem randCredit_measurable (z : Int) (H : ℕ → ℝ≥0∞) : Measurable (randCredit (rT := rT) z H) :=
  (measurable_litInt_elim _).comp Cfg.measurable_expr

variable [LawfulProbLangℝ rT]

theorem rand_headReducible {z : Int} (Hz : 0 < z) (σ : State rT) :
    HeadReducible (pl(rand(#z, #())) : Exp rT) σ :=
  (HeadStepSupport.RandNoTapeS Hz (le_refl _) Hz).ne_zero

theorem lintegral_randCredit_le {z : Int} (Hz : 0 < z) (σ : State rT) {H : ℕ → ℝ≥0∞} {b : ℝ≥0∞}
    (HSum : (∑ n ∈ Finset.range z.toNat, H n) / z.toNat ≤ b) :
    (∫⁻ ρ, randCredit z H ρ ∂(primStep ⟨pl(rand(#z, #())), σ⟩)) ≤ b := by
  rw [primStep_eq_headStep
    (Exp.decompItem_none_of_lc_headReducible (by is_lc) (rand_headReducible Hz σ))]
  show (∫⁻ ρ, randCredit z H ρ ∂(Cfg.uniform z σ)) ≤ b
  rw [Cfg.lintegral_uniform Hz σ (randCredit_measurable z H), ← ENNReal.div_eq_inv_mul]
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
    simp [randCredit, Finset.mem_Ico.mp hn]

variable {hlc : HasLC} {GF : BundledGFunctors} [LiveGS rT hlc GF]
variable {Q : State rT → State rT → Prop}
local bi IProp GF

private theorem creditAuth_creditInterp {ε δ : ℝ≥0∞} :
    creditAuth ε δ ⊢ LiveWpGS.creditInterp (creditVec ε δ) := by
  iintro Ha
  isimp only [liveWpGS_creditInterp_eq]
  iexists δ
  iframe Ha
  ipureintro
  rfl

/-! ## Spending credits at a step -/

/-- Spend `ε₁` error and `δ₁` divergence credits on a step, handing each reached outcome `ρ` the
credits `f ρ` and `g ρ`, whose averages are at most `ε₁` and `δ₁`. -/
theorem lwp_credit_spend {E : CoPset} {e₁ : Exp rT} {ε₁ δ₁ : ℝ≥0∞} {Φ : Val rT → IProp GF}
    {R : State rT → Cfg rT → Prop} {f g : Cfg rT → ℝ≥0∞}
    (hv : e₁.toVal? = none) (Hfm : Measurable f) (Hbdf : ∀ ρ, f ρ ≤ 1) (Hbdg : ∀ ρ, g ρ ≤ 1)
    (Hstate : ∀ {σ₁ : State rT} {ρ : Cfg rT}, R σ₁ ρ → ρ.state = σ₁)
    (Hred : ∀ σ₁, Reducible e₁ σ₁)
    (hRmeas : ∀ σ₁, MeasurableSet {ρ : Cfg rT | R σ₁ ρ})
    (hPgl : ∀ σ₁, Pgl 0 (R σ₁) (primStep ⟨e₁, σ₁⟩))
    (HIntf : ∀ σ₁, (∫⁻ ρ, f ρ ∂(primStep ⟨e₁, σ₁⟩)) ≤ ε₁)
    (HIntg : ∀ σ₁, (∫⁻ ρ, g ρ ∂(primStep ⟨e₁, σ₁⟩)) ≤ δ₁) :
    iprop(creditFrag ε₁ δ₁) ⊢
      iprop((∀ σ₁ ρ, ⌜R σ₁ ρ⌝ -∗ creditFrag (f ρ) (g ρ) -∗ lwp Q E ρ.expr Φ) -∗
        lwp Q E e₁ Φ) := by
  iintro Hcr Hcont
  iapply lwp_lift_step_glm hv
  iintro %σ₁ %c ⟨Hσ, Hc⟩
  isimp only [liveWpGS_creditInterp_eq] at Hc
  icases Hc with ⟨%d, %Hd, Ha⟩
  ihave %⟨hε, hδ⟩ := Credit.supply_bound $$ Ha Hcr
  ihave %⟨_, hdfin⟩ := Credit.auth_valid $$ Ha
  imod Credit.supply_decrease $$ Ha Hcr with Ha
  imod (BIFUpdate.subset Std.LawfulSet.empty_subset) with Hclose
  imodintro
  iapply glm_prim_step
  have hμ : primStep ⟨e₁, σ₁⟩ Set.univ ≤ 1 := primStep_univ_le_one _
  have hbnd : ∀ ρ : Cfg rT, creditVec (c .err - ε₁ + f ρ) (d - δ₁ + g ρ) ≤
      creditVec (c .err - ε₁ + 1) (d - δ₁ + 1) := by
    intro ρ i
    cases i
    · exact add_le_add_right (Hbdf ρ) _
    · exact add_le_add (add_le_add_right (Hbdf ρ) _) (add_le_add_right (Hbdg ρ) _)
  have hexp : charge 0 + expect (primStep ⟨e₁, σ₁⟩)
      (fun ρ => creditVec (c .err - ε₁ + f ρ) (d - δ₁ + g ρ)) ≤ c := by
    intro i
    cases i
    · simp only [charge, expect, Pi.add_apply, zero_add, creditVec]
      rw [MeasureTheory.lintegral_add_left measurable_const, MeasureTheory.lintegral_const]
      calc (c .err - ε₁) * primStep ⟨e₁, σ₁⟩ Set.univ + ∫⁻ ρ, f ρ ∂primStep ⟨e₁, σ₁⟩
          ≤ (c .err - ε₁) * 1 + ε₁ := by gcongr; exact HIntf σ₁
        _ = c .err := by rw [mul_one]; exact tsub_add_cancel_of_le hε
    · simp only [charge, expect, Pi.add_apply, zero_add, creditVec]
      rw [show (∫⁻ ρ, c .err - ε₁ + f ρ + (d - δ₁ + g ρ) ∂primStep ⟨e₁, σ₁⟩) =
          ∫⁻ ρ, (c .err - ε₁ + (d - δ₁)) + (f ρ + g ρ) ∂primStep ⟨e₁, σ₁⟩ from
          MeasureTheory.lintegral_congr fun ρ => by ring]
      rw [MeasureTheory.lintegral_add_left measurable_const, MeasureTheory.lintegral_const,
        MeasureTheory.lintegral_add_left Hfm, Hd]
      calc (c .err - ε₁ + (d - δ₁)) * primStep ⟨e₁, σ₁⟩ Set.univ +
            ((∫⁻ ρ, f ρ ∂primStep ⟨e₁, σ₁⟩) + ∫⁻ ρ, g ρ ∂primStep ⟨e₁, σ₁⟩)
          ≤ (c .err - ε₁ + (d - δ₁)) * 1 + (ε₁ + δ₁) := by
            gcongr
            exacts [HIntf σ₁, HIntg σ₁]
        _ = c .err + d := by
            rw [mul_one, add_add_add_comm, tsub_add_cancel_of_le hε, tsub_add_cancel_of_le hδ]
  specialize Hred σ₁
  specialize hRmeas σ₁
  specialize hPgl σ₁
  iexists (R σ₁), 0, (fun ρ => creditVec (c .err - ε₁ + f ρ) (d - δ₁ + g ρ)),
    creditVec (c .err - ε₁ + 1) (d - δ₁ + 1)
  iframe %Hred %hRmeas %hbnd %hexp %hPgl
  iintro %ρ %HRρ
  imodintro
  by_cases hlt : c .err - ε₁ + f ρ < 1
  · iright
    ileft
    have hfin : d - δ₁ + g ρ < ∞ :=
      ENNReal.add_lt_top.mpr ⟨tsub_le_self.trans_lt hdfin, (Hbdg ρ).trans_lt ENNReal.one_lt_top⟩
    imod Credit.supply_increase hlt hfin $$ Ha with ⟨Ha, Hfrag⟩
    imod Hclose with -
    imodintro
    rw [Hstate HRρ]
    iframe Hσ
    isplitl [Ha]
    · iapply creditAuth_creditInterp $$ Ha
    · iapply Hcont $$ %σ₁ %ρ %HRρ Hfrag
  · ileft
    ipureintro
    push Not at hlt
    intro i
    cases i
    · exact hlt
    · exact hlt.trans le_self_add

/-- `rand z` spends `ε₁` error and `δ₁` divergence credits, handing outcome `n` the credits `F n`
and `G n`. -/
theorem lwp_rand_credit {E : CoPset} {z : Int} {ε₁ δ₁ : ℝ≥0∞} {F G : ℕ → ℝ≥0∞}
    {Φ : Val rT → IProp GF} (Hz : 0 < z) (HF : ∀ n, F n ≤ 1) (HG : ∀ n, G n ≤ 1)
    (HSumF : (∑ n ∈ Finset.range z.toNat, F n) / z.toNat ≤ ε₁)
    (HSumG : (∑ n ∈ Finset.range z.toNat, G n) / z.toNat ≤ δ₁) :
    iprop(creditFrag ε₁ δ₁) ⊢
      iprop((∀ n, ⌜0 ≤ n ∧ n < z⌝ ∗ creditFrag (F n.toNat) (G n.toNat) -∗ Φ (.int n)) -∗
        lwp Q E (pl(rand(#z, #()))) Φ) := by
  set R : State rT → Cfg rT → Prop :=
    fun σ₁ ρ => ∃ n : Int, (0 ≤ n ∧ n < z) ∧ ρ = (⟨.lit (.int n), σ₁⟩ : Cfg rT)
  have hstate : ∀ {σ₁ : State rT} {ρ : Cfg rT}, R σ₁ ρ → ρ.state = σ₁ := by
    rintro σ₁ ρ ⟨n, -, rfl⟩; rfl
  have hred : ∀ σ₁ : State rT, Reducible (pl(rand(#z, #())) : Exp rT) σ₁ :=
    fun σ₁ => reducible_of_headReducible (by is_lc) (rand_headReducible Hz σ₁)
  have hrmeas : ∀ σ₁ : State rT, MeasurableSet {ρ : Cfg rT | R σ₁ ρ} := fun σ₁ => by
    apply Set.Countable.measurableSet
    apply Set.Countable.mono (s₂ := (fun n : Int => (⟨.lit (.int n), σ₁⟩ : Cfg rT)) '' Set.univ)
    · rintro ρ ⟨n, -, rfl⟩; exact ⟨n, trivial, rfl⟩
    · exact Set.countable_univ.image _
  have hpgl : ∀ σ₁ : State rT,
      Pgl 0 (R σ₁) (primStep ⟨pl(rand(#z, #())), σ₁⟩) := fun σ₁ => by
    show (primStep ⟨pl(rand(#z, #())), σ₁⟩) {ρ : Cfg rT | ¬ R σ₁ ρ} ≤ 0
    refine le_of_eq ?_
    rw [primStep_eq_headStep
      (Exp.decompItem_none_of_lc_headReducible (by is_lc) (rand_headReducible Hz σ₁))]
    show (Cfg.uniform z σ₁) {ρ : Cfg rT | ¬ R σ₁ ρ} = 0
    have hg : Measurable (fun n : Int => (⟨.lit (.int n), σ₁⟩ : Cfg rT)) := Measurable.of_discrete
    have hRc : MeasurableSet {ρ : Cfg rT | ¬ R σ₁ ρ} := (hrmeas σ₁).compl
    rw [Cfg.uniform_eq_map_uniformOfFinset Hz σ₁, MeasureTheory.Measure.map_apply hg hRc,
      PMF.toMeasure_apply_eq_zero_iff _ (hg hRc), PMF.support_uniformOfFinset,
      Set.disjoint_left]
    intro n hn hcontra
    rw [Finset.mem_coe, Finset.mem_Ico] at hn
    exact hcontra ⟨n, hn, rfl⟩
  iintro Hcr Hcont
  iapply (lwp_credit_spend (Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w)
    (randCredit_measurable z F) (randCredit_le_one HF) (randCredit_le_one HG) hstate hred hrmeas
    hpgl (fun σ₁ => lintegral_randCredit_le Hz σ₁ HSumF)
    (fun σ₁ => lintegral_randCredit_le Hz σ₁ HSumG)) $$ Hcr
  iintro %σ₁ %ρ %HRρ Hcr
  obtain ⟨n, hn, rfl⟩ := HRρ
  iapply lwp_value_of_toVal rfl
  iapply Hcont $$ %n
  iframe %hn
  iapply Credit.frag_ext (randCredit_int hn) (randCredit_int hn) $$ Hcr

/-- `rand z` spends error credits only; outcomes with more than one credit are impossible. -/
theorem lwp_rand_err {E : CoPset} {z : Int} {ε₁ : ℝ≥0∞} {F : ℕ → ℝ≥0∞} {Φ : Val rT → IProp GF}
    (Hz : 0 < z) (HSum : (∑ n ∈ Finset.range z.toNat, F n) / z.toNat ≤ ε₁) :
    iprop(↯ε₁) ⊢
      iprop((∀ n, ⌜0 ≤ n ∧ n < z⌝ ∗ ↯(F n.toNat) -∗ Φ (.int n)) -∗
        lwp Q E (pl(rand(#z, #()))) Φ) := by
  have hsum : (∑ n ∈ Finset.range z.toNat, min (F n) 1) / (z.toNat : ℝ≥0∞) ≤ ε₁ :=
    (ENNReal.div_le_div_right (Finset.sum_le_sum fun n _ => min_le_left _ _) _).trans HSum
  have hzero : (∑ n ∈ Finset.range z.toNat, (0 : ℝ≥0∞)) / (z.toNat : ℝ≥0∞) ≤ 0 := by simp
  iintro Hcr Hcont
  iapply (lwp_rand_credit Hz (fun n => min_le_right _ _) (fun _ => zero_le) hsum hzero) $$ Hcr
  iintro %n ⟨%Hn, Hcr⟩
  by_cases h : F n.toNat ≤ 1
  · iapply Hcont $$ %n
    iframe %Hn
    iapply Credit.frag_ext (min_eq_left h) rfl $$ Hcr
  · push Not at h
    iexfalso
    iapply Credit.err_contradict (le_min h.le le_rfl) $$ Hcr

/-- `rand z` spends divergence credits only. -/
theorem lwp_rand_div {E : CoPset} {z : Int} {δ₁ : ℝ≥0∞} {G : ℕ → ℝ≥0∞} {Φ : Val rT → IProp GF}
    (Hz : 0 < z) (HG : ∀ n, G n ≤ 1)
    (HSum : (∑ n ∈ Finset.range z.toNat, G n) / z.toNat ≤ δ₁) :
    iprop(↻δ₁) ⊢
      iprop((∀ n, ⌜0 ≤ n ∧ n < z⌝ ∗ ↻(G n.toNat) -∗ Φ (.int n)) -∗
        lwp Q E (pl(rand(#z, #()))) Φ) := by
  have hzero : (∑ n ∈ Finset.range z.toNat, (0 : ℝ≥0∞)) / (z.toNat : ℝ≥0∞) ≤ 0 := by simp
  iintro Hcr Hcont
  iapply (lwp_rand_credit Hz (fun _ => zero_le) HG hzero HSum) $$ Hcr
  iintro %n ⟨%Hn, Hcr⟩
  iapply Hcont $$ %n
  iframe %Hn Hcr

/-! ## Thin air -/

/-- Before a step, any held credits may be assumed strictly larger in both coordinates. -/
theorem lwp_credit_incr {E : CoPset} {e : Exp rT} {ε δ : ℝ≥0∞} {Φ : Val rT → IProp GF}
    (Hnv : e.toVal? = none) :
    iprop(creditFrag ε δ ∗
      ∀ ε' δ', ⌜ε < ε'⌝ -∗ ⌜δ < δ'⌝ -∗ creditFrag ε' δ' -∗ lwp Q E e Φ) ⊢
      lwp Q E e Φ := by
  iintro ⟨Hcr, Hwp⟩
  iapply lwp_lift_step_glm Hnv
  iintro %σ₁ %c ⟨Hσ, Hc⟩
  isimp only [liveWpGS_creditInterp_eq] at Hc
  icases Hc with ⟨%d, %Hd, Ha⟩
  ihave %⟨hε, hδ⟩ := Credit.supply_bound $$ Ha Hcr
  ihave %⟨ha, hdfin⟩ := Credit.auth_valid $$ Ha
  imod (BIFUpdate.subset Std.LawfulSet.empty_subset) with Hclose
  imodintro
  iapply glm_credit_bump
  iintro %c' %Hb
  have hlt_err : c .err < c' .err := Hb.2 .err (ha.trans ENNReal.one_lt_top)
  have hlt_tot : c .tot < c' .tot := Hb.2 .tot (by
    rw [Hd]; exact ENNReal.add_lt_top.mpr ⟨ha.trans ENNReal.one_lt_top, hdfin⟩)
  set η : ℝ≥0∞ := min 1 (min (c' .err - c .err) ((c' .tot - c .tot) / 2)) with hη
  have hηpos : 0 < η := lt_min one_pos (lt_min (tsub_pos_of_lt hlt_err)
    (ENNReal.half_pos (tsub_pos_of_lt hlt_tot).ne'))
  have hηfin : η < ∞ := (min_le_left _ _).trans_lt ENNReal.one_lt_top
  have hle : creditVec (c .err + η) (d + η) ≤ c' := by
    intro i
    cases i
    · calc c .err + η ≤ c .err + (c' .err - c .err) :=
            add_le_add_right ((min_le_right _ _).trans (min_le_left _ _)) _
        _ = c' .err := add_tsub_cancel_of_le hlt_err.le
    · show c .err + η + (d + η) ≤ c' .tot
      calc c .err + η + (d + η) = c .tot + (η + η) := by rw [Hd]; ring
        _ ≤ c .tot + ((c' .tot - c .tot) / 2 + (c' .tot - c .tot) / 2) := by
            have h2 : η ≤ (c' .tot - c .tot) / 2 := (min_le_right _ _).trans (min_le_right _ _)
            gcongr
        _ = c' .tot := by rw [ENNReal.add_halves, add_tsub_cancel_of_le hlt_tot.le]
  by_cases hsat : c .err + η < 1
  · iright
    have hfin : d + η < ∞ := ENNReal.add_lt_top.mpr ⟨hdfin, hηfin⟩
    imod Credit.supply_increase hsat hfin $$ Ha with ⟨Ha, Hη⟩
    icombine Hcr Hη as Hcr
    imod Hclose with -
    ihave HW := Hwp $$ %(ε + η) %(δ + η) %?hε' %?hδ' Hcr
    case hε' => exact ENNReal.lt_add_right (ne_top_of_le_ne_top ha.ne_top hε) hηpos.ne'
    case hδ' => exact ENNReal.lt_add_right (ne_top_of_le_ne_top hdfin.ne_top hδ) hηpos.ne'
    rw [lwp_unfold_step Hnv]
    imod HW $$ %σ₁ %(creditVec (c .err + η) (d + η)) [Hσ Ha] with HG
    · iframe Hσ
      iapply creditAuth_creditInterp $$ Ha
    imodintro
    iapply glm_mono_grading hle $$ HG
  · ileft
    ipureintro
    push Not at hsat
    intro i
    cases i
    · exact hsat.trans (hle .err)
    · exact (hsat.trans le_self_add).trans (hle .tot)

theorem lwp_err_incr {E : CoPset} {e : Exp rT} {ε : ℝ≥0∞} {Φ : Val rT → IProp GF}
    (Hnv : e.toVal? = none) :
    iprop(↯ε ∗ ∀ ε', ⌜ε < ε'⌝ -∗ ↯ε' -∗ lwp Q E e Φ) ⊢ lwp Q E e Φ := by
  iintro ⟨Hcr, Hwp⟩
  iapply lwp_credit_incr Hnv
  iframe Hcr
  iintro %ε' %δ' %Hε %- Hcr
  iapply Hwp $$ %ε' %Hε
  iapply Credit.frag_weaken le_rfl zero_le $$ Hcr

theorem lwp_div_incr {E : CoPset} {e : Exp rT} {δ : ℝ≥0∞} {Φ : Val rT → IProp GF}
    (Hnv : e.toVal? = none) :
    iprop(↻δ ∗ ∀ δ', ⌜δ < δ'⌝ -∗ ↻δ' -∗ lwp Q E e Φ) ⊢ lwp Q E e Φ := by
  iintro ⟨Hcr, Hwp⟩
  iapply lwp_credit_incr Hnv
  iframe Hcr
  iintro %ε' %δ' %- %Hδ Hcr
  iapply Hwp $$ %δ' %Hδ
  iapply Credit.frag_weaken zero_le le_rfl $$ Hcr

/-- A client may assume an arbitrarily small error credit. -/
theorem lwp_err_pos {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} (Hnv : e.toVal? = none) :
    iprop(∀ ε, ⌜0 < ε⌝ -∗ ↯ε -∗ lwp Q E e Φ) ⊢ lwp Q E e Φ := by
  iintro Hwp
  iapply fupd_lwp
  imod Credit.zero with Hcr
  imodintro
  iapply lwp_err_incr Hnv
  iframe

/-- A client may assume an arbitrarily small divergence credit. -/
theorem lwp_div_pos {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} (Hnv : e.toVal? = none) :
    iprop(∀ δ, ⌜0 < δ⌝ -∗ ↻δ -∗ lwp Q E e Φ) ⊢ lwp Q E e Φ := by
  iintro Hwp
  iapply fupd_lwp
  imod Credit.zero with Hcr
  imodintro
  iapply lwp_div_incr Hnv
  iframe

/-- If the spec holds at error cost `ε i` for every `i` in a set, it suffices to pay the infimum. -/
theorem lwp_err_biInf {ι : Type _} {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} {S : Set ι}
    {ε : ι → ℝ≥0∞} (Hnv : e.toVal? = none) :
    iprop(↯(⨅ i ∈ S, ε i) ∗ ∀ i, ⌜i ∈ S⌝ -∗ ↯(ε i) -∗ lwp Q E e Φ) ⊢ lwp Q E e Φ := by
  iintro ⟨Herr, Hwp⟩
  iapply lwp_err_incr Hnv
  iframe Herr
  iintro %ε' %Hlt Hε'
  obtain ⟨i, hi⟩ := iInf_lt_iff.mp Hlt
  obtain ⟨hiS, hlt⟩ := iInf_lt_iff.mp hi
  iapply Hwp $$ %i %hiS
  iapply Credit.err_weaken hlt.le $$ Hε'

/-- If the spec holds at divergence cost `δ i` for every `i` in a set, it suffices to pay the
infimum. -/
theorem lwp_div_biInf {ι : Type _} {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} {S : Set ι}
    {δ : ι → ℝ≥0∞} (Hnv : e.toVal? = none) :
    iprop(↻(⨅ i ∈ S, δ i) ∗ ∀ i, ⌜i ∈ S⌝ -∗ ↻(δ i) -∗ lwp Q E e Φ) ⊢ lwp Q E e Φ := by
  iintro ⟨Hdiv, Hwp⟩
  iapply lwp_div_incr Hnv
  iframe Hdiv
  iintro %δ' %Hlt Hδ'
  obtain ⟨i, hi⟩ := iInf_lt_iff.mp Hlt
  obtain ⟨hiS, hlt⟩ := iInf_lt_iff.mp hi
  iapply Hwp $$ %i %hiS
  iapply Credit.div_weaken hlt.le $$ Hδ'

theorem lwp_err_liminf {ι : Type _} {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    {l : Filter ι} {S : Set ι} {ε : ι → ℝ≥0∞} (hS : S ∈ l) (Hnv : e.toVal? = none) :
    iprop(↯(Filter.liminf ε l) ∗ ∀ i, ⌜i ∈ S⌝ -∗ ↯(ε i) -∗ lwp Q E e Φ) ⊢
      lwp Q E e Φ := by
  iintro ⟨Herr, Hwp⟩
  iapply lwp_err_biInf (S := S) Hnv
  iframe Hwp
  iapply Credit.err_weaken (Filter.le_liminf_of_le (h := Filter.mem_of_superset hS
    fun i hi => biInf_le ε hi)) $$ Herr

theorem lwp_div_liminf {ι : Type _} {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    {l : Filter ι} {S : Set ι} {δ : ι → ℝ≥0∞} (hS : S ∈ l) (Hnv : e.toVal? = none) :
    iprop(↻(Filter.liminf δ l) ∗ ∀ i, ⌜i ∈ S⌝ -∗ ↻(δ i) -∗ lwp Q E e Φ) ⊢
      lwp Q E e Φ := by
  iintro ⟨Hdiv, Hwp⟩
  iapply lwp_div_biInf (S := S) Hnv
  iframe Hwp
  iapply Credit.div_weaken (Filter.le_liminf_of_le (h := Filter.mem_of_superset hS
    fun i hi => biInf_le δ hi)) $$ Hdiv

/-! ## Conversion -/

/-- Before a step, error credits may be converted into divergence credits. -/
theorem lwp_convert {E : CoPset} {e : Exp rT} {ε : ℝ≥0∞} {Φ : Val rT → IProp GF}
    (Hnv : e.toVal? = none) :
    iprop(↯ε ∗ (↻ε -∗ lwp Q E e Φ)) ⊢ lwp Q E e Φ := by
  iintro ⟨Hcr, Hwp⟩
  iapply lwp_of_credit_decrease Hnv
  iintro %σ %c ⟨Hσ, Hc⟩
  isimp only [liveWpGS_creditInterp_eq] at Hc
  icases Hc with ⟨%d, %Hd, Ha⟩
  ihave %⟨hε, _⟩ := Credit.supply_bound $$ Ha Hcr
  imod Credit.supply_convert $$ Ha Hcr with ⟨Ha, Hdiv⟩
  imodintro
  iexists creditVec (c .err - ε) (d + ε)
  isplitr
  · ipureintro
    intro i
    cases i
    · exact tsub_le_self
    · show c .err - ε + (d + ε) ≤ c .tot
      rw [Hd, ← add_assoc, add_right_comm, tsub_add_cancel_of_le hε]
  iframe Hσ
  isplitl [Ha]
  · iapply creditAuth_creditInterp $$ Ha
  · iapply Hwp $$ Hdiv

end LiveEris
end ProbLang
