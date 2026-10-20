module

public import Metrology.TotalEris.TotalPrimitiveLaws
public import Metrology.TotalEris.TotalLifting
public import Metrology.TotalEris.Glm
public import Metrology.TotalEris.ErrorRules

@[expose] public section

/-! # Presample rules -/

open Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal

namespace ProbLang
namespace TotalEris

variable {rT : Type _}

abbrev TapeIdx (N : Int) := { z : Int // 0 ≤ z ∧ z < N }

noncomputable def tapeIdxFinset (N : Int) : Finset (TapeIdx N) :=
  (Finset.Ico 0 N).attach.image fun z => ⟨z.1, Finset.mem_Ico.mp z.2⟩

abbrev presampleUpdate (σ : State rT) (α : Loc) (N : Int) (bs : List (TapeIdx N))
    (n : TapeIdx N) : State rT :=
  σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)

/-- Distinct samples append distinct tape suffixes, so the presample state-update is injective. -/
theorem presample_update_injective {σ : State rT} {α : Loc} {N : Int} {bs : List (TapeIdx N)} :
    Function.Injective (presampleUpdate σ α N bs) := by
  intro n₁ n₂ heq
  have htape_eq : (σ.tapes.insert α ⟨N, bs ++ [n₁]⟩) = (σ.tapes.insert α ⟨N, bs ++ [n₂]⟩) := by
    simpa [State.update_tapes] using congrArg State.tapes heq
  have hget₁ : (σ.tapes.insert α ⟨N, bs ++ [n₁]⟩)[α]? = some ⟨N, bs ++ [n₁]⟩ :=
    Std.ExtTreeMap.getElem?_insert_self
  have hget₂ : (σ.tapes.insert α ⟨N, bs ++ [n₂]⟩)[α]? = some ⟨N, bs ++ [n₂]⟩ :=
    Std.ExtTreeMap.getElem?_insert_self
  rw [htape_eq, hget₂] at hget₁
  have hbs : bs ++ [n₂] = bs ++ [n₁] := by simpa using hget₁
  simpa using (List.append_cancel_left hbs).symm

theorem presample_choose_eq {σ σ' : State rT} {α : Loc} {N : Int} {bs : List (TapeIdx N)}
    {n : TapeIdx N} (h : ∃ m : TapeIdx N, σ' = presampleUpdate σ α N bs m)
    (hn : σ' = presampleUpdate σ α N bs n) : Classical.choose h = n :=
  presample_update_injective ((Classical.choose_spec h).symm.trans hn)

open Classical in
/-- Per-outcome credit for advanced composition: `ε₂ n` on the `n`-update, `0` off-support. -/
noncomputable def presampleAdvCompX₂ (σ : State rT) (α : Loc) (N : Int) (bs : List (TapeIdx N))
    (ε₂ : TapeIdx N → ENNReal) (σ' : State rT) : ENNReal :=
  if h : ∃ n : TapeIdx N, σ' = presampleUpdate σ α N bs n then ε₂ (Classical.choose h) else 0

open Classical in
/-- `presampleAdvCompX₂` is a countable sum of singleton indicators, one per sample. -/
theorem presampleAdvCompX₂_eq_tsum (σ : State rT) (α : Loc) (N : Int) (bs : List (TapeIdx N))
    (ε₂ : TapeIdx N → ENNReal) :
    presampleAdvCompX₂ σ α N bs ε₂ = fun σ' => ∑' n : TapeIdx N,
      ({presampleUpdate σ α N bs n} : Set (State rT)).indicator (fun _ => ε₂ n) σ' := by
  funext σ'
  unfold presampleAdvCompX₂
  by_cases h : ∃ n : TapeIdx N, σ' = presampleUpdate σ α N bs n
  · rw [dite_eq_left h, tsum_eq_single (Classical.choose h) ?_,
      Set.indicator_of_mem (Set.mem_singleton_iff.mpr (Classical.choose_spec h))]
    intro n hn
    refine Set.indicator_of_notMem (fun hmem => hn ?_) _
    exact (presample_choose_eq h (Set.mem_singleton_iff.mp hmem)).symm
  · rw [dite_eq_right h]
    refine (ENNReal.tsum_eq_zero.mpr fun n => ?_).symm
    exact Set.indicator_of_notMem (fun hmem => h ⟨n, Set.mem_singleton_iff.mp hmem⟩) _

open Classical in
@[simp] theorem presampleAdvCompX₂_update (σ : State rT) (α : Loc) (N : Int)
    (bs : List (TapeIdx N)) (ε₂ : TapeIdx N → ENNReal) (n : TapeIdx N) :
    presampleAdvCompX₂ σ α N bs ε₂ (presampleUpdate σ α N bs n) = ε₂ n := by
  unfold presampleAdvCompX₂
  rw [dite_eq_left ⟨n, rfl⟩]
  exact congrArg ε₂ (presample_choose_eq _ rfl)

theorem presampleAdvCompX₂_le_one {σ : State rT} {α : Loc} {N : Int} {bs : List (TapeIdx N)}
    {ε₂ : TapeIdx N → ENNReal} (Hbd : ∀ n, ε₂ n ≤ 1) (σ' : State rT) :
    presampleAdvCompX₂ σ α N bs ε₂ σ' ≤ 1 := by
  unfold presampleAdvCompX₂; split
  exacts [Hbd _, zero_le]

variable [LawfulProbLangℝ rT]

/-- The presample support is a countable set of tape-updated states, hence measurable. -/
theorem measurableSet_presample_support {σ₁ : State rT} {α : Loc} {N : Int}
    {bs : List (TapeIdx N)} :
    MeasurableSet {σ' : State rT | ∃ n : TapeIdx N, σ' = presampleUpdate σ₁ α N bs n} := by
  apply Set.Countable.measurableSet
  apply Set.Countable.mono (s₂ := presampleUpdate σ₁ α N bs '' Set.univ)
  · rintro σ' ⟨n, rfl⟩; exact ⟨n, trivial, rfl⟩
  · exact Set.countable_univ.image _

theorem measurable_presampleAdvCompX₂ (σ : State rT) (α : Loc) (N : Int)
    (bs : List (TapeIdx N)) (ε₂ : TapeIdx N → ENNReal) :
    Measurable (presampleAdvCompX₂ σ α N bs ε₂) := by
  rw [presampleAdvCompX₂_eq_tsum]
  exact Measurable.tsum fun n => measurable_const.indicator (measurableSet_singleton _)

/-- The integral reduces to the `Ico`-average of `ε₂` via
`tapePresample → tapeIndexUniform → Cfg.uniform → indicator-sum → (∑ ε₂)/N`. -/
theorem presampleAdvCompX₂_lintegral_le {σ₁ : State rT} {α : Loc} {N : Int}
    {bs : List (TapeIdx N)} {ε₂ : TapeIdx N → ENNReal} {ε₁ : ENNReal}
    (hlookup : σ₁.tapes[α]? = some ⟨N, bs⟩) (hN : 0 < N)
    (HSum : (∑ n ∈ tapeIdxFinset N, ε₂ n) / N.toNat ≤ ε₁) :
    ∫⁻ σ', presampleAdvCompX₂ σ₁ α N bs ε₂ σ' ∂(tapePresample σ₁ α) ≤ ε₁ := by
  classical
  set F : Int → ℝ≥0∞ := fun z => if hz : 0 ≤ z ∧ z < N then ε₂ ⟨z, hz⟩ else 0 with hF
  have hCard : (Finset.Ico (0:Int) N).card = N.toNat := by rw [Int.card_Ico, sub_zero]
  have hSumImage : (∑ n ∈ tapeIdxFinset N, ε₂ n) = ∑ z ∈ Finset.Ico (0:Int) N, F z := by
    rw [tapeIdxFinset, Finset.sum_image fun x _ y _ hxy =>
          Subtype.ext (by simpa using congrArg Subtype.val hxy),
        ← Finset.sum_attach (Finset.Ico (0:Int) N) F]
    exact Finset.sum_congr rfl fun a _ => by simp only [hF, dite_eq_left (Finset.mem_Ico.mp a.2)]
  calc ∫⁻ σ', presampleAdvCompX₂ σ₁ α N bs ε₂ σ' ∂(tapePresample σ₁ α)
      = ∫⁻ n : TapeIdx N, ε₂ n ∂tapeIndexUniform N := by
        rw [tapePresample_lintegral hlookup _ (measurable_presampleAdvCompX₂ σ₁ α N bs ε₂)]
        simp_rw [presampleAdvCompX₂_update]
    _ = ∑ z ∈ Finset.Ico (0:Int) N, F z / (N.toNat : ℝ≥0∞) := by
        have hf_eq : ∀ n : TapeIdx N,
            ε₂ n = (fun ρ : Cfg rT => match ρ.expr with | .lit (.int m) => F m | _ => 0)
              ⟨.lit (.int (↑n)), σ₁⟩ := fun n => by rw [hF]; simp only [dite_eq_left n.2]
        have hIndic : (fun z : Int => (match (⟨.lit (.int z), σ₁⟩ : Cfg rT).expr with
              | .lit (.int m) => F m | _ => 0))
            = ((Finset.Ico (0:Int) N) : Set Int).indicator F := by
          funext z
          by_cases hz : z ∈ Finset.Ico (0:Int) N
          · rw [Set.indicator_of_mem hz]
          · rw [Set.indicator_of_notMem hz]
            show F z = 0
            simp only [hF]
            exact dite_eq_right fun h => hz (Finset.mem_Ico.mpr h)
        simp_rw [hf_eq]
        rw [tapeIndexUniform_lintegral_eq_cfg_uniform hN σ₁
              (fun ρ => match ρ.expr with | .lit (.int m) => F m | _ => 0)
              ((measurable_litInt_elim F).comp Cfg.measurable_expr),
            Cfg.uniform_eq_map_uniformOfFinset hN σ₁, MeasureTheory.lintegral_map
              (f := fun ρ : Cfg rT => match ρ.expr with | .lit (.int m) => F m | _ => 0)
              ((measurable_litInt_elim F).comp Cfg.measurable_expr) .of_discrete,
            hIndic, MeasureTheory.lintegral_indicator ((Finset.Ico (0:Int) N).measurableSet),
            MeasureTheory.lintegral_finset]
        refine Finset.sum_congr rfl fun z hz => ?_
        rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton z),
            PMF.uniformOfFinset_apply, ite_eq_left hz, hCard, ENNReal.div_eq_inv_mul, mul_comm]
    _ = (∑ z ∈ Finset.Ico (0:Int) N, F z) / (N.toNat : ℝ≥0∞) := by
        simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]
    _ ≤ ε₁ := by rw [← hSumImage]; exact HSum

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]

/-- **Advanced-composition presample rule**: presample tape `α` of positive bound, spending
per-outcome credit `↯(ε₂ n)` whose `Ico`-average is `≤ ε₁`. -/
theorem twp_presample_adv_comp {E : CoPset} {e : Exp rT} {α : Loc}
    {Φ : Val rT → IProp GF} {t : Tape} (hN : 0 < t.bound)
    {ε₁ : ENNReal} {ε₂ : TapeIdx t.bound → ENNReal}
    (Hbd : ∀ n, ε₂ n ≤ 1)
    (HSum : (∑ n ∈ tapeIdxFinset t.bound, ε₂ n) / t.bound.toNat ≤ ε₁)
    (hv : e.toVal? = none) :
    iprop(↯ε₁ ∗ α ↪ₐ t ∗
      (∀ (n : TapeIdx t.bound),
        ↯(ε₂ n) ∗
        α ↪ₐ ⟨t.bound, t.presamples ++ [n]⟩ -∗ tglWp E e Φ))
      ⊢@{IProp GF} tglWp E e Φ := by
  iintro ⟨Herr, Htape, Hcont⟩
  iapply twp_lift_step_fupd_glm hv
  iintro %σ₁ %ε_now ⟨Hσ, Hε_now⟩
  ihave %hlookup := app_state_lookup_tape $$ Hσ Htape
  obtain ⟨N, bs⟩ := t
  ihave ⟨Hε_now, Herr, %hLe⟩ := errInterp_supply_bound $$ [$Hε_now $Herr]
  imod (BIFUpdate.subset Std.LawfulSet.empty_subset) with Hclose
  imodintro
  have hErase := ErasableExpr.tapePresample hlookup hN
  have hMeas : MeasurableSet
      {σ' : State rT | ∃ n : TapeIdx N, σ' = presampleUpdate σ₁ α N bs n} :=
    measurableSet_presample_support
  have hBnd : ∀ σ' : State rT,
      (ε_now - ε₁) + presampleAdvCompX₂ σ₁ α N bs ε₂ σ' ≤ (ε_now - ε₁) + 1 :=
    fun σ' => add_le_add_right (presampleAdvCompX₂_le_one Hbd σ') _
  have hInt : (0 : ℝ≥0∞) +
      ∫⁻ σ', ((ε_now - ε₁) + presampleAdvCompX₂ σ₁ α N bs ε₂ σ') ∂(tapePresample σ₁ α)
        ≤ ε_now := by
    have : MeasureTheory.IsProbabilityMeasure (tapePresample σ₁ α) :=
      ⟨tapePresample_univ_eq_one hlookup hN⟩
    rw [zero_add, MeasureTheory.lintegral_add_left measurable_const,
        MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]
    calc (ε_now - ε₁) + ∫⁻ σ', presampleAdvCompX₂ σ₁ α N bs ε₂ σ' ∂(tapePresample σ₁ α)
        ≤ (ε_now - ε₁) + ε₁ := by gcongr; exact presampleAdvCompX₂_lintegral_le hlookup hN HSum
      _ = ε_now := tsub_add_cancel_of_le hLe
  have hPgl : Pgl 0 (fun σ' : State rT => ∃ n : TapeIdx N, σ' = presampleUpdate σ₁ α N bs n)
      (tapePresample σ₁ α) :=
    le_of_eq (MeasureTheory.ae_iff.mp
      (tapePresample_ae hlookup hMeas fun n => ⟨n, rfl⟩))
  iapply glm'_erasable_step
  iexists (tapePresample σ₁ α),
    (fun σ' => ∃ n : TapeIdx N, σ' = presampleUpdate σ₁ α N bs n),
    0, (fun σ' => (ε_now - ε₁) + presampleAdvCompX₂ σ₁ α N bs ε₂ σ'),
    ((ε_now - ε₁) + 1)
  iframe %hErase %hMeas %hBnd %hInt %hPgl
  iintro %σ' %⟨n, rfl⟩
  simp only [presampleAdvCompX₂_update]
  imod Hclose with -
  imod (app_state_update_tape (s := ⟨N, bs ++ [n]⟩)) $$ Hσ Htape with ⟨Hσ', Htape'⟩
  ihave >Hε_rem := errInterp_supply_decrease $$ [$Hε_now $Herr]
  by_cases hlt : ε_now - ε₁ + ε₂ n < 1
  · imod errInterp_supply_increase hlt $$ Hε_rem with ⟨Hε_new, Hε₂_cr⟩
    ihave Hwp := Hcont $$ %n [$Hε₂_cr $Htape']
    isimp only [tglWp_unfold_step hv] at Hwp
    imod Hwp $$ %_ %(ε_now - ε₁ + ε₂ n) [$Hσ' $Hε_new] with HGlm
    imodintro
    iapply execStutter_free
    simp only [presampleUpdate, Std.ExtTreeMap.insert_eq_PartialMap_insert]
    iexact HGlm
  · push Not at hlt
    imod (BIFUpdate.subset Std.LawfulSet.empty_subset) with -
    imodintro
    iapply execStutter_spend hlt

/-- Basic total presample rule: append a freshly sampled `n` to tape `α`, spending no credit.
The `ε₂ := 0` instance of `twp_presample_adv_comp`. -/
theorem twp_presample {E : CoPset} {e : Exp rT} {α : Loc} {Φ : Val rT → IProp GF}
    {t : Tape} (hN : 0 < t.bound) (hv : e.toVal? = none) :
    iprop(α ↪ₐ t ∗
      (∀ (n : TapeIdx t.bound),
        α ↪ₐ ⟨t.bound, t.presamples ++ [n]⟩ -∗ tglWp E e Φ))
      ⊢@{IProp GF} tglWp E e Φ := by
  iintro ⟨Htape, Hcont⟩
  iapply fupd_tglWp
  imod ErrorCredit.zero with Herr
  imodintro
  iapply (twp_presample_adv_comp hN (fun _ => zero_le) (by simp) hv)
  iframe
  iintro %n ⟨-, Htape'⟩
  iapply Hcont $$ %n Htape'

end TotalEris
end ProbLang
