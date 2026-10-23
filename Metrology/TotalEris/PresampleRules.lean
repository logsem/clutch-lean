module

public import Metrology.TotalEris.TotalPrimitiveLaws
public import Metrology.TotalEris.TotalLifting
public import Metrology.TotalEris.Glm
public import Metrology.TotalEris.ErrorRules
import Metrology.Iris.LocalBI

@[expose] public section

/-! # Presample rules -/

open Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal
open Finset

namespace ProbLang
namespace TotalEris

variable {rT : Type _}

/-- Indices `z` of a tape of size `N`, with `0 ≤ z < N`. -/
abbrev TapeIdx (N : Int) := { z : Int // 0 ≤ z ∧ z < N }

/-- The finite set of all indices of a tape of size `N`. -/
noncomputable def tapeIdxFinset (N : Int) : Finset (TapeIdx N) :=
  (Ico 0 N).attach.image fun z => ⟨z.1, mem_Ico.mp z.2⟩

section presample
variable (σ : State rT) (α : Loc) (N : Int) (bs : List (TapeIdx N))

/-- The state obtained by writing tape index `n` onto the tape at `α`. -/
abbrev presampleUpdate (n : TapeIdx N) : State rT :=
  σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)

variable {σ α N bs}

/-- Distinct samples append distinct tape suffixes, so the presample state-update is injective. -/
theorem presample_update_injective :
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

/-- The chosen preimage of a presampled state is the presampling index. -/
theorem presample_choose_eq {σ' : State rT} {n : TapeIdx N}
    (h : ∃ m : TapeIdx N, σ' = presampleUpdate σ α N bs m)
    (hn : σ' = presampleUpdate σ α N bs n) : Classical.choose h = n :=
  presample_update_injective ((Classical.choose_spec h).symm.trans hn)

variable (σ α N bs)
variable (ε₂ : TapeIdx N → ENNReal)

open Classical in
/-- Per-outcome credit for advanced composition: `ε₂ n` on the `n`-update, `0` off-support. -/
noncomputable def presampleAdvCompX₂ (σ' : State rT) : ENNReal :=
  if h : ∃ n : TapeIdx N, σ' = presampleUpdate σ α N bs n then ε₂ (choose h) else 0

open Classical in
/-- `presampleAdvCompX₂` is a countable sum of singleton indicators, one per sample. -/
theorem presampleAdvCompX₂_eq_tsum :
    presampleAdvCompX₂ σ α N bs ε₂ = fun σ' => ∑' n : TapeIdx N,
      ({presampleUpdate σ α N bs n} : Set (State rT)).indicator (fun _ => ε₂ n) σ' := by
  funext σ'
  unfold presampleAdvCompX₂
  by_cases h : ∃ n : TapeIdx N, σ' = presampleUpdate σ α N bs n
  · rw [dite_eq_left h, tsum_eq_single (choose h) ?_,
      Set.indicator_of_mem (Set.mem_singleton_iff.mpr (choose_spec h))]
    intro n hn
    refine Set.indicator_of_notMem (fun hmem => hn ?_) _
    exact (presample_choose_eq h (Set.mem_singleton_iff.mp hmem)).symm
  · rw [dite_eq_right h]
    refine (ENNReal.tsum_eq_zero.mpr fun n => ?_).symm
    exact Set.indicator_of_notMem (fun hmem => h ⟨n, Set.mem_singleton_iff.mp hmem⟩) _

open Classical in
/-- `presampleAdvCompX₂` evaluates to `ε₂ n` on the state updated at `n`. -/
@[simp] theorem presampleAdvCompX₂_update (n : TapeIdx N) :
    presampleAdvCompX₂ σ α N bs ε₂ (presampleUpdate σ α N bs n) = ε₂ n := by
  unfold presampleAdvCompX₂
  rw [dite_eq_left ⟨n, rfl⟩]
  exact congrArg ε₂ (presample_choose_eq _ rfl)

end presample

variable [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {α : Loc} {N : Int}

/-- The presample support is a countable set of tape-updated states, hence measurable. -/
theorem measurableSet_presample_support {σ₁ : State rT}
    {bs : List (TapeIdx N)} :
    MeasurableSet {σ' : State rT | ∃ n : TapeIdx N, σ' = presampleUpdate σ₁ α N bs n} := by
  apply Set.Countable.measurableSet
  apply Set.Countable.mono (s₂ := presampleUpdate σ₁ α N bs '' Set.univ)
  · rintro σ' ⟨n, rfl⟩; exact ⟨n, trivial, rfl⟩
  · exact Set.countable_univ.image _

/-- `presampleAdvCompX₂` is measurable. -/
theorem measurable_presampleAdvCompX₂ (σ : State rT) (α : Loc) (N : Int)
    (bs : List (TapeIdx N)) (ε₂ : TapeIdx N → ENNReal) :
    Measurable (presampleAdvCompX₂ σ α N bs ε₂) := by
  rw [presampleAdvCompX₂_eq_tsum]
  exact Measurable.tsum fun n => measurable_const.indicator (measurableSet_singleton _)

/-- The integral reduces to the `Ico`-average of `ε₂` via
`tapePresample → tapeIndexUniform → Cfg.uniform → indicator-sum → (∑ ε₂)/N`. -/
theorem presampleAdvCompX₂_lintegral_le {σ₁ : State rT}
    {bs : List (TapeIdx N)} {ε₂ : TapeIdx N → ENNReal} {ε₁ : ENNReal}
    (hlookup : σ₁.tapes[α]? = some ⟨N, bs⟩) (hN : 0 < N)
    (HSum : (∑ n ∈ tapeIdxFinset N, ε₂ n) / N.toNat ≤ ε₁) :
    ∫⁻ σ', presampleAdvCompX₂ σ₁ α N bs ε₂ σ' ∂(tapePresample σ₁ α) ≤ ε₁ := by
  classical
  set F : Int → ℝ≥0∞ := fun z => if hz : 0 ≤ z ∧ z < N then ε₂ ⟨z, hz⟩ else 0 with hF
  have hCard : (Ico (0:Int) N).card = N.toNat := by rw [Int.card_Ico, sub_zero]
  have hSumImage : (∑ n ∈ tapeIdxFinset N, ε₂ n) = ∑ z ∈ Ico (0:Int) N, F z := by
    rw [tapeIdxFinset, sum_image fun x _ y _ hxy =>
          Subtype.ext (by simpa using congrArg Subtype.val hxy),
        ← sum_attach (Ico (0:Int) N) F]
    exact sum_congr rfl fun a _ => by simp only [hF, dite_eq_left (mem_Ico.mp a.2)]
  calc ∫⁻ σ', presampleAdvCompX₂ σ₁ α N bs ε₂ σ' ∂(tapePresample σ₁ α) =
      ∫⁻ n : TapeIdx N, ε₂ n ∂tapeIndexUniform N := by
        rw [tapePresample_lintegral hlookup _ (measurable_presampleAdvCompX₂ σ₁ α N bs ε₂)]
        simp_rw [presampleAdvCompX₂_update]
    _ = ∑ z ∈ Ico (0:Int) N, F z / (N.toNat : ℝ≥0∞) := by
        have hf_eq : ∀ n : TapeIdx N,
            ε₂ n = (fun ρ : Cfg rT => match ρ.expr with | .lit (.int m) => F m | _ => 0)
              ⟨.lit (.int (↑n)), σ₁⟩ := fun n => by rw [hF]; simp only [dite_eq_left n.2]
        have hIndic : (fun z : Int => (match (⟨.lit (.int z), σ₁⟩ : Cfg rT).expr with
              | .lit (.int m) => F m | _ => 0)) =
            ((Ico (0:Int) N) : Set Int).indicator F := by
          funext z
          by_cases hz : z ∈ Ico (0:Int) N
          · rw [Set.indicator_of_mem hz]
          · rw [Set.indicator_of_notMem hz]
            show F z = 0
            simp only [hF]
            exact dite_eq_right fun h => hz (mem_Ico.mpr h)
        simp_rw [hf_eq]
        rw [tapeIndexUniform_lintegral_eq_cfg_uniform hN σ₁
              (fun ρ => match ρ.expr with | .lit (.int m) => F m | _ => 0)
              ((measurable_litInt_elim F).comp Cfg.measurable_expr),
            Cfg.uniform_eq_map_uniformOfFinset hN σ₁, MeasureTheory.lintegral_map
              (f := fun ρ : Cfg rT => match ρ.expr with | .lit (.int m) => F m | _ => 0)
              ((measurable_litInt_elim F).comp Cfg.measurable_expr) .of_discrete,
            hIndic, MeasureTheory.lintegral_indicator ((Ico (0:Int) N).measurableSet),
            MeasureTheory.lintegral_finset]
        refine sum_congr rfl fun z hz => ?_
        rw [MeasureTheory.Measure.uniformOfFinset_apply_singleton, ite_eq_left hz, hCard,
            ENNReal.div_eq_inv_mul, mul_comm]
    _ = (∑ z ∈ Ico (0:Int) N, F z) / (N.toNat : ℝ≥0∞) := by
        simp_rw [div_eq_mul_inv]; rw [← sum_mul]
    _ ≤ ε₁ := by rw [← hSumImage]; exact HSum

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi IProp GF

/-- **Advanced-composition presample rule**: presample tape `α` of positive bound, spending
per-outcome credit `↯(ε₂ n)` whose `Ico`-average is `≤ ε₁`. -/
theorem twp_presample_adv_comp {E : CoPset} {e : Exp rT}
    {Φ : Val rT → IProp GF} {t : Tape} (hN : 0 < t.bound)
    {ε₁ : ENNReal} {ε₂ : TapeIdx t.bound → ENNReal}
    (HSum : (∑ n ∈ tapeIdxFinset t.bound, ε₂ n) / t.bound.toNat ≤ ε₁)
    (hv : e.toVal? = none) :
    iprop(↯ε₁ ∗ α ↪ₐ t ∗
      (∀ (n : TapeIdx t.bound),
        ↯(ε₂ n) ∗
        α ↪ₐ ⟨t.bound, t.presamples ++ [n]⟩ -∗ tglWp E e Φ))
      ⊢ tglWp E e Φ := by
  iintro ⟨Herr, Htape, Hcont⟩
  iapply twp_lift_step_fupd_glm hv
  iintro %σ₁ %ε_now ⟨Hσ, Hε_now⟩
  ihave %hlookup := app_state_lookup_tape $$ Hσ Htape
  obtain ⟨N, bs⟩ := t
  ihave ⟨Hε_now, Herr, %hLe⟩ := errInterp_supply_bound $$ [$Hε_now $Herr]
  imod (BIFUpdate.subset Std.LawfulSet.empty_subset) with Hclose
  imodintro
  have hErase := ErasableExpr.tapePresample hlookup hN
  have hMeas : MeasurableSet {σ' : State rT | ∃ n : TapeIdx N, σ' = presampleUpdate σ₁ α N bs n} :=
    measurableSet_presample_support
  have hInt : (0 : ℝ≥0∞) +
      ∫⁻ σ', ((ε_now - ε₁) + presampleAdvCompX₂ σ₁ α N bs ε₂ σ') ∂(tapePresample σ₁ α) ≤ ε_now := by
    have : MeasureTheory.IsProbabilityMeasure (tapePresample σ₁ α) :=
      ⟨tapePresample_univ_eq_one hlookup hN⟩
    rw [zero_add, MeasureTheory.lintegral_add_left measurable_const,
        MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]
    calc (ε_now - ε₁) + ∫⁻ σ', presampleAdvCompX₂ σ₁ α N bs ε₂ σ' ∂(tapePresample σ₁ α) ≤
        (ε_now - ε₁) + ε₁ := by gcongr; exact presampleAdvCompX₂_lintegral_le hlookup hN HSum
      _ = ε_now := tsub_add_cancel_of_le hLe
  have hPgl : Pgl 0 (fun σ' : State rT => ∃ n : TapeIdx N, σ' = presampleUpdate σ₁ α N bs n)
      (tapePresample σ₁ α) :=
    le_of_eq (MeasureTheory.ae_iff.mp (tapePresample_ae hlookup hMeas fun n => ⟨n, rfl⟩))
  iapply glm'_erasable_step
  iexists (tapePresample σ₁ α),
    (fun σ' => ∃ n : TapeIdx N, σ' = presampleUpdate σ₁ α N bs n),
    0, (fun σ' => (ε_now - ε₁) + presampleAdvCompX₂ σ₁ α N bs ε₂ σ')
  iframe %hErase %hMeas %hInt %hPgl
  iintro %σ' %⟨n, rfl⟩
  simp only [presampleAdvCompX₂_update]
  imod Hclose with -
  imod app_state_update_tape $$ Hσ Htape with ⟨Hσ', Htape'⟩
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

/-- Basic total presample rule: append a freshly sampled `n` to tape `α`, spending no credit; it is
the `ε₂ := 0` instance of `twp_presample_adv_comp`. -/
theorem twp_presample {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    {t : Tape} (hN : 0 < t.bound) (hv : e.toVal? = none) :
    iprop(α ↪ₐ t ∗
      (∀ (n : TapeIdx t.bound),
        α ↪ₐ ⟨t.bound, t.presamples ++ [n]⟩ -∗ tglWp E e Φ))
      ⊢ tglWp E e Φ := by
  iintro ⟨Htape, Hcont⟩
  iapply fupd_tglWp
  imod ErrorCredit.zero with Herr
  imodintro
  iapply (twp_presample_adv_comp (ε₂ := fun _ => 0) hN (by simp) hv)
  iframe
  iintro %n ⟨-, Htape'⟩
  iapply Hcont $$ %n Htape'

end TotalEris
end ProbLang
