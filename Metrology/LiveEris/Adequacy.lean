module

public import Metrology.LiveEris.CreditRules
public import Metrology.Iris.StepFupd

@[expose] public section

/-!
# LiveEris adequacy

`progressBound D φ m ρ` is the probability that the run from `ρ` terminates with a value
satisfying `φ`, or steps into a `D`-state `m` times, without getting stuck first. A LiveEris proof
with credits `c` bounds it from below by `1 - c i` for each coordinate `i` whose checkpoints are
`D`-steps or excused:

* the error coordinate with `D` = every state: the run neither fails nor gets stuck within any
  number of steps, except with probability `ε`;
* the total coordinate with `D` = the progress states: the run terminates well or makes `m` progress
  steps, except with probability `ε + δ`, for every `m`.
-/

open Iris Iris.Std Iris.BI Iris.ProofMode OFE ProbLang ProbLang.LiveEris.LiveWpGS
  ProbLang.LiveEris.CreditVec
open scoped AppGS ENNReal

namespace ProbLang
namespace LiveEris

variable {rT : Type _} [LawfulProbLangℝ rT]

/-! ## The semantic bound -/

theorem measurableEmbedding_ofVal :
    MeasurableEmbedding (Exp.ofVal : Val rT → Exp rT) := by
  refine ⟨fun a b h => Val.ext h, Exp.ofVal.measurable, fun s hs => ?_⟩
  obtain ⟨U, hU, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have hrange : Set.range (Val.fst : Val rT → Exp rT) = {e : Exp rT | e.isValue} := by
    ext e
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨v, rfl⟩; exact Val.isValue v
    · intro h; exact ⟨Val.mk e h.some h.some.lc, rfl⟩
  show MeasurableSet (Val.fst '' (Val.fst ⁻¹' U))
  rw [Set.image_preimage_eq_inter_range, hrange]
  have hsplit : {e : Exp rT | e.isValue} = {e | e.isValueR} ∩ {e | Exp.lcb 0 e = true} := by
    ext e; simp [Exp.isValue_iff_isValueR, Set.mem_inter_iff]
  rw [hsplit]
  exact hU.inter (Exp.isValueR.measurable.setOf.inter Exp.lcb_zero.measurableSet)

/-- Configurations that are values satisfying `φ`. -/
def goodVal (φ : Val rT → Prop) : Set (Cfg rT) := {ρ | ∃ v, ρ.expr = Exp.ofVal v ∧ φ v}

theorem measurableSet_goodVal {φ : Val rT → Prop} (hφ : MeasurableSet {v : Val rT | φ v}) :
    MeasurableSet (goodVal φ) := by
  have heq : {e : Exp rT | ∃ v, e = Exp.ofVal v ∧ φ v} = Exp.ofVal '' {v | φ v} := by
    ext e; simp only [Set.mem_ofPred_eq, Set.mem_image]
    exact ⟨fun ⟨v, he, hv⟩ => ⟨v, hv, he.symm⟩, fun ⟨v, hv, he⟩ => ⟨v, he.symm, hv⟩⟩
  have hexp : MeasurableSet {e : Exp rT | ∃ v, e = Exp.ofVal v ∧ φ v} := by
    rw [heq]; exact measurableEmbedding_ofVal.measurableSet_image' hφ
  exact hexp.preimage Cfg.measurable_expr

open Classical in
/-- The `n`-step approximation of `progressBound`, with `m` `D`-steps left to make. -/
noncomputable def progressGood (D : State rT → Prop) (φ : Val rT → Prop) :
    ℕ → ℕ → Cfg rT → ℝ≥0∞
  | 0, _, _ => 0
  | _ + 1, 0, _ => 1
  | n + 1, m + 1, ρ =>
    if ρ.expr.isValue then (goodVal φ).indicator 1 ρ
    else ∫⁻ ρ', progressGood D φ n (if D ρ'.state then m else m + 1) ρ' ∂primStep ρ

/-- The probability of terminating with `φ` or making `m` `D`-steps, without getting stuck. -/
noncomputable def progressBound (D : State rT → Prop) (φ : Val rT → Prop) (m : ℕ)
    (ρ : Cfg rT) : ℝ≥0∞ :=
  ⨆ n, progressGood D φ n m ρ

variable {D : State rT → Prop} {φ : Val rT → Prop}

open Classical in
theorem measurable_counter (hD : MeasurableSet {σ : State rT | D σ}) {F : ℕ → Cfg rT → ℝ≥0∞}
    (hF : ∀ m, Measurable (F m)) (m : ℕ) :
    Measurable fun ρ' : Cfg rT => F (if D ρ'.state then m else m + 1) ρ' := by
  have hfun : (fun ρ' : Cfg rT => F (if D ρ'.state then m else m + 1) ρ') =
      fun ρ' => if D ρ'.state then F m ρ' else F (m + 1) ρ' := by
    funext ρ'; split <;> rfl
  rw [hfun]
  exact Measurable.ite (hD.preimage Cfg.measurable_state) (hF m) (hF (m + 1))

open Classical in
theorem progressGood_measurable (hD : MeasurableSet {σ : State rT | D σ})
    (hφ : MeasurableSet {v : Val rT | φ v}) :
    ∀ n m, Measurable (progressGood (rT := rT) D φ n m)
  | 0, _ => measurable_const
  | _ + 1, 0 => measurable_const
  | n + 1, m + 1 => by
    have hg : Measurable fun ρ' : Cfg rT =>
        progressGood D φ n (if D ρ'.state then m else m + 1) ρ' :=
      measurable_counter hD (progressGood_measurable hD hφ n) m
    show Measurable fun ρ => if ρ.expr.isValue then (goodVal φ).indicator 1 ρ
      else ∫⁻ ρ', progressGood D φ n (if D ρ'.state then m else m + 1) ρ' ∂primStep ρ
    exact Measurable.ite (by measurability)
      (measurable_one.indicator (measurableSet_goodVal hφ))
      ((MeasureTheory.Measure.measurable_lintegral hg).comp primStep.measurable)

open Classical in
theorem progressGood_mono_fuel : ∀ n m (ρ : Cfg rT),
    progressGood D φ n m ρ ≤ progressGood D φ (n + 1) m ρ
  | 0, _, _ => zero_le
  | _ + 1, 0, _ => le_rfl
  | n + 1, m + 1, ρ => by
    show (if ρ.expr.isValue then (goodVal φ).indicator 1 ρ
        else ∫⁻ ρ', progressGood D φ n (if D ρ'.state then m else m + 1) ρ' ∂primStep ρ) ≤
      (if ρ.expr.isValue then (goodVal φ).indicator 1 ρ
        else ∫⁻ ρ', progressGood D φ (n + 1) (if D ρ'.state then m else m + 1) ρ' ∂primStep ρ)
    split
    · exact le_rfl
    · exact MeasureTheory.lintegral_mono fun ρ' => progressGood_mono_fuel n _ ρ'

theorem progressGood_monotone (m : ℕ) (ρ : Cfg rT) :
    Monotone fun n => progressGood D φ n m ρ :=
  monotone_nat_of_le_succ fun n => progressGood_mono_fuel n m ρ

theorem progressBound_measurable (hD : MeasurableSet {σ : State rT | D σ})
    (hφ : MeasurableSet {v : Val rT | φ v}) (m : ℕ) :
    Measurable (progressBound (rT := rT) D φ m) :=
  Measurable.iSup fun n => progressGood_measurable hD hφ n m

theorem progressBound_zero (ρ : Cfg rT) : progressBound D φ 0 ρ = 1 :=
  le_antisymm (iSup_le fun n => by cases n <;> simp [progressGood])
    (le_iSup_of_le 1 le_rfl)

theorem progressBound_val {m : ℕ} {v : Val rT} {σ : State rT} (hv : φ v) :
    1 ≤ progressBound D φ m ⟨Exp.ofVal v, σ⟩ := by
  cases m with
  | zero => exact (progressBound_zero _).ge
  | succ m =>
    refine le_iSup_of_le 1 ?_
    have hval : (Exp.ofVal v).isValue := Val.isValue v
    have hgood : (⟨Exp.ofVal v, σ⟩ : Cfg rT) ∈ goodVal φ := ⟨v, rfl, hv⟩
    simp [progressGood, hval, hgood]

open Classical in
theorem progressBound_step (hD : MeasurableSet {σ : State rT | D σ})
    (hφ : MeasurableSet {v : Val rT | φ v}) {m : ℕ} {ρ : Cfg rT} (hv : ¬ ρ.expr.isValue) :
    ∫⁻ ρ', progressBound D φ (if D ρ'.state then m else m + 1) ρ' ∂primStep ρ ≤
      progressBound D φ (m + 1) ρ := by
  have hpt : ∀ ρ' : Cfg rT, progressBound D φ (if D ρ'.state then m else m + 1) ρ' =
      ⨆ n, progressGood D φ n (if D ρ'.state then m else m + 1) ρ' := fun _ => rfl
  simp_rw [hpt]
  rw [MeasureTheory.lintegral_iSup]
  · refine iSup_le fun n => le_iSup_of_le (n + 1) ?_
    show _ ≤ if ρ.expr.isValue then (goodVal φ).indicator 1 ρ
      else ∫⁻ ρ', progressGood D φ n (if D ρ'.state then m else m + 1) ρ' ∂primStep ρ
    split
    · contradiction
    · exact le_rfl
  · exact fun n => measurable_counter hD (progressGood_measurable hD hφ n) m
  · exact fun _ _ hn ρ' => progressGood_monotone _ ρ' hn

/-- One averaged step against a probability measure: if the mass outside `R` is at most `ε₁` and
each outcome in `R` has value at least `1 - ε₂`, the average value is at least
`1 - (ε₁ + ∫ ε₂)`. -/
theorem lift_prob {α : Type*} [MeasurableSpace α] {M : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure M] {ε ε₁ : ℝ≥0∞} {ε₂ : α → ℝ≥0∞} {R : α → Prop}
    {k : α → ℝ≥0∞} (hR : MeasurableSet {a | R a}) (hk : Measurable k) (hpgl : Pgl ε₁ R M)
    (Hsum : ε₁ + (∫⁻ a, ε₂ a ∂M) ≤ ε) (Hcont : ∀ a, R a → 1 - ε₂ a ≤ k a) :
    1 - ε ≤ ∫⁻ a, k a ∂M := by
  have hMR : 1 - ε₁ ≤ M {a | R a} := by
    rw [tsub_le_iff_left]
    calc 1 = M {a | R a} + M {a | ¬ R a} := (MeasureTheory.prob_add_prob_compl hR).symm
      _ ≤ M {a | R a} + ε₁ := add_le_add le_rfl hpgl
      _ = ε₁ + M {a | R a} := add_comm _ _
  have h_split : M {a | R a}
      ≤ (∫⁻ a in {a | R a}, k a ∂M) + (∫⁻ a in {a | R a}, ε₂ a ∂M) := by
    have hone : M {a | R a} = ∫⁻ _ in {a | R a}, (1 : ℝ≥0∞) ∂M := by
      rw [MeasureTheory.setLIntegral_const, one_mul]
    rw [← MeasureTheory.lintegral_add_left hk, hone]
    refine MeasureTheory.lintegral_mono_ae ((MeasureTheory.ae_restrict_iff' hR).mpr
      (.of_forall fun a ha => ?_))
    exact tsub_le_iff_right.mp (Hcont a ha)
  have h_total : 1 - ε₁ ≤ (∫⁻ a, k a ∂M) + (∫⁻ a, ε₂ a ∂M) :=
    calc 1 - ε₁ ≤ M {a | R a} := hMR
      _ ≤ (∫⁻ a in {a | R a}, k a ∂M) + (∫⁻ a in {a | R a}, ε₂ a ∂M) := h_split
      _ ≤ (∫⁻ a, k a ∂M) + (∫⁻ a, ε₂ a ∂M) :=
        add_le_add (MeasureTheory.setLIntegral_le_lintegral _ k)
          (MeasureTheory.setLIntegral_le_lintegral _ ε₂)
  calc 1 - ε ≤ 1 - (ε₁ + ∫⁻ a, ε₂ a ∂M) := tsub_le_tsub_left Hsum 1
    _ = 1 - ε₁ - (∫⁻ a, ε₂ a ∂M) := by rw [tsub_tsub]
    _ ≤ ∫⁻ a, k a ∂M := tsub_le_iff_right.mpr h_total

/-- The bound that a proof at step index `k` establishes, for coordinate `i`. -/
def AdeqBound (D : State rT → Prop) (φ : Val rT → Prop) (i : Coord) (k : ℕ) (ρ : Cfg rT)
    (c : Coord → ℝ≥0∞) : Prop :=
  ∀ m ≤ k, 1 - c i ≤ progressBound D φ m ρ

open Classical in
/-- The bound a step's outcome `ρ` must satisfy for its parent, whose counter is `m`. -/
def AdeqLeaf (D : State rT → Prop) (φ : Val rT → Prop) (i : Coord) (k : ℕ) (ρ : Cfg rT)
    (c : Coord → ℝ≥0∞) : Prop :=
  ∀ m, m + 1 ≤ k → 1 - c i ≤ progressBound D φ (if D ρ.state then m else m + 1) ρ

theorem AdeqBound.of_one_le {i : Coord} {k : ℕ} {ρ : Cfg rT} {c : Coord → ℝ≥0∞}
    (h : 1 ≤ c i) : AdeqBound D φ i k ρ c := fun _ _ => by simp [tsub_eq_zero_of_le h]

theorem AdeqLeaf.of_one_le {i : Coord} {k : ℕ} {ρ : Cfg rT} {c : Coord → ℝ≥0∞}
    (h : 1 ≤ c i) : AdeqLeaf D φ i k ρ c := fun _ _ => by simp [tsub_eq_zero_of_le h]

open Classical in
theorem AdeqBound.leaf {i : Coord} {k : ℕ} {ρ : Cfg rT} {c : Coord → ℝ≥0∞}
    (h : AdeqBound D φ i k ρ c) : AdeqLeaf D φ i k ρ c := fun m hm =>
  h _ (by split <;> omega)

theorem AdeqBound.of_bump {i : Coord} {k : ℕ} {ρ : Cfg rT} {c : Coord → ℝ≥0∞}
    (h : ∀ c', Bump c c' → AdeqBound D φ i k ρ c') : AdeqBound D φ i k ρ c := by
  intro m hm
  by_cases hci : c i = ∞
  · simp [hci]
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  have hb : Bump c (fun j => c j + η) :=
    ⟨fun j => le_self_add, fun j hj => ENNReal.lt_add_right hj.ne (by exact_mod_cast hη.ne')⟩
  calc 1 - c i ≤ 1 - (c i + η) + η := by
        rw [tsub_add_eq_tsub_tsub]
        exact le_tsub_add
    _ ≤ progressBound D φ m ρ + η := add_le_add (h _ hb m hm) le_rfl

open Classical in
theorem AdeqBound.of_primStep (hD : MeasurableSet {σ : State rT | D σ})
    (hφ : MeasurableSet {v : Val rT | φ v}) {i : Coord} {k : ℕ} {e : Exp rT} {σ : State rT}
    {c : Coord → ℝ≥0∞} {R : Cfg rT → Prop} {ε₁ : ℝ≥0∞} {X₂ : Cfg rT → Coord → ℝ≥0∞}
    (Hred : Reducible e σ) (hR : MeasurableSet {ρ | R ρ})
    (Hexp : charge ε₁ + expect (primStep ⟨e, σ⟩) X₂ ≤ c) (Hpgl : Pgl ε₁ R (primStep ⟨e, σ⟩))
    (Hleaf : ∀ ρ, R ρ → AdeqLeaf D φ i k ρ (X₂ ρ)) :
    AdeqBound D φ i k ⟨e, σ⟩ c := by
  intro m hm
  cases m with
  | zero => rw [progressBound_zero]; exact tsub_le_self
  | succ m =>
    have : MeasureTheory.IsProbabilityMeasure (primStep ⟨e, σ⟩) := prim_step_mass Hred
    have hk : Measurable fun ρ' : Cfg rT =>
        progressBound D φ (if D ρ'.state then m else m + 1) ρ' :=
      measurable_counter hD (progressBound_measurable hD hφ) m
    refine le_trans ?_ (progressBound_step hD hφ (val_stuck Hred))
    exact lift_prob (ε₂ := fun ρ => X₂ ρ i) hR hk Hpgl (Hexp i)
      (fun ρ hρ => Hleaf ρ hρ m hm)

/-! ## The Iris side -/

section Iris

variable {GF : BundledGFunctors} [LiveGS rT .hasNoLC GF] {Q : State rT → State rT → Prop}

theorem glm_adequacy (hD : MeasurableSet {σ : State rT | D σ})
    (hφ : MeasurableSet {v : Val rT | φ v}) (i : Coord) (k : ℕ) {e : Exp rT} {σ : State rT}
    {c : Coord → ℝ≥0∞} {Z : Cfg rT → (Coord → ℝ≥0∞) → IProp GF} :
    glm e σ c Z ⊢
      (∀ ρ c₂, Z ρ c₂ -∗ |={∅}=> |={∅}[∅]▷=>^[k] ⌜AdeqLeaf D φ i k ρ c₂⌝) -∗
        |={∅}=> |={∅}[∅]▷=>^[k] ⌜AdeqBound D φ i k ⟨e, σ⟩ c⌝ := by
  let Ψ : GlmState rT Coord → IProp GF := fun s => iprop(
    (∀ ρ c₂, Z ρ c₂ -∗ |={∅}=> |={∅}[∅]▷=>^[k] ⌜AdeqLeaf D φ i k ρ c₂⌝) -∗
      |={∅}=> |={∅}[∅]▷=>^[k] ⌜AdeqBound D φ i k s.1 s.2⌝)
  let : NonExpansive Ψ := nonExpansive_of_discrete_leibniz Ψ
  iintro HG
  iapply (glm_strong_ind (Z := Z) (Ψ := Ψ)) $$ [] %((⟨e, σ⟩, c) : GlmState rT Coord) HG
  iintro !> %s HPre HZ
  obtain ⟨ρ, c⟩ := s
  icases HPre with ⟨HOT | HPS⟩
  · iapply BIFUpdate.mono
    · refine step_fupdN_mono (P := iprop(∀ c', ⌜Bump c c'⌝ -∗
        ⌜AdeqBound D φ i k ρ c'⌝ : IProp GF)) ?_
      iintro %Hpure !%
      exact AdeqBound.of_bump Hpure
    iapply fupd_step_fupdN_plain_forall_1
    iintro %c'
    iapply BIFUpdate.mono (step_fupdN_pure_wand_intro ∅ k)
    iapply fupd_pure_wand_intro
    iintro %Hb
    imod HOT $$ %c' %Hb with HS
    icases HS with ⟨%Hsat | ⟨HΨ, -⟩⟩
    · iapply fupd_step_fupdN_pure k (AdeqBound.of_one_le (Hsat i))
    · iapply HΨ $$ HZ
  · icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %HRmeas, %_, %Hexp, %Hpgl, HCont⟩
    iapply BIFUpdate.mono
    · refine step_fupdN_mono (P := iprop(∀ ρ', ⌜R ρ'⌝ -∗
        ⌜AdeqLeaf D φ i k ρ' (X₂ ρ')⌝ : IProp GF)) ?_
      iintro %Hpure !%
      exact AdeqBound.of_primStep hD hφ Hred HRmeas Hexp Hpgl Hpure
    iapply fupd_step_fupdN_plain_forall_1
    iintro %ρ'
    iapply BIFUpdate.mono (step_fupdN_pure_wand_intro ∅ k)
    iapply fupd_pure_wand_intro
    iintro %HR
    imod HCont $$ %ρ' %HR with HS
    icases HS with ⟨%Hsat | HZρ⟩
    · iapply fupd_step_fupdN_pure k (AdeqLeaf.of_one_le (Hsat i))
    · iapply HZ $$ HZρ

theorem lwp_adequacy_body (hD : MeasurableSet {σ : State rT | D σ})
    (hφ : MeasurableSet {v : Val rT | φ v}) (i : Coord)
    (hck : ∀ σ σ' c, Checkpoint Q σ σ' c → D σ' ∨ 1 ≤ c i) (k : ℕ)
    (IH : ∀ k' < k, ∀ (e : Exp rT) (σ : State rT) (c : Coord → ℝ≥0∞),
      iprop(stateInterp σ ∗ creditInterp c ∗ lwp Q ⊤ e (fun v => iprop(⌜φ v⌝))) ⊢@{IProp GF}
        iprop(|={⊤,∅}=> |={∅}[∅]▷=>^[k'] ⌜AdeqBound D φ i k' ⟨e, σ⟩ c⌝))
    (e : Exp rT) (σ : State rT) (c : Coord → ℝ≥0∞) :
    iprop(stateInterp σ ∗ creditInterp c ∗ lwp Q ⊤ e (fun v => iprop(⌜φ v⌝))) ⊢@{IProp GF}
      iprop(|={⊤,∅}=> |={∅}[∅]▷=>^[k] ⌜AdeqBound D φ i k ⟨e, σ⟩ c⌝) := by
  let Ψ : Exp rT → IProp GF := fun e' => iprop(∀ σ' c', stateInterp σ' ∗ creditInterp c' -∗
    |={⊤,∅}=> |={∅}[∅]▷=>^[k] ⌜AdeqBound D φ i k ⟨e', σ'⟩ c'⌝)
  let : NonExpansive Ψ := nonExpansive_of_discrete_leibniz Ψ
  iintro ⟨Hσ, Hc, HW⟩
  ihave HΨ : iprop(Ψ e) $$ [HW]
  · iapply (lwp_ind (Q := Q) (E := ⊤) (Φ := fun v => iprop(⌜φ v⌝)) Ψ) $$ [] HW
    iintro !> %e' HF %σ' %c' Hσc
    ispecialize HF $$ %σ' %c' Hσc
    cases htv : e'.toVal? with
    | some v =>
      obtain rfl : e' = Exp.ofVal v := (Exp.ofVal_of_toVal_some htv).symm
      imod HF with ⟨-, -, %hφv⟩
      imod (BIFUpdate.subset (E1 := ⊤) (E2 := ∅) Std.LawfulSet.empty_subset) with -
      iapply fupd_step_fupdN_pure (p := AdeqBound D φ i k _ c') k
        fun _ _ => tsub_le_self.trans (progressBound_val hφv)
    | none =>
      imod HF with HG
      iapply glm_adequacy hD hφ i k $$ HG
      iintro %ρ %c₂ HC
      icases HC with ⟨HX | ⟨%Hck, HL⟩⟩
      · imod HX with ⟨Hσ'', Hc'', HΨρ⟩
        iapply BIFUpdate.mono (step_fupdN_mono (pure_mono AdeqBound.leaf))
        iapply HΨρ $$ %ρ.state %c₂ [$Hσ'' $Hc'']
      · cases k with
        | zero => iapply fupd_step_fupdN_pure (p := AdeqLeaf D φ i 0 ρ c₂) 0 fun _ _ => by omega
        | succ k' =>
          rcases hck _ _ _ Hck with hDρ | h1
          · imodintro
            simp only [Nat.repeat]
            iintro !> !>
            imod HL with ⟨Hσ'', Hc'', HW'⟩
            iapply BIFUpdate.mono (step_fupdN_mono (pure_mono ?_))
            · exact fun (hb : AdeqBound D φ i k' ⟨ρ.expr, ρ.state⟩ c₂) m hm => by
                simpa [AdeqLeaf, hDρ] using hb m (by omega)
            iapply IH k' (Nat.lt_succ_self k') ρ.expr ρ.state c₂
            iframe
          · iapply fupd_step_fupdN_pure (k' + 1) (AdeqLeaf.of_one_le h1)
  iapply HΨ $$ %σ %c [$Hσ $Hc]

theorem lwp_adequacy_core (hD : MeasurableSet {σ : State rT | D σ})
    (hφ : MeasurableSet {v : Val rT | φ v}) (i : Coord)
    (hck : ∀ σ σ' c, Checkpoint Q σ σ' c → D σ' ∨ 1 ≤ c i) (k : ℕ) (e : Exp rT)
    (σ : State rT) (c : Coord → ℝ≥0∞) :
    iprop(stateInterp σ ∗ creditInterp c ∗ lwp Q ⊤ e (fun v => iprop(⌜φ v⌝))) ⊢@{IProp GF}
      iprop(|={⊤,∅}=> |={∅}[∅]▷=>^[k] ⌜AdeqBound D φ i k ⟨e, σ⟩ c⌝) := by
  induction k using Nat.strong_induction_on generalizing e σ c with
  | _ k IH => exact lwp_adequacy_body hD hφ i hck k IH e σ c

end Iris

/-! ## Soundness -/

variable {GF : BundledGFunctors} [AppPreGS rT GF] [LCPreGS GF] [InvGpreS GF]
  {Q : State rT → State rT → Prop}

/-- Adequacy for one coordinate of the credit vector: a LiveEris proof with `↯ε ∗ ↻δ` bounds
`progressBound D φ m` below by `1 - c i`, for every `m`, provided every checkpoint is a `D`-step or
leaves coordinate `i` at least 1. -/
theorem lwp_adequacy {e : Exp rT} {σ : State rT} {ε δ : ℝ≥0∞}
    (hD : MeasurableSet {σ : State rT | D σ}) (hφ : MeasurableSet {v : Val rT | φ v})
    (i : Coord) (hck : ∀ σ σ' c, Checkpoint Q σ σ' c → D σ' ∨ 1 ≤ c i) (hδ : δ < ∞)
    (Hwp : ∀ [LiveGS rT .hasNoLC GF],
      iprop(↯ε ∗ ↻δ) ⊢@{IProp GF} lwp Q ⊤ e (fun v => iprop(⌜φ v⌝)))
    (m : ℕ) : 1 - creditVec ε δ i ≤ progressBound D φ m ⟨e, σ⟩ := by
  by_cases hε : 1 ≤ ε
  · have h1 : 1 ≤ creditVec ε δ i := by
      cases i
      · exact hε
      · exact hε.trans le_self_add
    simp [tsub_eq_zero_of_le h1]
  push Not at hε
  refine pure_soundness (PROP := IProp GF) ?_
  refine step_fupdN_soundness (hlc := .hasNoLC) (GF := GF) m 0 (fun Hinv => ?_)
  iintro -
  imod (app_ra_init (GF := GF) σ) with ⟨%IA, HappAuth⟩
  imod (credit_alloc (GF := GF) ε δ hε hδ) with ⟨%γ, Ha, Hf⟩
  let ILS : LiveGS rT .hasNoLC GF :=
    { appGS := IA, lcGS := { toLCPreGS := inferInstance, γlc := γ }, invGS := Hinv }
  ihave Hf := Credit.frag_sep.1 $$ Hf
  ihave HW := Hwp $$ Hf
  iapply BIFUpdate.mono (step_fupdN_mono
    (pure_mono fun (h : AdeqBound D φ i m ⟨e, σ⟩ (creditVec ε δ)) => h m le_rfl))
  iapply lwp_adequacy_core hD hφ i hck m e σ (creditVec ε δ)
  iframe HappAuth HW
  isimp only [liveWpGS_creditInterp_eq]
  iexists δ
  iframe Ha
  ipureintro
  rfl

/-- **Safety.** A LiveEris proof with `↯ε ∗ ↻δ` never fails or gets stuck within any number of
steps, except with probability `ε`: within `m` steps it terminates satisfying `φ` or is still
running, with probability at least `1 - ε`. -/
theorem lwp_adequacy_safety {e : Exp rT} {σ : State rT} {ε δ : ℝ≥0∞} {φ : Val rT → Prop}
    (hφ : MeasurableSet {v : Val rT | φ v}) (hδ : δ < ∞)
    (Hwp : ∀ [LiveGS rT .hasNoLC GF],
      iprop(↯ε ∗ ↻δ) ⊢@{IProp GF} lwp Q ⊤ e (fun v => iprop(⌜φ v⌝)))
    (m : ℕ) : 1 - ε ≤ progressBound (fun _ => True) φ m ⟨e, σ⟩ :=
  lwp_adequacy (D := fun _ => True) (by simp) hφ .err (fun _ _ _ _ => .inl trivial) hδ Hwp m

/-- **Liveness.** If every progress step enters a `P`-state, a LiveEris proof with `↯ε ∗ ↻δ`
terminates satisfying `φ` or makes `m` steps into `P`-states, without failing first, with
probability at least `1 - (ε + δ)`, for every `m`. -/
theorem lwp_adequacy_liveness {e : Exp rT} {σ : State rT} {ε δ : ℝ≥0∞} {φ : Val rT → Prop}
    {P : State rT → Prop} (hP : MeasurableSet {σ : State rT | P σ})
    (hφ : MeasurableSet {v : Val rT | φ v}) (hQP : ∀ σ σ', Q σ σ' → P σ') (hδ : δ < ∞)
    (Hwp : ∀ [LiveGS rT .hasNoLC GF],
      iprop(↯ε ∗ ↻δ) ⊢@{IProp GF} lwp Q ⊤ e (fun v => iprop(⌜φ v⌝)))
    (m : ℕ) : 1 - (ε + δ) ≤ progressBound P φ m ⟨e, σ⟩ :=
  lwp_adequacy hP hφ .tot (fun σ σ' _ h => h.imp (hQP σ σ') id) hδ Hwp m

/-! ## Specialized forms

The safety theorem in the form of Eris's partial adequacy (a bound on the mass of values violating
the postcondition), and the liveness theorem without progress in the form of TotalEris's adequacy
(a lower bound on terminating with the postcondition). -/

/-- Configurations that are values violating `φ`. -/
abbrev badVal (φ : Val rT → Prop) : Set (Cfg rT) := goodVal fun v => ¬ φ v

theorem measurableSet_badVal (hφ : MeasurableSet {v : Val rT | φ v}) :
    MeasurableSet (badVal (rT := rT) φ) :=
  measurableSet_goodVal (φ := fun v => ¬ φ v) hφ.compl

theorem progressGood_le_one (n m : ℕ) (ρ : Cfg rT) : progressGood D φ n m ρ ≤ 1 := by
  induction n generalizing m ρ with
  | zero => simp [progressGood]
  | succ n ih =>
    cases m with
    | zero => simp [progressGood]
    | succ m =>
      rw [progressGood]
      split
      · unfold Set.indicator; split <;> simp
      · calc _ ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂primStep ρ := MeasureTheory.lintegral_mono fun ρ' => ih _ ρ'
          _ ≤ 1 := by rw [MeasureTheory.lintegral_one]; exact primStep_univ_le_one ρ

theorem progressBound_le_one (m : ℕ) (ρ : Cfg rT) : progressBound D φ m ρ ≤ 1 :=
  iSup_le fun n => progressGood_le_one n m ρ

theorem execN_bad_add_progressGood_le (hφ : MeasurableSet {v : Val rT | φ v}) (k n : ℕ)
    (ρ : Cfg rT) : execN k ρ (badVal φ) + progressGood (fun _ => True) φ n k ρ ≤ 1 := by
  induction k generalizing n ρ with
  | zero => simpa using progressGood_le_one n 0 ρ
  | succ k ih =>
    cases n with
    | zero =>
      simpa [progressGood] using
        (MeasureTheory.measure_mono (Set.subset_univ _)).trans (execN_univ_le_one (k + 1) ρ)
    | succ n =>
      rw [progressGood]
      by_cases hv : ρ.expr.isValue
      · rw [execN_succ_isValue hv, MeasureTheory.Measure.dirac_apply' _ (measurableSet_badVal hφ)]
        simp only [hv, ↓reduceIte]
        by_cases hg : ρ ∈ goodVal φ
        · have hb : ρ ∉ badVal φ := by
            rintro ⟨w, hw, hnw⟩
            obtain ⟨v, hv', hφv⟩ := hg
            exact hnw (Val.ext (hw.symm.trans hv') ▸ hφv)
          simp [hg, hb]
        · simp only [Set.indicator_of_notMem hg, add_zero]
          unfold Set.indicator; split <;> simp
      · rw [execN_succ_not_isValue hv, MeasureTheory.Measure.bind_apply (measurableSet_badVal hφ)
          (execN_measurable k).aemeasurable]
        simp only [hv, ↓reduceIte]
        have hm : Measurable fun ρ' : Cfg rT => execN k ρ' (badVal φ) :=
          (MeasureTheory.Measure.measurable_coe (measurableSet_badVal hφ)).comp (execN_measurable k)
        rw [← MeasureTheory.lintegral_add_left hm]
        calc ∫⁻ ρ', execN k ρ' (badVal φ) + progressGood (fun _ => True) φ n k ρ' ∂primStep ρ
            ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂primStep ρ := MeasureTheory.lintegral_mono fun ρ' => ih n ρ'
          _ ≤ 1 := by rw [MeasureTheory.lintegral_one]; exact primStep_univ_le_one ρ

theorem progressGood_never_le_execN (hφ : MeasurableSet {v : Val rT | φ v}) (n m : ℕ)
    (ρ : Cfg rT) : progressGood (fun _ => False) φ n (m + 1) ρ ≤ execN n ρ (goodVal φ) := by
  induction n generalizing ρ with
  | zero => simp [progressGood]
  | succ n ih =>
    rw [progressGood]
    by_cases hv : ρ.expr.isValue
    · rw [execN_succ_isValue hv, MeasureTheory.Measure.dirac_apply' _ (measurableSet_goodVal hφ)]
      simp [hv]
    · rw [execN_succ_not_isValue hv, MeasureTheory.Measure.bind_apply (measurableSet_goodVal hφ)
        (execN_measurable n).aemeasurable]
      simp only [hv, ↓reduceIte]
      exact MeasureTheory.lintegral_mono fun ρ' => ih ρ'

/-- A safety bound after `k` steps bounds the mass of values violating `φ` after `k` steps. -/
theorem execN_bad_le (hφ : MeasurableSet {v : Val rT | φ v}) {ρ : Cfg rT} {ε : ℝ≥0∞} {k : ℕ}
    (h : 1 - ε ≤ progressBound (fun _ => True) φ k ρ) : execN k ρ (badVal φ) ≤ ε := by
  have h2 : execN k ρ (badVal φ) + progressBound (fun _ => True) φ k ρ ≤ 1 := by
    rw [progressBound, ENNReal.add_iSup]
    exact iSup_le fun n => execN_bad_add_progressGood_le hφ k n _
  calc execN k ρ (badVal φ)
      ≤ 1 - progressBound (fun _ => True) φ k ρ :=
        ENNReal.le_sub_of_add_le_right ((progressBound_le_one k _).trans_lt
          ENNReal.one_lt_top).ne h2
    _ ≤ 1 - (1 - ε) := tsub_le_tsub_left h 1
    _ ≤ ε := tsub_tsub_le

/-- Safety bounds at every horizon bound the mass of values violating `φ` in the limit. -/
theorem limExec_bad_le (hφ : MeasurableSet {v : Val rT | φ v}) {ρ : Cfg rT} {ε : ℝ≥0∞}
    (h : ∀ k, 1 - ε ≤ progressBound (fun _ => True) φ k ρ) : limExec ρ (badVal φ) ≤ ε := by
  rw [limExec, iSup_measure_apply (fun _ _ h => execN_mono h _) (measurableSet_badVal hφ)]
  exact iSup_le fun k => execN_bad_le hφ (h k)

/-- Without progress states, `progressBound` is a lower bound on terminating with `φ`. -/
theorem limExec_good_ge (hφ : MeasurableSet {v : Val rT | φ v}) {ρ : Cfg rT} {x : ℝ≥0∞}
    (h : x ≤ progressBound (fun _ => False) φ 1 ρ) : x ≤ limExec ρ (goodVal φ) := by
  refine h.trans ?_
  rw [limExec, iSup_measure_apply (fun _ _ h => execN_mono h _) (measurableSet_goodVal hφ)]
  exact iSup_mono fun n => progressGood_never_le_execN hφ n 0 _

/-- **Eris-style adequacy, per step.** After any number of steps, the mass of values violating `φ`
is at most `ε`. -/
theorem lwp_adequacy_execN {e : Exp rT} {σ : State rT} {ε : ℝ≥0∞} {φ : Val rT → Prop}
    (hφ : MeasurableSet {v : Val rT | φ v})
    (Hwp : ∀ [LiveGS rT .hasNoLC GF], iprop(↯ε) ⊢@{IProp GF} lwp Q ⊤ e (fun v => iprop(⌜φ v⌝)))
    (k : ℕ) : execN k ⟨e, σ⟩ (badVal φ) ≤ ε :=
  execN_bad_le hφ (lwp_adequacy_safety (δ := 0) hφ ENNReal.zero_lt_top
    (fun [LiveGS rT .hasNoLC GF] => sep_elim_left.trans Hwp) k)

/-- **Eris-style adequacy.** In the limiting execution, the mass of values violating `φ` is at most
`ε`, whatever the progress predicate. -/
theorem lwp_adequacy_eris {e : Exp rT} {σ : State rT} {ε : ℝ≥0∞} {φ : Val rT → Prop}
    (hφ : MeasurableSet {v : Val rT | φ v})
    (Hwp : ∀ [LiveGS rT .hasNoLC GF], iprop(↯ε) ⊢@{IProp GF} lwp Q ⊤ e (fun v => iprop(⌜φ v⌝))) :
    limExec ⟨e, σ⟩ (badVal φ) ≤ ε :=
  limExec_bad_le hφ fun k => lwp_adequacy_safety (δ := 0) hφ ENNReal.zero_lt_top
    (fun [LiveGS rT .hasNoLC GF] => sep_elim_left.trans Hwp) k

/-- **TotalEris-style adequacy.** Without free checkpoints, the program terminates with a value
satisfying `φ` with probability at least `1 - ε`. -/
theorem lwp_adequacy_total {e : Exp rT} {σ : State rT} {ε : ℝ≥0∞} {φ : Val rT → Prop}
    (hφ : MeasurableSet {v : Val rT | φ v})
    (Hwp : ∀ [LiveGS rT .hasNoLC GF],
      iprop(↯ε) ⊢@{IProp GF} lwp (fun _ _ => False) ⊤ e (fun v => iprop(⌜φ v⌝))) :
    1 - ε ≤ limExec ⟨e, σ⟩ (goodVal φ) := by
  have h := lwp_adequacy_liveness (σ := σ) (δ := 0) (P := fun _ => False) (by simp) hφ
    (fun _ _ h => h) ENNReal.zero_lt_top (fun [LiveGS rT .hasNoLC GF] => sep_elim_left.trans Hwp) 1
  rw [add_zero] at h
  exact limExec_good_ge hφ h

end LiveEris
end ProbLang
