module

public import Metrology.Micrometer.Examples.RandomizedResponse
public import Metrology.Code.RandomizedResponseTwice
public import Metrology.Couplings.Divergences.RenyiStrassen
public import Metrology.Couplings.Divergences.Conversions
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Randomized response on two bits is zCDP

Each bit is randomized as in `RandomizedResponse`, but the proof runs in the zCDP lifting: each
draw spends a `(ln 3, 0)` credit, adequacy gives `(ln 9, 0)`-zCDP, and `zcdpToDp` turns the
lifting into `(ln 9, δ)`-DP for every `δ > 0`. -/

open scoped ENNReal

/-! ## Fibers in the zCDP lifting -/

section Fiber

open MeasureTheory Measure ProbabilityTheory GradedLifting Set

namespace GradedDivergence

variable {X Y Z : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [Countable Y] [MeasurableSingletonClass Y] [Countable Z] [MeasurableSingletonClass Z]
  {f : X → Z} {g : Y → Z} {μ : Measure X} {ν : Measure Y} {ε : ℝ≥0∞}

/-- Conditioning `μ` on the fiber of `f` over `g y`: the witness kernel for fiber bounds. -/
noncomputable def fiberKernel (μ : Measure X) (f : X → Z) (g : Y → Z) : Kernel Y X :=
  Kernel.ofFunOfCountable fun y ↦ μ[|f ⁻¹' {g y}]

/-- Conditioning on the fibers keeps a pointwise DP bound on the fibers. -/
theorem dp_fiberKernel (hf : Measurable f) (hg : Measurable g) [IsFiniteMeasure μ]
    (h : ∀ z, μ (f ⁻¹' {z}) ≤ expBudget ε * ν (g ⁻¹' {z})) :
    dp (ε, 0) μ (fiberKernel μ f g ∘ₘ ν) := by
  refine dp_of_forall_le fun A hA ↦ ?_
  have hF (z : Z) : MeasurableSet (f ⁻¹' {z}) := hf (measurableSet_singleton z)
  set φ : Z → ℝ≥0∞ := fun z ↦ μ[|f ⁻¹' {z}] A
  calc μ A = ∑' z, μ (f ⁻¹' {z} ∩ A) := by
        rw [← measure_iUnion (fun z z' hz ↦ ((disjoint_singleton.2 hz).preimage f).mono
          inter_subset_left inter_subset_left) fun z ↦ (hF z).inter hA, ← iUnion_inter,
          ← preimage_iUnion, iUnion_singleton_eq_range, ← Set.univ_inter A]
        simp
    _ ≤ ∑' z, expBudget ε * (φ z * ν (g ⁻¹' {z})) := by
        refine ENNReal.tsum_le_tsum fun z ↦ ?_
        simp only [φ, cond_apply (hF z)]
        rcases eq_or_ne (μ (f ⁻¹' {z})) 0 with h0 | h0
        · exact (measure_mono inter_subset_left).trans (by simp [h0])
        calc μ (f ⁻¹' {z} ∩ A)
            = (μ (f ⁻¹' {z}))⁻¹ * μ (f ⁻¹' {z} ∩ A) * μ (f ⁻¹' {z}) := by
              rw [mul_right_comm, ENNReal.inv_mul_cancel h0 (measure_ne_top _ _), one_mul]
          _ ≤ (μ (f ⁻¹' {z}))⁻¹ * μ (f ⁻¹' {z} ∩ A) * (expBudget ε * ν (g ⁻¹' {z})) := by
              gcongr
              exact h z
          _ = _ := by ring
    _ = expBudget ε * (fiberKernel μ f g ∘ₘ ν) A := by
        rw [ENNReal.tsum_mul_left, Measure.bind_apply hA (Kernel.aemeasurable _)]
        change _ = expBudget ε * ∫⁻ y, φ (g y) ∂ν
        rw [← lintegral_map (f := φ) .of_discrete hg, lintegral_countable']
        simp [map_apply hg (measurableSet_singleton _), φ]

omit [MeasurableSpace Y] [Countable Y] [MeasurableSingletonClass Y] [Countable Z] in
/-- The cost of equal images is measurable in the left point. -/
theorem measurable_relCost_fiber (hf : Measurable f) (y : Y) :
    Measurable fun x ↦ (relCost (fun x y ↦ f x = g y) x y : ℝ≥0∞) := by
  have : (fun x ↦ (relCost (fun x y ↦ f x = g y) x y : ℝ≥0∞)) =
      (f ⁻¹' {g y})ᶜ.indicator fun _ ↦ (⊤ : ℝ≥0∞) := by
    ext x
    by_cases hx : f x = g y <;> simp [hx]
  rw [this]
  exact measurable_const.indicator (hf (measurableSet_singleton _)).compl

omit [Countable Z] in
/-- The fiber kernel stays on equal images, so it pays no cost. -/
theorem lintegral_fiberKernel_le (hf : Measurable f) (y : Y) :
    ∫⁻ x, expBudget (relCost (fun x y ↦ f x = g y) x y) ∂(fiberKernel μ f g y) ≤ 1 := by
  have hF : MeasurableSet (f ⁻¹' {g y}) := hf (measurableSet_singleton _)
  change ∫⁻ x, _ ∂μ[|f ⁻¹' {g y}] ≤ 1
  rw [ProbabilityTheory.cond, lintegral_smul_measure,
    setLIntegral_congr_fun hF fun x hx ↦ by
      rw [relCost_of (S := fun x y ↦ f x = g y) hx, expBudget_zero], setLIntegral_const,
    one_mul]
  exact ENNReal.inv_mul_le_one _

/-- Fibers with a pointwise DP bound give a zCDP lifting of equal images: condition `μ` on the
fibers to witness each Rényi lifting. -/
theorem zcdpLifting_rel_of_fiber (hf : Measurable f) (hg : Measurable g)
    [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    (h : ∀ z, μ (f ⁻¹' {z}) ≤ expBudget ε * ν (g ⁻¹' {z})) :
    zcdpLifting.Rel (ε, 0) (fun x y ↦ f x = g y) μ ν := by
  refine concentratedLifting_rel_iff.2 fun α _ ↦ ?_
  rw [mul_zero, add_zero]
  have hr := lintegral_fiberKernel_le (μ := μ) (g := g) hf
  have := isSubMarkovKernel_of_lintegral_expBudget_le hr
  exact codensity_renyi_of_kernel (measurable_relCost_fiber hf) hr
    (renyi_of_dp α.2 (dp_fiberKernel hf hg h))

end GradedDivergence

end Fiber

open Iris Iris.BI Iris.ProofMode ProbLang.MicrometerWpGS GradedLifting
open GradedDivergence (dp zcdpDivergence zcdpLifting expBudget)

namespace ProbLang
namespace RandomizedResponse

/-! ## The coupling of one draw -/

/-- The two draws couple along equal reports in the zCDP lifting at budget `(ln 3, 0)`. -/
theorem rr_zcdp_coupling (b b' : Bool) :
    zcdpLifting.Rel budget (fun r r' ↦ rrOut b r = rrOut b' r')
      (unifInt 4 (by norm_num)) (unifInt 4 (by norm_num)) := by
  refine GradedDivergence.zcdpLifting_rel_of_fiber .of_discrete .of_discrete fun c ↦ ?_
  rw [expBudget_log_three]
  calc _ ≤ 1 - 4⁻¹ := rrOut_fiber_le b c
    _ ≤ 3 * 4⁻¹ := one_sub_quarter_le
    _ ≤ _ := by gcongr; exact rrOut_fiber_ge b' c

/-! ## The program logic proof -/

variable {rT : Type} [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

section Logic

variable {GF : BundledGFunctors} [MicrometerGS rT .hasNoLC GF]
  [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF]

/-- The program reports `bif d then b else !b`. -/
theorem wp_report_zcdp (d b : Bool) (Φ : Val rT → IProp GF) :
    Φ (.bool (bif d then b else !b)) ⊢
      wp zcdpLifting ⊤ pl(if #(.bool d) then #(.bool b) else ~#(.bool b)) Φ := by
  cases d
  all_goals cases b
  all_goals
    simp only [Bool.cond_false, Bool.cond_true, Bool.not_false, Bool.not_true]
    iintro H
    wp_pures
    wp_value
    imodintro
    iexact H

/-- The spec reports `bif d then b else !b`, under any evaluation context. -/
theorem tp_report_zcdp (K : Ectx rT) (d b : Bool) (e : Exp rT) (Φ : Val rT → IProp GF) :
    ⤇ K.fill pl(if #(.bool d) then #(.bool b) else ~#(.bool b)) ∗
      (⤇ K.fill pl(#(.bool (bif d then b else !b))) -∗ wp zcdpLifting ⊤ e Φ) ⊢
      wp zcdpLifting ⊤ e Φ := by
  cases d
  all_goals cases b
  all_goals
    simp only [Bool.cond_false, Bool.cond_true, Bool.not_false, Bool.not_true]
    iintro ⟨Hj, H⟩
    tp_pures
    iapply H
    iexact Hj

/-- One round of randomized response against the spec in context `K`, spending `(ln 3, 0)`:
both sides report the same bit. -/
theorem wp_rr_step (K : Ectx rT) (b b' : Bool) (Φ : Val rT → IProp GF) :
    ⤇ K.fill (rr b') ∗ ↯b budget ∗ (∀ c, ⤇ K.fill pl(#(.bool c)) -∗ Φ (.bool c)) ⊢
      wp zcdpLifting ⊤ (rr b) Φ := by
  iintro ⟨Hj, Hb, H⟩
  simp only [rr, Exp.close, Exp.closeRec, ↓reduceIte]
  wp_bind (pl% rand(#4, #.unit))
  tp_bind (pl% rand(#4, #.unit))
  iapply wp_couple_rand_rand_spend 4 (by norm_num) (fun r r' ↦ rrOut b r = rrOut b' r') budget
    isAddLeftRegular_budget (rr_zcdp_coupling b b')
  iframe Hj Hb
  iintro %r %r' %hR Hj
  wp_pures
  tp_pures
  iapply tp_report_zcdp
  iframe Hj
  iintro Hj
  iapply wp_report_zcdp
  have hc : (bif decide (r < 3) then b else !b) = (bif decide (r' < 3) then b' else !b') := by
    simpa [rrOut] using hR
  rw [hc]
  iapply H
  iexact Hj

omit [LawfulProbLangℝ rT] [MeasurableSingletonClass rT] in
/-- `rr b` is closed, so opening and closing leave it alone. -/
theorem rr_openRec_closeRec (n : Nat) (v : Exp rT) (x : Var) (b : Bool) :
    Exp.openRec n v (Exp.closeRec n x (rr b)) = rr b := by
  rfl

/-- The two-bit program against the spec in context `K`, spending `(ln 3, 0)` per bit: both
sides report the same pair. -/
theorem wp_rr2_fill (K : Ectx rT) (b₁ b₂ b₁' b₂' : Bool) (Φ : Val rT → IProp GF) :
    ⤇ K.fill (rr2 b₁' b₂') ∗ ↯b (budget + budget) ∗
      (∀ c₁ c₂, ⤇ K.fill (Exp.ofVal (.pair (.bool c₁) (.bool c₂))) -∗
        Φ (.pair (.bool c₁) (.bool c₂))) ⊢
      wp zcdpLifting ⊤ (rr2 b₁ b₂) Φ := by
  iintro ⟨Hj, Hb, H⟩
  icases BudgetCredit.split $$ Hb with ⟨Hb₁, Hb₂⟩
  simp only [rr2, Exp.close, Exp.closeRec, ↓reduceIte]
  wp_bind (rr b₁)
  tp_bind (rr b₁')
  iapply wp_rr_step
  iframe Hj Hb₁
  iintro %c₁ Hj
  wp_pures
  tp_pures
  -- substituting the first report leaves the closed `rr b₂` stuck behind `openRec`/`closeRec`
  simp only [rr_openRec_closeRec]
  wp_bind (rr b₂)
  tp_bind (rr b₂')
  iapply wp_rr_step
  iframe Hj Hb₂
  iintro %c₂ Hj
  wp_pures
  tp_pures
  wp_value
  imodintro
  iapply H
  iapply specProgFrag_reshape (e₁ := K.fill pl((#(.bool c₁), #(.bool c₂))))
    (e₂ := K.fill (Exp.ofVal (.pair (.bool c₁) (.bool c₂)))) rfl $$ Hj

/-- The two-bit program against itself, spending `(ln 3, 0)` per bit. -/
theorem wp_rr2 (b₁ b₂ b₁' b₂' : Bool) :
    ⊢@{IProp GF} ⤇ rr2 (rT := rT) b₁' b₂' -∗ ↯b (budget + budget) -∗
      wp zcdpLifting ⊤ (rr2 b₁ b₂) (fun v => iprop(∃ v', ⤇ Exp.ofVal v' ∗ ⌜v = v'⌝)) := by
  iintro Hj Hb
  iapply wp_rr2_fill []
  ihave Hj := specProgFrag_reshape (e₁ := rr2 b₁' b₂') (e₂ := Ectx.fill [] (rr2 b₁' b₂')) rfl $$ Hj
  iframe Hj Hb
  iintro %c₁ %c₂ Hj
  iexists .pair (.bool c₁) (.bool c₂)
  ihave Hj := specProgFrag_reshape (e₁ := Ectx.fill [] (Exp.ofVal (.pair (.bool c₁) (.bool c₂))))
    (e₂ := Exp.ofVal (.pair (.bool c₁) (.bool c₂))) rfl $$ Hj
  iframe Hj
  ipureintro
  rfl

end Logic

/-! ## The relational proof -/

/-- The two-bit program refines itself at equal pairs of reports, spending `(ln 3, 0)` per
bit. -/
theorem rr2_refines {GF : BundledGFunctors} [MicrometerRGS rT .hasNoLC GF]
    [BudgetCreditGS (ℝ≥0∞ × ℝ≥0∞) GF] (b₁ b₂ b₁' b₂' : Bool) :
    ⊢@{IProp GF} ↯b (budget + budget) -∗
      REL[zcdpLifting] (rr2 (rT := rT) b₁ b₂) << (rr2 b₁' b₂') : lrel_prod lrel_bool lrel_bool := by
  iunfold refines
  iintro Hb %K %ε Hj Hna Herr %Hpos
  iapply wp_rr2_fill
  iframe Hj Hb
  iintro %c₁ %c₂ Hj
  iexists .pair (.bool c₁) (.bool c₂), ε
  ihave Hj := specProgFrag_reshape (e₁ := K.fill (Exp.ofVal (.pair (.bool c₁) (.bool c₂))))
    (e₂ := K.fill (Val.pair (.bool c₁) (.bool c₂)).1) rfl $$ Hj
  iframe Hj Hna Herr %Hpos
  iunfold lrel_prod
  iexists .bool c₁, .bool c₁, .bool c₂, .bool c₂
  isplitr
  · ipureintro
    rfl
  isplitr
  · ipureintro
    rfl
  isplitr
  · iapply lrel_bool_lit
  iapply lrel_bool_lit

/-! ## Adequacy: exit the logic -/

/-- The budget `(ln 9, 0)` of two rounds. -/
noncomputable abbrev budget2 : ℝ≥0∞ × ℝ≥0∞ := (ENNReal.ofReal (Real.log 9), 0)

/-- Two rounds at `(ln 3, 0)` cost `(ln 9, 0)`. -/
theorem budget_add_budget : budget + budget = budget2 := by
  have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  rw [Prod.mk_add_mk, add_zero, ← ENNReal.ofReal_add h3 h3, ← Real.log_mul (by norm_num)
    (by norm_num)]
  norm_num

/-- Equal pairs of reports from `↯b (ln 9, 0)` couple the two runs in the zCDP lifting. -/
theorem rr2_coupling_of (GF : BundledGFunctors) [AppPreGS rT GF] [SpecPreGS rT GF]
    [BudgetCreditPreGS (ℝ≥0∞ × ℝ≥0∞) GF] [InvGpreS GF] (b₁ b₂ b₁' b₂' : Bool)
    (σ σ' : State rT) :
    zcdpLifting.Rel budget2 (· = ·) (limExecV ⟨rr2 b₁ b₂, σ⟩) (limExecV ⟨rr2 b₁' b₂', σ'⟩) :=
  (wp_adequacy (GF := GF) _ _ σ σ' budget2 (· = ·) fun _ _ ↦
    budget_add_budget ▸ wp_rr2 b₁ b₂ b₁' b₂').mono le_rfl adequacyRel_eq_subset

/-- The two-bit program is `(ln 9, 0)`-zCDP, through `wp_rr2`. -/
theorem rr2_zcdp_of (GF : BundledGFunctors) [AppPreGS rT GF] [SpecPreGS rT GF]
    [BudgetCreditPreGS (ℝ≥0∞ × ℝ≥0∞) GF] [InvGpreS GF] (b₁ b₂ b₁' b₂' : Bool)
    (σ σ' : State rT) :
    zcdpDivergence budget2 (limExecV ⟨rr2 b₁ b₂, σ⟩) (limExecV ⟨rr2 b₁' b₂', σ'⟩) :=
  wp_adequacy_div (GF := GF) (L := zcdpLifting) _ _ σ σ' budget2 fun _ _ ↦
    budget_add_budget ▸ wp_rr2 b₁ b₂ b₁' b₂'

/-- `rr2_zcdp_of`, through the refinement `rr2_refines`. -/
theorem rr2_zcdp_of_refines (GF : BundledGFunctors) [RefinesPreGS rT (ℝ≥0∞ × ℝ≥0∞) GF]
    (b₁ b₂ b₁' b₂' : Bool) (σ σ' : State rT) :
    zcdpDivergence budget2 (limExecV ⟨rr2 b₁ b₂, σ⟩) (limExecV ⟨rr2 b₁' b₂', σ'⟩) := by
  refine approximates_div (GF := GF) (L := zcdpLifting)
    (fun _ _ ↦ lrel_prod lrel_bool lrel_bool) _ _ σ σ' budget2 ?_ fun _ _ ↦
      budget_add_budget ▸ rr2_refines b₁ b₂ b₁' b₂'
  intro _ _ v v'
  iunfold lrel_prod
  iintro ⟨%a, %a', %c, %c', %hv, %hv', Ha, Hc⟩
  iunfold lrel_bool at Ha Hc
  icases Ha with ⟨%x, %⟨rfl, rfl⟩⟩
  icases Hc with ⟨%y, %⟨rfl, rfl⟩⟩
  ipureintro
  exact Val.ext (hv.trans hv'.symm)

/-- Randomized response on two bits is `(ln 9, 0)`-zCDP, for any two pairs of private bits. -/
theorem rr2_zcdp (b₁ b₂ b₁' b₂' : Bool) (σ σ' : State rT) :
    zcdpDivergence budget2 (limExecV ⟨rr2 b₁ b₂, σ⟩) (limExecV ⟨rr2 b₁' b₂', σ'⟩) :=
  rr2_zcdp_of (MicrometerFunctor rT (ℝ≥0∞ × ℝ≥0∞)) b₁ b₂ b₁' b₂' σ σ'

/-! ## From zCDP to DP -/

/-- Without the quadratic term, the best Rényi conversion of `(ξ, 0)` costs nothing over `ξ`:
send the order to infinity. -/
theorem iInf_conversion_le (ξ : ℝ≥0∞) {δ : ℝ} :
    ⨅ α ∈ Set.Ioi (1 : ℝ), ξ + ENNReal.ofReal α * 0 +
      ENNReal.ofReal (Real.log (1 / δ) / (α - 1)) ≤ ξ := by
  refine ENNReal.le_of_forall_pos_le_add fun t ht _ ↦ ?_
  set l := Real.log (1 / δ)
  have hl : 0 < |l| + 1 := by positivity
  have ht' : (0 : ℝ) < t := ht
  refine (iInf₂_le (1 + (|l| + 1) / t) (lt_add_of_pos_right _ (div_pos hl ht'))).trans ?_
  rw [mul_zero, add_zero, add_sub_cancel_left]
  gcongr
  refine ENNReal.ofReal_le_of_le_toReal ?_
  rw [ENNReal.coe_toReal, div_div_eq_mul_div, div_le_iff₀ hl]
  nlinarith [le_abs_self l]

/-- The two-bit program is `(ln 9, δ)`-DP for every `δ > 0`, converting the zCDP coupling with
`zcdpToDp`. -/
theorem rr2_dp (b₁ b₂ b₁' b₂' : Bool) (σ σ' : State rT) {δ : ℝ} (hδ : 0 < δ) :
    dp (ENNReal.ofReal (Real.log 9), ENNReal.ofReal δ)
      (limExecV ⟨rr2 b₁ b₂, σ⟩) (limExecV ⟨rr2 b₁' b₂', σ'⟩) := by
  have h := (LiftingRelHom.zcdpToDp hδ).map_rel
    (rr2_coupling_of (MicrometerFunctor rT (ℝ≥0∞ × ℝ≥0∞)) b₁ b₂ b₁' b₂' σ σ')
  dsimp only [LiftingRelHom.zcdpToDp, LiftingRelHom.comp, LiftingRelHom.codensityZcdpToDp,
    LiftingHom.toLiftingRelHom, LiftingHom.concentratedToCodensity, Function.comp] at h
  exact GradedDivergence.IsGraded.mono (Prod.mk_le_mk.2 ⟨iInf_conversion_le _, le_rfl⟩)
    (IsSound.sound (D := dp) h)

/-- Randomized response on pairs of private bits, started from state `σ`. -/
noncomputable def rr2Mech (σ : State rT) : Mechanism (Bool × Bool) (Exp rT) :=
  ⟨fun b ↦ limExecV ⟨rr2 b.1 b.2, σ⟩, .of_discrete⟩

/-- Randomized response on two bits is `(ln 9, 0)`-zCDP for any two pairs of bits (Def. 2.4). -/
theorem rr2_zCDP (σ : State rT) : (rr2Mech σ).zCDP ⊤ (ENNReal.ofReal (Real.log 9)) 0 :=
  fun b b' _ ↦ rr2_zcdp b.1 b.2 b'.1 b'.2 σ σ

/-- Randomized response on two bits is `(ln 9, δ)`-DP for any two pairs of bits and every
`δ > 0` (Def. 2.1). -/
theorem rr2_DP (σ : State rT) {δ : ℝ} (hδ : 0 < δ) :
    (rr2Mech σ).DP ⊤ (ENNReal.ofReal (Real.log 9)) (ENNReal.ofReal δ) :=
  fun b b' _ ↦ rr2_dp b.1 b.2 b'.1 b'.2 σ σ hδ

end RandomizedResponse
end ProbLang
