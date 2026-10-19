module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.UnitInterval
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Analysis.Real.OfDigits

public import Metrology.Couplings.ApproximateCouplings

/-! `(ε, δ)`-DP couplings as approximate couplings up to `x ↦ e^ε x + δ` (the old core). -/

@[expose] public section

noncomputable section DPCoupling

open MeasureTheory Measure EReal

/-- The DP error map `x ↦ e^ε x + δ`. -/
abbrev DPF (ε δ x : ENNReal) := exp ε * x + δ

variable {α β α' β' : Type _}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace α'] [MeasurableSpace β']
variable (ε δ : ENNReal)

/-- An `(ε, δ)`-DP coupling. -/
abbrev ARCoupling.DP (S : Set (α × β)) := ARCoupling (DPF ε δ) S

theorem ARCoupling.DP.trivial_δ {μₗ : Measure α} {μᵣ : Measure β} {S} (Hδ : μₗ .univ ≤ δ) :
    ARCoupling.DP ε δ S μₗ μᵣ := by
  refine fun ⟨f, _, Hf⟩ _ _ => ?_
  exact (lintegral_le_meas Hf fun _ => (·.elim trivial)).trans (Hδ.trans le_add_self)

theorem ARCoupling.DP.dirac {a : α} {b : β} (S : Set (α × β)) :
    S (a, b) → ARCoupling.DP ε δ S (.dirac a) (.dirac b) := by
  refine (ARCoupling.dirac (@fun _ => ?_) _ ·)
  refine .trans ?_ le_self_add
  refine le_mul_of_one_le_left' ?_
  exact EReal.one_le_exp_iff.mpr <| EReal.coe_ennreal_nonneg ε

-- TODO: remove ε ≠ ⊤ case by reduction (needs g ≠ 0?)
theorem ARCoupling.DP.bind {ε'} {δ' : NNReal} {f : α → Measure α'} {g : β → Measure β'} {S T}
   {μₗ μᵣ} (Hfm : Measurable f) (Hgm : Measurable g) (Huniv : μₗ .univ ≤ 1) (Hε : ε ≠ ⊤)
   (Hfsprob : ∀ {a}, (f a) Set.univ ≤ 1)
   (Hcpl : ARCoupling.DP ε δ S μₗ μᵣ)
   (Hbind : ∀ {a b}, S (a, b) → ARCoupling.DP ε' δ' T (f a) (g b)) :
   ARCoupling.DP (ε + ε') (δ + δ') T (μₗ.bind f) (μᵣ.bind g) := by
  rintro ⟨f', Hf'm, Hf'b⟩ ⟨g', Hg'm, Hg'b⟩ Hf'g'
  have Hf'le a : ∫⁻ (y : α'), f' y ∂f a - δ' ≤ 1 := by
    refine tsub_le_iff_left.mpr (.trans ?_ le_add_self)
    refine (lintegral_le_iSup_mul (f := f')).trans ?_
    exact Left.mul_le_one (iSup_le (Hf'b ·)) Hfsprob

  let F : CouplingFunction α := .mk (max 0 <| ∫⁻ y, f' y ∂ f · - δ') ⟨?Fm, fun a => ?Fb⟩
  case Fm =>
    refine measurable_const.max ?_
    refine .sub ?_ measurable_const
    exact measurable_lintegral Hf'm |>.comp Hfm
  case Fb => exact max_le (zero_le_one' _) (Hf'le _)
  let G : CouplingFunction β := .mk (min 1 <| (exp ε') * ∫⁻ y, g' y ∂ g ·) ⟨?Gm, fun b => ?Gb⟩
  case Gm =>
    refine measurable_const.min ?_
    refine measurable_const.mul ?_
    exact measurable_lintegral Hg'm |>.comp Hgm
  case Gb => exact min_le_left _ _

  rw [lintegral_bind Hfm.aemeasurable Hf'm.aemeasurable,
      lintegral_bind Hgm.aemeasurable Hg'm.aemeasurable]
  calc  ∫⁻ a, ∫⁻ (x : α'), f' x ∂f a ∂μₗ
    _ ≤ ∫⁻ a, δ' + F a ∂μₗ := ?_
    _ ≤ δ' + ∫⁻ a, F a ∂μₗ := ?_
    _ ≤ δ' + δ + exp ε * ∫⁻ b, G b ∂μᵣ := ?_
    _ ≤ δ' + δ + exp ε * ∫⁻ b, exp ε' * ∫⁻ b', g' b' ∂g b ∂μᵣ := ?_
  · refine lintegral_mono (fun x => ?_)
    simp only [zero_le, sup_of_le_right, F]
    exact le_add_tsub
  · rw [lintegral_add_left measurable_const, lintegral_const]
    refine (ENNReal.add_le_add_iff_right ?_).mpr ?_
    · refine LT.lt.ne (lt_of_le_of_lt ?_ ENNReal.one_lt_top)
      refine (lintegral_le_iSup_mul (f := F)).trans ?_
      refine Left.mul_le_one (iSup_le ?_) Huniv
      exact F.property.2
    exact mul_le_of_le_one_right' Huniv
  · rw [add_assoc]; refine add_le_add (le_refl _) ?_
    rw [add_comm]
    refine Hcpl F G (fun {a b} HS => ?_)
    simp only [G]
    refine max_le zero_le (le_min ?_ ?_)
    · exact Hf'le _
    · refine tsub_le_iff_left.mpr ?_
      rw [add_comm]; exact Hbind HS ⟨f', ⟨Hf'm, Hf'b⟩⟩ ⟨g', ⟨Hg'm, Hg'b⟩⟩ Hf'g'
  · dsimp only [G]; refine add_le_add (le_refl _) ?_
    refine (ENNReal.mul_le_mul_iff_right (by simp) (by simp [Hε])).mpr ?_
    refine lintegral_mono (fun b => ?_)
    exact min_le_right _ _
  · simp [exp_add, add_comm, mul_assoc]
    refine le_of_eq ?_
    congr
    exact lintegral_const_mul (exp ε') (measurable_lintegral Hg'm |>.comp Hgm)

end DPCoupling
