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

public import Metrology.Couplings.AdditiveCouplings

@[expose] public section

section Couplings

variable {α β α' β' : Type _}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace α'] [MeasurableSpace β']

open MeasureTheory Measure

/-- Exact relational coupling: the zero-slack case of `ARCoupling`. -/
def RelCoupl (Φ : Set (α × β)) (μₗ : Measure α) (μᵣ : Measure β) : Prop :=
  ARCoupling id Φ μₗ μᵣ

namespace RelCoupl

theorem relCoupl_addCoupl {Φ : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β} :
    RelCoupl Φ μₗ μᵣ = AddCoupl 0 Φ μₗ μᵣ := by
  unfold RelCoupl AddCoupl
  congr
  exact add_zero_eq_id.symm

theorem refl_zero (μ : Measure α) : RelCoupl (fun v => v.1 = v.2) μ μ :=
  ARCoupling.refl μ (refl _)

theorem map {h : α → β} (hm : Measurable h) (μ : Measure α) :
    RelCoupl (fun v => v.2 = h v.1) μ (μ.map h) := by
  erw [relCoupl_addCoupl]
  rintro ⟨f, _, _⟩ ⟨g, gm, _⟩ Hfg
  show ∫⁻ a, f a ∂μ ≤ ∫⁻ b, g b ∂(μ.map h) + 0
  rw [add_zero]
  calc ∫⁻ a, f a ∂μ
      _ ≤ ∫⁻ a, g (h a) ∂μ := lintegral_mono fun a => Hfg rfl
      _ = ∫⁻ b, g b ∂(μ.map h) := (lintegral_map gm hm).symm

theorem map_of_measurePreserving {h : α → β} {μ : Measure α} {ν : Measure β}
    (hp : MeasurePreserving h μ ν) :
    RelCoupl (fun v => v.2 = h v.1) μ ν := by
  rw [← hp.map_eq]
  exact map hp.measurable μ

/-- Measure-theoretic analogue of Clutch's `ARcoupl_dunif`. -/
theorem self_of_measurePreserving {h : α → α} {μ : Measure α}
    (hp : MeasurePreserving h μ μ) :
    RelCoupl (fun v => v.2 = h v.1) μ μ :=
  map_of_measurePreserving hp

theorem trivial {μₗ : Measure α} {μᵣ : Measure β}
    (Hμₗ : μₗ .univ = 1) (Hμᵣ : μᵣ .univ = 1) :
    RelCoupl Set.univ μₗ μᵣ := by
  rw [relCoupl_addCoupl]
  intro ⟨f, _, Hfb⟩ ⟨g, _, Hgb⟩ Hfg
  show ∫⁻ a, f a ∂μₗ ≤ ∫⁻ b, g b ∂μᵣ + 0
  rw [add_zero]
  calc ∫⁻ a, f a ∂μₗ
      _ ≤ ⨆ a, f a := (lintegral_le_iSup_mul f).trans (by rw [Hμₗ, mul_one])
      _ ≤ ⨅ b, g b := iSup_le fun a => le_iInf fun b => Hfg (Set.mem_univ (a, b))
      _ ≤ ∫⁻ b, g b ∂μᵣ :=
        (by rw [Hμᵣ, mul_one] : (⨅ b, g b) * μᵣ .univ = ⨅ b, g b) ▸ iInf_mul_le_lintegral g

theorem exact {ε : ENNReal} {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    (H : RelCoupl S μₗ μᵣ) : AddCoupl ε S μₗ μᵣ := by
  refine AddCoupl.mono_grading zero_le ?_
  rwa [← relCoupl_addCoupl]

theorem limit {ε : ENNReal} {S : Set (α × β)} {μₗ : Measure α} {μᵣ : Measure β}
    (H : ∀ ε', ε < ε' → AddCoupl ε' S μₗ μᵣ) : AddCoupl ε S μₗ μᵣ := by
  intro f g Hfg
  set a := ∫⁻ x, f.1 x ∂μₗ
  set b := ∫⁻ x, g.1 x ∂μᵣ
  suffices ∀ c > b + ε, a ≤ c from forall_gt_imp_ge_iff_le_of_dense.mp this
  intro c hc
  have hbc : b ≤ c := le_self_add.trans hc.le
  have hε' : ε < c - b := lt_tsub_iff_left.mpr (add_comm b ε ▸ hc)
  calc a ≤ b + (c - b) := H _ hε' f g Hfg
      _ = c             := add_tsub_cancel_of_le hbc

end RelCoupl
end Couplings
