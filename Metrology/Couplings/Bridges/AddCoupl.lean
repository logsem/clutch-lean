module

public import Metrology.Couplings.AdditiveCouplings
public import Metrology.Couplings.DPCouplings
public import Metrology.Couplings.Divergences.Tv
public import Metrology.Couplings.LiftingHom

/-! Additive, expectation and test-function DP couplings are codensity liftings of `tv` and
`dp` (Approximate Span Liftings, §6). -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory GradedDivergence GradedLifting
open scoped ENNReal

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {ε δ : ℝ≥0∞} {μ : Measure X}
  {ν : Measure Y}

/-! ## Total variation -/

/-- Couplings in expectation are the total variation codensity lifting. -/
theorem expCoupl_iff_codensity_tv [IsSubProbabilityMeasure μ] {E : X → Y → ℝ≥0∞} :
    ExpCoupl δ E μ ν ↔ tv.codensity δ E μ ν :=
  codensity_tv_iff.symm

/-- An additive coupling is a coupling in expectation for the relation's leftover. -/
theorem addCoupl_iff_expCoupl_relCost {S : Set (X × Y)} :
    AddCoupl δ S μ ν ↔ ExpCoupl δ (relCost fun x y ↦ (x, y) ∈ S) μ ν := by
  refine ⟨fun h f g hf hg hf1 hg1 hfg ↦ h ⟨f, hf, hf1⟩ ⟨g, hg, hg1⟩ fun {x y} hxy ↦ by
    simpa [relCost_of (S := fun x y ↦ (x, y) ∈ S) hxy] using hfg x y, ?_⟩
  rintro h ⟨f, hf, hf1⟩ ⟨g, hg, hg1⟩ hfg
  refine h f g hf hg hf1 hg1 fun x y ↦ ?_
  by_cases hxy : (x, y) ∈ S
  · simpa [relCost_of (S := fun x y ↦ (x, y) ∈ S) hxy] using hfg hxy
  · simp [relCost_of_not (S := fun x y ↦ (x, y) ∈ S) hxy]

/-- An additive coupling is a total variation codensity lifting. -/
theorem AddCoupl.codensity [IsSubProbabilityMeasure μ] {S : Set (X × Y)} (h : AddCoupl δ S μ ν) :
    (codensity tv).Rel δ (fun x y ↦ (x, y) ∈ S) μ ν :=
  expCoupl_iff_codensity_tv.1 (addCoupl_iff_expCoupl_relCost.1 h)

/-- A total variation codensity lifting is an additive coupling. -/
theorem GradedLifting.Rel.addCoupl {S : X → Y → Prop} (h : (codensity tv).Rel δ S μ ν) :
    AddCoupl δ {p | S p.1 p.2} μ ν := fun f g hfg ↦
  lintegral_le_of_codensity_tv h f.measurable g.measurable f.bounded g.bounded fun x y ↦ by
    by_cases hS : S x y
    · simpa [hS] using hfg hS
    · simp [hS]

/-- Additive couplings are the total variation codensity lifting (Rocq `ARcoupl_1`). -/
theorem addCoupl_iff_codensity_tv [IsSubProbabilityMeasure μ] {S : Set (X × Y)} :
    AddCoupl δ S μ ν ↔ (codensity tv).Rel δ (fun x y ↦ (x, y) ∈ S) μ ν :=
  ⟨AddCoupl.codensity, Rel.addCoupl⟩

/-- A total variation lifting may assume the right sample lies in a set carrying `ν`. -/
theorem GradedLifting.Rel.tv_restrict_right [IsSubProbabilityMeasure μ] {S : X → Y → Prop}
    {T : Set Y} (h : (codensity tv).Rel δ S μ ν) (hT : MeasurableSet T) (hν : ν Tᶜ = 0) :
    (codensity tv).Rel δ (fun x y ↦ S x y ∧ y ∈ T) μ ν :=
  (h.addCoupl.concentrated_R hT hν).codensity

/-! ## Differential privacy -/

/-- The DP multiplier is the extended exponential. -/
theorem expBudget_eq_exp (ε : ℝ≥0∞) : expBudget ε = (ε : EReal).exp := by
  rcases eq_or_ne ε ⊤ with rfl | hε
  · simp
  · rw [expBudget_of_ne_top hε, ← ENNReal.ofReal_toReal hε, EReal.coe_ennreal_ofReal,
      max_eq_left ENNReal.toReal_nonneg, EReal.exp_coe, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]

/-- A test-function DP coupling is a DP codensity lifting. -/
theorem ARCoupling.DP.codensity [IsSubProbabilityMeasure μ] {S : Set (X × Y)}
    (h : ARCoupling.DP ε δ S μ ν) : (codensity dp).Rel (ε, δ) (fun x y ↦ (x, y) ∈ S) μ ν := by
  rcases eq_or_ne ε ⊤ with rfl | hε
  · exact codensity_dp_top_left
  refine (codensity_dp_rel_iff hε).2 fun f g hf hg hf1 hg1 hfg ↦ ?_
  simpa [DPF, expBudget_eq_exp] using h ⟨f, hf, hf1⟩ ⟨g, hg, hg1⟩ fun hxy ↦ hfg _ _ hxy

/-- At a finite multiplier, a DP codensity lifting is a test-function DP coupling. -/
theorem GradedLifting.Rel.arCoupling_dp (hε : ε ≠ ⊤) {S : X → Y → Prop}
    (h : (codensity dp).Rel (ε, δ) S μ ν) : ARCoupling.DP ε δ {p | S p.1 p.2} μ ν :=
  fun f g hfg ↦ by
    simpa [DPF, expBudget_eq_exp] using lintegral_le_of_codensity_dp hε h f.measurable
      g.measurable f.bounded g.bounded fun x y ↦ by
        by_cases hS : S x y
        · simpa [hS] using hfg hS
        · simp [hS]

/-- At a finite multiplier, test-function DP couplings are the DP codensity lifting (Rocq
`DPcoupl`). -/
theorem arCoupling_dp_iff_codensity [IsSubProbabilityMeasure μ] (hε : ε ≠ ⊤) {S : Set (X × Y)} :
    ARCoupling.DP ε δ S μ ν ↔ (codensity dp).Rel (ε, δ) (fun x y ↦ (x, y) ∈ S) μ ν :=
  ⟨ARCoupling.DP.codensity, Rel.arCoupling_dp hε⟩

/-- Total variation liftings of relations are DP liftings at multiplier `1` (Rocq `CM_AR_DP`). -/
noncomputable def liftingRelHom_tv_dp : LiftingRelHom (codensity tv.{u}) (codensity dp.{u}) where
  map := dpSlack
  mono := dpSlack.monotone'
  map_rel := codensity_tv_rel_iff_dp.1
