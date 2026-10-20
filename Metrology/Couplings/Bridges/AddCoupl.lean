module

public import Metrology.Couplings.AdditiveCouplings
public import Metrology.Couplings.DPCouplings
public import Metrology.Couplings.Divergences.Tv
public import Metrology.Couplings.LiftingHom

/-! # Additive and DP couplings as codensity liftings

Additive couplings and test-function DP couplings are the codensity liftings of `tv` and `dp`
(Approximate Span Liftings, §6). -/

@[expose] public section

universe u

open MeasureTheory Measure ProbabilityTheory GradedDivergence GradedLifting
open scoped ENNReal

variable {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {ε δ : ℝ≥0∞} {μ : Measure X}
  {ν : Measure Y}

/-! ## Total variation: couplings in expectation and additive couplings -/

/-- A total variation codensity lifting is a coupling in expectation. -/
theorem expCoupl_of_codensity_tv {E : X → Y → ℝ≥0∞} (h : tv.codensity δ E μ ν) :
    ExpCoupl δ E μ ν :=
  fun _ _ ↦ lintegral_le_of_codensity_tv h

/-- Couplings in expectation are the total variation codensity lifting. -/
theorem expCoupl_iff_codensity_tv [IsSubProbabilityMeasure μ] {E : X → Y → ℝ≥0∞} :
    ExpCoupl δ E μ ν ↔ tv.codensity δ E μ ν :=
  ⟨codensity_tv_iff.2, expCoupl_of_codensity_tv⟩

/-- An additive coupling is a coupling in expectation for the relation's leftover. -/
theorem addCoupl_iff_expCoupl_relCost {S : Set (X × Y)} :
    AddCoupl δ S μ ν ↔ ExpCoupl δ (relCost fun x y ↦ (x, y) ∈ S) μ ν := by
  refine ⟨fun h f g hf hg hf1 hg1 hfg ↦ h ⟨f, hf, hf1⟩ ⟨g, hg, hg1⟩ fun {x y} hxy ↦ ?_, ?_⟩
  · exact le_add_relCost_iff.1 (hfg x y) hxy
  · rintro h ⟨f, hf, hf1⟩ ⟨g, hg, hg1⟩ hfg
    exact h f g hf hg hf1 hg1 fun x y ↦ le_add_relCost_iff.2 hfg

/-- An additive coupling is a total variation codensity lifting. -/
theorem AddCoupl.codensity [IsSubProbabilityMeasure μ] {S : Set (X × Y)} (h : AddCoupl δ S μ ν) :
    (codensity tv).Rel δ (fun x y ↦ (x, y) ∈ S) μ ν :=
  expCoupl_iff_codensity_tv.1 (addCoupl_iff_expCoupl_relCost.1 h)

/-- A total variation codensity lifting is an additive coupling. -/
theorem GradedLifting.Rel.addCoupl {S : X → Y → Prop} (h : (codensity tv).Rel δ S μ ν) :
    AddCoupl δ {p | S p.1 p.2} μ ν := fun f g hfg ↦
  lintegral_le_of_codensity_tv h f.measurable g.measurable f.bounded g.bounded
    fun _ _ ↦ le_add_relCost_iff.2 hfg

/-- Additive couplings are the total variation codensity lifting (Rocq `gcoupl_AR_eq`). -/
theorem addCoupl_iff_codensity_tv [IsSubProbabilityMeasure μ] {S : Set (X × Y)} :
    AddCoupl δ S μ ν ↔ (codensity tv).Rel δ (fun x y ↦ (x, y) ∈ S) μ ν :=
  ⟨AddCoupl.codensity, Rel.addCoupl⟩

/-! ### Using an additive coupling at a different cost or support -/

/-- An additive coupling gives a coupling in expectation for any cost bounded on the relation. -/
theorem expCoupl_of_addCoupl [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    {R : X → Y → Prop} {c : X → Y → ℝ≥0∞} {ε₁ ε₂ : ℝ≥0∞} (Hε : ε₁ + ε₂ ≤ δ)
    (HY : ∀ a b, R a b → c a b ≤ ε₂) (Hcpl : AddCoupl ε₁ {p | R p.1 p.2} μ ν) :
    ExpCoupl δ c μ ν :=
  fun f g hf hg hf1 hg1 hfg ↦
    (expCoupl_iff_codensity_tv.2
      ((addCoupl_iff_codensity_tv.1 Hcpl).frame_le_of_isTopAbsorbing HY)
        f g hf hg hf1 hg1 hfg).trans (by gcongr)

/-- Adding a constant to the cost of a coupling in expectation adds it to the bound. -/
theorem expCoupl_add_const [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    {c : X → Y → ℝ≥0∞} {ε₁ ε₂ : ℝ≥0∞}
    (Hε : ε₁ + ε₂ ≤ δ) (H : ExpCoupl ε₁ c μ ν) : ExpCoupl δ (fun a b ↦ c a b + ε₂) μ ν :=
  fun f g hf hg hf1 hg1 hfg ↦
    (expCoupl_iff_codensity_tv.2 (IsTopAbsorbing.frame (expCoupl_iff_codensity_tv.1 H))
      f g hf hg hf1 hg1 hfg).trans (by gcongr)

/-- A total variation lifting may assume the right sample lies in a set carrying `ν`.
`IsSupportLocal` restricts only the left side; the right restriction goes through
`AddCoupl.concentrated_R`. -/
theorem GradedLifting.Rel.tv_restrict_right [IsSubProbabilityMeasure μ] {S : X → Y → Prop}
    {T : Set Y} (h : (codensity tv).Rel δ S μ ν) (hT : MeasurableSet T) (hν : ν Tᶜ = 0) :
    (codensity tv).Rel δ (fun x y ↦ S x y ∧ y ∈ T) μ ν :=
  (h.addCoupl.concentrated_R hT hν).codensity

/-! ## Differential privacy: test-function DP couplings and the `tv` to `dp` maps -/

/-- A test-function DP coupling is a DP codensity lifting. -/
theorem ARCoupling.DP.codensity [IsSubProbabilityMeasure μ] {S : Set (X × Y)}
    (h : ARCoupling.DP ε δ S μ ν) : (codensity dp).Rel (ε, δ) (fun x y ↦ (x, y) ∈ S) μ ν := by
  rcases eq_or_ne ε ⊤ with rfl | hε
  · exact codensity_dp_top_left
  exact (codensity_dp_rel_iff hε).2 fun f g hf hg hf1 hg1 hfg ↦
    h ⟨f, hf, hf1⟩ ⟨g, hg, hg1⟩ fun hxy ↦ hfg _ _ hxy

/-- At a finite multiplier, a DP codensity lifting is a test-function DP coupling. -/
theorem GradedLifting.Rel.arCoupling_dp (hε : ε ≠ ⊤) {S : X → Y → Prop}
    (h : (codensity dp).Rel (ε, δ) S μ ν) : ARCoupling.DP ε δ {p | S p.1 p.2} μ ν :=
  fun f g hfg ↦
    lintegral_le_of_codensity_dp hε h f.measurable g.measurable f.bounded g.bounded fun x y ↦ by
      by_cases hS : S x y
      · simpa [hS] using hfg hS
      · simp [hS]

/-- At a finite multiplier, test-function DP couplings are the DP codensity lifting (Rocq
`gcoupl_DP_eq`). -/
theorem arCoupling_dp_iff_codensity [IsSubProbabilityMeasure μ] (hε : ε ≠ ⊤) {S : Set (X × Y)} :
    ARCoupling.DP ε δ S μ ν ↔ (codensity dp).Rel (ε, δ) (fun x y ↦ (x, y) ∈ S) μ ν :=
  ⟨ARCoupling.DP.codensity, Rel.arCoupling_dp hε⟩

/-- Total variation liftings are DP liftings at multiplier `1`, leftovers included. -/
noncomputable def LiftingHom.tvToDp : LiftingHom (codensity tv.{u}) (codensity dp.{u}) where
  map := dpSlack
  mono := dpSlack.monotone'
  map_lift := codensity_tv_iff_dp.1

/-- Total variation liftings of relations are DP liftings at multiplier `1` (Rocq `CM_AR_DP`). -/
noncomputable def LiftingRelHom.tvToDp : LiftingRelHom (codensity tv.{u}) (codensity dp.{u}) where
  map := dpSlack
  mono := dpSlack.monotone'
  map_rel := codensity_tv_rel_iff_dp.1
