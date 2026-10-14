module

public import Metrology.Couplings.CodensityLifting

/-! Further laws of the cost-graded codensity lifting `CodensityE`, whose total variation instance
is `ExpCoupl` (`CodensityTV.lean`) and whose bind law is `AddCoupl.bind_adv_kanto`. -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal

namespace GradedDivergence

variable {ι : Type v} [Monoid ι] {Δ : GradedDivergence.{u} ι}
variable {X Y X' Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X']
  [MeasurableSpace Y']

/-- A relational lifting is the cost lifting of the relation's cost. -/
theorem codensityE_relCost_iff {α : ι} {δ : ℝ≥0∞} {R : Set (X × Y)} {μ : Measure X}
    {ν : Measure Y} : Δ.CodensityE α δ (relCost R) μ ν ↔ Δ.Codensity α δ R μ ν :=
  Iff.rfl

/-- A relational lifting gives the cost lifting of any cost bounded on the relation, paying the
bound (cf. `expCoupl_of_addCoupl` in Micrometer). -/
theorem Codensity.codensityE {α : ι} {δ δ' : ℝ≥0∞} {R : Set (X × Y)} {E : X → Y → ℝ≥0∞}
    {μ : Measure X} {ν : Measure Y} (h : Δ.Codensity α δ R μ ν)
    (hE : ∀ ⦃x y⦄, (x, y) ∈ R → E x y ≤ δ') : Δ.CodensityE α (δ + δ') E μ ν :=
  (CodensityE.add_const h δ').mono_cost fun x y ↦ by
    by_cases hxy : (x, y) ∈ R
    · simpa [relCost_of_mem hxy] using hE hxy
    · simp [relCost_of_notMem hxy]

/-! ### Kleisli laws with relational continuations -/

/-- `CodensityE.bind` with a relational continuation. -/
theorem CodensityE.bind_codensity {α α' : ι} {δ : ℝ≥0∞} {E : X → Y → ℝ≥0∞}
    {S : Set (X' × Y')} {μ : Measure X} {ν : Measure Y} (h : Δ.CodensityE α δ E μ ν)
    {f : Kernel X X'} {g : Kernel Y Y'} [IsSubMarkovKernel f] [IsSubMarkovKernel g]
    (hfg : ∀ x y, Δ.Codensity α' (E x y) S (f x) (g y)) :
    Δ.Codensity (α * α') δ S (f ∘ₘ μ) (g ∘ₘ ν) :=
  h.bind hfg

/-- `CodensityE.bind_codensity` for measurable families of subprobability measures. -/
theorem CodensityE.bind_fun {α α' : ι} {δ : ℝ≥0∞} {E : X → Y → ℝ≥0∞} {S : Set (X' × Y')}
    {μ : Measure X} {ν : Measure Y} (h : Δ.CodensityE α δ E μ ν) {f : X → Measure X'}
    {g : Y → Measure Y'} [∀ x, IsSubProbabilityMeasure (f x)]
    [∀ y, IsSubProbabilityMeasure (g y)] (hfg : ∀ x y, Δ.Codensity α' (E x y) S (f x) (g y))
    (hf : Measurable f := by fun_prop) (hg : Measurable g := by fun_prop) :
    Δ.Codensity (α * α') δ S (μ.bind f) (ν.bind g) :=
  h.bind_codensity (f := ⟨f, hf⟩) (g := ⟨g, hg⟩) hfg

/-! ### Per-pair graded cost liftings -/

variable (Δ) in
/-- The per-pair graded cost lifting: kernels `Δ`-close at `x, y` within the slack plus `E x y`, at
grade `G x y` times the test grade, are `Δ`-close after binding at grade `α` times the test grade,
within the slack plus `δ` (the coupling side condition of clutch-dp's `spec_coupl`). -/
def CodensityG (α : ι) (δ : ℝ≥0∞) (G : X → Y → ι) (E : X → Y → ℝ≥0∞) (μ : Measure X)
    (ν : Measure Y) : Prop :=
  ∀ ⦃I : Type u⦄ [MeasurableSpace I] ⦃β : ι⦄ ⦃γ : ℝ≥0∞⦄ ⦃k : Kernel X I⦄ ⦃l : Kernel Y I⦄
    [IsSubMarkovKernel k] [IsSubMarkovKernel l],
    (∀ x y, Δ (G x y * β) (k x) (l y) ≤ γ + E x y) → Δ (α * β) (k ∘ₘ μ) (l ∘ₘ ν) ≤ δ + γ

/-- A cost lifting at grade `α` leaves the grade `α'` to every continuation. -/
theorem CodensityE.codensityG {α : ι} {δ : ℝ≥0∞} {E : X → Y → ℝ≥0∞} {μ : Measure X}
    {ν : Measure Y} (h : Δ.CodensityE α δ E μ ν) (α' : ι) :
    Δ.CodensityG (α * α') δ (fun _ _ ↦ α') E μ ν := by
  intro I _ β γ k l _ _ hkl
  rw [mul_assoc]
  exact h hkl

/-- A cost lifting at the unit grade leaves the whole grade to every continuation. -/
theorem CodensityE.codensityG_one {δ : ℝ≥0∞} {E : X → Y → ℝ≥0∞} {μ : Measure X}
    {ν : Measure Y} (h : Δ.CodensityE 1 δ E μ ν) (α : ι) :
    Δ.CodensityG α δ (fun _ _ ↦ α) E μ ν := by
  simpa using h.codensityG α

/-- Larger bounds give larger graded liftings. -/
theorem CodensityG.mono_bound {α : ι} {δ δ' : ℝ≥0∞} {G : X → Y → ι} {E : X → Y → ℝ≥0∞}
    {μ : Measure X} {ν : Measure Y} (h : Δ.CodensityG α δ G E μ ν) (hδ : δ ≤ δ') :
    Δ.CodensityG α δ' G E μ ν :=
  fun _ _ _ _ _ _ _ _ hkl ↦ (h hkl).trans (add_le_add_left hδ _)

/-- Smaller costs give larger graded liftings. -/
theorem CodensityG.mono_cost {α : ι} {δ : ℝ≥0∞} {G : X → Y → ι} {E E' : X → Y → ℝ≥0∞}
    {μ : Measure X} {ν : Measure Y} (h : Δ.CodensityG α δ G E μ ν)
    (hE : ∀ x y, E' x y ≤ E x y) : Δ.CodensityG α δ G E' μ ν :=
  fun _ _ _ _ _ _ _ _ hkl ↦ h fun x y ↦ (hkl x y).trans (add_le_add le_rfl (hE x y))

/-- Pushing forward along maps, with the grades and costs pulled back along them. -/
theorem CodensityG.map {α : ι} {δ : ℝ≥0∞} {G : X' → Y' → ι} {E : X' → Y' → ℝ≥0∞}
    {μ : Measure X} {ν : Measure Y} {f : X → X'} {g : Y → Y'}
    (h : Δ.CodensityG α δ (fun x y ↦ G (f x) (g y)) (fun x y ↦ E (f x) (g y)) μ ν)
    (hf : Measurable f := by fun_prop) (hg : Measurable g := by fun_prop) :
    Δ.CodensityG α δ G E (μ.map f) (ν.map g) := by
  intro I _ β γ k l _ _ hkl
  rw [bind_map_eq μ hf, bind_map_eq ν hg]
  exact h (k := k.comap f hf) (l := l.comap g hg) fun x y ↦ hkl (f x) (g y)

/-- Binding with continuations in the lifting at the grade and bound left at each pair. -/
theorem CodensityG.bind_codensity {α : ι} {δ : ℝ≥0∞} {G : X → Y → ι} {E : X → Y → ℝ≥0∞}
    {S : Set (X' × Y')} {μ : Measure X} {ν : Measure Y} (h : Δ.CodensityG α δ G E μ ν)
    {f : Kernel X X'} {g : Kernel Y Y'} [IsSubMarkovKernel f] [IsSubMarkovKernel g]
    (hfg : ∀ x y, Δ.Codensity (G x y) (E x y) S (f x) (g y)) :
    Δ.Codensity α δ S (f ∘ₘ μ) (g ∘ₘ ν) := by
  intro I _ β γ k l _ _ hkl
  rw [comp_assoc, comp_assoc]
  refine h fun x y ↦ ?_
  rw [Kernel.comp_apply, Kernel.comp_apply, add_comm]
  exact hfg x y hkl

/-- `CodensityG.bind_codensity` for measurable families of subprobability measures. -/
theorem CodensityG.bind_fun {α : ι} {δ : ℝ≥0∞} {G : X → Y → ι} {E : X → Y → ℝ≥0∞}
    {S : Set (X' × Y')} {μ : Measure X} {ν : Measure Y} (h : Δ.CodensityG α δ G E μ ν)
    {f : X → Measure X'} {g : Y → Measure Y'} [∀ x, IsSubProbabilityMeasure (f x)]
    [∀ y, IsSubProbabilityMeasure (g y)] (hfg : ∀ x y, Δ.Codensity (G x y) (E x y) S (f x) (g y))
    (hf : Measurable f := by fun_prop) (hg : Measurable g := by fun_prop) :
    Δ.Codensity α δ S (μ.bind f) (ν.bind g) :=
  h.bind_codensity (f := ⟨f, hf⟩) (g := ⟨g, hg⟩) hfg

/-! ### Concentration -/


/-- Only the cost on a set `T` carrying all of `μ` matters. -/
theorem CodensityE.concentrated_L [Δ.IsZeroLeft] {α : ι} {δ : ℝ≥0∞} {E E' : X → Y → ℝ≥0∞}
    {μ : Measure X} {ν : Measure Y} {T : Set X} (hT : MeasurableSet T) (hμ : μ Tᶜ = 0)
    (h : Δ.CodensityE α δ E μ ν) (hE : ∀ x ∈ T, ∀ y, E' x y ≤ E x y) :
    Δ.CodensityE α δ E' μ ν := by
  classical
  intro I _ β γ k l _ _ hkl
  have hk : Kernel.piecewise hT k 0 ∘ₘ μ = k ∘ₘ μ := comp_congr <| by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμ] with x hx
    simp [Kernel.piecewise_apply, not_not.1 hx]
  rw [← hk]
  refine h fun x y ↦ ?_
  by_cases hx : x ∈ T
  · simpa [Kernel.piecewise_apply, hx] using (hkl x y).trans (add_le_add le_rfl (hE x hx y))
  · simpa [Kernel.piecewise_apply, hx] using (IsZeroLeft.zero_left_le β (l y)).trans zero_le

/-- Only the cost on a set `T` carrying all of `μ` matters, at any grades. -/
theorem CodensityG.concentrated_L [Δ.IsZeroLeft] {α : ι} {δ : ℝ≥0∞} {G : X → Y → ι}
    {E E' : X → Y → ℝ≥0∞} {μ : Measure X} {ν : Measure Y} {T : Set X} (hT : MeasurableSet T)
    (hμ : μ Tᶜ = 0) (h : Δ.CodensityG α δ G E μ ν) (hE : ∀ x ∈ T, ∀ y, E' x y ≤ E x y) :
    Δ.CodensityG α δ G E' μ ν := by
  classical
  intro I _ β γ k l _ _ hkl
  have hk : Kernel.piecewise hT k 0 ∘ₘ μ = k ∘ₘ μ := comp_congr <| by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμ] with x hx
    simp [Kernel.piecewise_apply, not_not.1 hx]
  rw [← hk]
  refine h fun x y ↦ ?_
  by_cases hx : x ∈ T
  · simpa [Kernel.piecewise_apply, hx] using (hkl x y).trans (add_le_add le_rfl (hE x hx y))
  · simpa [Kernel.piecewise_apply, hx] using (IsZeroLeft.zero_left_le _ (l y)).trans zero_le

/-- Strengthen the relation with `x ∈ T` for a set `T` carrying all of `μ`. -/
theorem Codensity.concentrated_L [Δ.IsZeroLeft] {α : ι} {δ : ℝ≥0∞} {R : Set (X × Y)}
    {μ : Measure X} {ν : Measure Y} {T : Set X} (hT : MeasurableSet T) (hμ : μ Tᶜ = 0)
    (h : Δ.Codensity α δ R μ ν) : Δ.Codensity α δ {p | p ∈ R ∧ p.1 ∈ T} μ ν :=
  CodensityE.concentrated_L hT hμ h fun x hx y ↦ by
    by_cases hxy : (x, y) ∈ R
    · simp [relCost_of_mem (show (x, y) ∈ {p | p ∈ R ∧ p.1 ∈ T} from ⟨hxy, hx⟩)]
    · simp [relCost_of_notMem hxy]

/-- A Dirac measure lifts against a probability measure carried by `S`, relating its point to
`S`. -/
theorem codensity_dirac_left [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] {Y : Type u}
    [MeasurableSpace Y] {S : Set Y} (hS : MeasurableSet S) {ν : Measure Y}
    [IsProbabilityMeasure ν] (hν : ν Sᶜ = 0) (x₀ : X) :
    Δ.Codensity 1 0 {p | p.1 = x₀ ∧ p.2 ∈ S} (dirac x₀) ν := by
  have h := ((codensity_diag_of_le (IsReflexive.self_le_zero (Δ := Δ) ν)).concentrated_L hS
    hν).map (f := fun _ ↦ x₀) (g := id) (S := {p | p.1 = x₀ ∧ p.2 ∈ S})
    fun _ _ hxy ↦ ⟨rfl, hxy.1 ▸ hxy.2⟩
  rwa [Measure.map_const, measure_univ, one_smul, map_id] at h

/-- A probability measure carried by `S` lifts against a Dirac measure, relating `S` to its
point. -/
theorem codensity_dirac_right [Δ.IsReflexive] [Δ.IsComposable] [Δ.IsZeroLeft] {X : Type u}
    [MeasurableSpace X] {S : Set X} (hS : MeasurableSet S) {μ : Measure X}
    [IsProbabilityMeasure μ] (hμ : μ Sᶜ = 0) (y₀ : Y) :
    Δ.Codensity 1 0 {p | p.1 ∈ S ∧ p.2 = y₀} μ (dirac y₀) := by
  have h := ((codensity_diag_of_le (IsReflexive.self_le_zero (Δ := Δ) μ)).concentrated_L hS
    hμ).map (f := id) (g := fun _ ↦ y₀) (S := {p | p.1 ∈ S ∧ p.2 = y₀})
    fun _ _ hxy ↦ ⟨hxy.2, rfl⟩
  rwa [Measure.map_const, measure_univ, one_smul, map_id] at h

/-! ### Paying costs in expectation -/

variable (Δ) in
/-- A cost on the right sample may be paid in expectation (cf. `AddCoupl.bind_adv`); this is a
stopgap property of the lifting, pending a property of `Δ` itself. -/
class IsExpectationAdditive : Prop where
  add_right {α : ι} {δ : ℝ≥0∞} {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]
    {E : X → Y → ℝ≥0∞} {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ]
    (h : Δ.CodensityE α δ E μ ν) {c : Y → ℝ≥0∞} (hc : Measurable c) :
    Δ.CodensityE α (δ + ∫⁻ y, c y ∂ν) (fun x y ↦ E x y + c y) μ ν

/-- A measurable cost on the right sample may be paid in expectation. -/
theorem CodensityE.add_right [Δ.IsExpectationAdditive] {α : ι} {δ : ℝ≥0∞} {X Y : Type u}
    [MeasurableSpace X] [MeasurableSpace Y] {E : X → Y → ℝ≥0∞} {μ : Measure X} {ν : Measure Y}
    [IsSubProbabilityMeasure μ] (h : Δ.CodensityE α δ E μ ν) {c : Y → ℝ≥0∞}
    (hc : Measurable c := by fun_prop) :
    Δ.CodensityE α (δ + ∫⁻ y, c y ∂ν) (fun x y ↦ E x y + c y) μ ν :=
  IsExpectationAdditive.add_right h hc

/-- Binding with continuations whose bound `E₂ y` depends on the right sample, paying only its
expectation (cf. `AddCoupl.bind_adv`). -/
theorem Codensity.bind_adv [Δ.IsExpectationAdditive] {α α' : ι} {δ δ' : ℝ≥0∞} {X Y : Type u}
    [MeasurableSpace X] [MeasurableSpace Y] {S : Set (X × Y)} {T : Set (X' × Y')}
    {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ] (h : Δ.Codensity α δ S μ ν)
    {f : X → Measure X'} {g : Y → Measure Y'} [∀ x, IsSubProbabilityMeasure (f x)]
    [∀ y, IsSubProbabilityMeasure (g y)] {E₂ : Y → ℝ≥0∞} (hE₂ : ∫⁻ y, E₂ y ∂ν ≤ δ')
    (hfg : ∀ ⦃x y⦄, (x, y) ∈ S → Δ.Codensity α' (E₂ y) T (f x) (g y))
    (hf : Measurable f := by fun_prop) (hg : Measurable g := by fun_prop)
    (hE : Measurable E₂ := by fun_prop) :
    Δ.Codensity (α * α') (δ + δ') T (μ.bind f) (ν.bind g) :=
  ((CodensityE.add_right h hE).mono_bound (add_le_add_right hE₂ δ)).bind_fun (fun x y ↦ by
      by_cases hxy : (x, y) ∈ S
      · simpa [relCost_of_mem hxy] using hfg hxy
      · simp [relCost_of_notMem hxy, Codensity, codensityE_top]) hf hg

end GradedDivergence
