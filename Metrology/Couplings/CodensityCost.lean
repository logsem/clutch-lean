module

public import Metrology.Couplings.CodensityLifting

/-! Cost-graded codensity liftings: the relation of `Codensity` becomes a cost charged on top of
the test slack, so that `ExpCoupl` is the total variation instance (`CodensityTV.lean`) and
`AddCoupl.bind_adv_kanto` is the bind law. -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal

namespace GradedDivergence

variable {ι : Type v} [Monoid ι] {Δ : GradedDivergence.{u} ι}
variable {X Y X' Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X']
  [MeasurableSpace Y']

variable (Δ) in
/-- The cost-graded codensity lifting: kernels whose outputs at `x, y` are `Δ`-close up to the
slack plus the cost `E x y` are `Δ`-close after binding, up to the slack plus `δ`. -/
def CodensityE (α : ι) (δ : ℝ≥0∞) (E : X → Y → ℝ≥0∞) (μ : Measure X) (ν : Measure Y) : Prop :=
  ∀ ⦃I : Type u⦄ [MeasurableSpace I] ⦃β : ι⦄ ⦃γ : ℝ≥0∞⦄ ⦃k : Kernel X I⦄ ⦃l : Kernel Y I⦄
    [IsSubMarkovKernel k] [IsSubMarkovKernel l],
    (∀ x y, Δ β (k x) (l y) ≤ γ + E x y) → Δ (α * β) (k ∘ₘ μ) (l ∘ₘ ν) ≤ δ + γ

/-- The cost of a relation: free on it, infinite off it. -/
noncomputable def relCost (R : Set (X × Y)) (x : X) (y : Y) : ℝ≥0∞ := Rᶜ.indicator ⊤ (x, y)

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- A relation costs nothing on its pairs. -/
theorem relCost_of_mem {R : Set (X × Y)} {x : X} {y : Y} (h : (x, y) ∈ R) : relCost R x y = 0 :=
  Set.indicator_of_notMem (not_not.2 h) _

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- A relation costs `⊤` off its pairs. -/
theorem relCost_of_notMem {R : Set (X × Y)} {x : X} {y : Y} (h : (x, y) ∉ R) :
    relCost R x y = ⊤ :=
  Set.indicator_of_mem h _

/-- A relational lifting is the cost lifting of the relation's cost. -/
theorem codensityE_relCost_iff {α : ι} {δ : ℝ≥0∞} {R : Set (X × Y)} {μ : Measure X}
    {ν : Measure Y} : Δ.CodensityE α δ (relCost R) μ ν ↔ Δ.Codensity α δ R μ ν := by
  refine ⟨fun h I _ β γ k l _ _ hkl ↦ h fun x y ↦ ?_, fun h I _ β γ k l _ _ hkl ↦
    h fun x y hxy ↦ by simpa [relCost_of_mem hxy] using hkl x y⟩
  by_cases hxy : (x, y) ∈ R
  · simpa [relCost_of_mem hxy] using hkl hxy
  · simp [relCost_of_notMem hxy]

/-! ### Monotonicity and shifts -/

/-- Larger bounds give larger liftings. -/
theorem CodensityE.mono_bound {α : ι} {δ δ' : ℝ≥0∞} {E : X → Y → ℝ≥0∞} {μ : Measure X}
    {ν : Measure Y} (h : Δ.CodensityE α δ E μ ν) (hδ : δ ≤ δ') : Δ.CodensityE α δ' E μ ν :=
  fun _ _ _ _ _ _ _ _ hkl ↦ (h hkl).trans (add_le_add_left hδ _)

/-- Smaller costs give larger liftings. -/
theorem CodensityE.mono_cost {α : ι} {δ : ℝ≥0∞} {E E' : X → Y → ℝ≥0∞} {μ : Measure X}
    {ν : Measure Y} (h : Δ.CodensityE α δ E μ ν) (hE : ∀ x y, E' x y ≤ E x y) :
    Δ.CodensityE α δ E' μ ν :=
  fun _ _ _ _ _ _ _ _ hkl ↦ h fun x y ↦ (hkl x y).trans (add_le_add le_rfl (hE x y))

/-- Adding a constant to the cost adds it to the bound (cf. `expCoupl_add_const` in Approxis). -/
theorem CodensityE.add_const {α : ι} {δ : ℝ≥0∞} {E : X → Y → ℝ≥0∞} {μ : Measure X}
    {ν : Measure Y} (h : Δ.CodensityE α δ E μ ν) (c : ℝ≥0∞) :
    Δ.CodensityE α (δ + c) (fun x y ↦ E x y + c) μ ν :=
  fun _ _ _ γ _ _ _ _ hkl ↦ (h (γ := γ + c) fun x y ↦ (hkl x y).trans_eq (by ring)).trans_eq
    (by ring)

/-- A relational lifting gives the cost lifting of any cost bounded on the relation, paying the
bound (cf. `expCoupl_of_addCoupl` in Approxis). -/
theorem Codensity.codensityE {α : ι} {δ δ' : ℝ≥0∞} {R : Set (X × Y)} {E : X → Y → ℝ≥0∞}
    {μ : Measure X} {ν : Measure Y} (h : Δ.Codensity α δ R μ ν)
    (hE : ∀ ⦃x y⦄, (x, y) ∈ R → E x y ≤ δ') : Δ.CodensityE α (δ + δ') E μ ν :=
  (codensityE_relCost_iff.2 h |>.add_const δ').mono_cost fun x y ↦ by
    by_cases hxy : (x, y) ∈ R
    · simpa [relCost_of_mem hxy] using hE hxy
    · simp [relCost_of_notMem hxy]

/-! ### Kleisli laws -/

/-- Related Dirac measures lift at the unit grade with their cost as the bound. -/
theorem codensityE_dirac {E : X → Y → ℝ≥0∞} (x : X) (y : Y) :
    Δ.CodensityE 1 (E x y) E (dirac x) (dirac y) := by
  intro I _ β γ k l _ _ hkl
  rw [dirac_bind k.measurable, dirac_bind l.measurable, one_mul, add_comm]
  exact hkl x y

/-- Binding with kernels whose outputs at `x, y` are in the cost lifting with bound `E x y`: the
cost is charged once, through the outer lifting (cf. `AddCoupl.bind_adv_kanto`). -/
theorem CodensityE.bind {α α' : ι} {δ : ℝ≥0∞} {E : X → Y → ℝ≥0∞} {F : X' → Y' → ℝ≥0∞}
    {μ : Measure X} {ν : Measure Y} (h : Δ.CodensityE α δ E μ ν) {f : Kernel X X'}
    {g : Kernel Y Y'} [IsSubMarkovKernel f] [IsSubMarkovKernel g]
    (hfg : ∀ x y, Δ.CodensityE α' (E x y) F (f x) (g y)) :
    Δ.CodensityE (α * α') δ F (f ∘ₘ μ) (g ∘ₘ ν) := by
  intro I _ β γ k l _ _ hkl
  rw [comp_assoc, comp_assoc, mul_assoc]
  refine h fun x y ↦ ?_
  rw [Kernel.comp_apply, Kernel.comp_apply, add_comm]
  exact hfg x y hkl

/-- `CodensityE.bind` with a relational continuation. -/
theorem CodensityE.bind_codensity {α α' : ι} {δ : ℝ≥0∞} {E : X → Y → ℝ≥0∞}
    {S : Set (X' × Y')} {μ : Measure X} {ν : Measure Y} (h : Δ.CodensityE α δ E μ ν)
    {f : Kernel X X'} {g : Kernel Y Y'} [IsSubMarkovKernel f] [IsSubMarkovKernel g]
    (hfg : ∀ x y, Δ.Codensity α' (E x y) S (f x) (g y)) :
    Δ.Codensity (α * α') δ S (f ∘ₘ μ) (g ∘ₘ ν) :=
  codensityE_relCost_iff.1 <| h.bind fun x y ↦ codensityE_relCost_iff.2 (hfg x y)

/-- `CodensityE.bind_codensity` for measurable families of subprobability measures. -/
theorem CodensityE.bind_fun {α α' : ι} {δ : ℝ≥0∞} {E : X → Y → ℝ≥0∞} {S : Set (X' × Y')}
    {μ : Measure X} {ν : Measure Y} (h : Δ.CodensityE α δ E μ ν) {f : X → Measure X'}
    {g : Y → Measure Y'} [∀ x, IsSubProbabilityMeasure (f x)]
    [∀ y, IsSubProbabilityMeasure (g y)] (hfg : ∀ x y, Δ.Codensity α' (E x y) S (f x) (g y))
    (hf : Measurable f := by fun_prop) (hg : Measurable g := by fun_prop) :
    Δ.Codensity (α * α') δ S (μ.bind f) (ν.bind g) :=
  have : IsSubMarkovKernel ⟨f, hf⟩ := ⟨fun x ↦ inferInstanceAs (IsSubProbabilityMeasure (f x))⟩
  have : IsSubMarkovKernel ⟨g, hg⟩ := ⟨fun y ↦ inferInstanceAs (IsSubProbabilityMeasure (g y))⟩
  h.bind_codensity (f := ⟨f, hf⟩) (g := ⟨g, hg⟩) hfg

/-- Pushing forward along maps, with the cost pulled back along them. -/
theorem CodensityE.map {α : ι} {δ : ℝ≥0∞} {E : X' → Y' → ℝ≥0∞} {μ : Measure X} {ν : Measure Y}
    {f : X → X'} {g : Y → Y'} (h : Δ.CodensityE α δ (fun x y ↦ E (f x) (g y)) μ ν)
    (hf : Measurable f := by fun_prop) (hg : Measurable g := by fun_prop) :
    Δ.CodensityE α δ E (μ.map f) (ν.map g) := by
  intro I _ β γ k l _ _ hkl
  rw [bind_map_eq μ hf, bind_map_eq ν hg]
  exact h (k := k.comap f hf) (l := l.comap g hg) fun x y ↦ hkl (f x) (g y)

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

/-- Strengthen the relation with `x ∈ T` for a set `T` carrying all of `μ`. -/
theorem Codensity.concentrated_L [Δ.IsZeroLeft] {α : ι} {δ : ℝ≥0∞} {R : Set (X × Y)}
    {μ : Measure X} {ν : Measure Y} {T : Set X} (hT : MeasurableSet T) (hμ : μ Tᶜ = 0)
    (h : Δ.Codensity α δ R μ ν) : Δ.Codensity α δ {p | p ∈ R ∧ p.1 ∈ T} μ ν :=
  codensityE_relCost_iff.1 <| (codensityE_relCost_iff.2 h).concentrated_L hT hμ fun x hx y ↦ by
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
  (((codensityE_relCost_iff.2 h).add_right hE).mono_bound (add_le_add_right hE₂ δ)).bind_fun
    (fun x y ↦ by
      by_cases hxy : (x, y) ∈ S
      · simpa [relCost_of_mem hxy] using hfg hxy
      · exact fun _ _ _ _ _ _ _ _ _ ↦ by simp [relCost_of_notMem hxy]) hf hg

end GradedDivergence
