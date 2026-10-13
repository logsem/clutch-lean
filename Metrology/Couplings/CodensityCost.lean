module

public import Metrology.Couplings.CodensityTV

/-! Cost-graded codensity liftings: the relation of `Codensity` becomes a cost charged on top of
the test slack, so that `ExpCoupl` is the total variation instance and `AddCoupl.bind_adv_kanto`
is the bind law. -/

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
theorem relCost_of_mem {R : Set (X × Y)} {x : X} {y : Y} (h : (x, y) ∈ R) : relCost R x y = 0 :=
  Set.indicator_of_notMem (not_not.2 h) _

omit [MeasurableSpace X] [MeasurableSpace Y] in
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
    Δ.CodensityE α (δ + c) (fun x y ↦ E x y + c) μ ν := by
  intro I _ β γ k l _ _ hkl
  calc Δ (α * β) (k ∘ₘ μ) (l ∘ₘ ν) ≤ δ + (γ + c) :=
        h fun x y ↦ (hkl x y).trans_eq (by ring)
    _ = δ + c + γ := by rw [add_comm γ, add_assoc]

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
  have : IsSubMarkovKernel (Kernel.piecewise hT k 0) :=
    ⟨fun x ↦ by rw [Kernel.piecewise_apply]; split_ifs <;> infer_instance⟩
  have hk : Kernel.piecewise hT k 0 ∘ₘ μ = k ∘ₘ μ := comp_congr <| by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμ] with x hx
    simp [Kernel.piecewise_apply, not_not.1 hx]
  rw [← hk]
  refine h fun x y ↦ ?_
  by_cases hx : x ∈ T
  · simpa [Kernel.piecewise_apply, hx] using (hkl x y).trans (add_le_add le_rfl (hE x hx y))
  · simpa [Kernel.piecewise_apply, hx] using (IsZeroLeft.zero_left_le β (l y)).trans zero_le

end GradedDivergence

/-! ### The total variation instance is `ExpCoupl` -/

open GradedDivergence TVDiv

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {δ : ℝ≥0∞} {E : X → Y → ℝ≥0∞}
  {μ : Measure X} {ν : Measure Y}

/-- Measures in the total variation cost lifting are coupled in expectation. -/
theorem GradedDivergence.CodensityE.expCoupl (h : tv.{u}.CodensityE () δ E μ ν) :
    ExpCoupl δ E μ ν := by
  intro f g hf hg hf1 hg1 hfg
  have := isSubMarkovKernel_massKernel.{u} hf hf1
  have := isSubMarkovKernel_massKernel.{u} hg hg1
  have hc := h (β := ()) (γ := 0) (k := massKernel.{u} hf) (l := massKernel.{u} hg)
    fun x y ↦ tv_le_iff.2 fun S _ ↦ by
      rcases Set.eq_empty_or_nonempty S with rfl | ⟨⟨⟩, hS⟩
      · simp
      · simpa [massKernel, hS] using hfg x y
  simpa using tv_le_iff.1 hc .univ .univ

/-- A coupling in expectation is in the total variation cost lifting. -/
theorem ExpCoupl.codensityE [IsSubProbabilityMeasure μ] (h : ExpCoupl δ E μ ν) :
    tv.{u}.CodensityE () δ E μ ν := by
  intro I _ β γ k l _ _ hkl
  refine tv_le_iff.2 fun S hS ↦ ?_
  have hkS := k.measurable_coe hS
  have hfg := h (fun x ↦ k x S - γ) (fun y ↦ l y S) (hkS.sub measurable_const)
    (l.measurable_coe hS) (fun _ ↦ tsub_le_self.trans (IsSubProbabilityMeasure.measure_le_one S))
    (fun _ ↦ IsSubProbabilityMeasure.measure_le_one S)
    fun x y ↦ tsub_le_iff_right.2 <| (tv_le_iff.1 (hkl x y) S hS).trans_eq (by ring)
  rw [bind_apply hS k.measurable.aemeasurable, bind_apply hS l.measurable.aemeasurable]
  calc ∫⁻ x, k x S ∂μ
      ≤ ∫⁻ x, (k x S - γ) + γ ∂μ := lintegral_mono fun _ ↦ le_tsub_add
    _ ≤ ∫⁻ x, k x S - γ ∂μ + γ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
        gcongr
        exact mul_le_of_le_one_right' IsSubProbabilityMeasure.measure_univ_le_one
    _ ≤ ∫⁻ y, l y S ∂ν + (δ + γ) := by
        rw [← add_assoc]
        exact add_le_add_left hfg γ

/-- Couplings in expectation are exactly the total variation cost lifting. -/
theorem expCoupl_iff_codensityE [IsSubProbabilityMeasure μ] :
    ExpCoupl δ E μ ν ↔ tv.{u}.CodensityE () δ E μ ν :=
  ⟨ExpCoupl.codensityE, CodensityE.expCoupl⟩

/-- For total variation, a measurable cost on the right sample may be paid in expectation; this
uses linearity of tests, so it is specific to total variation (cf. `AddCoupl.bind_adv`). -/
theorem GradedDivergence.CodensityE.tv_add_right [IsSubProbabilityMeasure μ]
    (h : tv.{u}.CodensityE () δ E μ ν) {c : Y → ℝ≥0∞} (hc : Measurable c := by fun_prop) :
    tv.{u}.CodensityE () (δ + ∫⁻ y, c y ∂ν) (fun x y ↦ E x y + c y) μ ν := by
  refine ExpCoupl.codensityE fun f g hf hg hf1 hg1 hfg ↦ ?_
  calc ∫⁻ x, f x ∂μ
      ≤ ∫⁻ y, min (g y + c y) 1 ∂ν + δ :=
        h.expCoupl f _ hf ((hg.add hc).min measurable_const) hf1 (fun _ ↦ min_le_right _ _)
          fun x y ↦ by
            rcases le_total (g y + c y) 1 with hle | hle
            · rw [min_eq_left hle]
              exact (hfg x y).trans_eq (by ring)
            · exact (hf1 x).trans (by rw [min_eq_right hle]; exact le_self_add)
    _ ≤ ∫⁻ y, g y + c y ∂ν + δ := by gcongr with y; exact min_le_left _ _
    _ = ∫⁻ y, g y ∂ν + (δ + ∫⁻ y, c y ∂ν) := by
        rw [lintegral_add_right _ hc]; ring
