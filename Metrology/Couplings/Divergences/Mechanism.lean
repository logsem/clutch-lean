module

public import Metrology.Couplings.Divergences.Conversions

/-! Mechanisms and their privacy (Approximate Span Liftings, §2, Defs. 2.1–2.5).
Generic `Kernel.IsPrivate` with DP/RDP/zCDP/tCDP as instances, its post-processing and composition
laws, privacy as a lifting of equality (`isPrivate_iff_rel`), and the Fig. 4 conversions. -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory GradedDivergence GradedLifting Real
open scoped ENNReal

/-- A randomized algorithm: a kernel from inputs to distributions on outputs. -/
abbrev Mechanism (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] := Kernel X Y

/-- An adjacency relation on inputs. -/
abbrev Adjacency (X : Type*) := X → X → Prop

-- In `Kernel`, not `Mechanism`, so that `(m.map f).DP` and `(m ⊗ₖ k).IsPrivate` elaborate.
namespace ProbabilityTheory.Kernel

variable {X : Type*} {Y Z : Type u} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {B : Type v} {D : GradedDivergence.{u} B} {adj : Adjacency X} {b c : B}

/-- A mechanism is `b`-private for `D` when its outputs on adjacent inputs are within `b`. -/
def IsPrivate (m : Kernel X Y) (D : GradedDivergence.{u} B) (adj : Adjacency X) (b : B) : Prop :=
  ∀ ⦃x x'⦄, adj x x' → D b (m x) (m x')

/-- `(ε, δ)`-differential privacy (Def. 2.1). -/
abbrev DP (m : Kernel X Y) (adj : Adjacency X) (ε δ : ℝ≥0∞) : Prop :=
  m.IsPrivate dp adj (ε, δ)

/-- `(α, ρ)`-Rényi differential privacy (Def. 2.3). -/
abbrev RDP (m : Kernel X Y) (adj : Adjacency X) (α : ℝ) (ρ : ℝ≥0∞) : Prop :=
  m.IsPrivate (renyiDivergence α) adj ρ

/-- `(ξ, ρ)`-zero-concentrated differential privacy (Def. 2.4). -/
abbrev zCDP (m : Kernel X Y) (adj : Adjacency X) (ξ ρ : ℝ≥0∞) : Prop :=
  m.IsPrivate zcdpDivergence adj (ξ, ρ)

/-- `ρ`-truncated concentrated differential privacy up to order `ω` (Def. 2.5). -/
abbrev tCDP (m : Kernel X Y) (adj : Adjacency X) (ω : ℝ) (ρ : ℝ≥0∞) : Prop :=
  m.IsPrivate (tcdpDivergence ω) adj ρ

variable {m : Kernel X Y} {α ω : ℝ} {ε ξ ρ : ℝ≥0∞}

/-! ## Unfoldings -/

/-- Mechanism-level `(ε, δ)`-DP, stated on measurable sets. -/
theorem DP_iff {δ : ℝ≥0∞} (hε : ε ≠ ⊤) :
    m.DP adj ε δ ↔ ∀ ⦃x x'⦄, adj x x' → ∀ S, MeasurableSet S → m x S ≤ expBudget ε * m x' S + δ :=
  forall₃_congr fun _ _ _ ↦ dp_iff hε

/-- Mechanism-level RDP at a finite budget, stated on moments. -/
theorem RDP_iff (hα : 1 ≤ α) (hρ : ρ ≠ ⊤) :
    m.RDP adj α ρ ↔ ∀ ⦃x x'⦄, adj x x' →
      fDiv (· ^ α) (m x) (m x') ≤ ((exp ((α - 1) * ρ.toReal) : ℝ) : EReal) :=
  forall₃_congr fun _ _ _ ↦ renyiDivergence_iff_of_ne_top hα hρ

/-- Mechanism-level zCDP is RDP on the line `ξ + α ρ` at every order (Def. 2.4). -/
theorem zCDP_iff :
    m.zCDP adj ξ ρ ↔ ∀ ⦃x x'⦄, adj x x' → ∀ α, 1 < α →
      renyiDivergence α (ξ + ENNReal.ofReal α * ρ) (m x) (m x') :=
  forall₃_congr fun _ _ _ ↦ zcdpDivergence_iff

/-- Mechanism-level tCDP is RDP on the line `α ρ` at every order below `ω` (Def. 2.5). -/
theorem tCDP_iff :
    m.tCDP adj ω ρ ↔ ∀ ⦃x x'⦄, adj x x' → ∀ α, 1 < α → α < ω →
      renyiDivergence α (ENNReal.ofReal α * ρ) (m x) (m x') :=
  forall₃_congr fun _ _ _ ↦ tcdpDivergence_iff

/-! ## Laws of privacy -/

/-- Privacy at a budget gives privacy at every larger budget. -/
theorem IsPrivate.mono [LE B] [Top B] [D.IsGraded] [IsSubMarkovKernel m]
    (h : m.IsPrivate D adj b) {b' : B} (hb : b ≤ b') : m.IsPrivate D adj b' :=
  fun _ _ hx ↦ IsGraded.mono hb (h hx)

/-- Post-processing by a kernel keeps privacy. -/
theorem IsPrivate.comp [AddZeroClass B] [D.IsReflexive] [D.IsComposable] [IsSubMarkovKernel m]
    (h : m.IsPrivate D adj b) (k : Kernel Y Z) [IsSubMarkovKernel k] :
    (k ∘ₖ m).IsPrivate D adj b :=
  fun _ _ hx ↦ by simpa only [Kernel.comp_apply] using IsComposable.comp_self k (h hx)

/-- Post-processing by a measurable map keeps privacy. -/
theorem IsPrivate.map [AddZeroClass B] [D.IsReflexive] [D.IsComposable] [IsSubMarkovKernel m]
    (h : m.IsPrivate D adj b) {f : Y → Z} (hf : Measurable f := by fun_prop) :
    (m.map f).IsPrivate D adj b :=
  fun _ _ hx ↦ by simpa only [Kernel.map_apply _ hf] using IsComposable.map (h hx) hf

/-- Adaptive composition adds budgets: a second mechanism that sees the first output is private
for each fixed first output. -/
theorem IsPrivate.compProd [AddZeroClass B] [D.IsReflexive] [D.IsComposable]
    [IsSubMarkovKernel m] (h : m.IsPrivate D adj b) {k : Kernel (X × Y) Z} [IsSubMarkovKernel k]
    (hk : ∀ y, (k.sectL y).IsPrivate D adj c) : (m ⊗ₖ k).IsPrivate D adj (b + c) := by
  intro x x' hx
  rw [Kernel.compProd_apply_eq_compProd_sectR, Kernel.compProd_apply_eq_compProd_sectR,
    compProd_eq_comp_prod, compProd_eq_comp_prod]
  refine IsComposable.comp (h hx) fun y ↦ ?_
  simpa [Kernel.prod_apply, Kernel.id_apply, dirac_prod] using
    IsComposable.map (f := Prod.mk y) (hk y hx)

/-- DP composes along chains of adjacent inputs (group privacy). -/
theorem DP.trans {adj' : Adjacency X} {ε₁ ε₂ δ₁ δ₂ : ℝ≥0∞} (h₁ : m.DP adj ε₁ δ₁)
    (h₂ : m.DP adj' ε₂ δ₂) :
    m.DP (Relation.Comp adj adj') (ε₁ + ε₂) (expBudget ε₁ * δ₂ + δ₁) :=
  fun _ _ ⟨_, hx, hx'⟩ ↦ dp_trans (h₁ hx) (h₂ hx')

/-! ## Privacy as a lifting of equality -/

/-- A mechanism is private exactly when a sound and complete lifting relates adjacent outputs
along equality. -/
theorem isPrivate_iff_rel [Zero B] [Top B] (L : GradedLifting.{u} B) [L.IsSound D]
    [L.IsComplete D] [IsSubMarkovKernel m] :
    m.IsPrivate D adj b ↔ ∀ ⦃x x'⦄, adj x x' → L.Rel b (· = ·) (m x) (m x') :=
  ⟨fun h _ _ hx ↦ IsComplete.complete (h hx), fun h _ _ hx ↦ IsSound.sound (h hx)⟩

/-- A mechanism is private exactly when it relates adjacent outputs in the codensity lifting of
equality (Thm. 5.2). -/
theorem isPrivate_iff_codensity_rel [AddZeroClass B] [Preorder B] [CanonicallyOrderedAdd B]
    [OrderTop B] [D.IsGraded] [D.IsReflexive] [D.IsComposable] [IsSubMarkovKernel m] :
    m.IsPrivate D adj b ↔ ∀ ⦃x x'⦄, adj x x' → (codensity D).Rel b (· = ·) (m x) (m x') :=
  isPrivate_iff_rel (codensity D)

/-- A mechanism is zCDP exactly when the zCDP lifting relates adjacent outputs along equality. -/
theorem zCDP_iff_zcdpLifting_rel [IsSubMarkovKernel m] :
    m.zCDP adj ξ ρ ↔ ∀ ⦃x x'⦄, adj x x' → zcdpLifting.Rel (ξ, ρ) (· = ·) (m x) (m x') :=
  isPrivate_iff_rel _

/-- A mechanism is tCDP exactly when the tCDP lifting relates adjacent outputs along equality. -/
theorem tCDP_iff_tcdpLifting_rel [IsSubMarkovKernel m] :
    m.tCDP adj ω ρ ↔ ∀ ⦃x x'⦄, adj x x' → (tcdpLifting ω).Rel ρ (· = ·) (m x) (m x') :=
  isPrivate_iff_rel _

/-! ## Conversions (Fig. 4) -/

variable {δ : ℝ}

/-- Pure differential privacy gives zero-concentrated differential privacy ([D/z]). -/
theorem zCDP_of_DP [IsSubMarkovKernel m] (h : m.DP adj ε 0) : m.zCDP adj ε 0 :=
  fun _ _ hx ↦ zcdp_of_dp (h hx)

/-- zCDP gives Rényi differential privacy at every order (Def. 2.4). -/
theorem RDP_of_zCDP (hα : 1 < α) (h : m.zCDP adj ξ ρ) :
    m.RDP adj α (ξ + ENNReal.ofReal α * ρ) :=
  fun _ _ hx ↦ renyi_of_zcdp hα (h hx)

/-- tCDP gives Rényi differential privacy at every order below `ω` (Def. 2.5). -/
theorem RDP_of_tCDP (hα : 1 < α) (hω : α < ω) (h : m.tCDP adj ω ρ) :
    m.RDP adj α (ENNReal.ofReal α * ρ) :=
  fun _ _ hx ↦ renyi_of_tcdp hα hω (h hx)

/-- Rényi differential privacy gives differential privacy at every slack `δ > 0` ([R/D]). -/
theorem DP_of_RDP [IsFiniteKernel m] (hα : 1 < α) (hδ : 0 < δ) (h : m.RDP adj α ρ) :
    m.DP adj (ρ + ENNReal.ofReal (log (1 / δ) / (α - 1))) (ENNReal.ofReal δ) :=
  fun _ _ hx ↦ dp_of_renyi hα hδ (h hx)

/-- zCDP gives differential privacy at every slack `0 < δ < 1` ([z/D]). -/
theorem DP_of_zCDP [IsFiniteKernel m] (hδ : 0 < δ) (hδ₁ : δ < 1) (h : m.zCDP adj ξ ρ) :
    m.DP adj (ξ + ρ + ENNReal.ofReal (2 * √(ρ.toReal * log (1 / δ)))) (ENNReal.ofReal δ) :=
  fun _ _ hx ↦ dp_of_zcdp hδ hδ₁ (h hx)

/-- tCDP gives differential privacy at every slack `0 < δ < 1`, at the order
`β = min ω (1 + √(log (1 / δ) / ρ))` ([t/D]). -/
theorem DP_of_tCDP [IsFiniteKernel m] (hρ : 0 < ρ) (hω : 1 < ω) (hδ : 0 < δ) (hδ₁ : δ < 1)
    (h : m.tCDP adj ω ρ) :
    m.DP adj (ρ * ENNReal.ofReal (min ω (1 + √(log (1 / δ) / ρ.toReal))) +
      ENNReal.ofReal (log (1 / δ) / (min ω (1 + √(log (1 / δ) / ρ.toReal)) - 1)))
      (ENNReal.ofReal δ) :=
  fun _ _ hx ↦ dp_of_tcdp hρ hω hδ hδ₁ (h hx)

end ProbabilityTheory.Kernel
