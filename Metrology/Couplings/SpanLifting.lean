module

public import Metrology.Couplings.Codensity

/-! The span lifting of a graded divergence (Approximate Span Liftings, Def. 5.1). -/

@[expose] public section

universe u v

open MeasureTheory Measure ProbabilityTheory GradedLifting
open scoped ENNReal

namespace GradedDivergence

variable {B : Type v} {D : GradedDivergence.{u} B} {X Y X' Y' : Type u} [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace X'] [MeasurableSpace Y'] {b : B} {R : X → Y → B}
  {μ : Measure X} {ν : Measure Y}

variable (D) in
/-- The span lifting: a pair of witnesses within budget `g₁` on a set `S` of pairs where the
leftover is finite and at most `g₂`, with left marginal `μ`, right marginal below `ν`, and
`g₁ + g₂ ≤ b` (Rocq `span_top_head`). -/
def spanLifting [Add B] [LE B] [LT B] [Top B] : GradedLifting.{u} B :=
  fun b {X Y} _ _ R μ ν ↦ ∃ (S : Set (X × Y)) (g₁ g₂ : B), g₁ + g₂ ≤ b ∧
    (∀ z ∈ S, R z.1 z.2 < ⊤ ∧ R z.1 z.2 ≤ g₂) ∧
    ∃ p q : Measure S, IsSubProbabilityMeasure p ∧ IsSubProbabilityMeasure q ∧ D g₁ p q ∧
      p.map (fun z ↦ z.1.1) = μ ∧ q.map (fun z ↦ z.1.2) ≤ ν

/-! ## Structural laws -/

/-- Dirac masses are span-lifted by any reflexive pair with finite grade. -/
theorem spanLifting_dirac [AddZeroClass B] [Preorder B] [Top B] [D.IsReflexive] {x : X} {y : Y}
    (h : R x y < ⊤) : D.spanLifting (R x y) R (dirac x) (dirac y) := by
  refine ⟨{(x, y)}, 0, R x y, (zero_add _).le, fun z hz ↦ ?_, dirac ⟨(x, y), rfl⟩,
    dirac ⟨(x, y), rfl⟩, inferInstance, inferInstance, IsReflexive.refl _, ?_, ?_⟩
  · obtain rfl := hz
    exact ⟨h, le_rfl⟩
  · rw [map_dirac' (by fun_prop)]
  · rw [map_dirac' (by fun_prop)]

/-- Zero measures are span-lifted at every grade. -/
theorem spanLifting_zero [AddZeroClass B] [Preorder B] [CanonicallyOrderedAdd B] [Top B]
    [D.IsReflexive] (b : B) (R : X → Y → B) :
    D.spanLifting b R (0 : Measure X) (0 : Measure Y) :=
  ⟨∅, 0, 0, (zero_add _).trans_le zero_le, fun _ ↦ False.elim, 0, 0, inferInstance,
    inferInstance, IsReflexive.refl _, Measure.map_zero _, (Measure.map_zero _).le⟩

/-- Span lifting is monotone in the grade and antitone in the relation. -/
theorem spanLifting_mono [Add B] [Preorder B] [Top B] {b' : B} {R' : X → Y → B}
    (h : D.spanLifting b R μ ν) (hb : b ≤ b') (hR : R' ≤ R) : D.spanLifting b' R' μ ν := by
  obtain ⟨S, g₁, g₂, hg, hS, w⟩ := h
  exact ⟨S, g₁, g₂, hg.trans hb, fun z hz ↦
    ⟨(hR _ _).trans_lt (hS z hz).1, (hR _ _).trans (hS z hz).2⟩, w⟩

/-- Framing needs finite budgets to stay finite under addition, which product and function
budgets break: `(⊤, 0) + (0, ⊤) = ⊤`. -/
theorem spanLifting_frame [AddSemigroup B] [Preorder B] [AddRightMono B] [Top B] {c : B}
    (hB : ∀ a, a < ⊤ → a + c < ⊤) (h : D.spanLifting b R μ ν) :
    D.spanLifting (b + c) (fun x y ↦ R x y + c) μ ν := by
  obtain ⟨S, g₁, g₂, hg, hS, w⟩ := h
  refine ⟨S, g₁, g₂ + c, ?_, fun z hz ↦ ⟨hB _ (hS z hz).1, add_le_add_left (hS z hz).2 c⟩, w⟩
  rw [← add_assoc]
  exact add_le_add_left hg c

/-- Witnesses move to the image of their support. -/
theorem spanLifting_map [AddZeroClass B] [LE B] [LT B] [Top B] [D.IsReflexive] [D.IsComposable]
    {R : X' → Y' → B} {f : X → X'} {g : Y → Y'} (hf : Measurable f) (hg : Measurable g)
    (h : D.spanLifting b (fun x y ↦ R (f x) (g y)) μ ν) :
    D.spanLifting b R (μ.map f) (ν.map g) := by
  obtain ⟨S, g₁, g₂, hb, hS, p, q, _, _, hpq, rfl, hq⟩ := h
  let φ : S → Prod.map f g '' S := fun z ↦ ⟨Prod.map f g z, Set.mem_image_of_mem _ z.2⟩
  have hφ : Measurable φ := ((hf.prodMap hg).comp measurable_subtype_coe).subtype_mk
  refine ⟨_, g₁, g₂, hb, ?_, p.map φ, q.map φ, inferInstance, inferInstance,
    IsComposable.map hpq hφ, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hS z hz
  · rw [map_map (by fun_prop) hφ, map_map hf (by fun_prop)]
    rfl
  · rw [map_map (by fun_prop) hφ]
    exact (map_map hg (by fun_prop) (μ := q)).symm.trans_le (map_mono hq hg)

/-- Spans are lawful once finite budgets stay finite under addition. -/
theorem isLawful_spanLifting [AddMonoid B] [Preorder B] [AddRightMono B] [CanonicallyOrderedAdd B]
    [Top B] [D.IsReflexive] [D.IsComposable] (hB : ∀ a c : B, a < ⊤ → c < ⊤ → a + c < ⊤) :
    D.spanLifting.IsLawful where
  pure := spanLifting_dirac
  zero := spanLifting_zero
  mono := spanLifting_mono
  frame hc := spanLifting_frame fun a ha ↦ hB a _ ha hc
  map := spanLifting_map

/-! ## Soundness and the codensity lifting -/

/-- A span of equality is supported on the diagonal, so both marginals come from one witness. -/
instance isSound_spanLifting [AddZeroClass B] [Preorder B] [CanonicallyOrderedAdd B] [Top B]
    [D.IsGraded] [D.IsReflexive] [D.IsComposable] [D.IsRightMonotone] :
    D.spanLifting.IsSound D where
  sound {X} _ b μ ν _ _ h := by
    obtain ⟨S, g₁, g₂, hb, hS, p, q, _, _, hpq, rfl, hq⟩ := h
    have hdiag : (fun z : S ↦ z.1.1) = fun z ↦ z.1.2 := funext fun z ↦ by
      by_contra hz
      exact (relCost_of_not (B := B) hz ▸ (hS z z.2).1).false
    have := IsComposable.map (f := fun z : S ↦ z.1.1) hpq (by fun_prop)
    rw [congrArg q.map hdiag] at this
    exact IsGraded.mono (le_self_add.trans hb) (IsRightMonotone.right_mono hq this)

/-- Spans lie below the codensity lifting: a test pulled back to the witnesses' support composes
with the witnesses, and the right marginal grows to `ν` (Rocq `cod_of_witness`). -/
theorem spanLifting_le_codensity [AddSemigroup B] [Preorder B] [AddRightMono B] [Top B]
    [D.IsGraded] [D.IsComposable] [D.IsRightMonotone] [IsSubProbabilityMeasure ν]
    (h : D.spanLifting b R μ ν) : D.codensity b R μ ν := by
  obtain ⟨S, g₁, g₂, hb, hS, p, q, _, _, hpq, rfl, hq⟩ := h
  intro I _ c _ k l _ _ hkl
  have hcomp : D (g₁ + (g₂ + c)) (k ∘ₘ p.map fun z ↦ z.1.1) (l ∘ₘ q.map fun z ↦ z.1.2) := by
    rw [bind_map_eq p (by fun_prop) k.measurable, bind_map_eq q (by fun_prop) l.measurable]
    exact IsComposable.comp (κ := k.comap (fun z : S ↦ z.1.1) (by fun_prop))
      (η := l.comap (fun z : S ↦ z.1.2) (by fun_prop)) hpq fun z ↦
      IsGraded.mono (add_le_add_left (hS z z.2).2 c) (hkl z.1.1 z.1.2)
  rw [← add_assoc] at hcomp
  exact IsRightMonotone.right_mono (bind_mono_left hq l.measurable)
    (IsGraded.mono (add_le_add_left hb c) hcomp)

/-! ## No absorbing budget, no lawfulness at product budgets -/

/-- Spans have no absorbing budget: the leftover `⊤` leaves no support for a witness. -/
theorem not_absorbing_spanLifting [Add B] [Preorder B] [Top B] (b : B) :
    ¬D.spanLifting.Absorbing b := fun h ↦ by
  obtain ⟨S, _, _, _, hS, p, _, _, _, _, hp, _⟩ :=
    h (fun _ _ ↦ (⊤ : B)) (dirac PUnit.unit.{u + 1}) (dirac PUnit.unit.{u + 1})
  have : IsEmpty S := ⟨fun z ↦ (hS z z.2).1.false⟩
  rw [p.eq_zero_of_isEmpty, Measure.map_zero] at hp
  exact dirac_ne_zero hp.symm

/-- Spans are not lawful at product budgets: framing `(⊤, 0)` by `(0, ⊤)` reaches `⊤`. -/
theorem not_isLawful_spanLifting_prod (D : GradedDivergence.{u} (ℝ≥0∞ × ℝ≥0∞))
    [D.IsReflexive] : ¬D.spanLifting.IsLawful := fun hL ↦ by
  let R : PUnit.{u + 1} → PUnit.{u + 1} → ℝ≥0∞ × ℝ≥0∞ := fun _ _ ↦ (⊤, 0)
  have h0 := hL.pure (R := R) (x := PUnit.unit) (y := PUnit.unit) (by simp [R, Prod.lt_iff])
  have h1 := hL.frame (c := ((0, ⊤) : ℝ≥0∞ × ℝ≥0∞)) (by simp [Prod.lt_iff]) h0
  obtain ⟨S, _, _, _, hS, p, _, _, _, _, hp, _⟩ := h1
  have : IsEmpty S := ⟨fun z ↦ (hS z z.2).1.ne (by simp [R]; rfl)⟩
  rw [p.eq_zero_of_isEmpty, Measure.map_zero] at hp
  exact dirac_ne_zero hp.symm

end GradedDivergence
