module

public import Metrology.Couplings.Lifting

/-! Maps between graded liftings and regrading along a budget map (Rocq `morphism.v`,
`regrade.v`). -/

@[expose] public section

universe u v w

open MeasureTheory Measure ProbabilityTheory GradedLifting

/-! ## Homomorphisms -/

/-- A monotone budget map carrying every lifting of `L₁` to a lifting of `L₂`, leftovers
included (Rocq `CouplingMorphism`). -/
structure LiftingHom {B₁ : Type v} {B₂ : Type w} [Preorder B₁] [Preorder B₂]
    (L₁ : GradedLifting.{u} B₁) (L₂ : GradedLifting.{u} B₂) where
  /-- The budget map. -/
  map : B₁ → B₂
  mono : Monotone map
  map_lift {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {b : B₁} {R : X → Y → B₁}
    {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    L₁ b R μ ν → L₂ (map b) (fun x y ↦ map (R x y)) μ ν

/-- A monotone budget map carrying every relational lifting of `L₁` to one of `L₂`: enough when
the map is not additive (Rényi to DP). -/
structure LiftingRelHom {B₁ : Type v} {B₂ : Type w} [Preorder B₁] [Zero B₁] [Top B₁]
    [Preorder B₂] [Zero B₂] [Top B₂] (L₁ : GradedLifting.{u} B₁) (L₂ : GradedLifting.{u} B₂) where
  /-- The budget map. -/
  map : B₁ → B₂
  mono : Monotone map
  map_rel {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {b : B₁} {S : X → Y → Prop}
    {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    L₁.Rel b S μ ν → L₂.Rel (map b) S μ ν

namespace LiftingHom

variable {B₁ : Type v} {B₂ : Type w} {L₁ : GradedLifting.{u} B₁} {L₂ : GradedLifting.{u} B₂}

/-- A homomorphism keeping `⊤` carries relational liftings. -/
def toRelHom [Preorder B₁] [Zero B₁] [Top B₁] [AddZeroClass B₂] [Preorder B₂] [OrderTop B₂]
    [CanonicallyOrderedAdd B₂] [L₂.IsLawful] (F : LiftingHom L₁ L₂) (htop : F.map ⊤ = ⊤) :
    LiftingRelHom L₁ L₂ where
  map := F.map
  mono := F.mono
  map_rel {X Y} _ _ b S μ ν _ _ h := IsLawful.mono (F.map_lift h) le_rfl fun x y ↦ by
    by_cases hS : S x y <;> simp [hS, htop]

end LiftingHom

namespace GradedLifting

/-! ## Regrading -/

variable {B : Type v} {B' : Type w} {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]
  {φ : B' → B} {L : GradedLifting.{u} B}

variable (φ) (L) in
/-- Regrading a lifting along a budget map: budget and leftovers are read through `φ`
(Rocq `GCF_regrade`). -/
def comap : GradedLifting.{u} B' :=
  fun b _ _ _ _ R ↦ L (φ b) fun x y ↦ φ (R x y)

/-- Unfolds the regraded lifting. -/
theorem comap_def {b : B'} {R : X → Y → B'} {μ : Measure X} {ν : Measure Y} :
    L.comap φ b R μ ν ↔ L (φ b) (fun x y ↦ φ (R x y)) μ ν :=
  Iff.rfl

/-- Regrading keeps relations when `φ` keeps `0` and `⊤`. -/
theorem comap_rel_iff [Zero B] [Top B] [Zero B'] [Top B'] (h0 : φ 0 = 0) (htop : φ ⊤ = ⊤)
    {b : B'} {S : X → Y → Prop} {μ : Measure X} {ν : Measure Y} :
    (L.comap φ).Rel b S μ ν ↔ L.Rel (φ b) S μ ν := by
  have : (fun x y ↦ φ (relCost (B := B') S x y)) = relCost S := by
    ext x y
    by_cases hS : S x y <;> simp [hS, h0, htop]
  simp only [Rel, comap, this]

/-- A monotone additive budget map that keeps finite budgets finite regrades a lawful lifting. -/
theorem isLawful_comap [Add B] [Preorder B] [Top B] [Add B'] [Preorder B'] [Top B']
    [L.IsLawful] (hφ : Monotone φ) (hadd : ∀ a b, φ (a + b) = φ a + φ b)
    (hlt : ∀ a, a < ⊤ → φ a < ⊤) : (L.comap φ).IsLawful where
  pure {_ _} _ _ R _ _ h := IsLawful.pure (L := L) (R := fun x y ↦ φ (R x y)) (hlt _ h)
  zero b _ := IsLawful.zero (L := L) (φ b) _
  mono h hb hR := IsLawful.mono (L := L) h (hφ hb) fun x y ↦ hφ (hR x y)
  frame hc h := by
    simpa only [comap, hadd] using IsLawful.frame (L := L) (hlt _ hc) h
  map hf hg h := IsLawful.map (L := L) hf hg h

/-- A budget map keeping `⊤` regrades a lifting with bind. -/
theorem hasBind_comap [Preorder B] [Top B] [PartialOrder B'] [OrderTop B'] [L.HasBind]
    (htop : φ ⊤ = ⊤) : (L.comap φ).HasBind where
  bind h hk := HasBind.bind (L := L) h fun x y hR ↦ hk x y <| lt_top_iff_ne_top.2 fun hxy ↦
    (lt_irrefl (⊤ : B) (by rwa [hxy, htop] at hR))

/-- A budget map keeping `⊤` regrades a support-local lifting. -/
theorem isSupportLocal_comap [Top B] [Top B'] [L.IsSupportLocal] (htop : φ ⊤ = ⊤) :
    (L.comap φ).IsSupportLocal where
  restrict {X Y} _ _ b R μ ν A _ hA hμ h := by
    have : (fun x y ↦ φ (A.piecewise R (fun _ _ ↦ ⊤) x y)) =
        A.piecewise (fun x y ↦ φ (R x y)) fun _ _ ↦ ⊤ := by
      ext x y
      by_cases hx : x ∈ A <;> simp [hx, htop]
    simpa only [comap, this] using IsSupportLocal.restrict (L := L) hA hμ h

/-- A budget map keeping `0` and `⊤` regrades a reflexive lifting. -/
theorem isReflexive_comap [Zero B] [Top B] [Zero B'] [Top B'] [L.IsReflexive] (h0 : φ 0 = 0)
    (htop : φ ⊤ = ⊤) : (L.comap φ).IsReflexive where
  refl μ _ := (comap_rel_iff h0 htop).2 (h0 ▸ IsReflexive.refl μ)

instance isZeroLeft_comap [L.IsZeroLeft] : (L.comap φ).IsZeroLeft where
  zero_left b _ ν _ := IsZeroLeft.zero_left (L := L) (φ b) _ ν

instance isLeftContinuous_comap [L.IsLeftContinuous] : (L.comap φ).IsLeftContinuous where
  iSup_left hμ _ _ h := IsLeftContinuous.iSup_left (L := L) hμ h

/-- Regrading preserves absorbing grades. -/
theorem Absorbing.comap {b : B'} (h : L.Absorbing (φ b)) : (L.comap φ).Absorbing b :=
  fun _ μ ν _ _ ↦ h _ μ ν

variable (φ) (L) in
/-- The regraded lifting maps back to the original along `φ`. -/
def comapHom [Preorder B] [Preorder B'] (hφ : Monotone φ) : LiftingHom (L.comap φ) L where
  map := φ
  mono := hφ
  map_lift h := h

end GradedLifting
