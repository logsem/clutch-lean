module

public import Metrology.Couplings.Codensity

/-! # Lifting homomorphisms and regrading

Budget maps between graded liftings (`LiftingRelHom`, `LiftingHom`) and regrading a lifting
along one (`GradedLifting.comap`) (Rocq `morphism.v`, `regrade.v`). -/

@[expose] public section

universe u v w x

open MeasureTheory Measure ProbabilityTheory GradedLifting

/-! ## Homomorphisms between liftings -/

/-- A monotone budget map carrying every relational lifting of `L₁` to one of `L₂` (Rocq
`CouplingMorphism`). Used for conversions that apply only at the end of a proof, such as Rényi/zCDP
to DP, whose budget map adds a one-off `log (1/δ)` term and so cannot act on leftovers. -/
structure LiftingRelHom {B₁ : Type v} {B₂ : Type w} [Preorder B₁] [Zero B₁] [Top B₁]
    [Preorder B₂] [Zero B₂] [Top B₂] (L₁ : GradedLifting.{u} B₁) (L₂ : GradedLifting.{u} B₂) where
  /-- The budget map. -/
  map : B₁ → B₂
  mono : Monotone map
  map_rel {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {b : B₁} {S : X → Y → Prop}
    {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    L₁.Rel b S μ ν → L₂.Rel (map b) S μ ν

/-- The per-pair strengthening of `LiftingRelHom`: every lifting with leftover `R` maps to one at
`map b` with leftover `map ∘ R`. -/
structure LiftingHom {B₁ : Type v} {B₂ : Type w} [Preorder B₁] [Preorder B₂]
    (L₁ : GradedLifting.{u} B₁) (L₂ : GradedLifting.{u} B₂) where
  /-- The budget map. -/
  map : B₁ → B₂
  mono : Monotone map
  map_lift {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y] {b : B₁} {R : X → Y → B₁}
    {μ : Measure X} {ν : Measure Y} [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν] :
    L₁ b R μ ν → L₂ (map b) (fun x y ↦ map (R x y)) μ ν

namespace LiftingRelHom

variable {B₁ : Type v} {B₂ : Type w} {B₃ : Type x} [Preorder B₁] [Zero B₁] [Top B₁]
  [Preorder B₂] [Zero B₂] [Top B₂] [Preorder B₃] [Zero B₃] [Top B₃]
  {L₂ : GradedLifting.{u} B₂} {L₃ : GradedLifting.{u} B₃}

variable (L₁ : GradedLifting.{u} B₁) in
/-- The identity map as a relational homomorphism. -/
def id : LiftingRelHom L₁ L₁ where
  map := fun b ↦ b
  mono := monotone_id
  map_rel h := h

@[simp]
theorem id_map (b : B₁) : (id L₁).map b = b :=
  rfl

variable {L₁ : GradedLifting.{u} B₁}

/-- Composition of relational homomorphisms, composing the budget maps. -/
def comp (G : LiftingRelHom L₂ L₃) (F : LiftingRelHom L₁ L₂) : LiftingRelHom L₁ L₃ where
  map := G.map ∘ F.map
  mono := G.mono.comp F.mono
  map_rel h := G.map_rel (F.map_rel h)

@[simp]
theorem comp_map (G : LiftingRelHom L₂ L₃) (F : LiftingRelHom L₁ L₂) (b : B₁) :
    (G.comp F).map b = G.map (F.map b) :=
  rfl

end LiftingRelHom

namespace LiftingHom

variable {B₁ : Type v} {B₂ : Type w} {B₃ : Type x} [Preorder B₁] [Preorder B₂] [Preorder B₃]
  {L₂ : GradedLifting.{u} B₂} {L₃ : GradedLifting.{u} B₃}

variable (L₁ : GradedLifting.{u} B₁) in
/-- The identity map as a homomorphism. -/
def id : LiftingHom L₁ L₁ where
  map := fun b ↦ b
  mono := monotone_id
  map_lift h := h

@[simp]
theorem id_map (b : B₁) : (id L₁).map b = b :=
  rfl

variable {L₁ : GradedLifting.{u} B₁}

/-- Composition of homomorphisms, composing the budget maps. -/
def comp (G : LiftingHom L₂ L₃) (F : LiftingHom L₁ L₂) : LiftingHom L₁ L₃ where
  map := G.map ∘ F.map
  mono := G.mono.comp F.mono
  map_lift h := G.map_lift (F.map_lift h)

@[simp]
theorem comp_map (G : LiftingHom L₂ L₃) (F : LiftingHom L₁ L₂) (b : B₁) :
    (G.comp F).map b = G.map (F.map b) :=
  rfl

end LiftingHom

namespace GradedLifting

/-! ## Regrading along a budget map -/

variable {B : Type v} {B' : Type w} {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]
  {φ : B' → B} {L : GradedLifting.{u} B} {b : B'} {S : X → Y → Prop} {μ : Measure X}
  {ν : Measure Y}

variable (φ) (L) in
/-- Regrading a lifting along a budget map: budget and leftovers are read through `φ`
(Rocq `GCF_regrade`). -/
def comap : GradedLifting.{u} B' :=
  fun b _ _ _ _ R ↦ L (φ b) fun x y ↦ φ (R x y)

theorem comap_def {R : X → Y → B'} :
    L.comap φ b R μ ν ↔ L (φ b) (fun x y ↦ φ (R x y)) μ ν :=
  Iff.rfl

theorem comap_comap {B'' : Type*} {ψ : B'' → B'} : (L.comap φ).comap ψ = L.comap (φ ∘ ψ) :=
  rfl

/-- Regrading keeps `Rel` when `φ` keeps `0` and `⊤`. -/
theorem comap_rel_iff [Zero B] [Top B] [Zero B'] [Top B'] (h0 : φ 0 = 0) (htop : φ ⊤ = ⊤) :
    (L.comap φ).Rel b S μ ν ↔ L.Rel (φ b) S μ ν := by
  have : (fun x y ↦ φ (relCost (B := B') S x y)) = relCost S := by
    ext x y
    by_cases hS : S x y <;> simp [hS, h0, htop]
  simp only [Rel, comap, this]

/-- A regraded relational lifting is one of the original lifting when `φ` keeps `⊤`; `φ 0` may
exceed `0` (Rocq `GCF_regrade_le`). -/
theorem Rel.of_comap [AddZeroClass B] [Preorder B] [OrderTop B] [CanonicallyOrderedAdd B]
    [Zero B'] [Top B'] [L.IsLawful] [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    (htop : φ ⊤ = ⊤) (h : (L.comap φ).Rel b S μ ν) : L.Rel (φ b) S μ ν :=
  IsLawful.mono h le_rfl fun x y ↦ by by_cases hS : S x y <;> simp [hS, htop]

/-- A monotone additive budget map that keeps finite budgets finite regrades a lawful lifting. -/
theorem isLawful_comap [Add B] [Preorder B] [Top B] [Add B'] [Preorder B'] [Top B']
    [L.IsLawful] (hφ : Monotone φ) (hadd : ∀ a b, φ (a + b) = φ a + φ b)
    (hlt : ∀ a, a < ⊤ → φ a < ⊤) : (L.comap φ).IsLawful where
  pure {_ _} _ _ R _ _ h := IsLawful.pure (R := fun x y ↦ φ (R x y)) (hlt _ h)
  zero b _ := IsLawful.zero (φ b) _
  mono h hb hR := IsLawful.mono (L := L) h (hφ hb) fun x y ↦ hφ (hR x y)
  frame hc h := by simpa only [comap, hadd] using IsLawful.frame (hlt _ hc) h
  map hf hg h := IsLawful.map (L := L) hf hg h

/-- A monotone additive budget map regrades a lawful lifting whose top budget relates every pair
of measures, even when finite budgets map to `⊤` (the zCDP line at `(⊤, 0)`). -/
theorem isLawful_comap_of_top [AddCommMagma B] [PartialOrder B] [OrderTop B]
    [CanonicallyOrderedAdd B] [Add B'] [Preorder B'] [Top B'] [L.IsLawful] [L.IsTopAbsorbing]
    (hφ : Monotone φ) (hadd : ∀ a b, φ (a + b) = φ a + φ b) : (L.comap φ).IsLawful where
  pure {_ _} _ _ R x y _ :=
    comap_def.2 <| IsTopAbsorbing.of_lt_top fun h ↦
      IsLawful.pure (R := fun x y ↦ φ (R x y)) h
  zero b _ := IsLawful.zero (φ b) _
  mono h hb hR := IsLawful.mono (L := L) h (hφ hb) fun x y ↦ hφ (hR x y)
  frame {_ _} _ _ _ c _ _ _ _ h := by
    simpa only [comap, hadd] using IsTopAbsorbing.frame (c := φ c) h
  map hf hg h := IsLawful.map (L := L) hf hg h

/-- A budget map keeping `⊤` regrades a lifting with bind. -/
theorem hasBind_comap [Preorder B] [Top B] [PartialOrder B'] [OrderTop B'] [L.HasBind]
    (htop : φ ⊤ = ⊤) : (L.comap φ).HasBind where
  bind h hk := HasBind.bind (L := L) h fun x y hR ↦
    hk x y <| lt_top_iff_ne_top.2 fun hxy ↦ hR.ne (by rw [hxy, htop])

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

/-- A budget map with `φ 0` finite regrades a lawful reflexive lifting: frame reflexivity by
`φ 0` (tCDP lines move `0`; Rocq `GCF_regrade_le`). -/
theorem isReflexive_comap_of_lt_top [AddZeroClass B] [Preorder B] [OrderTop B]
    [CanonicallyOrderedAdd B] [Zero B'] [Top B'] [L.IsLawful] [L.IsReflexive]
    (h0 : φ 0 < ⊤) : (L.comap φ).IsReflexive where
  refl μ _ := by
    have := (IsReflexive.refl (L := L) μ).frame_le
      (R := fun x y ↦ φ (relCost (· = ·) x y)) (fun _ _ h ↦ by simp [h]) h0
    rwa [zero_add] at this

/-- Regrading keeps a lifting zero on the left. -/
instance isZeroLeft_comap [L.IsZeroLeft] : (L.comap φ).IsZeroLeft where
  zero_left b _ ν _ := IsZeroLeft.zero_left (φ b) _ ν

/-- Regrading keeps a lifting left-continuous. -/
instance isLeftContinuous_comap [L.IsLeftContinuous] : (L.comap φ).IsLeftContinuous where
  iSup_left hμ _ _ h := IsLeftContinuous.iSup_left (L := L) hμ h

/-- Regrading preserves absorbing grades (Rocq `GCFTop_regrade`). -/
theorem Absorbing.comap (h : L.Absorbing (φ b)) : (L.comap φ).Absorbing b :=
  fun _ μ ν _ _ ↦ h _ μ ν

/-- A budget sent to `⊤` is absorbing for the regrading of a lifting absorbing at `⊤` (Rocq
`regrade_top_triv`). -/
theorem absorbing_comap [Top B] [L.IsTopAbsorbing] (h : φ b = ⊤) : (L.comap φ).Absorbing b :=
  Absorbing.comap (h ▸ IsTopAbsorbing.absorbing_top)

/-- A budget map keeping `⊤` regrades a lifting absorbing at `⊤`. -/
theorem isTopAbsorbing_comap [Top B] [Top B'] [L.IsTopAbsorbing] (htop : φ ⊤ = ⊤) :
    (L.comap φ).IsTopAbsorbing :=
  ⟨fun _ _ _ ↦ comap_def.2 (htop ▸ IsTopAbsorbing.top _ _ _)⟩

/-- Regrading is a homomorphism: `φ` itself maps `L.comap φ` to `L`. -/
def comapHom [Preorder B] [Preorder B'] (hφ : Monotone φ) : LiftingHom (L.comap φ) L where
  map := φ
  mono := hφ
  map_lift h := h

/-! ### Regrading codensity liftings -/

open GradedDivergence

variable {D : GradedDivergence.{u} B}

/-- The regraded codensity lifting lies below the codensity lifting of the regraded divergence:
a test at slack `c` is a test at slack `φ c`, and one reaching `⊤` holds by grading. -/
theorem comap_codensity_le [Add B] [Preorder B] [OrderTop B] [Add B'] [LT B'] [Top B']
    [D.IsGraded] [IsSubProbabilityMeasure μ] [IsSubProbabilityMeasure ν]
    (hadd : ∀ a b, φ (a + b) = φ a + φ b) {R : X → Y → B'}
    (h : (codensity D).comap φ b R μ ν) : (D.comap φ).codensity b R μ ν := by
  intro I _ c _ k l _ _ hkl
  refine IsGraded.of_lt_top (D := D) fun hbc ↦ ?_
  rw [hadd] at hbc ⊢
  exact h hbc fun x y ↦ hadd _ _ ▸ hkl x y

/-- A monotone additive regrading of a codensity lifting is lawful, whatever it does to finite
budgets: the codensity lifting at `⊤` relates every pair of measures. -/
theorem isLawful_comap_codensity [AddCommMonoid B] [PartialOrder B] [OrderTop B]
    [CanonicallyOrderedAdd B] [Add B'] [Preorder B'] [Top B'] [D.IsGraded] [D.IsReflexive]
    (hφ : Monotone φ) (hadd : ∀ a b, φ (a + b) = φ a + φ b) : ((codensity D).comap φ).IsLawful :=
  isLawful_comap_of_top hφ hadd

end GradedLifting

/-! ## From `LiftingHom` to `LiftingRelHom` -/

namespace LiftingHom

variable {B₁ : Type v} {B₂ : Type w} [Preorder B₁] [Preorder B₂] {L₁ : GradedLifting.{u} B₁}
  {L₂ : GradedLifting.{u} B₂}

/-- A homomorphism keeping `⊤` is a relational homomorphism. -/
def toLiftingRelHom [Zero B₁] [Top B₁] [AddZeroClass B₂] [OrderTop B₂]
    [CanonicallyOrderedAdd B₂] [L₂.IsLawful] (F : LiftingHom L₁ L₂) (htop : F.map ⊤ = ⊤) :
    LiftingRelHom L₁ L₂ where
  map := F.map
  mono := F.mono
  -- `F.map_lift h` is `(L₂.comap F.map).Rel b S` by unfolding `comap`; `Rel.of_comap` turns
  -- `map ∘ relCost S` back into `relCost S`
  map_rel h := Rel.of_comap htop (F.map_lift h)

@[simp]
theorem toLiftingRelHom_map [Zero B₁] [Top B₁] [AddZeroClass B₂] [OrderTop B₂]
    [CanonicallyOrderedAdd B₂] [L₂.IsLawful] (F : LiftingHom L₁ L₂) (htop : F.map ⊤ = ⊤)
    (b : B₁) : (F.toLiftingRelHom htop).map b = F.map b :=
  rfl

end LiftingHom

/-! ## Regrading bind laws -/

namespace GradedLifting.BindLaw

variable {B : Type v} {B' : Type w} [Preorder B] [Top B] [PartialOrder B'] [OrderTop B']
  {L : GradedLifting.{u} B} {φ : B' → B} {X Y X' Y' : Type u} [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace X'] [MeasurableSpace Y']

omit [Preorder B] [MeasurableSpace X] [MeasurableSpace Y] in
/-- Reading a leftover set to `⊤` off `A` through a map keeping `⊤`. -/
theorem comp_piecewise_top {A : Set X} [DecidablePred (· ∈ A)] {R : X → Y → B'}
    (htop : φ ⊤ = ⊤) :
    (fun x y ↦ φ (A.piecewise R (fun _ _ ↦ ⊤) x y)) =
      A.piecewise (fun x y ↦ φ (R x y)) fun _ _ ↦ ⊤ := by
  ext x y
  by_cases hx : x ∈ A <;> simp [hx, htop]

/-- A bind law regraded along a monotone budget map keeping `⊤`: head and side condition read
budgets and leftovers through `φ`, as `GradedLifting.comap` does. -/
def comap (law : BindLaw L) (hφ : Monotone φ) (htop : φ ⊤ = ⊤) : BindLaw (L.comap φ) where
  head μ ν R b := law.head μ ν (fun x y ↦ φ (R x y)) (φ b)
  side μ ν R f g := law.side μ ν (fun x y ↦ φ (R x y)) f g
  sound h hs hk := law.sound h hs fun x y hR ↦
    hk x y <| lt_top_iff_ne_top.2 fun hxy ↦ hR.ne (by rw [hxy, htop])
  mono_out h hb := law.mono_out h (hφ hb)
  head_supp := by
    rintro _ _ _ _ b R μ ν A _ hA hμ h
    show law.head μ ν (fun x y ↦ φ (A.piecewise R (fun _ _ ↦ ⊤) x y)) (φ b)
    rw [comp_piecewise_top htop]
    exact law.head_supp hA hμ h
  side_supp := by
    rintro _ _ _ _ _ _ _ _ R μ ν f g A _ h
    show law.side μ ν (fun x y ↦ φ (A.piecewise R (fun _ _ ↦ ⊤) x y)) f g
    rw [comp_piecewise_top htop]
    exact law.side_supp h

variable {law : BindLaw L} {hφ : Monotone φ} {htop : φ ⊤ = ⊤}

@[simp]
theorem head_comap {b : B'} {R : X → Y → B'} {μ : Measure X} {ν : Measure Y} :
    (law.comap hφ htop).head μ ν R b ↔ law.head μ ν (fun x y ↦ φ (R x y)) (φ b) :=
  Iff.rfl

@[simp]
theorem side_comap {R : X → Y → B'} {μ : Measure X} {ν : Measure Y} {f : Kernel X X'}
    {g : Kernel Y Y'} : (law.comap hφ htop).side μ ν R f g ↔
      law.side μ ν (fun x y ↦ φ (R x y)) f g :=
  Iff.rfl

/-- An additive regrading keeping finite budgets finite keeps heads shiftable. -/
theorem headShift_comap [Add B] [Add B'] [law.HeadShift] (hadd : ∀ a b, φ (a + b) = φ a + φ b)
    (hlt : ∀ a, a < ⊤ → φ a < ⊤) : (law.comap hφ htop).HeadShift where
  shift hc h := by
    simpa only [head_comap, hadd] using HeadShift.shift (law := law) (hlt _ hc) h

/-- An additive regrading keeping `0`, `⊤` and finite budgets keeps heads diagonal. -/
theorem headDiag_comap [Zero B] [Add B] [Zero B'] [Add B'] [law.HeadDiag] (h0 : φ 0 = 0)
    (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hlt : ∀ a, a < ⊤ → φ a < ⊤) :
    (law.comap hφ htop).HeadDiag where
  diag {X} _ μ _ b hb := by
    have hrel (x y : X) : φ (relCost (B := B') (· = ·) x y) = relCost (· = ·) x y := by
      by_cases hxy : x = y <;> simp [hxy, h0, htop]
    simpa only [head_comap, hadd, hrel] using HeadDiag.diag (law := law) μ (hlt b hb)
  side_diag μ R f g := HeadDiag.side_diag (law := law) μ _ f g

/-- Regrading keeps a law free of side conditions. -/
theorem sideFree_comap [law.SideFree] : (law.comap hφ htop).SideFree :=
  ⟨fun μ ν _ f g ↦ SideFree.side (law := law) μ ν _ f g⟩

end GradedLifting.BindLaw
