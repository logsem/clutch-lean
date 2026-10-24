module

public import Metrology.Micrometer.MicrometerWpGS
import Metrology.Iris.LocalBI

/-! # The `specCoupl` modality -/

@[expose] public section

open Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE GradedLifting
open MeasureTheory (Measure)

namespace ProbLang

open MeasureTheory.Measure ErasableExpr BindLaw IsTopAbsorbing BIFUpdate LawfulSet

variable {rT : Type}

namespace MicrometerWpGS
variable {B : Type} {GF : BundledGFunctors}

/-! ## The modality -/

/-- The data of a spec coupling: program state, spec configuration and remaining budget. -/
abbrev SpecCouplState (rT B : Type) : Type := State rT × Cfg rT × B

/-- The COFE structure on spec coupling states. -/
instance : COFE (SpecCouplState rT B) := ofDiscrete _

/-- Spec coupling states are discrete. -/
instance : Discrete (SpecCouplState rT B) := ⟨id⟩

/-- Every predicate on spec coupling states is non-expansive. -/
theorem specCouplState_ne {Φ : SpecCouplState rT B → IProp GF} : NonExpansive Φ :=
  nonExpansive_of_discrete_leibniz Φ

variable [MeasurableSpace rT] [LawfulProbLangℝ rT] [PartialOrder B] [OrderTop B]
  {L : GradedLifting.{0} B} [MicrometerWpGS (rT := rT) GF]
local bi IProp GF

section
variable (L) (E : CoPset)

/-- Coupling case of `specCoupl`: a bind law with a budget-`b` head coupling and continuations
satisfying `Φ`. -/
abbrev specCouplCouple (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT) (b : B)
    (Φ : SpecCouplState rT B → IProp GF) := iprop%
  (∃ (law : L.BindLaw) (n : Nat) (μ₁ μ₁' : Measure (State rT))
      (ν₀ : Measure (Cfg rT)) (f' : Cfg rT → Cfg rT) (R : State rT → Cfg rT → B),
      ⌜Measurable f' ∧ (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) = ν₀.map f'⌝ ∗
      ⌜law.head μ₁ ν₀ R b⌝ ∗
      ⌜law.SideForExec μ₁ ν₀ R f'⌝ ∗
      ⌜ErasableExpr μ₁ σ₁⌝ ∗
      ⌜ErasableExpr μ₁' σ₁'⌝ ∗
      (∀ σ₂ ρ, ⌜R σ₂ ρ < (⊤ : B)⌝ -∗ |={E}=> Φ (σ₂, f' ρ, R σ₂ ρ)))

/-- The body of the `specCoupl` fixpoint: absorbing, done, or coupled via `specCouplCouple`. -/
abbrev specCouplPre (Z : State rT → Cfg rT → B → IProp GF) (Φ : SpecCouplState rT B → IProp GF) :
    SpecCouplState rT B → IProp GF :=
  fun ⟨σ₁, ⟨e₁', σ₁'⟩, b⟩ => iprop%
    ⌜L.Absorbing b⌝ ∨ Z σ₁ ⟨e₁', σ₁'⟩ b ∨ specCouplCouple L E σ₁ e₁' σ₁' b Φ

/-- The spec coupling modality: the least fixpoint of `specCouplPre`. -/
abbrev specCoupl (σ : State rT) (e' : Exp rT) (σ' : State rT) (b : B)
    (Z : State rT → Cfg rT → B → IProp GF) :=
  bi_least_fixpoint (specCouplPre L E Z) (σ, ⟨e', σ'⟩, b)

end

variable {E : CoPset} {σ σ₁ σ' σ₁' : State rT} {e' e₁' : Exp rT} {b : B} {n : Nat}
  {Z Z₁ Z₂ : State rT → Cfg rT → B → IProp GF} {μ₁ μ₁' : Measure (State rT)}
  {R : State rT → Cfg rT → B}

/-- A coupling case is monotone in its continuation, up to a fancy update on a larger mask. -/
theorem specCouplCouple_mono {E₁ E₂ : CoPset} (HE : E₁ ⊆ E₂)
    {Φ Ψ : SpecCouplState rT B → IProp GF} : iprop%
    (∀ s, Φ s -∗ |={E₂}=> Ψ s) ∗ specCouplCouple L E₁ σ₁ e₁' σ₁' b Φ ⊢
      specCouplCouple L E₂ σ₁ e₁' σ₁' b Ψ := by
  iintro ⟨HΦ, HCpl⟩
  icases HCpl with ⟨%law, %n, %μ₁, %μ₁', %ν₀, %f', %R, %Hmap, %Hc, %Hside, %Herase₁,
    %Herase₂, Hcont⟩
  iexists law, n, μ₁, μ₁', ν₀, f', R
  iframe %
  iintro %σ₂ %ρ %hR
  imod subset HE with Hclose
  imod Hcont $$ %σ₂ %ρ %hR
  imod Hclose
  iapply HΦ $$ %(σ₂, f' ρ, R σ₂ ρ) Hcont

/-- `specCouplPre` is monotone, so its least fixpoint `specCoupl` exists. -/
instance specCouplPre_mono : BIMonoPred (specCouplPre L E Z) where
  mono_pred {Φ Ψ _ _} := by
    iintro #Hwand %s Hs
    icases Hs with ⟨HVac | HZ | HCpl⟩
    · ileft
      iexact HVac
    · iright
      ileft
      iexact HZ
    · iright
      iright
      iapply specCouplCouple_mono subset_refl
      iframe HCpl
      iintro %s' HΦ
      imodintro
      iapply Hwand $$ %s' HΦ
  mono_pred_ne := specCouplState_ne

/-! ## Introduction rules -/

/-- A spec coupling holds when the budget is absorbing. -/
theorem specCoupl_absorbing (hb : L.Absorbing b) : ⊢ specCoupl L E σ e' σ' b Z := by
  iapply least_fixpoint_unfold_mpr (specCouplPre L E Z)
  ileft; ipureintro; exact hb

/-- A spec coupling holds when its exit predicate does. -/
theorem specCoupl_ret : Z σ ⟨e', σ'⟩ b ⊢ specCoupl L E σ e' σ' b Z := by
  iintro HZ
  iapply least_fixpoint_unfold_mpr (specCouplPre L E Z)
  iright; ileft; iexact HZ

/-- A spec coupling holds when its coupling case does. -/
theorem specCoupl_rec :
    specCouplCouple L E σ e' σ' b (fun s => specCoupl L E s.1 s.2.1.expr s.2.1.state s.2.2 Z) ⊢
      specCoupl L E σ e' σ' b Z := by
  iintro HCpl
  iapply least_fixpoint_unfold_mpr (specCouplPre L E Z)
  iright; iright; iexact HCpl

/-! ## Structural rules -/

/-- Run a second spec coupling from each exit of the first. -/
theorem specCoupl_bind {E1 E2 : CoPset} (HE : E1 ⊆ E2) : iprop%
    (∀ σ₂ ρ₂ b', Z₁ σ₂ ρ₂ b' -∗ specCoupl L E2 σ₂ ρ₂.expr ρ₂.state b' Z₂) ∗
      specCoupl L E1 σ e' σ' b Z₁ ⊢ specCoupl L E2 σ e' σ' b Z₂ := by
  iintro ⟨HZ, HC⟩
  -- iterate on the fixpoint with the claim "the bind hypothesis gives `specCoupl … Z₂` here"
  let Φ : SpecCouplState rT B → IProp GF := fun s => iprop%
    (∀ σ₂ ρ₂ b', Z₁ σ₂ ρ₂ b' -∗ specCoupl L E2 σ₂ ρ₂.expr ρ₂.state b' Z₂) -∗
      specCoupl L E2 s.1 s.2.1.expr s.2.1.state s.2.2 Z₂
  have : NonExpansive Φ := specCouplState_ne
  iapply least_fixpoint_iter (Φ := Φ) $$ [] %(σ, ⟨e', σ'⟩, b) HC HZ
  iintro !> %s HF HZ
  icases HF with ⟨%HVac | HZ1 | HCpl⟩
  · iapply specCoupl_absorbing HVac
  · iapply HZ $$ HZ1
  · iapply specCoupl_rec
    iapply specCouplCouple_mono (Φ := Φ) HE
    isplitl [HZ]
    · iintro %s' HΦ
      imodintro
      iapply HΦ $$ HZ
    · iexact HCpl

/-- A spec coupling is monotone in its exit predicate. -/
theorem specCoupl_mono : iprop%
    (∀ σ' ρ' b', Z₁ σ' ρ' b' -∗ Z₂ σ' ρ' b') ∗ specCoupl L E σ e' σ' b Z₁ ⊢
      specCoupl L E σ e' σ' b Z₂ := by
  iintro ⟨HZ, HC⟩
  iapply specCoupl_bind subset_refl
  iframe HC
  iintro %σ₂ %ρ₂ %b₂ Hz1
  iapply specCoupl_ret
  iapply HZ $$ Hz1

/-- A spec coupling is non-expansive in its exit predicate. -/
theorem specCoupl_ne (HZ : ∀ σ ρ b, Z₁ σ ρ b ≡{n}≡ Z₂ σ ρ b) :
    specCoupl L E σ e' σ' b Z₁ ≡{n}≡ specCoupl L E σ e' σ' b Z₂ := by
  unfold specCoupl
  refine least_fixpoint_ne_outer (fun _ s => ?_) (.of_eq rfl)
  exact or_ne.ne (.of_eq rfl) (or_ne.ne (HZ s.1 s.2.1 s.2.2) (.of_eq rfl))

/-- Induction on `specCoupl`: `Ψ` holds if it follows from one unfolding of `specCouplPre` with
`Ψ` at every recursive call. -/
theorem specCoupl_ind {Ψ : State rT → Cfg rT → B → IProp GF} : iprop%
    □ (∀ σ c b, specCouplPre L E Z (fun s => iprop(Ψ s.1 s.2.1 s.2.2 ∧
        specCoupl L E s.1 s.2.1.expr s.2.1.state s.2.2 Z)) (σ, c, b) -∗ Ψ σ c b) ⊢
      ∀ σ e' σ' b, specCoupl L E σ e' σ' b Z -∗ Ψ σ ⟨e', σ'⟩ b := by
  iintro #IH %σ %e' %σ' %b HC
  let Ψ' : SpecCouplState rT B → IProp GF := fun s => Ψ s.1 s.2.1 s.2.2
  have HΨne : NonExpansive Ψ' := specCouplState_ne
  iapply least_fixpoint_ind (F := specCouplPre L E Z) (Φ := Ψ') $$ [] %(σ, ⟨e', σ'⟩, b) HC
  iintro !> %s HF
  obtain ⟨σ'', c, b'⟩ := s
  iapply IH $$ %σ'' %c %b' HF

/-! ## Bind Law introduction rules -/

/-- A spec coupling from one bind-law round whose spec run is the image of `ν₀` under a
measurable `f'`. -/
theorem specCoupl_couple_map (law : L.BindLaw) {ν₀ : Measure (Cfg rT)} {f' : Cfg rT → Cfg rT}
    (hf' : Measurable f') (hspec : (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) = ν₀.map f')
    (hhead : law.head μ₁ ν₀ R b) (hside : law.SideForExec μ₁ ν₀ R f')
    (Heras₁ : ErasableExpr μ₁ σ₁) (Heras₁' : ErasableExpr μ₁' σ₁') : iprop%
    (∀ σ₂ ρ, ⌜R σ₂ ρ < (⊤ : B)⌝ -∗ |={E}=>
        specCoupl L E σ₂ (f' ρ).expr (f' ρ).state (R σ₂ ρ) Z) ⊢
      specCoupl L E σ₁ e₁' σ₁' b Z := by
  have hmap : _ ∧ _ := ⟨hf', hspec⟩
  iintro H
  iapply specCoupl_rec
  iexists law, n, μ₁, μ₁', ν₀, f', R
  iframe %
  iexact H

/-- `specCoupl_couple_map` with `f' = id`. -/
theorem specCoupl_couple_law (law : L.BindLaw)
    (hhead : law.head μ₁ (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) R b)
    (hside : law.SideForExec μ₁ (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) R id)
    (Heras₁ : ErasableExpr μ₁ σ₁) (Heras₁' : ErasableExpr μ₁' σ₁') : iprop%
    (∀ σ₂ e₂' σ₂', ⌜R σ₂ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={E}=>
        specCoupl L E σ₂ e₂' σ₂' (R σ₂ ⟨e₂', σ₂'⟩) Z) ⊢
      specCoupl L E σ₁ e₁' σ₁' b Z := by
  iintro H
  iapply specCoupl_couple_map law measurable_id map_id.symm hhead hside Heras₁ Heras₁'
  iintro %σ₂ %⟨e₂', σ₂'⟩ %hR
  simp only [id]
  iapply H $$ %σ₂ %e₂' %σ₂' %hR

/-- A spec coupling from a lifting `L b R` of the state distribution and the spec run, by the
canonical bind law. -/
theorem specCoupl_couple [Add B] [L.IsLawful] [L.HasBind] [L.IsSupportLocal]
    (Hcpl : L b R μ₁ (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩))
    (Heras₁ : ErasableExpr μ₁ σ₁) (Heras₁' : ErasableExpr μ₁' σ₁') : iprop%
    (∀ σ₂ e₂' σ₂', ⌜R σ₂ ⟨e₂', σ₂'⟩ < (⊤ : B)⌝ -∗ |={E}=>
        specCoupl L E σ₂ e₂' σ₂' (R σ₂ ⟨e₂', σ₂'⟩) Z) ⊢
      specCoupl L E σ₁ e₁' σ₁' b Z :=
  specCoupl_couple_law (canonical L) Hcpl (.of_forall fun _ _ => trivial) Heras₁ Heras₁'

section SplitBudget
variable [AddCommMonoid B] [CanonicallyOrderedAdd B] [L.IsLawful] [L.IsTopAbsorbing] [L.HasBind]
  [L.IsSupportLocal]

section
variable {b₁ b₂ : B} (hb : b₁ + b₂ ≤ b)
include hb

variable {S : State rT → Cfg rT → Prop}

/-- Introduce a spec coupling from a relational lifting within `b₁`, leaving `b₂` to every
related pair. -/
theorem specCoupl_couple_rel
    (Hcpl : L.Rel b₁ S μ₁ (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩))
    (Heras₁ : ErasableExpr μ₁ σ₁) (Heras₁' : ErasableExpr μ₁' σ₁') : iprop%
    (∀ σ₂ e₂' σ₂', ⌜S σ₂ ⟨e₂', σ₂'⟩⌝ -∗ |={E}=> specCoupl L E σ₂ e₂' σ₂' b₂ Z) ⊢
      specCoupl L E σ₁ e₁' σ₁' b Z := by
  have := Heras₁.isProbabilityMeasure
  have := Heras₁'.isProbabilityMeasure
  iintro H
  iapply specCoupl_couple (IsLawful.mono (frame Hcpl) hb le_rfl) Heras₁ Heras₁'
  iintro %σ₂ %e₂' %σ₂' %hR
  obtain ⟨hS, -⟩ := relCost_add_lt_top_iff.1 hR
  rw [relCost_of hS, zero_add]
  iapply H $$ %σ₂ %e₂' %σ₂' %hS

/-- Couple two erasable distributions before `Z`, leaving `b₂` to the continuation. -/
theorem specCoupl_erasables {S' : State rT → State rT → Prop} (Hcpl : L.Rel b₁ S' μ₁ μ₁')
    (Heras₁ : ErasableExpr μ₁ σ₁) (Heras₁' : ErasableExpr μ₁' σ₁') : iprop%
    (∀ σ₂ σ₂', ⌜S' σ₂ σ₂'⌝ -∗ |={E}=> specCoupl L E σ₂ e₁' σ₂' b₂ Z) ⊢
      specCoupl L E σ₁ e₁' σ₁' b Z := by
  have := Heras₁.isProbabilityMeasure
  have := Heras₁'.isProbabilityMeasure
  iintro H
  have heq : μ₁'.bind (fun σ => pexecN 0 ⟨e₁', σ⟩) = μ₁'.map (fun σ => (⟨e₁', σ⟩ : Cfg rT)) := by
    simp only [pexecN_zero]
    exact bind_dirac_eq_map _ (by fun_prop)
  iapply specCoupl_couple_rel (S := fun σ₂ c => S' σ₂ c.state ∧ c.expr = e₁') (n := 0) hb
    (heq ▸ Hcpl.map_right fun _ _ HS => ⟨HS, rfl⟩) Heras₁ Heras₁'
  iintro %σ₂ %e₂' %σ₂' %HS
  obtain ⟨HS, rfl⟩ := HS
  iapply H $$ %σ₂ %σ₂' %HS

/-- Couple an erasable distribution against `n` spec steps. -/
theorem specCoupl_erasable_steps
    (Hcpl : L.Rel b₁ S μ₁ (pexecN n ⟨e₁', σ₁'⟩))
    (Heras₁ : ErasableExpr μ₁ σ₁) : iprop%
    (∀ σ₂ e₂' σ₂', ⌜S σ₂ ⟨e₂', σ₂'⟩⌝ -∗ |={E}=> specCoupl L E σ₂ e₂' σ₂' b₂ Z) ⊢
      specCoupl L E σ₁ e₁' σ₁' b Z :=
  specCoupl_couple_rel (n := n) hb (by rwa [dirac_bind (by fun_prop)]) Heras₁ (dret σ₁')

/-- Couple a Dirac program state against `n` spec steps. -/
theorem specCoupl_steps
    (Hcpl : L.Rel b₁ S (dirac σ₁) (pexecN n ⟨e₁', σ₁'⟩)) : iprop%
    (∀ σ₂ e₂' σ₂', ⌜S σ₂ ⟨e₂', σ₂'⟩⌝ -∗ |={E}=> specCoupl L E σ₂ e₂' σ₂' b₂ Z) ⊢
      specCoupl L E σ₁ e₁' σ₁' b Z :=
  specCoupl_erasable_steps hb Hcpl (dret σ₁)

end

/-! ## Discrete steps -/

/- TODO: move to the file defining `primStep_atomic`. -/
/-- Away from `urand`, a step is carried by its support of positive-mass points. -/
theorem concentrated_primStep_support (e : Exp rT) (σ : State rT) (hne : e.decomp.2 ≠ .urand) :
    Concentrated (primStep ⟨e, σ⟩) {ρ | 0 < primStep ⟨e, σ⟩ {ρ}} := by
  have heq : {ρ | 0 < primStep ⟨e, σ⟩ {ρ}}ᶜ = {ρ | primStep ⟨e, σ⟩ {ρ} = 0} := by
    ext ρ
    simp [pos_iff_ne_zero]
  show primStep ⟨e, σ⟩ _ = 0
  rw [heq]
  exact primStep_atomic e σ hne

variable [L.IsReflexive]

/-- Couple a Dirac program state against one spec step, on a measurable set carrying the step. -/
theorem specCoupl_step_concentrated {S : Set (Cfg rT)} (Hred : Reducible e₁' σ₁')
    (hSmeas : MeasurableSet S) (hSconc : Concentrated (primStep ⟨e₁', σ₁'⟩) S) : iprop%
    (∀ e₂' σ₂', ⌜⟨e₂', σ₂'⟩ ∈ S⌝ -∗ |={E}=> specCoupl L E σ₁ e₂' σ₂' b Z) ⊢
      specCoupl L E σ₁ e₁' σ₁' b Z := by
  iintro H
  have := prim_step_mass Hred
  have hpexec1 : pexecN 1 ⟨e₁', σ₁'⟩ = primStep ⟨e₁', σ₁'⟩ := by
    rw [pexecN_one, stepOrFinal_not_isValue (val_stuck Hred)]
  have HcplR : L.Rel 0 (fun σ c => σ = σ₁ ∧ c ∈ S) (dirac σ₁) (pexecN 1 ⟨e₁', σ₁'⟩) := by
    rw [hpexec1]
    exact rel_dirac_left _ hSmeas hSconc σ₁
  iapply specCoupl_steps (zero_add b).le HcplR
  iintro %σ₂ %e₂' %σ₂' %HS
  obtain ⟨rfl, Hmem⟩ := HS
  iapply H $$ %e₂' %σ₂' %Hmem

/-- Introduce a `specCoupl` around a discrete step. -/
@[discrete]
theorem specCoupl_step (Hred : Discrete.Reducible e₁' σ₁')
    (hne : e₁'.decomp.2 ≠ .urand := by no_urand) : iprop%
    (∀ e₂' σ₂', ⌜0 < primStep ⟨e₁', σ₁'⟩ {⟨e₂', σ₂'⟩}⌝ -∗ |={E}=> specCoupl L E σ₁ e₂' σ₂' b Z) ⊢
      specCoupl L E σ₁ e₁' σ₁' b Z :=
  specCoupl_step_concentrated Hred.toReducible (measurableSet_primStep_support e₁' σ₁')
    (concentrated_primStep_support e₁' σ₁' hne)

end SplitBudget

/-! ## Budget weakening and fancy updates -/

section Budget
variable [Add B] [L.IsLawful] [L.IsTopAbsorbing]

/-- A fancy-updated spec coupling at the end of a deterministic `n`-step spec run, at a budget
`b₁ ≤ b`, gives one at its start at `b` (Rocq `spec_coupl_steps_det`, `spec_coupl_mono_grade`). -/
theorem fupd_specCoupl_steps_det_of_le {e₂' : Exp rT} {σ₂' : State rT} {b₁ : B}
    (Hstep : pexecN n ⟨e₁', σ₁'⟩ = dirac ⟨e₂', σ₂'⟩) (hb : b₁ ≤ b) :
    iprop(|={E}=> specCoupl L E σ e₂' σ₂' b₁ Z) ⊢ specCoupl L E σ e₁' σ₁' b Z := by
  classical
  -- the unit law only carries a finite budget; at b₁ = ⊤ exit through absorption
  obtain hb₁ | rfl := (eq_top_or_lt_top b₁).symm
  · iintro HF
    -- one unit-law round between point masses: leftover `b₁` at the target pair, `⊤` elsewhere
    let R : State rT → Cfg rT → B := fun s c => if s = σ ∧ c = ⟨e₂', σ₂'⟩ then b₁ else (⊤ : B)
    have hR : R σ ⟨e₂', σ₂'⟩ = b₁ := ite_eq_left ⟨rfl, rfl⟩
    have hhead : (BindLaw.unit L).head (dirac σ)
        ((dirac σ₁').bind fun σ => pexecN n ⟨e₁', σ⟩) R b := by
      rw [dirac_bind (by fun_prop), Hstep]
      exact unit_head_dirac (hR ▸ hb₁) (hR ▸ hb)
    iapply specCoupl_couple_law (.unit L) hhead (.of_forall fun _ _ => trivial) (dret σ) (dret σ₁')
    iintro %σ₂ %e₂'' %σ₂'' %hlt
    by_cases hS : σ₂ = σ ∧ e₂'' = e₂' ∧ σ₂'' = σ₂'
    · obtain ⟨rfl, rfl, rfl⟩ := hS
      rw [hR]
      iexact HF
    · simp [R, hS] at hlt
  · iintro -
    iapply specCoupl_absorbing
    exact (top_le_iff.1 hb) ▸ absorbing_top

/-- A spec coupling absorbs a leading fancy update and may weaken its budget. -/
theorem fupd_specCoupl_of_le {b₁ b₂ : B} (hb : b₁ ≤ b₂) :
    iprop(|={E}=> specCoupl L E σ e' σ' b₁ Z) ⊢ specCoupl L E σ e' σ' b₂ Z :=
  fupd_specCoupl_steps_det_of_le (pexecN_zero _) hb

/-- A spec coupling at a smaller budget proves one at a larger budget. -/
theorem specCoupl_mono_budget {b₁ b₂ : B} (hb : b₁ ≤ b₂) :
    specCoupl L E σ e' σ' b₁ Z ⊢ specCoupl L E σ e' σ' b₂ Z :=
  fupd_intro.trans (fupd_specCoupl_of_le hb)

/-- A spec coupling absorbs a leading fancy update. -/
theorem fupd_specCoupl : iprop(|={E}=> specCoupl L E σ e' σ' b Z) ⊢ specCoupl L E σ e' σ' b Z :=
  fupd_specCoupl_of_le le_rfl

/-- A spec coupling at the end of a deterministic `n`-step spec run gives one at its start. -/
theorem specCoupl_steps_det {e₂' : Exp rT} {σ₂' : State rT}
    (Hstep : pexecN n ⟨e₁', σ₁'⟩ = dirac ⟨e₂', σ₂'⟩) :
    specCoupl L E σ e₂' σ₂' b Z ⊢ specCoupl L E σ e₁' σ₁' b Z :=
  fupd_intro.trans (fupd_specCoupl_steps_det_of_le Hstep le_rfl)

end Budget

end MicrometerWpGS

end ProbLang
