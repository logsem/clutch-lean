module

public import Metrology.Micrometer.MicrometerWpGS
import Metrology.Iris.LocalBI

/-! # The `specCoupl` modality -/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang GradedLifting
open MeasureTheory (Measure)
open MeasureTheory.Measure ErasableExpr BindLaw IsTopAbsorbing BIFUpdate

namespace ProbLang

variable {rT : Type} [ProbLang.LawfulProbLangℝ rT]

namespace MicrometerWpGS
variable {B : Type} {GF : BundledGFunctors}

/-! ## The modality -/

abbrev SpecCouplState (rT : Type) [LawfulProbLangℝ rT] [MeasurableSingletonClass rT] (B : Type) :
    Type _ := State rT × Cfg rT × B

instance cofe_specCouplState : COFE (SpecCouplState rT B) := COFE.ofDiscrete _
instance discrete_specCouplState : OFE.Discrete (SpecCouplState rT B) := ⟨id⟩

theorem specCouplState_ne {Φ : SpecCouplState rT B → IProp GF} : NonExpansive Φ where
  ne _ _ _ hd := .of_eq (congrArg Φ (OFE.Discrete.discrete_0 hd))

variable [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B} [MicrometerWpGS (rT := rT) GF]
local bi IProp GF

section
variable (E : CoPset)

variable (L) in
/-- Coupling case of `specCoupl`
- Total budget is `b`,
- Accepts any bind law,
- Head must hold on an (erased) step on the left and (erased) `n` steps on the right,
- `Φ` must hold on the continuation, for all cases with finite credit.
-/
abbrev specCouplCouple (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT) (b : B)
    (Φ : SpecCouplState rT B → IProp GF) : IProp GF := iprop%
  (∃ (law : L.BindLaw) (n : Nat) (μ₁ μ₁' : Measure (State rT))
      (ν₀ : Measure (Cfg rT)) (f' : Cfg rT → Cfg rT) (R : State rT → Cfg rT → B),
      ⌜Measurable f' ∧ (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) = ν₀.map f'⌝ ∗
      ⌜law.head μ₁ ν₀ R b⌝ ∗
      ⌜law.SideForExec μ₁ ν₀ R f'⌝ ∗
      ⌜ErasableExpr μ₁ σ₁⌝ ∗
      ⌜ErasableExpr μ₁' σ₁'⌝ ∗
      (∀ σ₂ ρ, ⌜R σ₂ ρ < (⊤ : B)⌝ -∗ |={E}=> Φ (σ₂, f' ρ, R σ₂ ρ)))

variable (L) in
/-- The body of the `specCoupl` fixpoint. One of
- Absorbing: the credit is sufficiently high,
- Done,
- Coupled: via `specCouplCouple`
-/
abbrev specCouplPre (Z : State rT → Cfg rT → B → IProp GF) (Φ : SpecCouplState rT B → IProp GF) :
    SpecCouplState rT B → IProp GF :=
  fun ⟨σ₁, ⟨e₁', σ₁'⟩, b⟩ => iprop%
    ⌜L.Absorbing b⌝ ∨ Z σ₁ ⟨e₁', σ₁'⟩ b ∨ specCouplCouple L E σ₁ e₁' σ₁' b Φ

variable (L) in
abbrev specCoupl (σ : State rT) (e' : Exp rT) (σ' : State rT) (b : B)
    (Z : State rT → Cfg rT → B → IProp GF) : IProp GF :=
  bi_least_fixpoint (specCouplPre L E Z) (σ, ⟨e', σ'⟩, b)

end

variable {E : CoPset} {σ σ₁ σ' σ₁' : State rT} {e' e₁' : Exp rT} {b : B} {n : Nat}
  {Z Z₁ Z₂ : State rT → Cfg rT → B → IProp GF} {μ₁ μ₁' : Measure (State rT)}
  {R : State rT → Cfg rT → B}

/-- `specCouplPre` is monotone, so its least fixpoint `specCoupl` exists. -/
instance specCouplPre_mono : BIMonoPred (specCouplPre L E Z) where
  mono_pred {Φ Ψ _ _} := by
    iintro #Hwand %s Hs
    icases Hs with ⟨HVac | HZ | HCpl⟩
    · ileft; iexact HVac
    · iright; ileft; iexact HZ
    · iright; iright
      icases HCpl with ⟨%law, %n, %μ₁, %μ₁', %ν₀, %f', %R, %Hmap, %Hc, %Hside, %Herase₁,
        %Herase₂, Hcont⟩
      iexists law, n, μ₁, μ₁', ν₀, f', R
      iframe %
      iintro %σ₂ %ρ %hR
      imod Hcont $$ %σ₂ %ρ %hR with HΦ
      imodintro
      iapply Hwand $$ HΦ
  mono_pred_ne := specCouplState_ne

/-! ## Introduction rules -/

theorem specCoupl_absorbing (hb : L.Absorbing b) : ⊢ specCoupl L E σ e' σ' b Z := by
  iapply least_fixpoint_unfold_mpr (specCouplPre L E Z)
  ileft; ipureintro; exact hb

theorem specCoupl_ret : Z σ ⟨e', σ'⟩ b ⊢ specCoupl L E σ e' σ' b Z := by
  iintro HZ
  iapply least_fixpoint_unfold_mpr (specCouplPre L E Z)
  iright; ileft; iexact HZ

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
    icases HCpl with ⟨%law, %n, %μ₁, %μ₁', %ν₀, %f', %R, %HCpl_map, %HCpl_coupl, %HCpl_side,
      %HCpl_e1, %HCpl_e2, HCpl_cont⟩
    iexists law, n, μ₁, μ₁', ν₀, f', R
    iframe %
    iintro %σ₂ %ρ %hR
    imod subset HE with Hclose
    imod HCpl_cont $$ %σ₂ %ρ %hR
    imod Hclose
    imodintro
    iapply HCpl_cont $$ HZ

theorem specCoupl_mono : iprop%
    (∀ σ' ρ' b', Z₁ σ' ρ' b' -∗ Z₂ σ' ρ' b') ∗ specCoupl L E σ e' σ' b Z₁ ⊢
      specCoupl L E σ e' σ' b Z₂ := by
  iintro ⟨HZ, HC⟩
  iapply specCoupl_bind LawfulSet.subset_refl
  iframe HC
  iintro %σ₂ %ρ₂ %b₂ Hz1
  iapply specCoupl_ret
  iapply HZ $$ Hz1

/-- `specCoupl` is non-expansive in the continuation `Z`. -/
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

/-! ## Coupling rules: wrappers around `specCoupl_rec` -/

variable (law : L.BindLaw)

/-- Introduce a spec coupling by a step of any bind law, whose spec distribution is the image of
the law's spec-side head measure under `f'` (Rocq `spec_coupl_rec_map`). -/
theorem specCoupl_couple_map {ν₀ : Measure (Cfg rT)} {f' : Cfg rT → Cfg rT}
    (hf' : Measurable f') (hspec : (μ₁'.bind fun σ => pexecN n ⟨e₁', σ⟩) = ν₀.map f')
    (hhead : law.head μ₁ ν₀ R b) (hside : law.SideForExec μ₁ ν₀ R f')
    (Heras₁ : ErasableExpr μ₁ σ₁) (Heras₁' : ErasableExpr μ₁' σ₁') : iprop%
    (∀ σ₂ ρ, ⌜R σ₂ ρ < (⊤ : B)⌝ -∗ |={E}=>
        specCoupl L E σ₂ (f' ρ).expr (f' ρ).state (R σ₂ ρ) Z) ⊢
      specCoupl L E σ₁ e₁' σ₁' b Z := by
  -- `iframe %` closes the pure conjunct `⌜Measurable f' ∧ …⌝` from this hypothesis
  have hmap : _ ∧ _ := ⟨hf', hspec⟩
  iintro H
  iapply specCoupl_rec
  iexists law, n, μ₁, μ₁', ν₀, f', R
  iframe %
  iexact H

/-- Introduce a spec coupling by a step of any bind law between erasable distributions (Rocq
`spec_coupl_rec`). -/
theorem specCoupl_couple_law
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

/-- Introduce a spec coupling from a lifting of erasable distributions, via the canonical law. -/
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
theorem specCoupl_erasables {S : State rT → State rT → Prop} (Hcpl : L.Rel b₁ S μ₁ μ₁')
    (Heras₁ : ErasableExpr μ₁ σ₁) (Heras₁' : ErasableExpr μ₁' σ₁') : iprop%
    (∀ σ₂ σ₂', ⌜S σ₂ σ₂'⌝ -∗ |={E}=> specCoupl L E σ₂ e₁' σ₂' b₂ Z) ⊢
      specCoupl L E σ₁ e₁' σ₁' b Z := by
  have := Heras₁.isProbabilityMeasure
  have := Heras₁'.isProbabilityMeasure
  iintro H
  have heq : μ₁'.bind (fun σ => pexecN 0 ⟨e₁', σ⟩) = μ₁'.map (fun σ => (⟨e₁', σ⟩ : Cfg rT)) := by
    simp only [pexecN_zero]
    exact bind_dirac_eq_map _ (by fun_prop)
  iapply specCoupl_couple_rel (S := fun σ₂ c => S σ₂ c.state ∧ c.expr = e₁') (n := 0) hb
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

/-! ## One spec step -/

/-- Away from `urand`, a step is carried by its support of positive-mass points. -/
theorem concentrated_primStep_support (e : Exp rT) (σ : State rT) (hne : e.decomp.2 ≠ .urand) :
    Concentrated (primStep ⟨e, σ⟩) {ρ | 0 < primStep ⟨e, σ⟩ {ρ}} := by
  have heq : {ρ | 0 < primStep ⟨e, σ⟩ {ρ}}ᶜ = {ρ | primStep ⟨e, σ⟩ {ρ} = 0} := by
    ext ρ; simp [pos_iff_ne_zero]
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

/-- `specCoupl_step_concentrated` on the step's support, for a non-`urand` redex. -/
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

variable {e₂' : Exp rT}
variable {σ₂' : State rT}

/-- A deterministic spec run to `⟨e₂', σ₂'⟩` passes on any smaller budget, by a step of the unit
law (Rocq `spec_coupl_steps_det`, `spec_coupl_mono_grade`). -/
theorem fupd_specCoupl_steps_det_of_le {b₁ : B}
    (Hstep : pexecN n ⟨e₁', σ₁'⟩ = dirac ⟨e₂', σ₂'⟩) (hb : b₁ ≤ b) :
    iprop(|={E}=> specCoupl L E σ e₂' σ₂' b₁ Z) ⊢ specCoupl L E σ e₁' σ₁' b Z := by
  classical
  -- the unit law only carries a finite budget; at b₁ = ⊤ exit through absorption
  rcases lt_or_eq_of_le (le_top : b₁ ≤ (⊤ : B)) with hb₁ | rfl
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

variable {b₁ b₂ : B}

/-- A spec coupling absorbs a leading fancy update and may weaken its budget. -/
theorem fupd_specCoupl_of_le (hb : b₁ ≤ b₂) :
    iprop(|={E}=> specCoupl L E σ e' σ' b₁ Z) ⊢ specCoupl L E σ e' σ' b₂ Z :=
  fupd_specCoupl_steps_det_of_le (pexecN_zero _) hb

/-- A spec coupling at a smaller budget proves one at a larger budget. -/
theorem specCoupl_mono_budget (hb : b₁ ≤ b₂) :
    specCoupl L E σ e' σ' b₁ Z ⊢ specCoupl L E σ e' σ' b₂ Z :=
  fupd_intro.trans (fupd_specCoupl_of_le hb)

/-- A spec coupling absorbs a leading fancy update. -/
theorem fupd_specCoupl : iprop(|={E}=> specCoupl L E σ e' σ' b Z) ⊢ specCoupl L E σ e' σ' b Z :=
  fupd_specCoupl_of_le le_rfl

/-- A deterministic spec run to `⟨e₂', σ₂'⟩` passes on the coupling at its end. -/
theorem specCoupl_steps_det
    (Hstep : pexecN n ⟨e₁', σ₁'⟩ = dirac ⟨e₂', σ₂'⟩) :
    specCoupl L E σ e₂' σ₂' b Z ⊢ specCoupl L E σ e₁' σ₁' b Z :=
  fupd_intro.trans (fupd_specCoupl_steps_det_of_le Hstep le_rfl)

end Budget

end MicrometerWpGS

end ProbLang
