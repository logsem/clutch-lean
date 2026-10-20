module

public import Metrology.Micrometer.AdequacyRel
public import Metrology.Couplings.Divergences.Mechanism

/-! # Programs as mechanisms

A ProbLang program family `p : X → Exp` run from a fixed state is a mechanism (`progMech`).
Main result: `progMech_isPrivate`, a refinement from `↯b b` on adjacent inputs makes it
`b`-private. -/

@[expose] public section

namespace ProbLang

open Iris Iris.BI GradedLifting ProbabilityTheory

variable {rT : Type} [LawfulProbLangℝ rT] {X : Type} [MeasurableSpace X]

/-! ## The mechanism of a program family -/

/-- The program family `p` run from state `σ`, as a mechanism on its inputs. -/
noncomputable def progMech (p : X → Exp rT) (σ : State rT)
    (hp : Measurable fun x ↦ (⟨p x, σ⟩ : Cfg rT) := by exact .of_discrete) :
    Mechanism X (Exp rT) :=
  ⟨fun x ↦ limExecV ⟨p x, σ⟩, limExecV.measurable.comp hp⟩

@[simp]
theorem progMech_apply (p : X → Exp rT) (σ : State rT) {hp} (x : X) :
    progMech p σ hp x = limExecV ⟨p x, σ⟩ :=
  rfl

/-- A program mechanism has total mass at most one. -/
instance isSubMarkovKernel_progMech (p : X → Exp rT) (σ : State rT) {hp} :
    IsSubMarkovKernel (progMech p σ hp) where
  isSubProbabilityMeasure _ := limExecV.isSubProbabilityMeasure _

variable [MeasurableSingletonClass rT] {B : Type} [AddCommMonoid B] [PartialOrder B]
  [CanonicallyOrderedAdd B] [OrderTop B] [Nontrivial B] {L : GradedLifting.{0} B} [L.IsLawful]
  [L.IsZeroLeft] [L.IsLeftContinuous] [L.IsBudgetClosed]

/-! ## Privacy from refinement -/

/-- A refinement at equal results from `↯b b` on adjacent inputs couples the mechanism's
outputs at `b` along equality (clutch-dp's `adequacy_rel.v`). -/
theorem progMech_rel (GF : BundledGFunctors) [RefinesPreGS rT B GF] (p : X → Exp rT)
    (σ : State rT) {hp} {adj : Adjacency X} (b : B)
    (A : ∀ (_ : MicrometerRGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF), lrel rT GF)
    (HA : ∀ (IR : MicrometerRGS rT .hasNoLC GF) (IBC : BudgetCreditGS B GF) (v v' : Val rT),
      ⊢@{IProp GF} (A IR IBC).car v v' -∗ ⌜v = v'⌝)
    (Hlog : ∀ x x', adj x x' → ∀ (IR : MicrometerRGS rT .hasNoLC GF)
      (IBC : BudgetCreditGS B GF), ⊢@{IProp GF} ↯b b -∗ refines L ⊤ (p x) (p x') (A IR IBC))
    ⦃x x' : X⦄ (hx : adj x x') :
    L.Rel b (· = ·) (progMech p σ hp x) (progMech p σ hp x') :=
  -- closed-program adequacy gives `L.Rel b (adequacyRel (· = ·))`; weaken that relation to `=`
  (approximates_coupling A (· = ·) _ _ σ σ b HA (Hlog x x' hx)).mono le_rfl
    adequacyRel_eq_subset

/-- A program family whose members on adjacent inputs refine each other at equal results from
`↯b b` is a `b`-private mechanism, for every divergence the lifting is sound for
(Approximate Span Liftings, Def. 2.1–2.5). -/
theorem progMech_isPrivate (GF : BundledGFunctors) [RefinesPreGS rT B GF]
    {D : GradedDivergence.{0} B} [L.IsSound D] (p : X → Exp rT) (σ : State rT) {hp}
    {adj : Adjacency X} (b : B)
    (A : ∀ (_ : MicrometerRGS rT .hasNoLC GF) (_ : BudgetCreditGS B GF), lrel rT GF)
    (HA : ∀ (IR : MicrometerRGS rT .hasNoLC GF) (IBC : BudgetCreditGS B GF) (v v' : Val rT),
      ⊢@{IProp GF} (A IR IBC).car v v' -∗ ⌜v = v'⌝)
    (Hlog : ∀ x x', adj x x' → ∀ (IR : MicrometerRGS rT .hasNoLC GF)
      (IBC : BudgetCreditGS B GF), ⊢@{IProp GF} ↯b b -∗ refines L ⊤ (p x) (p x') (A IR IBC)) :
    (progMech p σ hp).IsPrivate D adj b :=
  fun _ _ hx ↦ IsSound.sound (progMech_rel GF p σ b A HA Hlog hx)

end ProbLang
