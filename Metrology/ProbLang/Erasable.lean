module

public import Metrology.ProbLang.Exec

@[expose] public section

/-!
# Erasable and rewritable distributions

Port of `theories/common/erasable.v` from Clutch.

Clutch's `erasable` is phrased over `distr val`, so it ignores tape differences at final values.
Our `Erasable` is phrased over `Measure Cfg`, so it is strictly stronger: `tapePresample`-style
distributions are not erasable, and `Erasure.lean` states those results as couplings instead.
-/

namespace ProbLang

variable {rT : Type _} [LawfulProbLangℝ rT]

open MeasureTheory MeasureTheory.Measure ProbLang.Measure

/-! ## Erasable -/

/-- Sampling the initial state from `μ` does not change `execN m` at any budget `m`. -/
def Erasable (μ : Measure (State rT)) (σ : State rT) : Prop :=
  ∀ (e : Exp rT) (m : Nat),
    μ.bind (fun σ' => execN m ⟨e, σ'⟩) = execN m ⟨e, σ⟩

namespace Erasable

theorem dret (σ : State rT) : Erasable (Measure.dirac σ) σ := by
  intro e m
  rw [Measure.dirac_bind (by measurability)]

theorem dbind
    {μ₁ : Measure (State rT)} {μ₂ : State rT → Measure (State rT)} {σ : State rT}
    (h₁ : Erasable μ₁ σ) (h₂ : ∀ σ', Erasable (μ₂ σ') σ') (hm₂ : AEMeasurable μ₂ μ₁) :
    Erasable (μ₁.bind μ₂) σ := by
  intro e m
  rw [Measure.bind_bind hm₂ (Measurable.aemeasurable (by measurability))]
  simp only [fun σ' => h₂ σ' e m]
  exact h₁ e m

theorem lim_exec
    {μ : Measure (State rT)} {σ : State rT} (h : Erasable μ σ) (e : Exp rT) :
    μ.bind (fun σ' => limExec ⟨e, σ'⟩) = limExec ⟨e, σ⟩ := by
  ext S HS
  rw [bind_apply HS (by measurability)]
  simp_rw [limExec_apply _ HS]
  rw [lintegral_iSup (fun n => ?measurable) ?mono]
  case measurable =>
    exact (Measure.measurable_coe HS).comp ((execN_measurable n).comp (by measurability))
  case mono => exact fun n m hnm a => execN_mono hnm ⟨e, a⟩ S
  suffices hbind : ∀ n, ∫⁻ σ', (execN n ⟨e, σ'⟩) S ∂μ = (execN n ⟨e, σ⟩) S by
    simp [hbind]
  intro n
  rw [← h e n, bind_apply HS (by measurability)]

theorem dret_final {μ : Measure (State rT)} {σ : State rT} {e : Exp rT} (hv : IsVal e)
    (h : Erasable μ σ) :
    μ.bind (fun σ' => Measure.dirac (⟨e, σ'⟩ : Cfg rT)) =
      Measure.dirac (⟨e, σ⟩ : Cfg rT) := by
  have hstep : ∀ σ' : State rT,
      execN 1 (⟨e, σ'⟩ : Cfg rT) = Measure.dirac (⟨e, σ'⟩ : Cfg rT) :=
    fun _ => execN_succ_isValue hv.toIsValue 0
  calc μ.bind (fun σ' => Measure.dirac (⟨e, σ'⟩ : Cfg rT))
      = μ.bind (fun σ' => execN 1 ⟨e, σ'⟩) := by simp only [hstep]
    _ = execN 1 ⟨e, σ⟩ := h e 1
    _ = Measure.dirac ⟨e, σ⟩ := hstep σ

theorem pexecN_lim_exec
    {μ : Measure (State rT)} {σ : State rT}
    (h : Erasable μ σ) (n : Nat) (e : Exp rT) :
    (μ.bind (fun σ' => pexecN n ⟨e, σ'⟩)).bind limExec = limExec ⟨e, σ⟩ := by
  rw [Measure.bind_bind
        (Measurable.aemeasurable (by measurability))
        (Measurable.aemeasurable (by measurability))]
  simp only [fun σ' => (limExec_pexecN n ⟨e, σ'⟩).symm]
  exact h.lim_exec e

theorem mass
    {μ : Measure (State rT)} {σ : State rT} (h : Erasable μ σ) :
    μ Set.univ = 1 := by
  have hv : IsVal (Exp.lit (rT := rT) .unit) := .lit
  have hstep : ∀ σ' : State rT,
      execN 1 ((⟨.lit .unit, σ'⟩ : Cfg rT)) = Measure.dirac (⟨.lit .unit, σ'⟩ : Cfg rT) :=
    fun σ' => execN_succ_isValue hv.toIsValue 0
  have huniv := congrArg (fun ν => ν (Set.univ : Set (Cfg rT))) (h (.lit .unit) 1)
  rw [hstep σ, Measure.dirac_apply' _ .univ] at huniv
  simp at huniv
  rw [bind_apply .univ (Measurable.aemeasurable (by measurability))] at huniv
  simp_rw [hstep, Measure.dirac_apply' _ .univ] at huniv
  simpa using huniv

/-- Branching on a Boolean through a probability distribution preserves erasability. -/
theorem dbind_predicate {A : Type*} [MeasurableSpace A] [DiscreteMeasurableSpace A]
    {μ : Measure A} {μ₁ μ₂ : Measure (State rT)} {σ : State rT} {f : A → Bool}
    (hμ : μ Set.univ = 1) (h₁ : Erasable μ₁ σ) (h₂ : Erasable μ₂ σ) :
    Erasable (μ.bind (fun a => if f a then μ₁ else μ₂)) σ := by
  intro e m
  rw [Measure.bind_bind
        (Measurable.aemeasurable .of_discrete)
        (Measurable.aemeasurable (by measurability))]
  have hker : ∀ a : A,
      (if f a then μ₁ else μ₂).bind (fun σ' => execN m ⟨e, σ'⟩) = execN m ⟨e, σ⟩ := by
    intro a
    split
    exacts [h₁ e m, h₂ e m]
  simp only [hker]
  refine Measure.ext fun S hS => ?_
  rw [bind_apply hS measurable_const.aemeasurable, lintegral_const, hμ, mul_one]

end Erasable

/-! ## Rewritable -/

def Rewritable (ρ : Cfg rT) (μ : Measure (Cfg rT)) : Prop :=
  limExec ρ = μ.bind limExec

namespace Rewritable

theorem dret (ρ : Cfg rT) : Rewritable ρ (Measure.dirac ρ) :=
  (Measure.dirac_bind limExec.measurable ρ).symm

theorem ofPexecN (ρ : Cfg rT) (m : Nat) : Rewritable ρ (ProbLang.pexecN m ρ) :=
  limExec_pexecN m ρ

theorem of_erasable {ρ : Cfg rT} {μ : Measure (State rT)} (h : Erasable μ ρ.state) :
    Rewritable ρ (μ.bind (fun σ => Measure.dirac (⟨ρ.expr, σ⟩ : Cfg rT))) := by
  show limExec ρ
      = (μ.bind (fun σ => Measure.dirac (⟨ρ.expr, σ⟩ : Cfg rT))).bind limExec
  rw [Measure.bind_bind
        (Measurable.aemeasurable (by measurability))
        (Measurable.aemeasurable limExec.measurable)]
  simp only [Measure.dirac_bind limExec.measurable]
  rw [h.lim_exec ρ.expr]

theorem of_erasable_pexecN {ρ : Cfg rT} {μ : Measure (State rT)} (m : Nat)
    (h : Erasable μ ρ.state) :
    Rewritable ρ (μ.bind (fun σ => pexecN m ⟨ρ.expr, σ⟩)) := by
  show limExec ρ = (μ.bind (fun σ => pexecN m ⟨ρ.expr, σ⟩)).bind limExec
  rw [Measure.bind_bind
        (Measurable.aemeasurable (by measurability))
        (Measurable.aemeasurable limExec.measurable)]
  simp only [fun σ => (limExec_pexecN m ⟨ρ.expr, σ⟩).symm]
  rw [h.lim_exec ρ.expr]

end Rewritable

/-- Mirrors Clutch's `rewritable_of_erasable`. -/
noncomputable def rewritableOfErasable (μ : Measure (State rT)) (e : Exp rT) : Measure (Cfg rT) :=
  μ.bind (fun σ => Measure.dirac ⟨e, σ⟩)

end ProbLang
