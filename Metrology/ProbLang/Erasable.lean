module

public import Metrology.ProbLang.Exec

@[expose] public section

/-!
# Erasable and rewritable distributions

Port of Clutch's `erasable.v`. Clutch compares final values; ours compares whole `Measure Cfg`s,
so it is stronger: `tapePresample` is not erasable here; it satisfies the expression-projected
`ErasableExpr` (`Erasure/ErasableExpr.lean`).
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

/-- A Dirac state distribution is erasable. -/
theorem dret (σ : State rT) : Erasable (Measure.dirac σ) σ := by
  intro e m
  rw [Measure.dirac_bind (by measurability)]

/-- Sequencing preserves erasability. -/
theorem dbind
    {μ₁ : Measure (State rT)} {μ₂ : State rT → Measure (State rT)} {σ : State rT}
    (h₁ : Erasable μ₁ σ) (h₂ : ∀ σ', Erasable (μ₂ σ') σ') (hm₂ : AEMeasurable μ₂ μ₁) :
    Erasable (μ₁.bind μ₂) σ := by
  intro e m
  rw [Measure.bind_bind hm₂ (Measurable.aemeasurable (by measurability))]
  simp only [fun σ' => h₂ σ' e m]
  exact h₁ e m

/-- Erasability passes from every bounded run to the limit (monotone convergence). -/
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

/-- Pairing a value with an erasable state distribution gives the Dirac at the value in `σ`. -/
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

/-- An erasable distribution is a probability measure (run `()` one step). -/
theorem mass
    {μ : Measure (State rT)} {σ : State rT} (h : Erasable μ σ) :
    μ Set.univ = 1 := by
  have huniv := congrArg (fun ν => ν (Set.univ : Set (Cfg rT)))
    (h.dret_final (e := Exp.lit .unit) .lit)
  simp only [Measure.dirac_apply' _ MeasurableSet.univ] at huniv
  rw [bind_apply .univ (Measurable.aemeasurable (by measurability))] at huniv
  simpa [Measure.dirac_apply' _ MeasurableSet.univ] using huniv

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

/-- `μ` is a rewriting of `ρ`: running `ρ` equals sampling from `μ` then running. -/
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

/-- Samples the state from `μ` and keeps the expression `e` (Clutch `rewritable_of_erasable`). -/
noncomputable def rewritableOfErasable (μ : Measure (State rT)) (e : Exp rT) : Measure (Cfg rT) :=
  μ.bind (fun σ => Measure.dirac ⟨e, σ⟩)

end ProbLang
