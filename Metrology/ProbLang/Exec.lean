module

public import Metrology.ProbLang.Measure
public import Metrology.Couplings.SubProbability
public import Metrology.ProbLang.HeadStep
public import Metrology.ProbLang.DetStep
public import Metrology.ProbLang.Discrete
public import Metrology.Couplings.Lifting
public import Metrology.Couplings.AdditiveCouplings

@[expose] public section

/-! # Program execution and the output distribution

Bounded execution `execN`, its supremum `limExec`, and the output distribution `limExecV`.
Main results: the one-step unfolding `limExec_not_final` and the limit rule `limExecV_lift`. -/

noncomputable section
open Classical MeasureTheory ProbabilityTheory Measure ProbLang

namespace ProbLang

variable {rT : Type _} [LawfulProbLangℝ rT]

/-! ## Bounded execution `execN` -/

/-- The final configurations of runs that reach a value within `n - 1` steps; runs still going are
dropped (so `execN 0 = 0`). -/
def execN (n : Nat) (ρ : Cfg rT) : Measure (Cfg rT) :=
  match n with
  | 0 => 0
  | n + 1 => if ρ.expr.isValue then dirac ρ else (primStep ρ).bind (execN n)

@[fun_prop]
theorem execN_measurable (n : Nat) : Measurable (execN (rT := rT) n) := by
  induction n
  · simp [execN]
  · exact Measurable.ite (by measurability) (by measurability) (by measurability)

@[simp] theorem execN_zero (ρ : Cfg rT) : execN 0 ρ = 0 := rfl

@[simp] theorem execN_succ_isValue {ρ : Cfg rT} (hv : ρ.expr.isValue) (n : Nat) :
    execN (n + 1) ρ = dirac ρ := by
  simp [execN, hv]

theorem execN_succ_not_isValue {ρ : Cfg rT} (hv : ¬ ρ.expr.isValue) (n : Nat) :
    execN (n + 1) ρ = (primStep ρ).bind (execN n) := by
  simp [execN, hv]

/-! ## Mass and monotonicity of `execN` -/

/-- Bounded execution has mass at most one. -/
theorem execN_univ_le_one
    (n : Nat) (ρ : Cfg rT) : (execN n ρ) Set.univ ≤ 1 := by
  induction n generalizing ρ with
  | zero => simp [execN]
  | succ k ih =>
    unfold execN
    by_cases hv : ρ.expr.isValue
    · simp [hv]
    · simp only [hv, ↓reduceIte]
      rw [bind_apply (by measurability) (Measurable.aemeasurable (by measurability))]
      calc ∫⁻ a, (execN k a) Set.univ ∂(primStep ρ)
          ≤ ∫⁻ _, 1 ∂(primStep ρ) := lintegral_mono fun a => ih a
        _ = (primStep ρ) Set.univ := by simp
        _ ≤ 1 := primStep_univ_le_one ρ

/-- Bounded execution is a sub-probability measure. -/
instance execN.isSubProbabilityMeasure (n : Nat) (ρ : Cfg rT) :
    IsSubProbabilityMeasure (execN n ρ) := ⟨execN_univ_le_one n ρ⟩

/-- Bind is monotone in the kernel (ported from `SampCert/SLang.lean`). -/
theorem Measure.bind_mono_right' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f g : α → Measure β) (Hf : Measurable f) (Hg : Measurable g)
    (h : ∀ a, f a ≤ g a) :
    μ.bind f ≤ μ.bind g := by
  refine le_intro fun S HS HNE => ?_
  rw [bind_apply HS Hf.aemeasurable, bind_apply HS Hg.aemeasurable]
  exact lintegral_mono (fun a => h a S)

/-- One more step of fuel only adds terminated runs. -/
theorem execN_le_succ (n : ℕ) (ρ : Cfg rT) : execN n ρ ≤ execN (n + 1) ρ := by
  induction n generalizing ρ with
  | zero => exact bot_le
  | succ k ih =>
    rw [execN, execN]
    split
    · exact le_rfl
    · exact Measure.bind_mono_right' _ _ _ (execN_measurable _) (execN_measurable _) ih

/-- Bounded execution is monotone in the fuel. -/
theorem execN_mono {n m : ℕ} (h : n ≤ m) (ρ : Cfg rT) : execN n ρ ≤ execN m ρ := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (execN_le_succ _ ρ)

theorem execN_monotone : Monotone fun i ↦ execN (rT := rT) i ρ := fun _ _ h => execN_mono h _

theorem execN_mono_singleton
    {n m : ℕ} (h : n ≤ m) (ρ : Cfg rT) (c : Cfg rT) :
    execN n ρ {c} ≤ execN m ρ {c} :=
  execN_mono h ρ {c}

/-! ## The output distribution `limExec` / `limExecV` -/

/-- The output distribution over final configurations: the supremum of `execN` over fuel. -/
def limExec (ρ : Cfg rT) : Measure (Cfg rT) := ⨆ (i : ℕ), execN i ρ

/-- The expression marginal of a measure on configurations. -/
def asExpr (μ : Measure (Cfg rT)) : Measure (Exp rT) := μ.map (·.expr)

/-- `asExpr` preserves sub-probability measures. -/
instance asExpr.isSubProbabilityMeasure (μ : Measure (Cfg rT)) [IsSubProbabilityMeasure μ] :
    IsSubProbabilityMeasure (asExpr μ) :=
  isSubProbabilityMeasure_map _ _

/-- The output distribution over values: `limExec` with the final state forgotten. -/
def limExecV (ρ : Cfg rT) : Measure (Exp rT) := asExpr <| limExec ρ

/-- A monotone supremum of measures is computed setwise. -/
theorem iSup_measure_apply {f : ℕ → Measure (Cfg rT)} (hf : Monotone f)
    {S : Set (Cfg rT)} (HS : MeasurableSet S) :
    (⨆ i, f i) S = ⨆ i, f i S :=
  Measure.iSup_apply_of_monotone hf HS

/-- The probability of an event under `limExec` is the supremum over bounded runs. -/
theorem limExec_apply (ρ : Cfg rT) (HS : MeasurableSet S) :
    limExec ρ S = ⨆ n, (execN n ρ) S :=
  iSup_measure_apply execN_monotone HS

theorem limExec_univ (ρ : Cfg rT) : (limExec ρ) .univ = ⨆ n, (execN n ρ) .univ :=
  limExec_apply _ .univ

theorem asExpr.measurable :
    Measurable (asExpr : Measure (Cfg rT) → Measure (Exp rT)) :=
  Measure.measurable_map _ Cfg.measurable_expr

@[fun_prop]
theorem limExec.measurable : Measurable (limExec : Cfg rT → Measure (Cfg rT)) :=
  Measure.measurable_iSup_of_monotone (fun n => execN_measurable n)
    (fun ρ _ _ h => execN_mono h ρ)

@[fun_prop]
theorem limExecV.measurable : Measurable (limExecV : Cfg rT → Measure (Exp rT)) :=
  asExpr.measurable.comp limExec.measurable

/-- A bound on an event under every bounded run bounds it under `limExec`. -/
theorem limExec_leq_setwise {ρ : Cfg rT} {S : Set (Cfg rT)} {r : ENNReal} (HS : MeasurableSet S)
    (H : ∀ n, (execN n ρ) S ≤ r) : (limExec ρ) S ≤ r :=
  (limExec_apply _ HS).trans_le (iSup_le H)

/-- A bound on the mass of every bounded run bounds the mass of `limExec` (Rocq `lim_exec_leq`). -/
theorem limExec_leq_mass {ρ : Cfg rT} {r : ENNReal}
    (H : ∀ n, (execN n ρ) Set.univ ≤ r) : (limExec ρ) Set.univ ≤ r :=
  (limExec_univ ρ).trans_le (iSup_le H)

/-- `limExec` is a sub-probability measure: its missing mass is the probability of not returning. -/
instance limExec.isSubProbabilityMeasure (ρ : Cfg rT) : IsSubProbabilityMeasure (limExec ρ) :=
  ⟨limExec_leq_mass fun n ↦ execN_univ_le_one n ρ⟩

/-- `limExecV` is a sub-probability measure. -/
instance limExecV.isSubProbabilityMeasure (ρ : Cfg rT) : IsSubProbabilityMeasure (limExecV ρ) :=
  isSubProbabilityMeasure_map _ _

/-- `limExecV` as a kernel from configurations to expressions. -/
def limExecVKernel : Kernel (Cfg rT) (Exp rT) := ⟨limExecV, limExecV.measurable⟩

instance limExecVKernel.isSubMarkovKernel : IsSubMarkovKernel (limExecVKernel (rT := rT)) :=
  ⟨limExecV.isSubProbabilityMeasure⟩

/-! ## Terminating runs -/

/-- A value's execution is its Dirac measure (Rocq `lim_exec_final`, value case). -/
theorem limExec_of_isVal {e : Exp rT} {σ : State rT} (Hv : IsVal e) :
    limExec ⟨e, σ⟩ = dirac ⟨e, σ⟩ := by
  unfold limExec
  have hv : e.isValue := ⟨Hv⟩
  apply le_antisymm
  · refine iSup_le fun
      | 0 => bot_le
      | n + 1 => by simp [execN, hv]
  · exact le_iSup_of_le 1 (by simp [execN, hv])

/-- A run of mass `1` within `n` steps is the whole execution. -/
theorem limExec_term {ρ : Cfg rT} {n : Nat} (Hv : (execN n ρ) Set.univ = 1) :
    limExec ρ = execN n ρ :=
  have hle : execN n ρ ≤ limExec ρ := le_iSup (fun i ↦ execN i ρ) n
  (Measure.eq_of_le_of_measure_univ_eq hle
    (le_antisymm (hle _) (Hv ▸ IsSubProbabilityMeasure.measure_le_one _))).symm

/-- A bounded run that deterministically ends at `ρ'` is the whole execution. -/
theorem limExec_det_final {ρ ρ' : Cfg rT} {n : Nat} (H : (execN n ρ) = dirac ρ') :
    limExec ρ = dirac ρ' := by
  have htot : (execN n ρ) Set.univ = 1 := H ▸ dirac_apply_of_mem trivial
  rw [limExec_term htot, H]

/-! ## Unfolding `limExec` one step -/

/-- Running a non-value is one step followed by running the result. -/
theorem limExec_not_final
    {e : Exp rT} {σ : State rT} (Hnv : ¬ e.isValue) :
    limExec ⟨e, σ⟩ = (primStep ⟨e, σ⟩).bind limExec := by
  have hmono : Monotone (fun n => execN n ⟨e, σ⟩) := fun _ _ h => execN_mono h _
  have hstep : Monotone fun n => (primStep ⟨e, σ⟩).bind (execN n) := fun n m h =>
    Measure.bind_mono_right' _ _ _ (execN_measurable n) (execN_measurable m) fun a => execN_mono h a
  -- Drop the `n = 0` term, unfold each `execN (n + 1)`, then swap sup and integral setwise.
  rw [limExec, ← hmono.iSup_nat_add 1]
  simp_rw [execN_succ_not_isValue (ρ := ⟨e, σ⟩) Hnv]
  refine Measure.ext fun S HS => ?_
  rw [iSup_measure_apply hstep HS, Measure.bind_apply HS limExec.measurable.aemeasurable]
  calc ⨆ n, ((primStep ⟨e, σ⟩).bind (execN n)) S
      = ⨆ n, ∫⁻ a, execN n a S ∂primStep ⟨e, σ⟩ :=
        iSup_congr fun n => Measure.bind_apply HS (execN_measurable n).aemeasurable
    _ = ∫⁻ a, ⨆ n, execN n a S ∂primStep ⟨e, σ⟩ :=
        (lintegral_iSup (fun n => (measurable_coe HS).comp (execN_measurable n))
          fun n m h a => execN_mono h a S).symm
    _ = ∫⁻ a, limExec a S ∂primStep ⟨e, σ⟩ :=
        lintegral_congr fun a => (iSup_measure_apply (fun _ _ h => execN_mono h a) HS).symm

/-- One step, except that a value stays put. -/
def stepOrFinal (ρ : Cfg rT) : Measure (Cfg rT) :=
  if ρ.expr.isValue then dirac ρ else primStep ρ

theorem stepOrFinal_isValue {ρ : Cfg rT} (hv : ρ.expr.isValue) :
    stepOrFinal ρ = dirac ρ := by
  simp [stepOrFinal, hv]

theorem stepOrFinal_not_isValue {ρ : Cfg rT} (hv : ¬ ρ.expr.isValue) :
    stepOrFinal ρ = primStep ρ := by
  simp [stepOrFinal, hv]

@[fun_prop]
theorem stepOrFinal.measurable :
    Measurable (stepOrFinal : Cfg rT → Measure (Cfg rT)) := by
  exact Measurable.ite Cfg.isValue_measurableSet measurable_dirac primStep.measurable

/-- `limExec` is a fixed point of `stepOrFinal`. -/
theorem limExec_step (ρ : Cfg rT) : limExec ρ = (stepOrFinal ρ).bind limExec := by
  show limExec ρ = (if ρ.expr.isValue then dirac ρ else primStep ρ).bind limExec
  obtain ⟨e, σ⟩ := ρ
  by_cases hv : e.isValue
  · simp only [hv, ↑reduceIte]
    rw [Measure.dirac_bind (by measurability)]
  · simp only [hv, ↑reduceIte]
    exact limExec_not_final hv

/-! ## `pexecN`: the `n`-step unfolding

Unlike `execN` (where `execN 0 = 0`), `pexecN` keeps unfinished runs, so it is additive
(`pexecN_plus`); `limExec_pexecN` is the `n`-step unfolding of `limExec`. -/

/-- `n` iterations of `stepOrFinal`. -/
def pexecN (n : Nat) (ρ : Cfg rT) : Measure (Cfg rT) :=
  match n with
  | 0 => dirac ρ
  | n + 1 => (stepOrFinal ρ).bind (pexecN n)

@[fun_prop]
theorem pexecN_measurable {n : Nat} : Measurable (pexecN (rT := rT) n) := by
  induction n <;> simp [pexecN] <;> measurability

@[simp] theorem pexecN_zero (ρ : Cfg rT) : pexecN 0 ρ = dirac ρ := rfl

theorem pexecN_succ (n : Nat) (ρ : Cfg rT) :
    pexecN (n + 1) ρ = (stepOrFinal ρ).bind (pexecN n) := rfl

theorem pexecN_univ_le_one (n : Nat) (ρ : Cfg rT) : pexecN n ρ Set.univ ≤ 1 := by
  induction n generalizing ρ with
  | zero => simp
  | succ k ih =>
    rw [pexecN_succ, bind_apply .univ pexecN_measurable.aemeasurable]
    calc ∫⁻ a, pexecN k a Set.univ ∂(stepOrFinal ρ)
      _ ≤ ∫⁻ _, 1 ∂(stepOrFinal ρ) := lintegral_mono fun a => ih a
      _ = stepOrFinal ρ Set.univ := by simp
      _ ≤ 1 := by
        by_cases hv : ρ.expr.isValue
        · simp [stepOrFinal_isValue hv]
        · simpa [stepOrFinal_not_isValue hv] using primStep_univ_le_one ρ

/-- Iterated stepping has mass at most one. -/
instance pexecN.isSubProbabilityMeasure (n : Nat) (ρ : Cfg rT) :
    IsSubProbabilityMeasure (pexecN n ρ) := ⟨pexecN_univ_le_one n ρ⟩

/-- Running an expression for `n` steps from a sub-probability measure of states keeps mass at
most one. -/
instance isSubProbabilityMeasure_bind_pexecN (μ : Measure (State rT)) [IsSubProbabilityMeasure μ]
    (e : Exp rT) (n : Nat) : IsSubProbabilityMeasure (μ.bind fun σ ↦ pexecN n ⟨e, σ⟩) :=
  have hk : Measurable fun σ : State rT ↦ pexecN n ⟨e, σ⟩ :=
    pexecN_measurable.comp (Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
  isSubProbabilityMeasure_bind _ _ hk.aemeasurable

theorem pexecN_one (ρ : Cfg rT) : pexecN 1 ρ = stepOrFinal ρ := by
  show (stepOrFinal ρ).bind dirac = stepOrFinal ρ
  exact Measure.bind_dirac

/-- Running `n + m` steps is running `n` steps, then `m` more. -/
theorem pexecN_plus (n m : Nat) (ρ : Cfg rT) : pexecN (n + m) ρ = (pexecN n ρ).bind (pexecN m) := by
  induction n generalizing ρ with
  | zero =>
    simp
    rw [Measure.dirac_bind (by measurability)]
  | succ k ih =>
    rw [show (k + 1 + m) = (k + m) + 1 by linarith]
    simp [pexecN]
    rw [Measure.bind_bind]
    · congr 1
      grind
    all_goals exact Measurable.aemeasurable (by measurability)

/-- Deterministic multi-step runs compose. -/
theorem pexecN_det_trans {n m : Nat} {ρ ρ' ρ'' : Cfg rT} (Hn : pexecN n ρ = dirac ρ')
    (Hm : pexecN m ρ' = dirac ρ'') : pexecN (n + m) ρ = dirac ρ'' := by
  rw [pexecN_plus, Hn, dirac_bind pexecN_measurable, Hm]

/-- `limExec` is `n` steps of `pexecN` followed by `limExec`. -/
theorem limExec_pexecN (n : Nat) (ρ : Cfg rT) : limExec ρ = (pexecN n ρ).bind limExec := by
  induction n generalizing ρ with
  | zero =>
    rw [pexecN_zero, Measure.dirac_bind]
    measurability
  | succ k ih =>
    rw [pexecN_succ]
    conv_lhs => rw [limExec_step]
    rw [Measure.bind_bind]
    · exact congrArg _ (funext ih)
    all_goals exact Measurable.aemeasurable (by measurability)

/-! ## Integrals against `limExec` -/

/-- An integral against `limExec` is the supremum of the integrals against bounded runs. -/
theorem lintegral_limExec
    (ρ : Cfg rT) (f : Cfg rT → ENNReal) :
    ∫⁻ x, f x ∂(limExec ρ) = ⨆ n, ∫⁻ x, f x ∂(execN n ρ) := by
  unfold limExec
  -- ≤: reduce to simple functions g, whose integral is Σ x · μ(g⁻¹{x}); each term commutes with
  -- the monotone sup. ≥: monotonicity.
  apply le_antisymm
  · rw [lintegral_def]
    refine iSup_le fun g => iSup_le fun hg => ?_
    have hstep : g.lintegral (⨆ i, execN i ρ) = ⨆ n, g.lintegral (execN n ρ) := by
      have hms : ∀ x, MeasurableSet (⇑g ⁻¹' {x}) := fun x => g.measurableSet_preimage _
      simp_rw [MeasureTheory.SimpleFunc.lintegral,
        show ∀ x, (⨆ i, execN i ρ) (⇑g ⁻¹' {x}) = ⨆ n, (execN n ρ) (⇑g ⁻¹' {x})
          from fun x => iSup_measure_apply execN_monotone (hms x),
        ENNReal.mul_iSup]
      exact ENNReal.finsetSum_iSup_of_monotone
        (fun x _ _ h => mul_le_mul' le_rfl ((execN_mono h ρ) _))
    rw [hstep]
    refine iSup_mono fun n => ?_
    rw [lintegral_def]
    exact le_iSup_of_le g (le_iSup_of_le hg le_rfl)
  · exact iSup_le fun n => lintegral_mono' (le_iSup (fun i => execN i ρ) n) le_rfl

/-! ## Liftings of the limit (Micrometer glue) -/

section Lifting

open GradedLifting

variable {B : Type*} {L : GradedLifting B} [L.IsLeftContinuous]

/-- The limit of the finite executions inherits a lifting from every stage. -/
theorem limExec_map_lift {X Y : Type _} [MeasurableSpace X] [MeasurableSpace Y] {b : B}
    {R : X → Y → B} {ρ : Cfg rT} {ν : Measure Y} [IsSubProbabilityMeasure ν] {F : Cfg rT → X}
    (hF : Measurable F) (H : ∀ n, L b R ((execN n ρ).map F) ν) :
    L b R ((limExec ρ).map F) ν := by
  -- Pushforward commutes with the monotone sup; left-continuity of `L` does the rest.
  rw [limExec, Measure.map_iSup_of_monotone execN_monotone hF]
  exact IsLeftContinuous.iSup_left (fun _ _ h ↦ Measure.map_mono (execN_mono h ρ) hF) H

/-- `limExec_map_lift` at `F := Cfg.expr`: the form `adequacy` needs. -/
theorem limExecV_lift {Y : Type _} [MeasurableSpace Y] {b : B} {R : Exp rT → Y → B}
    {ρ : Cfg rT} {ν : Measure Y} [IsSubProbabilityMeasure ν]
    (H : ∀ n, L b R (asExpr (execN n ρ)) ν) : L b R (limExecV ρ) ν :=
  limExec_map_lift Cfg.measurable_expr H

end Lifting

/-! ## Additive (total-variation) couplings of the limit -/

/-- The limit inherits an additive coupling from every stage (Rocq `lim_exec_ARcoupl`). -/
theorem limExec_AddCoupl
    {β : Type*} [MeasurableSpace β] {ε : ENNReal}
    {Φ : Set (Cfg rT × β)} {ρ : Cfg rT} {μ₂ : Measure β}
    (H : ∀ n, AddCoupl ε Φ (execN n ρ) μ₂) :
    AddCoupl ε Φ (limExec ρ) μ₂ := by
  intro ⟨f, hf, hfb⟩ ⟨g, hg, hgb⟩ hfg
  rw [lintegral_limExec ρ f]
  exact iSup_le fun n => H n ⟨f, hf, hfb⟩ ⟨g, hg, hgb⟩ hfg

/-- `limExec_AddCoupl` through a measurable map, without a discrete σ-algebra on its codomain. -/
theorem limExec_map_AddCoupl
    {γ β : Type*} [MeasurableSpace γ] [MeasurableSpace β] {ε : ENNReal}
    {Φ : Set (γ × β)} {ρ : Cfg rT} {μ₂ : Measure β}
    {F : Cfg rT → γ} (hF : Measurable F)
    (H : ∀ n, AddCoupl ε Φ ((execN n ρ).map F) μ₂) :
    AddCoupl ε Φ ((limExec ρ).map F) μ₂ := by
  refine AddCoupl.iSup_left (fun f hf => ?_) H
  simp_rw [lintegral_map hf hF]
  exact le_of_eq (lintegral_limExec ρ (fun a => f (F a)))

/-- `limExec_map_AddCoupl` at `F := Cfg.expr`: the additive-coupling form of `limExecV_lift`. -/
theorem limExecV_AddCoupl
    {β : Type*} [MeasurableSpace β] {ε : ENNReal}
    {Φ : Set (Exp rT × β)} {ρ : Cfg rT} {μ₂ : Measure β}
    (H : ∀ n, AddCoupl ε Φ (asExpr (execN n ρ)) μ₂) :
    AddCoupl ε Φ (limExecV ρ) μ₂ :=
  limExec_map_AddCoupl Cfg.measurable_expr H

/-! ## Splitting `execN` by termination time

Technical support ported from SampCert; not used by the rest of the execution theory above. -/

/-- Execution that reaches a value in exactly `N` steps. -/
def execExactN (N : Nat) (ρ : Cfg rT) : Measure (Cfg rT) :=
  match N with
  | 0 => if ρ.expr.isValue then dirac ρ else 0
  | N + 1 => if ρ.expr.isValue then 0 else (primStep ρ).bind (execExactN N)

@[fun_prop]
theorem execExactN_measurable (n : Nat) : Measurable (execExactN (rT := rT) n) := by
  induction n <;> simp only [execExactN] <;>
    exact Measurable.ite (by measurability) (by measurability) (by measurability)

/-- `execN n` splits by exact termination time (setwise form of SampCert's `execExactN_sum`). -/
theorem execExactN_sum_continuous {n : Nat} {ρ : Cfg rT} {S} (HS : MeasurableSet S) :
    execN n ρ S = ∑'(N : Nat), if N < n then execExactN N ρ S else 0 := by
  induction n generalizing ρ with
  | zero => simp [execN]
  | succ n ih =>
    simp only [execN]
    by_cases hv : ρ.expr.isValue
    · simp only [↓reduceIte, hv]
      rw [tsum_eq_zero_add' ENNReal.summable]
      simp only [Nat.zero_lt_succ, ↓reduceIte, execExactN, hv]
      simp
    · simp only [↓reduceIte, hv]
      rw [tsum_eq_zero_add' ENNReal.summable]
      have hzero : (if 0 < n + 1 then (execExactN 0 ρ) S else 0) = 0 := by simp [execExactN, hv]
      rw [hzero, zero_add, bind_apply HS (by measurability)]
      simp_rw [ih]
      rw [lintegral_tsum (fun k => ?G3)]
      case G3 =>
        refine Measurable.aemeasurable ?_
        refine Measurable.ite (by measurability) ?_ (by measurability)
        exact (measurable_coe HS).comp (execExactN_measurable _)
      congr 1
      ext k
      by_cases hk : k < n
      · have hk' : ∀ k, k + 1 < n + 1 ↔ k < n := by omega
        simp only [hk, hk', ↑reduceIte]
        rw [← bind_apply HS (Measurable.aemeasurable (by measurability))]
        simp only [execExactN, hv, ↑reduceIte]
      · simp [hk]

/-- Terminating in exactly `n` steps is part of terminating within `n + 1`. -/
theorem execExactN_mono_continuous {n : Nat} {ρ : Cfg rT} {S} (HS : MeasurableSet S) :
    execExactN n ρ S ≤ execN (n + 1) ρ S := by
  have hunfold : execExactN n ρ S = (if n < n + 1 then execExactN n ρ S else 0) := by simp
  rw [execExactN_sum_continuous HS, hunfold]
  exact ENNReal.le_tsum (f := fun N => if N < n + 1 then execExactN N ρ S else 0) n

end ProbLang
end
