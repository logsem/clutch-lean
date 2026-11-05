module

public import Metrology.ProbLang.EctxTactic
public import Metrology.ProbLang.Exec
public import Metrology.ProbLang.Reals
public import Metrology.ProbLang.Syntax.LocallyClosed

/-! # Foreign calls: a toy instance

Foreign code given by Lean functions, with a callback into ProbLang, run end to end. -/

@[expose] public section

noncomputable section

open MeasureTheory Measure

namespace ProbLang.Test.FFI

open FFIOutcome DetHeadStep PureHeadStep

/-- Pairing a value with itself is measurable. -/
theorem measurable_pair_self : Measurable fun v : Val ℝ => v.pair v :=
  measurable_comap_iff.mpr (Exp.pair.measurable.comp (Val.fst.measurable.prodMk Val.fst.measurable))

/-- Toy foreign code: `#code 0` and `#code 2` pair their argument with itself, `#code 1` calls
`impl` and resumes at `#code 2`, `#code 3` writes its argument to location `0`; every other call is
stuck. -/
@[instance_reducible]
def toyFFI (impl : Val ℝ) : ProbLangFFI ℝ :=
  .ofCode (fun n x => match n with
    | 0 | 2 => some (.ret (x.1.pair x.1), x.2)
    | 1 => some (.call impl x.1 (.code 2), x.2)
    | 3 => some (.ret (.ofBaseLit .unit), x.2.insert 0 x.1)
    | _ => none) fun n => by
    have hret : Measurable fun x : Val ℝ × LocHeap (Val ℝ) =>
        some ((ret (x.1.pair x.1), x.2) : FFIOutcome ℝ × LocHeap (Val ℝ)) :=
      measurable_some.comp ((ret.measurable.comp
        (measurable_pair_self.comp measurable_fst)).prodMk measurable_snd)
    rcases n with _ | _ | _ | _ | n
    · exact hret
    · exact measurable_some.comp ((call.measurable.comp
        (measurable_const.prodMk (measurable_fst.prodMk measurable_const))).prodMk measurable_snd)
    · exact hret
    · exact measurable_some.comp (measurable_const.prodMk (by fun_prop))
    · exact measurable_const

/-- The call of `#code n` on `a`. -/
abbrev callOn (n : ℕ) (a : Exp ℝ) : Exp ℝ := .ffi (.pair (.lit (.code n)) a)

/-- ProbLang's `fun x => x + 1`. -/
abbrev incr : Exp ℝ := .lam (.binop .plus (.bvar 0) (.lit (.int 1)))

/-- `incr` as a value. -/
def incrVal : Val ℝ := ⟨incr, .lam (by is_lc), by is_lc⟩

/-- `pure_steps` works under any `ProbLangFFI`, also inside a foreign call's argument. -/
example {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT] [ProbLangDist rT] [ProbLangFFI rT]
    [ProbLangObs rT] :
    PureSteps (pl(ffi((#code 2, #1 + #2))) : Exp rT) pl(ffi((#code 2, #3))) := by
  pure_steps

variable [ProbLangDist ℝ] [ProbLangObs ℝ]

/-- With stuck foreign code, every foreign call is stuck. -/
example [ProbLangFFI ℝ] [ProbLangFFI.Stuck ℝ] (σ : State ℝ) :
    primStep (⟨callOn 1 (.lit (.int 3)), σ⟩ : Cfg ℝ) = 0 := by
  rw [primStep_eq_headStep rfl]
  simp only [headStep, Exp.asValM, Cfg.ffi_of_stuck]
  split <;> rfl

/-- The toy foreign code with `incr` as its callback. -/
@[instance_reducible]
def toyIncrFFI : ProbLangFFI ℝ := toyFFI incrVal

problang
  ffi toyIncrFFI

/-- The callback body `incr #3` runs to `#4` inside the paused call. -/
example : PureSteps (callOn 2 (.app incr (.lit (.int 3)))) (callOn 2 (.lit (.int 4))) := by
  pure_steps

/-- `#code 0` returns its argument paired with itself, in one step. -/
example (σ : State ℝ) :
    pexecN 1 (⟨callOn 0 (.lit (.int 3)), σ⟩ : Cfg ℝ) =
      dirac ⟨.pair (.lit (.int 3)) (.lit (.int 3)), σ⟩ :=
  pexecN_1_of_DetStep (ffi (r := (.ret (Val.int 3 |>.pair (Val.int 3)), σ.heap)) σ
    rfl rfl).toDetStep

/-- A callback: `#code 1` on `#3` calls `incr` on `#3` and resumes at `#code 2` with the reply
`#4`. -/
example (σ : State ℝ) :
    pexecN 4 (⟨callOn 1 (.lit (.int 3)), σ⟩ : Cfg ℝ) =
      dirac ⟨.pair (.lit (.int 4)) (.lit (.int 4)), σ⟩ := by
  have hcall : pexecN 1 (⟨callOn 1 (.lit (.int 3)), σ⟩ : Cfg ℝ) =
      dirac ⟨callOn 2 (.app incr (.lit (.int 3))), σ⟩ :=
    pexecN_1_of_DetStep (ffi (r := (.call incrVal (Val.int 3) (.code 2), σ.heap)) σ
      rfl rfl).toDetStep
  have hbody : nsteps PureStep 2 (.app incr (.lit (.int 3)) : Exp ℝ) (.lit (.int 4)) :=
    ⟨_, (app_lam incrVal.lc .lit).toPureStep,
      _, (binop .lit .lit rfl).toPureStep, rfl⟩
  have hreply : pexecN 2 (⟨callOn 2 (.app incr (.lit (.int 3))), σ⟩ : Cfg ℝ) =
      dirac ⟨callOn 2 (.lit (.int 4)), σ⟩ :=
    pexecN_of_DetExec (DetExec.of_nsteps_PureStep σ
      (PureStep.fill_nsteps [.pairR (.lit (.code 2)), .ffi] hbody))
  have hret : pexecN 1 (⟨callOn 2 (.lit (.int 4)), σ⟩ : Cfg ℝ) =
      dirac ⟨.pair (.lit (.int 4)) (.lit (.int 4)), σ⟩ :=
    pexecN_1_of_DetStep (ffi (r := (.ret (Val.int 4 |>.pair (Val.int 4)), σ.heap)) σ
      rfl rfl).toDetStep
  exact pexecN_det_trans hcall (pexecN_det_trans hreply hret)

/-- `#code 3` writes its argument to the heap and returns `()`. -/
example (σ : State ℝ) :
    pexecN 1 (⟨callOn 3 (.lit (.int 3)), σ⟩ : Cfg ℝ) =
      dirac ⟨.lit .unit, σ.updateHeap (·.insert 0 (Val.int 3))⟩ :=
  pexecN_1_of_DetStep (ffi (r := (.ret (.ofBaseLit .unit), σ.heap.insert 0 (Val.int 3)))
    σ
      rfl rfl).toDetStep

end ProbLang.Test.FFI
