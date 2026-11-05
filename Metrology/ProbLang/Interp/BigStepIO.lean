module

public import Metrology.ProbLang.BigStep
public import Metrology.ProbLang.EnvStep
public import Metrology.ProbLang.Comp

@[expose] public section

/-! # The ProbLang interpreter

`run` uses heap-stored frames through `ioStepOps` and `runRet`, the hand-audited boundary against
`Step.interp`; `runSubst` is the substitution reference for differential testing.
-/

namespace ProbLang
namespace Interp

/-- The lawless IEEE `Float` model, where `NaN = NaN` is false and `LawfulProbLangℝ` results do
not apply. -/
instance : ProbLangℝ Float where
  realLt a b := decide (a < b)
  realLe a b := decide (a ≤ b)
  realAdd a b := a + b
  realNeg a := -a
  realOfInt z := Float.ofInt z
  realOfRat q := Float.ofInt q.num / Float.ofNat q.den
  realFrac a := a - a.floor

/-- Draw from the unit interval: `k · 2^-53` for `k` uniform on `[0, 2^53)`. -/
def sampleUnit : IO Float := return (Float.ofNat (← IO.rand 0 (2 ^ 53 - 1))).scaleB (-53)

/-- Draw uniformly from `[0, z)`, or `-1` when `z ≤ 0`, as `Cfg.uniform` does. -/
def sampleInt (z : Int) : IO Int := if 0 < z then return (← IO.rand 0 (z - 1).toNat) else return -1

variable {C R : Type}

/-- Run `c` through `step`, then the continuations `ks` last-first; stuck terms and `fail` raise an
`IO` error. -/
@[specialize]
partial def drive (step : C → Comp Float C R) (c : Comp Float C R)
    (ks : Array (R → Comp Float C R)) : IO R := do
  match c with
  | .call x => drive step (step x) ks
  | .bind c k => drive step c (ks.push k)
  | .ret r =>
    match ks.back? with
    | none => return r
    | some k => drive step (k r) ks.pop
  | .stuck msg => throw (IO.userError s!"stuck: {msg}")
  | .sample z k => drive step (k (← sampleInt z)) ks
  | .sampleReal k => drive step (k (← sampleUnit)) ks

/-- The interpreter's `StepOps`, whose heap-stored `ks` frames are pushed by `evalThen` and popped
by `runRet`. -/
@[inline] def ioStepOps
    (runEval : Env Float → Exp Float → State Float → Array (Frame Float) → IO (RCfg Float))
    (runApply : RVal Float → RVal Float → State Float → Array (Frame Float) → IO (RCfg Float))
    (runRet : RVal Float → State Float → Array (Frame Float) → IO (RCfg Float)) :
    StepOps Float (Array (Frame Float) → IO (RCfg Float)) where
  ret v σ ks := runRet v σ ks
  eval env e σ ks := runEval env e σ ks
  evalThen env e σ f ks := runEval env e σ (ks.push f)
  apply f v σ ks := runApply f v σ ks
  stuck msg _ := throw (IO.userError s!"stuck: {msg}")
  uniform z σ ks := do runRet (.lit (.int (← sampleInt z))) σ ks
  uniformReal σ ks := do runRet (.lit (.real (← sampleUnit))) σ ks
  sample n v σ ks :=
    if n = unifIntName then
      match v.fst with
      | .lit (.int z) => do runRet (.lit (.int (← sampleInt z))) σ ks
      | _ => throw (IO.userError "stuck: invalid uniform-integer argument")
    else if n = unifRealName then
      match v.fst with
      | .lit .unit => do runRet (.lit (.real (← sampleUnit))) σ ks
      | _ => throw (IO.userError "stuck: invalid uniform-real argument")
    else throw (IO.userError "stuck: sample has no interpreter")
  test _ _ _ _ _ := throw (IO.userError "stuck: test has no interpreter")

mutual
/-- Evaluate `e` under `env`, then resume the frames `ks`. -/
partial def runEval (env : Env Float) (e : Exp Float) (σ : State Float)
    (ks : Array (Frame Float)) : IO (RCfg Float) :=
  evalK (ioStepOps runEval runApply runRet) env e σ ks

/-- Apply `f` to `v`, then resume the frames `ks`. -/
partial def runApply (f v : RVal Float) (σ : State Float) (ks : Array (Frame Float)) :
    IO (RCfg Float) :=
  applyK (ioStepOps runEval runApply runRet) f v σ ks

/-- Resume the frames `ks` with the value `v`, the last frame first. -/
partial def runRet (v : RVal Float) (σ : State Float) (ks : Array (Frame Float)) :
    IO (RCfg Float) :=
  match ks.back? with
  | none => return ⟨v, σ⟩
  | some f => resumeK (ioStepOps runEval runApply runRet) f v σ ks.pop
end

/-- Run the environment machine on a configuration. -/
def run : EnvCfg Float → IO (RCfg Float)
  | .eval env e σ => runEval env e σ #[]
  | .apply f v σ => runApply f v σ #[]
  | .resume f v σ => resumeK (ioStepOps runEval runApply runRet) f v σ #[]

/-- Run a closed expression from the empty state and read its value back. -/
def eval (e : Exp Float) : IO (Exp Float) :=
  return (← run (.eval [] e default)).val.rb

/-- `bigStepF` read into `Comp`. -/
def compOps : EvalOps Float (Comp Float (Cfg Float) (Cfg Float)) where
  ret := .ret
  bind := .bind
  stuck := .stuck
  uniform z σ := .sample z fun n => .ret ⟨.lit (.int n), σ⟩
  uniformReal σ := .sampleReal fun r => .ret ⟨.lit (.real r), σ⟩
  sample n v σ :=
    if n = unifIntName then
      match v.fst with
      | .lit (.int z) => .sample z fun i => .ret ⟨.lit (.int i), σ⟩
      | _ => .stuck "invalid uniform-integer argument"
    else if n = unifRealName then
      match v.fst with
      | .lit .unit => .sampleReal fun r => .ret ⟨.lit (.real r), σ⟩
      | _ => .stuck "invalid uniform-real argument"
    else .stuck "sample has no interpreter"
  test _ _ _ _ := .stuck "test has no interpreter"

/-- Run the substitution evaluator `bigStepF` on a configuration. -/
def runSubst (ρ : Cfg Float) : IO (Cfg Float) :=
  drive (bigStepF compOps .call) (.call ρ) #[]

end Interp
end ProbLang
