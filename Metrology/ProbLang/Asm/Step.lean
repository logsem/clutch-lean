module

public import Metrology.ProbLang.Asm.Execution
public import Metrology.ProbLang.Asm.Capture
public import Metrology.ProbLang.CtxStep

/-! # ProbLang foreign-call reduction -/

@[expose] public section

noncomputable section

namespace ProbLang.Asm

open MeasureTheory MeasureTheory.Measure

variable {rT : Type}

/-- A boundary tuple of values is a value. -/
theorem argumentTuple_isValue (args : List BoundaryValue) :
    (argumentTuple (rT := rT) args).isValue := by
  rw [argumentTuple_eq]
  exact (argumentValues args).2.toIsValue

/-- A bare assembly call with value operands has no surrounding evaluation frames. -/
theorem asm_decomp (code : Code) (args : List BoundaryValue) :
    (Exp.asm (.lit (.code code)) (argumentTuple (rT := rT) args)).decomp =
      ([], .asm (.lit (.code code)) (argumentTuple args)) := by
  obtain ⟨v, hv⟩ := Exp.toVal?_eq_some_of_isValue (argumentTuple_isValue (rT := rT) args)
  have hd : (Exp.asm (.lit (.code code)) (argumentTuple (rT := rT) args)).decompItem = none := by
    simp only [Exp.decompItem, hv]
    rfl
  rw [Exp.decomp_unfold, hd]

variable [MeasurableSpace rT] [LawfulProbLangℝ rT]

/-- Perform one observable foreign action and overwrite exactly its footprint. -/
def actionStep (env : FfiEnv rT) (F : Finset Loc) (σ : State rT) : Action → Measure (Cfg rT) :=
  let write (heap : LocHeap BoundaryValue) :=
    σ.update_heap (fun h => overwrite F h (valueHeap heap))
  fun
  | .invalid => dirac ⟨.fail, σ⟩
  | .stuck => 0
  | .ret value heap => dirac ⟨value.toVal.fst, write heap⟩
  | .call name args heap archive =>
    dirac ⟨.asmResume archive (.app (env.impls name).fst (argumentTuple args)), write heap⟩

/-- Start an assembly call after its two operands have become values. -/
def callStep (env : FfiEnv rT) (code args : Exp rT) (σ : State rT) : Measure (Cfg rT) :=
  match code with
  | .lit (.code c) =>
    match readTuple c.sig.args.length args with
    | none => dirac ⟨.fail, σ⟩
    | some values =>
      let F := callFootprint c values
      match capture F σ.heap with
      | none => dirac ⟨.fail, σ⟩
      | some entry => actionStep env F σ (start env.machine c values entry.restore)
  | _ => dirac ⟨.fail, σ⟩

/-- Resume using the current fragment after the import's ProbLang implementation returns. -/
def resumeStep (env : FfiEnv rT) (archive : Replay) (reply : Val rT) (σ : State rT) :
    Measure (Cfg rT) :=
  let F := callFootprint archive.code archive.args
  match BoundaryValue.ofVal reply, capture F σ.heap with
  | some r, some current => actionStep env F σ (resume env.machine archive r current.restore)
  | _, _ => dirac ⟨.fail, σ⟩

/-- Head reduction with an explicit foreign-call environment. -/
def headStepWith (env : FfiEnv rT) (cfg : Cfg rT) : Measure (Cfg rT) :=
  match cfg with
  | ⟨.asm code args, σ⟩ => code.isValM (args.isValM (callStep env code args σ))
  | ⟨.asmResume archive reply, σ⟩ => reply.asValM (fun value => resumeStep env archive value σ)
  | _ => headStep cfg

/-- Contextual reduction with an explicit foreign-call environment. -/
def primStepWith (env : FfiEnv rT) (cfg : Cfg rT) : Measure (Cfg rT) :=
  let (K, e) := cfg.expr.decomp
  (headStepWith env ⟨e, cfg.state⟩).map K.fillCfg

/-- Head reduction of a literal assembly call is `callStep`. -/
theorem headStepWith_asm (env : FfiEnv rT) (code : Code) (args : List BoundaryValue)
    (σ : State rT) :
    headStepWith env ⟨.asm (.lit (.code code)) (argumentTuple args), σ⟩ =
      callStep env (.lit (.code code)) (argumentTuple args) σ := by
  simp only [headStepWith, Exp.isValM_some (argumentTuple_isValue (rT := rT) args),
    Exp.isValM_some (IsVal.lit.toIsValue)]

/-- A bare assembly call uses the foreign dispatcher as its primitive step. -/
theorem primStepWith_asm (env : FfiEnv rT) (code : Code) (args : List BoundaryValue)
    (σ : State rT) :
    primStepWith env ⟨.asm (.lit (.code code)) (argumentTuple args), σ⟩ =
      callStep env (.lit (.code code)) (argumentTuple args) σ := by
  simp only [primStepWith, asm_decomp, headStepWith_asm, Ectx.fillCfg_empty, map_id]

/-- A contextual foreign step is the inner foreign step with the context reattached. -/
theorem primStepWith_fill (env : FfiEnv rT) (K : Ectx rT) {e : Exp rT} (σ : State rT)
    (hv : ¬e.isValue) :
    primStepWith env ⟨K.fill e, σ⟩ = (primStepWith env ⟨e, σ⟩).map K.fillCfg := by
  simp only [primStepWith]
  set d := e.decomp with hd
  obtain ⟨K', e''⟩ := d
  simp only [Exp.decomp_fill_comp hv hd.symm]
  rw [map_map (by measurability) (by measurability)]
  congr 1
  funext ⟨e', σ'⟩
  simp [Ectx.fillCfg, Ectx.fill_append]

end ProbLang.Asm
