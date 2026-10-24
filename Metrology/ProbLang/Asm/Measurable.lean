module

public import Metrology.ProbLang.Asm.Step

/-! # Measurability and mass bounds of the explicit foreign-call kernels -/

@[expose] public section
noncomputable section

namespace ProbLang.Asm

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set

/-- Foreign actions have the discrete measurable space. -/
instance : MeasurableSpace Action := ⊤

variable {rT : Type} [MeasurableSpace rT]

/-- The boundary scalar denoted by a base literal, if it is one. -/
private def scalarLit : BaseLit rT → Option BoundaryValue
  | .int z => some (.int z)
  | .loc l => some (.loc l)
  | .unit => some .unit
  | _ => none

private theorem measurable_scalarLit : Measurable (scalarLit (rT := rT)) := by
  convert BaseLit.measurable_casesOn (α := Option BoundaryValue)
    (fun z => some (.int z)) (fun _ => none) (fun _ => some .unit)
    (fun l => some (.loc l)) (fun _ => none) (fun _ : rT => none)
    (fun _ => none) measurable_const using 1
  funext l
  cases l <;> rfl

/-- The boundary scalar denoted by an expression, if it is a scalar literal. -/
private def scalarExp (e : Exp rT) : Option BoundaryValue := (Exp.lit.π e).bind scalarLit

private theorem measurable_scalarExp : Measurable (scalarExp (rT := rT)) :=
  Option.measurable_bind_param Exp.lit.π.measurable (measurable_scalarLit.comp measurable_snd)

/-- Boundary decoding ignores all non-boundary values, including real literals. -/
@[fun_prop] theorem measurable_ofVal :
    Measurable (BoundaryValue.ofVal : Val rT → Option BoundaryValue) := by
  convert measurable_scalarExp.comp Val.fst.measurable using 1
  funext v
  rcases v with ⟨e, he, hlc⟩
  cases e <;> try rfl
  rename_i lit
  cases lit <;> rfl

@[fun_prop] theorem measurable_intValue :
    Measurable (intValue : Val rT → Option Int) := by
  have h := Option.measurable_bind_param (f := fun v : Val rT => Exp.litExtract v.fst)
    (Exp.litExtract.measurable.comp Val.fst.measurable)
    (some_branch := fun p : Val rT × BaseLit rT => BaseLit.intExtract p.2)
    (BaseLit.intExtract.measurable.comp measurable_snd)
  convert h using 1
  funext ⟨e, he, hlc⟩
  cases e <;> try rfl
  rename_i lit
  cases lit <;> rfl

private theorem measurable_mapM {α β γ : Type} [MeasurableSpace α] [MeasurableSpace γ]
    [Countable γ] [MeasurableSingletonClass γ] (xs : List β) (f : β → α → Option γ)
    (hf : ∀ b, Measurable (f b)) : Measurable (fun a => xs.mapM (fun b => f b a)) := by
  induction xs with
  | nil => exact measurable_const
  | cons x xs ih =>
    simp only [List.mapM_cons]
    exact Option.measurable_bind_param (hf x)
      (some_branch := fun p : α × γ => (xs.mapM (fun b => f b p.1)).bind (some <| p.2 :: ·))
      (Option.measurable_bind_param (ih.comp measurable_fst)
        (some_branch := fun p : (α × γ) × List γ => some (p.1.2 :: p.2))
        (measurable_some.comp ((measurable_of_countable (fun p : γ × List γ => p.1 :: p.2)).comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))))

/-- Capturing a fixed finite footprint is measurable in the heap. -/
@[fun_prop] theorem measurable_capture (F : Finset Loc) :
    Measurable (capture F : LocHeap (Val rT) → Option HeapSnapshot) := by
  apply measurable_mapM
  intro l
  refine Option.measurable_bind_param (LocHeap.measurable_getElem? l)
    (some_branch := fun p : LocHeap (Val rT) × Val rT =>
      (intValue p.2).bind (fun z => some (l,z))) ?_
  have hz := measurable_intValue.comp (measurable_snd :
    Measurable (fun p : LocHeap (Val rT) × Val rT => p.2))
  simpa only [Option.map_eq_bind, Function.comp_def] using
    ((measurable_of_countable (fun z : Int => (l, z))).option_map).comp hz

/-- Updating a fixed finite fragment preserves measurability of states. -/
@[fun_prop] theorem measurable_overwriteState (F : Finset Loc) (fragment : LocHeap (Val rT)) :
    Measurable (fun σ : State rT => σ.update_heap (fun h => overwrite F h fragment)) := by
  apply State.measurable_mk_param
  · apply LocHeap.measurable_iff.mpr
    intro l
    simp only [overwrite_get]
    by_cases h : l ∈ F
    · simp [h]
    · simpa only [ite_eq_right h, Function.comp_def] using
        (LocHeap.measurable_getElem? l).comp State.measurable_heap
  · exact State.measurable_tapes

/-- The action interpreter is jointly measurable. -/
@[fun_prop] theorem measurable_actionStep (env : FfiEnv rT) (F : Finset Loc) :
    Measurable (fun p : Action × State rT => actionStep env F p.2 p.1) := by
  apply measurable_from_prod_countable_right
  intro action
  cases action with
  | invalid => exact Cfg.measurable_dirac_mk measurable_const measurable_id
  | stuck => exact measurable_const
  | ret _ _ | call _ _ _ _ =>
    exact Cfg.measurable_dirac_mk measurable_const (measurable_overwriteState F _)

/-- Finite boundary tuples are decoded measurably from expression syntax. -/
@[fun_prop] theorem measurable_readTuple (n : Nat) :
    Measurable (readTuple (rT := rT) n) := by
  induction n with
  | zero =>
    have h := (measurable_of_countable (fun v : Option BoundaryValue =>
      match v with | some .unit => some ([] : List BoundaryValue) | _ => none)).comp
        (measurable_scalarExp (rT := rT))
    convert h using 1
    funext e
    cases e <;> try rfl
    rename_i lit
    cases lit <;> rfl
  | succ n ih =>
    have htail : Measurable (fun p : (Exp rT × Exp rT) × BoundaryValue =>
        (readTuple n p.1.2).map (p.2 :: ·)) := by
      simpa only [Option.map_eq_bind, Function.comp_def] using
        Option.measurable_bind_param (ih.comp (measurable_snd.comp measurable_fst))
          (some_branch := fun p : ((Exp rT × Exp rT) × BoundaryValue) × List BoundaryValue =>
            some (p.1.2 :: p.2))
          (measurable_some.comp ((measurable_of_countable
            (fun p : BoundaryValue × List BoundaryValue => p.1 :: p.2)).comp
              ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
    have hpair := Option.measurable_bind_param
      (measurable_scalarExp.comp (measurable_fst : Measurable (fun p : Exp rT × Exp rT => p.1)))
      htail
    have h := Option.measurable_bind_param (Exp.pair.π.measurable (rT := rT))
      (some_branch := fun p : Exp rT × (Exp rT × Exp rT) =>
        (scalarExp p.2.1).bind (fun v => (readTuple n p.2.2).map (v :: ·)))
      (hpair.comp measurable_snd)
    convert h using 1
    funext e
    cases e <;> try rfl
    rename_i first rest
    cases first <;> try rfl
    rename_i lit
    cases lit <;> rfl

/-- The machine code denoted by an expression, if it is a code literal. -/
private def codeExp (e : Exp rT) : Option Code :=
  (Exp.lit.π e).bind BaseLit.code.π

private theorem measurable_codeExp : Measurable (codeExp (rT := rT)) :=
  Option.measurable_bind_param Exp.lit.π.measurable (BaseLit.code.π.measurable.comp measurable_snd)

/-- Calling a fixed code value depends measurably on its tuple and the current state. -/
@[fun_prop] theorem measurable_callStep_code (env : FfiEnv rT) (c : Code) :
    Measurable (fun p : Exp rT × State rT => callStep env (.lit (.code c)) p.1 p.2) := by
  have hc : ∀ values : List BoundaryValue, Measurable (fun σ : State rT =>
      match capture (callFootprint c values) σ.heap with
      | none => dirac (Cfg.mk (.fail : Exp rT) σ)
      | some entry => actionStep env (callFootprint c values) σ
          (start env.machine c values entry.restore)) := by
    intro values
    have h := Option.measurable_elim_param
      (f := fun σ : State rT => capture (callFootprint c values) σ.heap)
      ((measurable_capture (callFootprint c values)).comp State.measurable_heap)
      (default := fun σ => dirac (Cfg.mk (.fail : Exp rT) σ))
      (Cfg.measurable_dirac_mk measurable_const measurable_id)
      (some_branch := fun p : State rT × HeapSnapshot =>
        actionStep env (callFootprint c values) p.1 (start env.machine c values p.2.restore))
      ((measurable_actionStep env (callFootprint c values)).comp
        (((measurable_of_countable (fun entry : HeapSnapshot =>
          start env.machine c values entry.restore)).comp measurable_snd).prodMk measurable_fst))
    convert h using 1
    funext σ
    cases capture (callFootprint c values) σ.heap <;> rfl
  have hd : Measurable (fun p : Option (List BoundaryValue) × State rT =>
      match p.1 with
      | none => dirac (Cfg.mk (.fail : Exp rT) p.2)
      | some values =>
        match capture (callFootprint c values) p.2.heap with
        | none => dirac (Cfg.mk (.fail : Exp rT) p.2)
        | some entry => actionStep env (callFootprint c values) p.2
            (start env.machine c values entry.restore)) := by
    apply measurable_from_prod_countable_right
    intro values
    cases values with
    | none => exact Cfg.measurable_dirac_mk measurable_const measurable_id
    | some values => exact hc values
  exact hd.comp ((measurable_readTuple c.sig.args.length |>.comp measurable_fst).prodMk
    measurable_snd)

/-- The complete call dispatcher is measurable, including malformed operands. -/
@[fun_prop] theorem measurable_callStep (env : FfiEnv rT) :
    Measurable (fun p : Exp rT × Exp rT × State rT => callStep env p.1 p.2.1 p.2.2) := by
  have hd : Measurable (fun p : Option Code × Exp rT × State rT =>
      match p.1 with
      | none => dirac (Cfg.mk (.fail : Exp rT) p.2.2)
      | some c => callStep env (.lit (.code c)) p.2.1 p.2.2) := by
    apply measurable_from_prod_countable_right
    intro code
    cases code with
    | none => exact Cfg.measurable_dirac_mk measurable_const measurable_snd
    | some c => exact measurable_callStep_code env c
  have h := hd.comp (((measurable_codeExp (rT := rT)).comp measurable_fst).prodMk measurable_snd)
  convert h using 1
  funext ⟨code, args, σ⟩
  cases code <;> try rfl
  rename_i lit
  cases lit <;> rfl

/-- Resumption observes only the boundary reply and a finite heap snapshot. -/
@[fun_prop] theorem measurable_resumeStep (env : FfiEnv rT) (archive : Replay) :
    Measurable (fun p : Val rT × State rT => resumeStep env archive p.1 p.2) := by
  let F := callFootprint archive.code archive.args
  have hd : Measurable (fun p : (Option BoundaryValue × Option HeapSnapshot) × State rT =>
      match p.1.1, p.1.2 with
      | some r, some current =>
        actionStep env F p.2 (resume env.machine archive r current.restore)
      | _, _ => dirac (Cfg.mk (.fail : Exp rT) p.2)) := by
    apply measurable_from_prod_countable_right
    rintro ⟨reply, current⟩
    cases reply <;> cases current
    all_goals first
      | exact Cfg.measurable_dirac_mk measurable_const measurable_id
      | exact (measurable_actionStep env F).comp (measurable_const.prodMk measurable_id)
  exact hd.comp (((measurable_ofVal.comp measurable_fst).prodMk
    ((measurable_capture F).comp (State.measurable_heap.comp measurable_snd))).prodMk
      measurable_snd)

private theorem measurable_asmRedex (env : FfiEnv rT) :
    Measurable (fun p : Exp rT × Exp rT × State rT =>
      p.1.isValM (p.2.1.isValM (callStep env p.1 p.2.1 p.2.2))) :=
  Exp.isValM.measurable_param measurable_fst
    (Exp.isValM.measurable_param (measurable_fst.comp measurable_snd) (measurable_callStep env))

private theorem measurable_resumeRedex (env : FfiEnv rT) :
    Measurable (fun p : Replay × Exp rT × State rT =>
      p.2.1.asValM (fun value => resumeStep env p.1 value p.2.2)) := by
  apply measurable_from_prod_countable_right
  intro archive
  exact Exp.asValM.measurable ((measurable_resumeStep env archive).comp measurable_swap)

/-- A foreign action produces at most one unit of probability mass. -/
theorem actionStep_univ_le_one (env : FfiEnv rT) (F : Finset Loc) (σ : State rT)
    (action : Action) : actionStep env F σ action univ ≤ 1 := by
  cases action <;> simp [actionStep]

/-- A foreign call produces at most one unit of probability mass. -/
theorem callStep_univ_le_one (env : FfiEnv rT) (code args : Exp rT) (σ : State rT) :
    callStep env code args σ univ ≤ 1 := by
  cases code <;> try simp [callStep]
  rename_i lit
  cases lit <;> try simp
  rename_i c
  split
  · simp
  · split
    · simp
    · exact actionStep_univ_le_one _ _ _ _

/-- Resuming an archive produces at most one unit of probability mass. -/
theorem resumeStep_univ_le_one (env : FfiEnv rT) (archive : Replay)
    (reply : Val rT) (σ : State rT) : resumeStep env archive reply σ univ ≤ 1 := by
  dsimp only [resumeStep]
  split
  · exact actionStep_univ_le_one _ _ _ _
  · simp

variable [LawfulProbLangℝ rT]

/-- The explicit foreign-call head kernel is measurable. -/
@[fun_prop] theorem measurable_headStepWith (env : FfiEnv rT) :
    Measurable (headStepWith env : Cfg rT → Measure (Cfg rT)) := by
  have hr := Option.measurable_elim_param (f := fun cfg : Cfg rT => Exp.asmResume.π cfg.expr)
    (Exp.asmResume.π.measurable.comp Cfg.measurable_expr)
    (default := headStep) headStep.measurable
    (some_branch := fun p : Cfg rT × (Replay × Exp rT) =>
      p.2.2.asValM (fun value => resumeStep env p.2.1 value p.1.state))
    ((measurable_resumeRedex env).comp ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_snd.comp measurable_snd).prodMk (Cfg.measurable_state.comp measurable_fst))))
  have ha := Option.measurable_elim_param (f := fun cfg : Cfg rT => Exp.asm.π cfg.expr)
    (Exp.asm.π.measurable.comp Cfg.measurable_expr) hr
    (some_branch := fun p : Cfg rT × (Exp rT × Exp rT) =>
      p.2.1.isValM (p.2.2.isValM (callStep env p.2.1 p.2.2 p.1.state)))
    ((measurable_asmRedex env).comp ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_snd.comp measurable_snd).prodMk (Cfg.measurable_state.comp measurable_fst))))
  convert ha using 1
  funext ⟨e, σ⟩
  cases e <;> rfl

/-- The explicit foreign-call head kernel is a subprobability kernel. -/
theorem headStepWith_univ_le_one (env : FfiEnv rT) (cfg : Cfg rT) :
    headStepWith env cfg univ ≤ 1 := by
  rcases cfg with ⟨e, σ⟩
  cases e <;> try exact headStep_univ_le_one _
  case asm code args =>
    simp only [headStepWith, Exp.isValM]
    split
    · split
      · exact callStep_univ_le_one _ _ _ _
      · simp
    · simp
  case asmResume archive reply =>
    simp only [headStepWith, Exp.asValM]
    split
    · simp
    · exact resumeStep_univ_le_one _ _ _ _

/-- Context decomposition and replugging preserve measurability of the FFI kernel. -/
@[fun_prop] theorem measurable_primStepWith (env : FfiEnv rT) :
    Measurable (primStepWith env : Cfg rT → Measure (Cfg rT)) := by
  have hk : Measurable (fun cfg : Cfg rT => headStepWith env ⟨cfg.expr.decomp.2, cfg.state⟩) :=
    (measurable_headStepWith env).comp (by fun_prop)
  have hh : Measurable (fun p : Cfg rT × Cfg rT => p.1.expr.decomp.1.fillCfg p.2) := by
    rw [Cfg.measurable_iff]
    exact ⟨Exp.Ectx_fill.measurable.comp ((by fun_prop : Measurable _).prodMk
      (by fun_prop)), by fun_prop⟩
  have : IsFiniteKernel (Kernel.mk _ hk) :=
    ⟨1, ENNReal.one_lt_top, fun _ => headStepWith_univ_le_one _ _⟩
  exact measurable_map_uncurry hh hk

/-- Replugging a foreign head step preserves its subprobability bound. -/
theorem primStepWith_univ_le_one (env : FfiEnv rT) (cfg : Cfg rT) :
    primStepWith env cfg univ ≤ 1 := by
  have hfill : Measurable cfg.expr.decomp.1.fillCfg := by fun_prop
  rw [primStepWith, map_apply hfill MeasurableSet.univ]
  simpa using headStepWith_univ_le_one env ⟨cfg.expr.decomp.2, cfg.state⟩

end ProbLang.Asm
