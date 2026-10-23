module

public import Lean

/-! # `mkAppByName`

Applies a constant to arguments given by binder name, not by position. -/

@[expose] public section

open Lean Meta

/-- The binder names of the leading `∀` telescope of a type. -/
meta def binderNames : Expr → List Name
  | .forallE n _ b _ => n.eraseMacroScopes :: binderNames b
  | _ => []

/-- Applies `c` to the arguments `named` by binder name, filling instance binders from `insts` or
by synthesis, and failing loudly on an unknown or unassigned binder. -/
meta def mkAppByName (c : Name) (named : List (Name × Expr)) (insts : List Expr := []) :
    MetaM Expr := do
  let info ← getConstInfo c
  let lvls ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  let (mvars, bis, _) ← forallMetaTelescope (info.instantiateTypeLevelParams lvls)
  let names := binderNames info.type
  for (k, _) in named do
    unless names.contains k do throwError "`{c}` has no binder named `{k}`"
  for ((m, bi), n) in (mvars.toList.zip bis.toList).zip names do
    if let some v := named.lookup n then
      unless ← isDefEq m v do throwError "`{c}`: cannot assign binder `{n}` the value {v}"
    else if bi.isInstImplicit then
      let ty ← inferType m
      match ← insts.findM? fun i => do isDefEq ty (← inferType i) with
      | some i => m.mvarId!.assign i
      | none => m.mvarId!.assign (← synthInstance ty)
  let unassigned ← (mvars.toList.zip names).filterM fun (m, _) => do
    return !(← m.mvarId!.isAssigned)
  unless unassigned.isEmpty do
    throwError "`{c}`: unassigned binders {unassigned.map (·.2)}"
  instantiateMVars (mkAppN (.const c lvls) mvars)
