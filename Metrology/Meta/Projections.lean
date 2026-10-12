module

public import Lean
public import Metrology.Meta.Inspect
public import Lean.Meta.Constructions.CtorElim
public import Lean.AuxRecursor

@[expose] public section

open Lean Elab Command Term Meta

/-- The type of a constructor argument, without `optParam`/`autoParam` annotations. -/
def argType (x : Expr) : MetaM Expr := return (← inferType x).cleanupAnnotations

-- Helper to construct nested Prod types: A × B × C (right-associative)
-- For empty list: Unit
-- For non-empty list: uses last element as base, folds rest to build nested Prod
def mkNestedProdType (types : List Expr) : MetaM Expr :=
  match types with
  | [] => pure (Expr.const ``Unit [])
  | _ =>
    types.dropLast.foldrM (fun ty acc => mkAppM ``Prod #[ty, acc]) types.getLast!

-- Helper to construct nested Prod values: (a, (b, c)) (right-associative)
-- For empty list: ()
-- For non-empty list: uses last element as base, folds rest to build nested Prod
def mkNestedProdValue (exprs : List Expr) : MetaM Expr :=
  match exprs with
  | [] => pure (Lean.mkConst `Unit.unit)
  | _ =>
    exprs.dropLast.foldrM  (fun e acc => mkAppM ``Prod.mk #[e, acc]) exprs.getLast!


def ProjectionName (cinfo : ConstructorVal) : Name := cinfo.name.str "π"

def ProjectionType (c : ConstructorVal) : MetaM Expr := do
  forallBoundedTelescope c.type (some c.numParams) fun univs e' => do
    forallTelescope e' (fun args core => do
      let argTyps ← args.toList.mapM argType
      let projs ← mkNestedProdType argTyps
      let optionType ← mkAppM ``Option #[projs]
      let funType := mkForall .anonymous .default core optionType
      mkForallFVars univs funType)

def displayFVars (pref : String) (A : Array Expr) : MetaM Unit := do
  for a in A do logInfo s!"{pref} {a}: {← inferType a}"

/-- For a projection `projName` of `decl` that picks out constructor `ictor`, emit one
`@[simp]`-tagged rfl theorem per constructor `c'` of `decl`, of the form:
  * if `c'` is constructor `ictor`: `projName params (c' params args) = some? args`
  * otherwise:                      `projName params (c' params args) = none`
Theorems are named `projName.eq_<short c'>`. -/
def mkProjectionEqTheorems (decl : Name) (ictor : Nat) (some? : Array Expr → MetaM Expr)
    (projName : Name) (projLevelParams : List Name) : MetaM Unit := do
  let info ← getConstInfoInduct decl
  let projLevels : List Level := projLevelParams.map Level.param
  for h : i in [:info.ctors.length] do
    let ctorName := info.ctors[i]
    let ctorInfo ← getConstInfoCtor ctorName
    forallTelescope ctorInfo.type fun xs _ => do
      let params : Array Expr := xs[:info.numParams]
      let ctorArgs : Array Expr := xs[info.numParams:]
      -- LHS: projName @params (ctorName @params @ctorArgs)
      let ctorApp ← mkAppOptM ctorName (xs.map some)
      let projConst : Expr := Expr.const projName projLevels
      let projApplied := mkAppN projConst params
      let lhs := mkApp projApplied ctorApp
      let lhsType ← inferType lhs
      let rhs ←
        if i = ictor then some? ctorArgs
        else
          let fieldType ←
            match lhsType with
            | .app (.const ``Option _) ft => pure ft
            | _ => throwError "expected projection LHS to have type `Option _`, got {lhsType}"
          mkAppOptM ``Option.none #[some fieldType]
      let eqType ← mkEq lhs rhs
      let proof ← mkEqRefl lhs
      let eqTypeClosed ← mkForallFVars (params ++ ctorArgs) eqType
      let proofClosed ← mkLambdaFVars (params ++ ctorArgs) proof
      let ctorShort := ctorName.componentsRev.head!.toString
      let thmName := projName.str ("eq_" ++ ctorShort)
      addDecl <| .thmDecl {
        name := thmName
        levelParams := projLevelParams
        type := (← instantiateMVars eqTypeClosed)
        value := (← instantiateMVars proofClosed)
      }
      addSimpTheorem (ext := simpExtension) thmName (post := true) (inv := false)
        AttributeKind.global (prio := eval_prio default)

def mkProjection (decl : Name) (ictor : Nat) (cinfo : ConstructorVal) : MetaM Unit := do
  -- Skip constructors with no fields — nothing to project.
  if cinfo.numFields == 0 then return
  -- Collect the casesOn information
  let info ← getConstInfoInduct decl
  let casesOnInfo ← getConstVal <| mkCasesOnName decl
  let (e, τ) ← forallTelescope casesOnInfo.type fun xs _ => do
    let params : Array Expr := xs[:info.numParams]
    let majorIdx := info.numParams + 1 + info.numIndices
    let targetIdx := info.numParams + 2 + ictor
    unless xs.size > majorIdx && xs.size > targetIdx do
      throwError "unexpected arity in casesOn type"
    let majorArg := xs[majorIdx]!
    let target_arg := xs[targetIdx]!

    -- Construct the return type (optPair)
    let argtypes ← forallTelescope (← inferType target_arg) (fun args _ => args.mapM argType)
    let projs ← mkNestedProdType argtypes.toList
    let retNone ← mkNone projs
    let returnType : Expr ← mkAppM ``Option #[projs]

    -- Construct the motive
    let motive := mkLambda .anonymous .default (← inferType majorArg) returnType

    -- Construct the cases
    let alts : Array Expr ← info.ctors.toArray.mapIdxM fun i ctorName => do
      let ctor ← mkAppOptM ctorName (params.map some)
      let ctorType ← inferType ctor
      forallTelescope ctorType fun ctorargs _ =>
        if (i = ictor)
          then do
            let ret_tup ← mkNestedProdValue ctorargs.toList
            mkLambdaFVars ctorargs (← mkSome projs ret_tup)
          else mkLambdaFVars ctorargs retNone

    -- Apply the cases to the parameters, motives, etc
    let e ← mkAppOptM casesOnInfo.name ((params ++ #[motive, majorArg] ++ alts).map some)
    let e ← mkLambdaFVars (params ++ #[majorArg]) e

    -- Apply the
    let eτ ← mkArrow (← inferType majorArg) returnType
    let eτ ← mkForallFVars params eτ
    return (e, eτ)

  addAndCompile <| .defnDecl {
    name := ProjectionName cinfo
    levelParams := casesOnInfo.levelParams.drop 1
    type := τ
    value := e
    hints := ReducibilityHints.abbrev
    safety := .safe
  }
  mkProjectionEqTheorems decl ictor
    (fun args => do mkSome (← mkNestedProdType (← args.toList.mapM argType)) (← mkNestedProdValue args.toList))
    (ProjectionName cinfo) (casesOnInfo.levelParams.drop 1)

syntax (name := uncurriedProjections) "uncurriedProjections" : attr

-- TODO: Add projection type itself to the context?
def uncurriedProjectionsImpl : AttributeImpl := {
    name  := `uncurriedProjections
    descr := "Automatically construct uncurried (tuple-returning) projection functions for an inductive datatype"
    add   := fun decl _stx _kind => do
      let info ← getConstInfoInduct decl
      unless info.numNested == 0 do
        throwError "expected inductive with no nesting"
      unless info.numIndices == 0 do
        throwError "expected inductive with no indexing"
      let _ ← info.ctors.toArray.mapIdxM fun x y => do
        let cinfo ← getConstInfoCtor y
        mkProjection decl x cinfo |>.run'
    }

initialize registerBuiltinAttribute uncurriedProjectionsImpl

def SingleProjectionName (cinfo : ConstructorVal) (field : Name) : Name :=
  cinfo.name.str "π" ++ field

/-- For a single constructor `c` of `decl` and a chosen field index `ifield`,
generate `decl.c.π.<fieldname> : params → decl params → Option fieldType`
returning `some field` on the `c` branch and `none` elsewhere. -/
def mkSingleProjection (decl : Name) (ictor : Nat) (cinfo : ConstructorVal)
    (ifield : Nat) (fieldName : Name) : MetaM Unit := do
  let info ← getConstInfoInduct decl
  let casesOnInfo ← getConstVal <| mkCasesOnName decl
  let (e, τ) ← forallTelescope casesOnInfo.type fun xs _ => do
    let params : Array Expr := xs[:info.numParams]
    let majorIdx := info.numParams + 1 + info.numIndices
    let targetIdx := info.numParams + 2 + ictor
    unless xs.size > majorIdx && xs.size > targetIdx do
      throwError "unexpected arity in casesOn type"
    let majorArg := xs[majorIdx]!
    let target_arg := xs[targetIdx]!

    -- Compute the type of the chosen field by telescoping the target alternative.
    let fieldType ← forallTelescope (← inferType target_arg) (fun args _ => do
      unless ifield < args.size do
        throwError "field index out of range"
      argType args[ifield]!)
    let retNone ← mkNone fieldType
    let returnType : Expr ← mkAppM ``Option #[fieldType]

    let motive := mkLambda .anonymous .default (← inferType majorArg) returnType

    let alts : Array Expr ← info.ctors.toArray.mapIdxM fun i ctorName => do
      let ctor ← mkAppOptM ctorName (params.map some)
      let ctorType ← inferType ctor
      forallTelescope ctorType fun ctorargs _ =>
        if (i = ictor)
          then do
            mkLambdaFVars ctorargs (← mkSome fieldType ctorargs[ifield]!)
          else mkLambdaFVars ctorargs retNone

    let e ← mkAppOptM casesOnInfo.name ((params ++ #[motive, majorArg] ++ alts).map some)
    let e ← mkLambdaFVars (params ++ #[majorArg]) e

    let eτ ← mkArrow (← inferType majorArg) returnType
    let eτ ← mkForallFVars params eτ
    return (e, eτ)

  let projName := SingleProjectionName cinfo fieldName
  let projLevelParams := casesOnInfo.levelParams.drop 1
  addAndCompile <| .defnDecl {
    name := projName
    levelParams := projLevelParams
    type := τ
    value := e
    hints := ReducibilityHints.abbrev
    safety := .safe
  }
  -- Emit one `@[simp]`-tagged definitional-unfolding theorem per constructor.
  mkProjectionEqTheorems decl ictor (fun args => do mkSome (← argType args[ifield]!) args[ifield]!)
    projName projLevelParams

/-- For each constructor of `decl`, emit one `decl.c.π.<field>` per argument.
Throws if two arguments within a single constructor share a name. -/
def mkSingleProjections (decl : Name) (ictor : Nat) (cinfo : ConstructorVal) : MetaM Unit := do
  -- Collect the user-facing field names for this constructor.
  let fieldNames ← forallBoundedTelescope cinfo.type (some cinfo.numParams) fun _ rest => do
    forallTelescope rest fun args _ => args.mapM fun a => a.fvarId!.getUserName
  -- Check for duplicates within this constructor.
  let mut seen : NameSet := {}
  for nm in fieldNames do
    if seen.contains nm then
      throwError "constructor `{cinfo.name}` has duplicate field name `{nm}`; \
        @[curriedProjections] requires distinct argument names within each constructor"
    seen := seen.insert nm
  for h : i in [:fieldNames.size] do
    mkSingleProjection decl ictor cinfo i fieldNames[i]

syntax (name := curriedProjections) "curriedProjections" : attr

def curriedProjectionsImpl : AttributeImpl := {
    name  := `curriedProjections
    descr := "Generate per-field (curried) projection functions for an inductive datatype"
    add   := fun decl _stx _kind => do
      let info ← getConstInfoInduct decl
      unless info.numNested == 0 do
        throwError "expected inductive with no nesting"
      unless info.numIndices == 0 do
        throwError "expected inductive with no indexing"
      let _ ← info.ctors.toArray.mapIdxM fun x y => do
        let cinfo ← getConstInfoCtor y
        mkSingleProjections decl x cinfo |>.run'
    }

initialize registerBuiltinAttribute curriedProjectionsImpl

def ConstructorName (cinfo : ConstructorVal) : Name := cinfo.name.str "ι"

def mkConstructor (decl : Name) (_ictor : Nat) (cinfo : ConstructorVal) : MetaM Unit := do
  let info ← getConstInfoInduct decl
  let _ ← forallTelescope cinfo.type fun xs typ => do
    let params : Array Expr := xs[:info.numParams]
    let args : Array Expr := xs[info.numParams:]

    -- Construct the uncurried constructor type
    let argtypes ← args.mapM argType
    let projargtyp ← mkNestedProdType argtypes.toList
    let typOpen ← mkArrow projargtyp typ
    let typClosed ← mkForallFVars params typOpen

    -- Construct the uncurried constructor function
    let body : Expr ← withLocalDecl `x BinderInfo.default projargtyp λ x => do
      match args.size with
        | 0 => mkLambdaFVars #[x] (← mkAppOptM cinfo.name (params.map some))
        | 1 => mkLambdaFVars #[x] (← mkAppOptM cinfo.name (params.map some ++ [some x]))
        | n => do
          -- Extract the i-th component from nested Prod structure
          -- For structure (a, (b, (c, d))), we need to extract each component
          let mkAppProj (i : Nat) : MetaM Expr := do
            if i == n - 1 then
              -- Last element: apply snd repeatedly (i times)
              let mut result := x
              for _ in [:i] do
                result ← mkAppM ``Prod.snd #[result]
              return result
            else
              -- Other elements: apply snd (i times) then fst
              let mut result := x
              for _ in [:i] do
                result ← mkAppM ``Prod.snd #[result]
              mkAppM ``Prod.fst #[result]
          let mkAppArgs ← List.ofFnM (n := n) (fun i : Fin n => mkAppProj i.val)
          mkLambdaFVars #[x] (← mkAppOptM cinfo.name (params.map some ++ mkAppArgs.map some))
    let bodyClosed ← mkLambdaFVars params body

    let iotaName := ConstructorName cinfo
    addAndCompile <| .defnDecl {
      name := iotaName
      levelParams := cinfo.levelParams
      type := typClosed
      value := bodyClosed
      hints := ReducibilityHints.abbrev
      safety := .safe
    }
    simpExtension.add (.toUnfold iotaName) AttributeKind.global

syntax (name := constructors) "constructors" : attr

-- TODO: Add projection type itself to the context?
def constructorsImpl : AttributeImpl := {
    name  := `constructors
    descr := "Automatically construct constructor functions for a inductive datatype"
    add   := fun decl _stx _kind => do
      let info ← getConstInfoInduct decl
      unless info.numNested == 0 do
        throwError "expected inductive with no nesting"
      unless info.numIndices == 0 do
        throwError "expected inductive with no indexing"
      let _ ← info.ctors.toArray.mapIdxM fun x y => do
        let cinfo ← getConstInfoCtor y
        mkConstructor decl x cinfo |>.run'
    }

initialize registerBuiltinAttribute constructorsImpl
