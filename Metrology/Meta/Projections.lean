module

public import Lean
public import Metrology.Meta.Inspect
public import Lean.Meta.Constructions.CtorElim
public import Lean.AuxRecursor

@[expose] public section

open Lean Elab Command Term Meta

/-- The type of a constructor argument, without `optParam`/`autoParam` annotations. -/
def argType (x : Expr) : MetaM Expr := return (← inferType x).cleanupAnnotations

/-- `A × B × C`, or `Unit` for no types. -/
def mkNestedProdType : List Expr → MetaM Expr
  | [] => pure (.const ``Unit [])
  | types => types.dropLast.foldrM (fun ty acc => mkAppM ``Prod #[ty, acc]) types.getLast!

/-- `(a, b, c)`, or `()` for no values. -/
def mkNestedProdValue : List Expr → MetaM Expr
  | [] => pure (Lean.mkConst `Unit.unit)
  | exprs => exprs.dropLast.foldrM (fun e acc => mkAppM ``Prod.mk #[e, acc]) exprs.getLast!

def ProjectionName (cinfo : ConstructorVal) : Name := cinfo.name.str "π"

/-- For a projection `projName` of `decl` that picks out constructor `ictor`, emit one
`@[simp]` rfl theorem `projName.eq_<c'>` per constructor `c'` of `decl`:
`projName params (c' params args) = some? args` if `c'` is `ictor`, `= none` otherwise. -/
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
      let ctorApp ← mkAppOptM ctorName (xs.map some)
      let lhs := mkApp (mkAppN (.const projName projLevels) params) ctorApp
      let lhsType ← inferType lhs
      let rhs ←
        if i = ictor then some? ctorArgs
        else
          let fieldType ←
            match lhsType with
            | .app (.const ``Option _) ft => pure ft
            | _ => throwError "expected projection LHS to have type `Option _`, got {lhsType}"
          mkAppOptM ``Option.none #[some fieldType]
      let eqTypeClosed ← mkForallFVars (params ++ ctorArgs) (← mkEq lhs rhs)
      let proofClosed ← mkLambdaFVars (params ++ ctorArgs) (← mkEqRefl lhs)
      let thmName := projName.str ("eq_" ++ ctorName.componentsRev.head!.toString)
      addDecl <| .thmDecl {
        name := thmName
        levelParams := projLevelParams
        type := (← instantiateMVars eqTypeClosed)
        value := (← instantiateMVars proofClosed)
      }
      addSimpTheorem (ext := simpExtension) thmName (post := true) (inv := false)
        AttributeKind.global (prio := eval_prio default)

/-- Define `projName : params → decl params → Option (payloadType args)` by `casesOn`,
returning `some (payload args)` on constructor `ictor` and `none` elsewhere,
together with its `mkProjectionEqTheorems`. -/
def mkOptionProjection (decl : Name) (ictor : Nat) (projName : Name)
    (payloadType payload : Array Expr → MetaM Expr) : MetaM Unit := do
  let info ← getConstInfoInduct decl
  let casesOnInfo ← getConstVal <| mkCasesOnName decl
  let (e, τ) ← forallTelescope casesOnInfo.type fun xs _ => do
    let params : Array Expr := xs[:info.numParams]
    let majorIdx := info.numParams + 1 + info.numIndices
    let targetIdx := info.numParams + 2 + ictor
    unless xs.size > majorIdx && xs.size > targetIdx do
      throwError "unexpected arity in casesOn type"
    let majorArg := xs[majorIdx]!
    let targetArg := xs[targetIdx]!
    let fieldType ← forallTelescope (← inferType targetArg) fun args _ => payloadType args
    let retNone ← mkNone fieldType
    let returnType : Expr ← mkAppM ``Option #[fieldType]
    let motive := mkLambda .anonymous .default (← inferType majorArg) returnType
    let alts : Array Expr ← info.ctors.toArray.mapIdxM fun i ctorName => do
      let ctor ← mkAppOptM ctorName (params.map some)
      forallTelescope (← inferType ctor) fun ctorArgs _ =>
        if i = ictor then do mkLambdaFVars ctorArgs (← mkSome fieldType (← payload ctorArgs))
        else mkLambdaFVars ctorArgs retNone
    let e ← mkAppOptM casesOnInfo.name ((params ++ #[motive, majorArg] ++ alts).map some)
    let e ← mkLambdaFVars (params ++ #[majorArg]) e
    let eτ ← mkForallFVars params (← mkArrow (← inferType majorArg) returnType)
    return (e, eτ)
  let projLevelParams := casesOnInfo.levelParams.drop 1
  addAndCompile <| .defnDecl {
    name := projName
    levelParams := projLevelParams
    type := τ
    value := e
    hints := ReducibilityHints.abbrev
    safety := .safe
  }
  mkProjectionEqTheorems decl ictor
    (fun args => do mkSome (← payloadType args) (← payload args)) projName projLevelParams

/-- Run `k` on every constructor of `decl`, which must be neither nested nor indexed. -/
def forEachCtor (decl : Name) (k : Nat → ConstructorVal → MetaM Unit) : CoreM Unit := do
  let info ← getConstInfoInduct decl
  unless info.numNested == 0 do
    throwError "expected inductive with no nesting"
  unless info.numIndices == 0 do
    throwError "expected inductive with no indexing"
  for (ctorName, i) in info.ctors.zipIdx do
    (k i (← getConstInfoCtor ctorName)).run'

def mkProjection (decl : Name) (ictor : Nat) (cinfo : ConstructorVal) : MetaM Unit := do
  if cinfo.numFields == 0 then return
  mkOptionProjection decl ictor (ProjectionName cinfo)
    (fun args => do mkNestedProdType (← args.toList.mapM argType))
    (fun args => mkNestedProdValue args.toList)

syntax (name := uncurriedProjections) "uncurriedProjections" : attr

-- TODO: Add projection type itself to the context?
def uncurriedProjectionsImpl : AttributeImpl := {
    name  := `uncurriedProjections
    descr := "Automatically construct uncurried (tuple-returning) projection functions for an inductive datatype"
    add   := fun decl _stx _kind => forEachCtor decl (mkProjection decl)
    }

initialize registerBuiltinAttribute uncurriedProjectionsImpl

def SingleProjectionName (cinfo : ConstructorVal) (field : Name) : Name :=
  cinfo.name.str "π" ++ field

/-- `decl.c.π.<fieldName> : params → decl params → Option fieldType` for field `ifield`
of constructor `c`. -/
def mkSingleProjection (decl : Name) (ictor : Nat) (cinfo : ConstructorVal)
    (ifield : Nat) (fieldName : Name) : MetaM Unit :=
  mkOptionProjection decl ictor (SingleProjectionName cinfo fieldName)
    (fun args => do
      unless ifield < args.size do
        throwError "field index out of range"
      argType args[ifield]!)
    (fun args => pure args[ifield]!)

/-- One `decl.c.π.<field>` per field of `cinfo`; field names must be distinct. -/
def mkSingleProjections (decl : Name) (ictor : Nat) (cinfo : ConstructorVal) : MetaM Unit := do
  let fieldNames ← forallBoundedTelescope cinfo.type (some cinfo.numParams) fun _ rest => do
    forallTelescope rest fun args _ => args.mapM fun a => a.fvarId!.getUserName
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
    add   := fun decl _stx _kind => forEachCtor decl (mkSingleProjections decl)
    }

initialize registerBuiltinAttribute curriedProjectionsImpl

def ConstructorName (cinfo : ConstructorVal) : Name := cinfo.name.str "ι"

/-- `decl.c.ι : params → (A × B × ...) → decl params`, the uncurried constructor `c`. -/
def mkConstructor (decl : Name) (cinfo : ConstructorVal) : MetaM Unit := do
  let info ← getConstInfoInduct decl
  forallTelescope cinfo.type fun xs typ => do
    let params : Array Expr := xs[:info.numParams]
    let args : Array Expr := xs[info.numParams:]
    let n := args.size
    let argTuple ← mkNestedProdType (← args.mapM argType).toList
    let typClosed ← mkForallFVars params (← mkArrow argTuple typ)
    let body : Expr ← withLocalDecl `x BinderInfo.default argTuple fun x => do
      let component (i : Nat) : MetaM Expr := do
        let mut rest := x
        for _ in [:i] do
          rest ← mkAppM ``Prod.snd #[rest]
        if i == n - 1 then return rest else mkAppM ``Prod.fst #[rest]
      let components ← (Array.range n).mapM component
      mkLambdaFVars #[x] (← mkAppOptM cinfo.name (params.map some ++ components.map some))
    let iotaName := ConstructorName cinfo
    addAndCompile <| .defnDecl {
      name := iotaName
      levelParams := cinfo.levelParams
      type := typClosed
      value := (← mkLambdaFVars params body)
      hints := ReducibilityHints.abbrev
      safety := .safe
    }
    simpExtension.add (.toUnfold iotaName) AttributeKind.global

syntax (name := constructors) "constructors" : attr

def constructorsImpl : AttributeImpl := {
    name  := `constructors
    descr := "Automatically construct constructor functions for a inductive datatype"
    add   := fun decl _stx _kind => forEachCtor decl fun _ => mkConstructor decl
    }

initialize registerBuiltinAttribute constructorsImpl
