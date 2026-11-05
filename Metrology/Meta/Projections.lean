module

public import Lean
public import Metrology.Meta.Build

/-! # Constructors and projections of tuples

The uncurried constructor `c.ι` and its inverse `c.π`, for deriving `MeasurableSpace`. -/

@[expose] public section

open Lean Meta

namespace Metrology.Meta

/-- The type of a constructor argument, without `optParam`/`autoParam` annotations. -/
def argType (x : Expr) : MetaM Expr := return (← inferType x).cleanupAnnotations

/-- Runs `k` with the fields of the constructor `c` (applied to `params`) as local variables. -/
def withCtorArgs {α : Type} (c : Name) (params : Array Expr) (k : Array Expr → MetaM α) :
    MetaM α := do
  forallTelescope (← instantiateForall (← getConstInfo c).type params) fun args _ => k args

/-- Runs `k` on every constructor of `decl`, which must be neither nested nor indexed, and whose
fields must not depend on each other (so that they form a tuple). -/
def forEachCtor (decl : Name) (k : ConstructorVal → MetaM Unit) : CoreM Unit := do
  let info ← getConstInfoInduct decl
  unless info.numNested == 0 do
    throwError "expected inductive with no nesting"
  unless info.numIndices == 0 do
    throwError "expected inductive with no indexing"
  for c in info.ctors do
    let c ← getConstInfoCtor c
    MetaM.run' do
      let dependent ← forallTelescope c.type fun xs _ => do
        let fields := xs.extract c.numParams xs.size
        fields.anyM fun x => return (← inferType x).hasAnyFVar (fields.contains <| .fvar ·)
      if dependent then throwError "constructor `{c.name}` has a field depending on another one"
      k c

variable (c : ConstructorVal)

/-- Runs `k params T tuple` with the parameters of `c` (implicit, as in `c`'s type), the type
`T params`, and the type `A × B × ...` of the tuple of the fields of `c`. -/
def withCtorTuple {α : Type} (k : Array Expr → Expr → Expr → MetaM α) : MetaM α := do
  forallBoundedTelescope c.type c.numParams fun params _ => do
    let T := mkAppN (mkConst c.induct (c.levelParams.map .param)) params
    let tuple ← withCtorArgs c.name params fun args => do
      mkNestedProdType (← args.toList.mapM argType)
    k params T tuple

/-- The type of `c.ι`: `params → (A × B × ...) → T params`. -/
def ctorUncurriedType : MetaM Expr :=
  withCtorTuple c fun params T tuple => do mkForallFVars params (← mkArrow tuple T)

/-- The type of `c.π`: `params → T params → Option (A × B × ...)`. -/
def ctorProjType : MetaM Expr :=
  withCtorTuple c fun params T tuple => do
    mkForallFVars params (← mkArrow T (← mkAppM ``Option #[tuple]))

/-- `c.ι : params → (A × B × ...) → T params`, the constructor `c` as a function of the tuple of
its fields. -/
def mkCtorUncurried : MetaM Unit := do
  let value ← withCtorTuple c fun params _ tuple => do
    let body ← withLocalDeclD `x tuple fun x => do
      let components ← (Array.range c.numFields).mapM (mkNestedProdProj x · c.numFields)
      let ctor := mkConst c.name (c.levelParams.map .param)
      mkLambdaFVars #[x] (mkAppN ctor (params ++ components))
    mkLambdaFVars params body
  let name := c.name.str "ι"
  addAndCompile <| .defnDecl {
    name, levelParams := c.levelParams, type := ← inferType value, value
    hints := .abbrev, safety := .safe }
  simpExtension.add (.toUnfold name) .global

/-- `c.π : params → T params → Option (A × B × ...)`, by `casesOn`: `some` of the tuple of the
fields on `c`, and `none` elsewhere, with a `@[simp]` equation `c.π.eq_d` per constructor `d`,
and defines nothing for a constructor without fields. -/
def mkCtorProj : MetaM Unit := do
  if c.numFields == 0 then return
  let info ← getConstInfoInduct c.induct
  let levels := c.levelParams.map .param
  let name := c.name.str "π"
  withCtorTuple c fun params T tuple => do
    let value (d : Name) (args : Array Expr) : MetaM Expr := do
      if d == c.name then mkSome tuple (← mkNestedProdValue args.toList) else mkNone tuple
    let alts ← info.ctors.toArray.mapM fun d => withCtorArgs d params fun args => do
      mkLambdaFVars args (← value d args)
    let body ← withLocalDeclD `x T fun x => do
      let resultTy ← mkAppM ``Option #[tuple]
      mkLambdaFVars (params.push x) (← mkCasesOnConst c.induct levels params resultTy x alts)
    addAndCompile <| .defnDecl {
      name, levelParams := c.levelParams, type := ← inferType body, value := body
      hints := .abbrev, safety := .safe }
    for d in info.ctors do
      let thm := name.str ("eq_" ++ d.getString!)
      withCtorArgs d params fun args => do
        let xs := params ++ args
        let lhs := mkApp (mkAppN (mkConst name levels) params) (mkAppN (mkConst d levels) xs)
        addDecl <| .thmDecl {
          name := thm, levelParams := c.levelParams
          type := ← mkForallFVars xs (← mkEq lhs (← value d args))
          value := ← mkLambdaFVars xs (← mkEqRefl lhs) }
      addSimpTheorem simpExtension thm (post := true) (inv := false) .global (eval_prio default)

syntax (name := constructors) "constructors" : attr

initialize registerBuiltinAttribute {
  name := `constructors
  descr := "Declares `c.ι`, constructor `c` as a function of the tuple of its fields"
  add := fun decl _ _ => forEachCtor decl mkCtorUncurried }

syntax (name := uncurriedProjections) "uncurriedProjections" : attr

initialize registerBuiltinAttribute {
  name := `uncurriedProjections
  descr := "Declares `c.π`, the projection of the values of constructor `c` on their fields"
  add := fun decl _ _ => forEachCtor decl mkCtorProj }

end Metrology.Meta
