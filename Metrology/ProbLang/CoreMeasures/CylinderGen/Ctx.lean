module

public meta import Lean
public meta import Metrology.Meta.Projections
public import Metrology.ProbLang.CoreMeasures.Shapes

@[expose] public section

open Lean Meta Metrology.Meta

/-! # The shared context of the `MeasurableSpace` deriving handler

`Ctx` reads an inductive type `T` with its classified constructor fields, and builds the terms
that the stages of `CylinderGen.lean` share. -/

namespace Metrology.CylinderGen

meta section

/-! ## Reading the inductive type -/

/-- How a field of a constructor enters the shape and the leaves. -/
inductive Kind
  /-- A field of type `T`. -/
  | recursive
  /-- A countable field with measurable singletons, part of the shape. -/
  | base
  /-- Any other field, a leaf. -/
  | data
  deriving BEq, Inhabited

instance : ToString Kind := ⟨fun | .recursive => "recursive" | .base => "base" | .data => "data"⟩

/-- A field of a constructor, with its classification. -/
structure Field where
  /-- The name of the field. -/
  name : Name
  /-- The classification of the field. -/
  kind : Kind
  /-- The type, with the parameters of `T` free. -/
  type : Expr
  deriving Inhabited

/-- A constructor of `T`, with its fields. -/
structure Ctor where
  /-- The full name of the constructor. -/
  name : Name
  /-- The position among the constructors of `T`. -/
  idx : Nat
  /-- The explicit fields, in order. -/
  fields : Array Field
  deriving Inhabited

/-- Whether the field is part of the shape: a base or recursive field, not a data field. -/
def Field.indexed (f : Field) : Bool := f.kind != .data

/-- Whether the arm takes `f` of the field rather than its value: at a recursive field of a
structural recursion (`structural`). -/
def Field.callsF (structural : Bool) (f : Field) : Bool := structural && f.kind == .recursive

variable (c : Ctor)

/-- Whether the constructor has a recursive field. -/
def Ctor.isRecursive : Bool := c.fields.any (·.kind == .recursive)

/-- The name of the constructor, without the namespace of `T`. -/
def Ctor.short : String := c.name.lastComponentAsString

/-- `pre_c`, the name of a hypothesis about `c` in the generated lemmas. -/
def Ctor.named (pre : String) : Name := .mkSimple s!"{pre}_{c.short}"

/-- What the generator knows about `T`, with its parameters and their measurable spaces free. -/
structure Ctx where
  /-- The name of the inductive type. -/
  T : Name
  /-- The universe parameters of `T`. -/
  levelParams : List Name
  /-- The parameters of `T`, as free variables. -/
  params : Array Expr
  /-- A `MeasurableSpace` instance variable per parameter. -/
  insts : Array Expr
  /-- The constructors, in declaration order (`Ctor.idx`). -/
  ctors : Array Ctor
  /-- The universe of `T`. -/
  w : Level

/-- A field is recursive if its type is `T`, base if its type is closed, countable and has
measurable singletons, and data otherwise. -/
def classifyField (T : Name) (ty : Expr) : MetaM Kind := do
  if ← isProp ty then throwError "cylinders: proof field of type {ty} is not supported"
  if ty.getAppFn.isConstOf T then return .recursive
  if (ty.find? (·.isConstOf T)).isSome then
    throwError "cylinders: field type {ty} contains `{T}` in an unsupported position"
  unless ← hasInstance ``MeasurableSpace #[ty] do
    throwError "cylinders: field type {ty} has no `MeasurableSpace` instance"
  if !ty.hasFVar && !ty.hasLevelParam && (← hasInstance ``Countable #[ty]) &&
      (← hasInstance ``MeasurableSingletonClass #[ty, none]) then
    return .base
  return .data

/-- Runs `k` with the parameters of `T` and their measurable spaces in scope. -/
def withCtx [Inhabited α] (T : Name) (k : Ctx → MetaM α) : MetaM α := do
  let info ← getConstInfoInduct T
  unless info.all.length == 1 do
    throwError "cylinders: mutual inductive blocks are not supported yet"
  unless info.numNested == 0 do throwError "cylinders: nested inductives are not supported"
  unless info.numIndices == 0 do throwError "cylinders: indexed families are not supported"
  forallBoundedTelescope info.type info.numParams fun params sort => do
  if sort.isProp then throwError "cylinders: `{T}` is a `Prop`"
  for p in params do
    unless (← inferType p).isType do
      throwError "cylinders: parameter {p} must be a `Type _`, got {← inferType p}"
    unless (← p.fvarId!.getBinderInfo).isExplicit do
      throwError "cylinders: parameter `{p}` must be explicit"
  let insts := params.map fun p => decl `inst .instImplicit (mkAppM ``MeasurableSpace #[p])
  withLocalDecls insts fun insts => do
  let ctors ← info.ctors.toArray.mapIdxM fun idx c => do
    withCtorArgs c params fun xs => do
      let fields ← xs.mapIdxM fun i x => do
        let d ← x.fvarId!.getDecl
        let type := d.type.cleanupAnnotations
        unless d.binderInfo.isExplicit do
          throwError "cylinders: constructor `{c}` has a non-explicit field `{d.userName}`; \
            only explicit fields are supported"
        if xs[:i].any (type.containsFVar ·.fvarId!) then
          throwError "cylinders: dependent field type {type} is not supported"
        return { name := d.userName, kind := ← classifyField T type, type : Field }
      return { name := c, idx, fields }
  let some w := (← getLevel (mkAppN (mkConst T (info.levelParams.map .param)) params)).dec
    | throwError "cylinders: `{T}` must be in `Type _`"
  k { T, levelParams := info.levelParams, params, insts, ctors, w }

/-! ## Constants -/

variable (ctx : Ctx) (c : Ctor)

/-- The universes of `T`. -/
def Ctx.levels : List Level := ctx.levelParams.map .param

/-- The constant `n`, at the universes of `T`, applied to the parameters (and, with `insts`, their
measurable spaces). -/
def Ctx.const (n : Name) (insts := false) : Expr :=
  mkAppN (mkConst n ctx.levels) (if insts then ctx.params ++ ctx.insts else ctx.params)

/-- The constant `T.suffix`, built by `Ctx.const` with the parameters of `T`. -/
def Ctx.member (suffix : Name) (insts := false) : Expr :=
  ctx.const (ctx.T ++ suffix) insts

/-- The type `T params`. -/
def Ctx.ty : Expr := ctx.const ctx.T
/-- The type `T.Shape` (not the function `T.shape`). -/
def Ctx.shape : Expr := mkConst (ctx.T ++ `Shape)
/-- The name of the shape constructor `T.Shape.c`. -/
def Ctx.shapeCtor : Name := (ctx.T ++ `Shape).str c.short
/-- The shape `T.Shape.c args`. -/
def Ctx.shapeOf (args : Array Expr) : Expr :=
  mkAppN (mkConst (ctx.shapeCtor c)) args
/-- The type `T.Leaves s` of the leaves of the shape `s`. -/
def Ctx.leaves (s : Expr) : Expr := mkApp (ctx.member `Leaves) s
/-- The constant `T.measurableEquiv`, applied to the parameters and their instances. -/
def Ctx.equiv : Expr := ctx.member `measurableEquiv (insts := true)
/-- `PUnit`, in the universe of the leaves. -/
def Ctx.punit : Expr := mkConst ``PUnit [ctx.w.succ]
/-- `PUnit.unit`, in the universe of the leaves. -/
def Ctx.unit : Expr := mkConst ``PUnit.unit [ctx.w.succ]

/-- `ULift A`, in the universe of `T`. -/
def Ctx.ulift (A : Expr) : MetaM Expr :=
  return mkApp (mkConst ``ULift [ctx.w, ← getDecLevel A]) A

/-- `ULift.up x`, in the universe of `T`. -/
def Ctx.up (x : Expr) : MetaM Expr := do
  let A ← inferType x
  return mkApp2 (mkConst ``ULift.up [ctx.w, ← getDecLevel A]) A x

/-- The type `Σ s, T.Leaves s` of shapes with their leaves. -/
def Ctx.sigma : MetaM Expr := mkAppM ``Sigma #[ctx.member `Leaves]
/-- The pair `⟨s, v⟩ : Σ s, T.Leaves s` of a shape and its leaves. -/
def Ctx.sigmaMk (s v : Expr) : MetaM Expr :=
  mkAppOptM ``Sigma.mk #[ctx.shape, ctx.member `Leaves, s, v]

/-- The type of a field, with `T` at the recursive fields. -/
def Ctx.fieldType (f : Field) : Expr := if f.kind == .recursive then ctx.ty else f.type

/-! ## Local variables -/

/-- Runs `k` with the fields of `c` as local variables, with `T` at the recursive fields. -/
def Ctx.withFields [Inhabited α] (k : Array Expr → MetaM α) : MetaM α :=
  withLocalDecls (c.fields.map fun f => decl f.name .default (pure (ctx.fieldType f))) k

/-! ## Recursors -/

/-- `I.rec` on `major`, where `I` is `T` or `T.Shape`, whose constructors are those of `ctx.ctors`,
with the arm of `c` built by `arm c xs ihs` from its first `numFields c`
arguments `xs` (fields) and the rest `ihs` (the motive at the recursive fields). -/
def Ctx.mkRec (I : Name) (levels : List Level) (params : Array Expr)
    (numFields : Ctor → Nat) (motive major : Expr)
    (arm : Ctor → List Expr → List Expr → MetaM Expr) : MetaM Expr := do
  let u ← lambdaTelescope motive fun _ b => getLevel b
  let rec_ := mkAppN (mkConst (I ++ `rec) (u :: levels)) (params.push motive)
  let arms ← forallBoundedTelescope (← inferType rec_) ctx.ctors.size fun ms _ =>
    (ctx.ctors.zip ms).mapM fun (c, m) => do
      let n := numFields c
      let numRecs := (c.fields.filter (·.kind == .recursive)).size
      forallBoundedTelescope (← inferType m) (n + numRecs) fun xs _ => do
        mkLambdaFVars xs (← arm c (xs.toList.take n) (xs.toList.drop n))
  return mkAppN rec_ (arms.push major)

/-- A field of a constructor in an arm of `T.rec`: its value, and the motive there if it is
recursive. -/
inductive Slot
  /-- A base field, with its value. -/
  | base (x : Expr)
  /-- A data field, with its value. -/
  | data (x : Expr)
  /-- A recursive field, with its value and the motive there. -/
  | recursive (x ih : Expr)

/-- `T.rec` on `major`, with arm `arm c slots` for constructor `c`. -/
def Ctx.recurse (motive major : Expr) (arm : Ctor → Array Slot → MetaM Expr) :
    MetaM Expr :=
  ctx.mkRec ctx.T ctx.levels ctx.params (·.fields.size) motive major fun c xs ihs => do
    let mut (ihs, slots) := (ihs, #[])
    for f in c.fields, x in xs do
      match f.kind with
      | .base => slots := slots.push (.base x)
      | .data => slots := slots.push (.data x)
      | .recursive =>
        let ih :: ihs' := ihs | unreachable!
        (ihs, slots) := (ihs', slots.push (.recursive x ih))
    arm c slots

/-- A field of a constructor in an arm of `T.Shape.rec`: a base field with its value, a data field
with its type (`T.Shape` has no data fields), a recursive field with its shape and the motive
there. -/
inductive ShapeSlot
  /-- A base field, with its value. -/
  | base (x : Expr)
  /-- A data field, with its type. -/
  | leaf (ty : Expr)
  /-- A recursive field, with its shape and the motive there. -/
  | recursive (s ih : Expr)

/-- The argument of the shape constructor at this slot. -/
def ShapeSlot.shapeArg? : ShapeSlot → Option Expr
  | .base x | .recursive x _ => some x
  | .leaf _ => none

/-- `T.Shape.rec` on `major`, with arm `arm c slots` for constructor `c`. -/
def Ctx.recurseShape (motive major : Expr) (arm : Ctor → Array ShapeSlot → MetaM Expr) :
    MetaM Expr :=
  let numFields (c : Ctor) := (c.fields.filter (·.indexed)).size
  ctx.mkRec (ctx.T ++ `Shape) [] #[] numFields motive major fun c xs ihs => do
    let mut (xs, ihs, slots) := (xs, ihs, #[])
    for f in c.fields do
      if f.kind == .data then
        slots := slots.push (.leaf f.type)
        continue
      let x :: xs' := xs | unreachable!
      xs := xs'
      if f.kind == .base then
        slots := slots.push (.base x)
      else
        let ih :: ihs' := ihs | unreachable!
        (ihs, slots) := (ihs', slots.push (.recursive x ih))
    arm c slots

/-! ## Shapes and leaves of values -/

/-- The leaves of the values of shape `c slots`: `PUnit` at base fields, the lifted type at data
fields, and `leaves s ih` at recursive fields. -/
def Ctx.leavesTy (slots : Array ShapeSlot)
    (leaves : Expr → Expr → Expr := fun s _ => ctx.leaves s) : MetaM Expr := do
  let tys ← slots.mapM fun
    | .base _ => pure ctx.punit
    | .leaf ty => ctx.ulift ty
    | .recursive s ih => pure (leaves s ih)
  mkNestedProdType tys.toList ctx.punit

/-! ## Declarations -/

/-- Fails if `name` is taken, such as by a constructor of `T`. -/
def ensureFresh (name : Name) : MetaM Unit := do
  if (← getEnv).contains name then throwError "cylinders: `{name}` already exists"

/-- Adds `name`, abstracted over the parameters (and, with `insts`, their measurable spaces) and
then `binders`, as a `fun_prop` lemma if `funProp`. -/
def Ctx.declare (name : Name) (type value : Expr) (insts := false) (isDef := false)
    (binders : Array Expr := #[]) (funProp := false) : MetaM Unit := do
  ensureFresh name
  let xs := ctx.params ++ (if insts then ctx.insts else #[]) ++ binders
  let type ← instantiateMVars (← mkForallFVars xs type)
  let value ← instantiateMVars (← mkLambdaFVars xs value)
  let type := implicitPrefix ctx.params.size type
  let used := (collectLevelParams (collectLevelParams {} type) value).params.toList
  let levelParams := ctx.levelParams ++ used.filter (!ctx.levelParams.contains ·)
  if isDef then
    -- by recursors, or terms built on them, which have no compiled code
    addDecl <| .defnDecl { name, levelParams, type, value, hints := .abbrev, safety := .safe }
    modifyEnv (addNoncomputable · name)
  else
    addDecl <| .thmDecl { name, levelParams, type, value }
  if funProp then addAttribute `fun_prop name

/-- Adds the instance `name`, abstracted over the parameters and their measurable spaces. -/
def Ctx.declareInstance (name : Name) (type value : Expr)
    (binders : Array Expr := #[]) : MetaM Unit := do
  ctx.declare name type value (insts := true) (isDef := true) (binders := binders)
  setReducibilityStatus name .instanceReducible
  addInstance name .global (eval_prio default)

end

end Metrology.CylinderGen
