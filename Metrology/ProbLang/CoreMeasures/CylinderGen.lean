module

public meta import Lean
public import Metrology.ProbLang.CoreMeasures.Cylinders

@[expose] public section

open Lean Elab Command Meta

/-!
# Cylinder generator

`cylinder_defs T` generates the cylinder σ-algebra on an inductive type `T` and its measurability
API, from the constructors of `T`. `cylinder_defs? T` also logs the generated code.
`#cylinder_classify T` shows how each field is classified: recursive (of type `T`), base (countable
with measurable singletons: kept in `Shape`), or data (a `Set` in `Cylinder`, dropped from `Shape`).

The code is built with syntax quotations, so names bound in it are hygienic, and global names in it
are resolved here. The exceptions are the names the generated code declares, which are resolved
where it is elaborated (`exposeNames`), and binders the user refers to by name (`Ctx.plain`).
-/

namespace Metrology.CylinderGen

meta section

/-! ## Classification -/

inductive Kind | recursive | base | data
  deriving BEq, Inhabited

instance : ToString Kind := ⟨fun | .recursive => "recursive" | .base => "base" | .data => "data"⟩

structure Field where
  name : Name
  kind : Kind
  inhabited : Bool
  /-- Singletons are measurable (given measurable singletons in the parameters). -/
  singletons : Bool
  type : Term
  deriving Inhabited

structure Ctor where
  name : Name
  fields : Array Field
  deriving Inhabited

def Ctor.short (c : Ctor) : Name := .mkSimple c.name.getString!
def Ctor.raw (c : Ctor) : String := c.name.getString!
def Ctor.ident (c : Ctor) : Ident := mkIdent c.short

/-- `c.short` with `suffix` appended, as in `c.measurable`. -/
def Ctor.lemma (c : Ctor) (suffix : Name) : Ident := mkIdent (c.short ++ suffix)

structure Spec where
  name : Name
  params : Array Ident
  ctors : Array Ctor
  deriving Inhabited

/-- Names the generated code declares, in the current namespace or under `Cylinder` and `Shape`. -/
def generated : List Name :=
  [`Cylinder, `Shape, `cover, `singletonCyl, `decompCell, `decompCell_param, `ι, `π, `measurable,
   `measurableEmbedding, `casesOn_preimage_decomp, `casesOn_preimage_decomp_param, `measurable_rec,
   `measurable_rec_param, `singletonCyl_flatten, `singletonCyl_hasMeasurableLeaves,
   `instMeasurableSingletonClass, `measurable_struct_rec, `measurable_struct_rec_param,
   `measurable_struct_rec_param_shift, `flatten_measurable, `flatten, `flatten_eqs, `shape_eqs,
   `cylinder_eqs, `singletonCyl_eqs, `HasMeasurableLeaves, `shape, `inter?, `cylinder,
   `cylinder_hasMeasurableLeaves, `cylinder_preimage_shape, `mem_cylinder_shape,
   `shape_of_mem_flatten, `flatten_disjoint_of_shape_ne, `flatten_inter, `flatten_inter_some,
   `hasMeasurableLeaves_inter, `flatten_isPiSystem, `flatten_isCountablySpanning]

/-- The identifiers in `stx`, and the components of dotted ones. -/
partial def identNames : Syntax → List Name
  | .ident _ _ n _ => n :: n.components
  | .node _ _ args => args.toList.flatMap identNames
  | _ => []

def hasInstance (cls : Name) (args : Array (Option Expr)) : MetaM Bool := do
  try return (← synthInstance? (← mkAppOptM cls args)).isSome catch _ => return false

def classifyField (T : Name) (ty : Expr) : MetaM Kind := do
  if ty.getAppFn.isConstOf T then return .recursive
  if (ty.find? (·.isConstOf T)).isSome then
    throwError "cylinders: field type {ty} contains `{T}` in an unsupported position"
  unless ← hasInstance ``MeasurableSpace #[ty] do
    throwError "cylinders: field type {ty} has no `MeasurableSpace` instance"
  if (← hasInstance ``Countable #[ty]) && (← hasInstance ``MeasurableSingletonClass #[ty, none]) then
    return .base
  return .data

/-- `ty` as syntax, checked to elaborate back to `ty`. -/
def typeSyntax (ty : Expr) : MetaM Term := do
  let stx ← withOptions (fun o => o |>.setBool `pp.fullNames true |>.setBool `pp.funBinderTypes true
    |>.setBool `pp.numericTypes true |>.setBool `pp.coercions.types true) (PrettyPrinter.delab ty)
  let ok ← withoutModifyingState do
    modifyThe Core.State ({ · with messages := {} })
    try
      Term.TermElabM.run' <| Term.withoutErrToSorry do
        let ty' ← Term.elabType stx
        Term.synthesizeSyntheticMVarsNoPostponing
        return (← isDefEq ty ty') && !(← MonadLog.hasErrors)
    catch _ => return false
  unless ok do
    throwError "cylinders: cannot reproduce field type {ty} as source (printed as `{stx}`)"
  return stx

def classify (T : Name) : MetaM Spec := do
  let info ← getConstInfoInduct T
  unless info.all.length == 1 do throwError "cylinders: mutual inductive blocks are not supported yet"
  unless info.numNested == 0 do throwError "cylinders: nested inductives are not supported"
  unless info.numIndices == 0 do throwError "cylinders: indexed families are not supported"
  if ← forallTelescope info.type fun _ ty => return ty.isProp then
    throwError "cylinders: `{T}` is a `Prop`"
  forallBoundedTelescope info.type info.numParams fun params _ => do
  for p in params do
    let n ← p.fvarId!.getUserName
    let ty ← whnf (← inferType p)
    unless ty.isSort && ty.sortLevel!.dec.isSome do
      throwError "cylinders: parameter {p} must be a `Type _`, got {ty}"
    if n.hasMacroScopes then throwError "cylinders: parameters must be named"
    unless (← p.fvarId!.getBinderInfo).isExplicit do
      throwError "cylinders: parameter `{n}` must be explicit"
    if (generated ++ T.components).contains n then
      throwError "cylinders: parameter name `{n}` clashes with a name used by the generated code"
  let insts := params.map fun p => (`inst, BinderInfo.instImplicit, fun _ => mkAppM ``MeasurableSpace #[p])
  withLocalDecls insts fun _ => do
  -- Field types are printed without the fields in scope, so that a field named like a
  -- parameter does not make the parameter print as inaccessible.
  let lctx ← getLCtx
  let linsts ← getLocalInstances
  let ctors ← info.ctors.toArray.mapM fun c => do
    if (generated ++ [Name.mkSimple s!"instMeasurableSpace{T.getString!}"]).contains (Name.mkSimple c.getString!) then
      throwError "cylinders: constructor name `{c.getString!}` clashes with a name used by the generated code"
    forallTelescope (← instantiateForall (← getConstInfo c).type params) fun xs _ => do
      let fields ← xs.mapIdxM fun i x => do
        let d ← x.fvarId!.getDecl
        let d := d.setType d.type.cleanupAnnotations
        unless d.binderInfo.isExplicit do
          throwError "cylinders: constructor `{c}` has a non-explicit field `{d.userName}`; \
            only explicit fields are supported"
        if xs[:i].any (d.type.containsFVar ·.fvarId!) then
          throwError "cylinders: dependent field type {d.type} is not supported"
        let type ← withLCtx lctx linsts (typeSyntax d.type)
        if let some g := generated.find? (identNames type).contains then
          throwError "cylinders: field type {d.type} mentions `{g}`, which the generated code defines"
        let mscs := params.map fun p => (`inst, BinderInfo.instImplicit, fun _ =>
          mkAppOptM ``MeasurableSingletonClass #[some p, none])
        return { name := d.userName, kind := ← classifyField T d.type, type,
                 inhabited := ← hasInstance ``Inhabited #[d.type]
                 singletons := ← withLocalDecls mscs fun _ =>
                   hasInstance ``MeasurableSingletonClass #[d.type, none] : Field }
      return { name := c, fields }
  for c in ctors do
    if ctors.any (·.raw == c.raw ++ "_univ_eq_range") then
      throwError "cylinders: constructors `{c.raw}` and `{c.raw}_univ_eq_range` would both define \
        `cover.{c.raw}_univ_eq_range`"
  return { name := T, params := ← params.mapM fun p => return mkIdent (← p.fvarId!.getUserName), ctors }

/-! ## Context -/

abbrev Binder := TSyntax ``Parser.Term.bracketedBinder
abbrev Tactic := TSyntax `tactic
abbrev Pat := TSyntax `rcasesPat

structure Ctx where
  spec : Spec
  /-- Constructors whose recursive fields are under a binder (`cylinder_defs T shifting c …`). -/
  shifting : List Name
  /-- Names a plain binder must not take: it would capture them. -/
  avoid : List Name
  /-- `T α β …` -/
  ty : Term
  /-- `Cylinder α β …` -/
  cyl : Term
  /-- `{α : Type _} …` -/
  implicits : Array Binder
  /-- `[MeasurableSpace α] …` -/
  insts : Array Binder
  /-- `(α := α) …` -/
  named : Array (TSyntax ``Parser.Term.namedArgument)

def Ctx.make (spec : Spec) (shifting : List Name) : CommandElabM Ctx := do
  let ps : Array Term := spec.params.map fun p => p
  let types := spec.ctors.toList.flatMap (·.fields.toList.map (·.type))
  return {
    spec, shifting
    avoid := spec.params.toList.map (·.getId) ++ generated ++ spec.name.components ++
      spec.ctors.toList.map (·.short) ++ types.flatMap identNames
    ty := Syntax.mkApp (mkIdent spec.name) ps
    cyl := Syntax.mkApp (← `(Cylinder)) ps
    implicits := ← spec.params.mapM fun p => `(bracketedBinder| {$p : Type _})
    insts := ← spec.params.mapM fun p => `(bracketedBinder| [MeasurableSpace $p])
    named := ← spec.params.mapM fun p => `(Parser.Term.namedArgument| ($p:ident := $p)) }

def Ctx.ctors (ctx : Ctx) : Array Ctor := ctx.spec.ctors

/-- A binder the user can refer to by name, primed until it captures nothing. -/
def Ctx.plain (ctx : Ctx) (n : String) (taken : List Name := []) : Ident := Id.run do
  let mut n := Name.mkSimple n
  while ctx.avoid.contains n || taken.contains n do n := n.appendAfter "'"
  return mkIdent n

/-- A type variable the user can refer to by name: `pref`, or failing that the first of `γ`, `δ`,
`ε`, `ζ` that captures nothing. -/
def Ctx.greek (ctx : Ctx) (pref : String) (taken : List Ident := []) : Ident :=
  let free (n : String) := !ctx.avoid.contains (.mkSimple n) && !taken.any (·.getId == .mkSimple n)
  match (pref :: ["γ", "δ", "ε", "ζ"]).find? free with
  | some n => mkIdent (.mkSimple n)
  | none => ctx.plain pref (taken.map (·.getId))

/-- The codomain `α` and the threaded parameter `β` of the `_param` lemmas. -/
def Ctx.paramVars (ctx : Ctx) : Ident × Ident :=
  let β := ctx.greek "β"
  (ctx.greek "α" [β], β)

/-- `{α β : Type _}`, in alphabetical order. -/
def typeVars (α β : Ident) : CommandElabM Binder := do
  let (a, b) := if α.getId.toString < β.getId.toString then (α, β) else (β, α)
  `(bracketedBinder| {$a $b : Type _})

/-- A hygienic name. -/
def fresh (n : String) : CommandElabM Ident :=
  return mkIdent (← MonadQuotation.addMacroScope (.mkSimple n))

/-- Hygienic names `pre1`, `pre2`, … for `c`'s fields. -/
def Ctor.vars (c : Ctor) (pre : String) : CommandElabM (Array Ident) :=
  c.fields.mapIdxM fun i _ => fresh s!"{pre}{i + 1}"

/-- Hygienic names for `c`'s fields, by kind: `x` (base), `S` (data) and `rec` (recursive). -/
def Ctor.fieldVars (c : Ctor) (rec := "c") : CommandElabM (Array Ident) :=
  c.fields.mapIdxM fun i f =>
    fresh s!"{match f.kind with | .base => "x" | .data => "S" | .recursive => rec}{i + 1}"

/-- Plain names for `c`'s fields in the declarations of `Cylinder` and `Shape`: a field's own
name where it captures nothing, so that named arguments like `(op := op)` work. -/
def Ctx.ownNames (ctx : Ctx) (c : Ctor) (rec : String) : Array Ident :=
  let gen := c.fields.mapIdx fun i f =>
    ctx.plain s!"{match f.kind with | .base => "x" | .data => "S" | .recursive => rec}{i + 1}"
  c.fields.mapIdx fun i f =>
    let own := f.name.isAtomic && !f.name.hasMacroScopes && !ctx.avoid.contains f.name &&
      !gen.any (·.getId == f.name) && (c.fields.filter (·.name == f.name)).size == 1
    if own && f.kind == .base then mkIdent f.name else gen[i]!

/-- The plain `<pre>_<c>` binders of the constructors, pairwise distinct. -/
def Ctx.perCtor (ctx : Ctx) (pre : String) : Array (Ctor × Ident) :=
  ctx.ctors.zip <| ctx.ctors.foldl (init := #[]) fun acc c =>
    acc.push (ctx.plain s!"{pre}_{c.raw}" (acc.toList.map (·.getId)))

def Ctor.idx (c : Ctor) (p : Kind → Bool) : Array Nat :=
  (Array.range c.fields.size).filter (p c.fields[·]!.kind)

/-- The fields that `flatten` takes sets of: data and recursive. -/
def Ctor.sets (c : Ctor) : Array Nat := c.idx (· != .base)
/-- The fields that `Shape` keeps: base and recursive. -/
def Ctor.keys (c : Ctor) : Array Nat := c.idx (· != .data)
def Ctor.recs (c : Ctor) : Array Nat := c.idx (· == .recursive)
def Ctor.bases (c : Ctor) : Array Nat := c.idx (· == .base)
def Ctor.kind (c : Ctor) (i : Nat) : Kind := c.fields[i]!.kind

/-- The position of field `i` among the fields `is`. -/
def pos (is : Array Nat) (i : Nat) : Nat := (is.findIdx? (· == i)).get!

/-! ## Syntax helpers -/

/-- `A × B × …`, or `Unit`. -/
def tupleType (tys : Array Term) : CommandElabM Term :=
  if tys.isEmpty then `(Unit) else tys.pop.foldrM (fun a b => `($a × $b)) tys.back!

/-- Component `k` of a right-nested `n`-tuple `p`: `p.1`, `p.2.1`, …, `p.2.….2`. -/
def proj (p : Term) (k n : Nat) : CommandElabM Term := do
  if n ≤ 1 then return p
  let mut t := p
  for _ in [:k] do t ← `($t.2)
  if k + 1 < n then t ← `($t.1)
  return t

/-- `⟨x, y, …⟩`, or `x` alone. -/
def anon (xs : Array Term) : CommandElabM Term :=
  if h : xs.size = 1 then return xs[0] else `(⟨$xs,*⟩)

/-- The pattern `⟨p, q, …⟩`, or `p` alone. -/
def tuplePat (ps : Array Pat) : CommandElabM Pat := do
  if h : ps.size = 1 then return ps[0]
  let ps ← ps.mapM fun p => `(Lean.Parser.Tactic.rcasesPatLo| $p:rcasesPat)
  `(rcasesPat| ⟨$ps,*⟩)

def identPat (x : Ident) : CommandElabM Pat := `(rcasesPat| $x:ident)

/-- `a ∧ b ∧ …`, or `True`. -/
def conj (ps : Array Term) : CommandElabM Term :=
  if ps.isEmpty then `(True) else ps.pop.foldrM (fun a b => `($a ∧ $b)) ps.back!

/-- Identifiers as terms. -/
def terms (xs : Array Ident) : Array Term := xs.map fun x => x

def Ctx.params (ctx : Ctx) : Array Term := terms ctx.spec.params

/-- `@T.c α … args`: with `@`, fields with default values are not filled in. -/
def Ctx.apply (ctx : Ctx) (c : Ctor) (args : Array Term) : CommandElabM Term :=
  return Syntax.mkApp (← `(@$(mkIdent c.name))) (ctx.params ++ args)

/-- `.c args` -/
def Ctor.dot (c : Ctor) (args : Array Term) : CommandElabM Term :=
  return Syntax.mkApp (← `(.$c.ident:ident)) args

/-- `@T.c.<suffix> α …`, for the projections `ι` and `π` of `@[uncurriedProjections]`. -/
def Ctx.uncurried (ctx : Ctx) (c : Ctor) (suffix : Name) : CommandElabM Term :=
  return Syntax.mkApp (← `(@$(mkIdent (c.name ++ suffix)))) ctx.params

def Ctx.T (ctx : Ctx) (suffix : Name) : Ident := mkIdent (ctx.spec.name ++ suffix)

/-- The type of the field as it appears in `T`. -/
def Ctx.fieldType (ctx : Ctx) (f : Field) : Term := if f.kind == .recursive then ctx.ty else f.type

/-- The tuple of `c`'s fields. -/
def Ctx.dom (ctx : Ctx) (c : Ctor) : CommandElabM Term := tupleType (c.fields.map ctx.fieldType)

/-- The type of the field as it appears in `Cylinder`. -/
def Ctx.cylFieldType (ctx : Ctx) (f : Field) : CommandElabM Term :=
  match f.kind with
  | .base => return f.type
  | .data => `(Set $f.type)
  | .recursive => return ctx.cyl

/-- The type of the field as it appears in `Shape`, if it does. -/
def shapeFieldType (f : Field) : CommandElabM Term :=
  if f.kind == .base then return f.type else `(Shape)

def matchAlt (pats : Array Term) (rhs : Term) : CommandElabM (TSyntax ``Parser.Term.matchAlt) :=
  `(Parser.Term.matchAltExpr| | $pats,* => $rhs)

def inductionAlt (c : Ctor) (vars : Array Ident) (tacs : Array Tactic) :
    CommandElabM (TSyntax ``Parser.Tactic.inductionAlt) :=
  `(Parser.Tactic.inductionAlt| | $c.ident:ident $vars* => $tacs*)

def simpOnly (lemmas : Array Term) : CommandElabM Tactic := `(tactic| simp only [$[$lemmas:term],*])

/-- A proof that `p` holds of the non-base fields of `c`, from proofs `t i` of them. -/
def Ctor.leaves (c : Ctor) (t : Nat → CommandElabM Term) : CommandElabM Term := do
  let ts ← c.sets.mapM t
  if ts.isEmpty then `(True.intro) else ts.pop.foldrM (fun a b => `(And.intro $a $b)) ts.back!

/-- Destructs the measurable leaves `h` of a `c`-cylinder with fields `ns` into `hs` (at the non-base
fields). -/
def Ctor.obtainLeaves (c : Ctor) (ns hs : Array Ident) (h : Ident) : CommandElabM (Array Tactic) := do
  match c.sets with
  | #[] => return #[]
  | #[i] =>
    let ty ← if c.kind i == .data then `(MeasurableSet $(ns[i]!):ident)
      else `(Cylinder.HasMeasurableLeaves $(ns[i]!):ident)
    return #[← `(tactic| have $(hs[i]!):ident : $ty := $h)]
  | sets => return #[← `(tactic| obtain $(← tuplePat (← sets.mapM (identPat hs[·]!))):rcasesPat := $h)]

/-- Membership in the flatten of a `c`-cylinder, as a term or a pattern: the values `vs` of the
non-base fields, their memberships `ms`, and the equation `eq`. -/
def Ctor.flattenMem {α} [Inhabited α] (c : Ctor) (tuple : Array α → CommandElabM α)
    (vs ms : Array α) (eq : α) : CommandElabM α :=
  match c.sets.size with
  | 0 => return eq
  | 1 => tuple #[vs[0]!, ms[0]!, eq]
  | _ => do tuple #[← tuple vs, ← tuple ms, eq]

/-- Generated declarations are named without hygiene, so that the user can refer to them, and so
are the references to them. So is `rfl` in patterns, which `rcases` matches by name. -/
partial def exposeNames : Syntax → Syntax
  | .ident info raw n pre =>
    if generated.contains n.eraseMacroScopes.getRoot then .ident info raw n.eraseMacroScopes pre
    else .ident info raw n pre
  | .node info k args =>
    if k == ``Parser.Tactic.rcasesPat.one && args[0]!.getId.eraseMacroScopes == `rfl then
      .node info k #[mkIdent `rfl]
    else .node info k (args.map exposeNames)
  | stx => stx

/-- `stx` with every name unhygienic, for display. -/
partial def eraseScopes : Syntax → Syntax
  | .ident info _ n pre => .ident info n.eraseMacroScopes.toString.toRawSubstring n.eraseMacroScopes pre
  | .node info k args => .node info k (args.map eraseScopes)
  | stx => stx

/-! ## Definitions -/

/-- Proves that a function out of an `n`-tuple that applies a constructor is injective. -/
def injective (n : Nat) : CommandElabM Tactic := do
  if n ≤ 1 then `(tactic| (intro a b h; cases h; rfl))
  else
    let tuple ← tuplePat (Array.replicate n (← `(rcasesPat| _)))
    `(tactic| (intro a b h; obtain $tuple:rcasesPat := a; obtain $tuple:rcasesPat := b; cases h; rfl))

def genInj (ctx : Ctx) (c : Ctor) : CommandElabM Command := do
  `(theorem $(c.lemma `ι.inj) $ctx.implicits* :
      Function.Injective $(← ctx.uncurried c `ι) := by $(← injective c.fields.size):tactic)

def genCylinder (ctx : Ctx) : CommandElabM Command := do
  let ctors ← ctx.ctors.mapM fun c => do
    let ns := ctx.ownNames c "c"
    let bs ← c.fields.mapIdxM fun i f => do `(bracketedBinder| ($(ns[i]!):ident : $(← ctx.cylFieldType f)))
    `(Parser.Command.ctor| | $c.ident:ident $bs*)
  let params ← ctx.spec.params.mapM fun p => `(bracketedBinder| ($p : Type _))
  `(/-- Cylinders: values with data fields replaced by sets of values. -/
    inductive Cylinder $params* $ctors:ctor*)

def genShape (ctx : Ctx) : CommandElabM Command := do
  let ctors ← ctx.ctors.mapM fun c => do
    let ns := ctx.ownNames c "s"
    let bs ← c.keys.mapM fun i => do `(bracketedBinder| ($(ns[i]!):ident : $(← shapeFieldType c.fields[i]!)))
    `(Parser.Command.ctor| | $c.ident:ident $bs*)
  let shape ← `(/-- Shapes: values with data fields forgotten, so that `Shape` is countable. -/
    inductive Shape $ctors:ctor* deriving Countable)
  let n := ctx.ctors.size
  -- `deriving Countable` is quadratic in the number of constructors
  if n ≤ 30 then return shape
  `(set_option maxHeartbeats $(Syntax.mkNumLit (toString (200000 * (n * n / 900 + 1)))) in $shape:command)

/-- The equations of `fn` on a type `dom`, as one conjunction proved by `rfl`: Lean's own equation
lemmas are slow to generate. `arm c` gives the fields of `c` and the right-hand side. -/
def Ctx.eqs (ctx : Ctx) (name : Ident) (fn : Term → CommandElabM Term) (dom : Term)
    (arm : Ctor → CommandElabM (Array Ident × Term)) : CommandElabM Command := do
  let parts ← ctx.ctors.mapM fun c => do
    let (xs, rhs) ← arm c
    let eq ← `($(← fn (← `(($(← c.dot (terms xs)) : $dom)))) = $rhs)
    if xs.isEmpty then return (eq, ← `(rfl))
    let holes := Array.replicate xs.size (← `(_))
    return (← `(∀ $xs*, $eq), ← `(fun $holes* => rfl))
  `(theorem $name $ctx.implicits* : $(← conj (parts.map (·.1))) := $(← anon (parts.map (·.2))))

/-- The image of `c` over the sets of its non-base fields, with fields `ns`. -/
def Ctx.image (ctx : Ctx) (c : Ctor) (ns : Array Ident) : CommandElabM Term := do
  let n := c.fields.size
  let set (i : Nat) : CommandElabM Term :=
    if c.kind i == .recursive then `(Cylinder.flatten $(ns[i]!):ident) else return ns[i]!
  if c.sets.isEmpty then `({$(← ctx.apply c (terms ns)):term})
  else if c.sets == #[n - 1] then `($(← ctx.apply c (terms ns.pop)) '' $(← set (n - 1)))
  else
    let args ← ns.mapIdxM fun i x => do
      if c.sets.contains i then proj (← `(p)) (pos c.sets i) c.sets.size else return x
    let sets ← c.sets.mapM set
    `((fun p : $(← tupleType (c.sets.map (ctx.fieldType c.fields[·]!))) => $(← ctx.apply c args)) ''
      $(← sets.pop.foldrM (fun a b => `($a ×ˢ $b)) sets.back!))

def genFlatten (ctx : Ctx) : CommandElabM (Array Command) := do
  let alts ← ctx.ctors.mapM fun c => do
    let ns ← c.fieldVars
    matchAlt #[← c.dot (terms ns)] (← ctx.image c ns)
  return #[
    ← `(/-- The set of values described by a cylinder. -/
      def Cylinder.flatten $ctx.implicits* : $ctx.cyl → Set $ctx.ty $alts:matchAlt*),
    ← ctx.eqs (mkIdent `Cylinder.flatten_eqs) (fun x => `(Cylinder.flatten $x)) ctx.cyl fun c => do
      let ns ← c.fieldVars
      return (ns, ← ctx.image c ns)]

def genHasMeasurableLeaves (ctx : Ctx) : CommandElabM Command := do
  let alts ← ctx.ctors.mapM fun c => do
    let ns ← c.fieldVars
    let pats ← c.fields.mapIdxM fun i f => if f.kind == .base then `(_) else return ns[i]!
    let conds ← c.sets.mapM fun i =>
      if c.kind i == .data then `(MeasurableSet $(ns[i]!):ident) else `(Cylinder.HasMeasurableLeaves $(ns[i]!):ident)
    matchAlt #[← c.dot pats] (← conj conds)
  `(/-- A cylinder has measurable leaves if every set it carries is measurable. -/
    def Cylinder.HasMeasurableLeaves $ctx.implicits* $ctx.insts* : $ctx.cyl → Prop $alts:matchAlt*)

def genInstance (ctx : Ctx) : CommandElabM Command := do
  `(instance $(mkIdent (.mkSimple s!"instMeasurableSpace{ctx.spec.name.getString!}")):ident
      $ctx.implicits* $ctx.insts* : MeasurableSpace $ctx.ty :=
    .generateFrom <| Cylinder.flatten '' { c : $ctx.cyl | c.HasMeasurableLeaves })

/-- The shape of a `c`-value or `c`-cylinder with fields `ns`, with `self` the recursive call. -/
def Ctor.shapeOf (c : Ctor) (ns : Array Ident) (self : Ident) : CommandElabM Term := do
  let ns := terms ns
  c.dot (← c.keys.mapM fun i => if c.kind i == .base then return ns[i]! else `($self $(ns[i]!)))

/-- `T.shape` (`ofValue`) or `Cylinder.shape`: the same arms, on values or on cylinders. -/
def genShapeOf (ctx : Ctx) (ofValue : Bool) : CommandElabM (Array Command) := do
  let (self, dom) := if ofValue then (ctx.T `shape, ctx.ty) else (mkIdent `Cylinder.shape, ctx.cyl)
  let owner := if ofValue then `_root_ ++ ctx.spec.name else `Cylinder
  let alts ← ctx.ctors.mapM fun c => do
    let ns ← c.fieldVars
    let pats ← c.fields.mapIdxM fun i f => if f.kind == .data then `(_) else return ns[i]!
    matchAlt #[← c.dot pats] (← c.shapeOf ns self)
  let eqs ← ctx.eqs (mkIdent (owner ++ `shape_eqs)) (fun x => `($self $x)) dom fun c => do
    let ns ← c.fieldVars
    return (ns, ← c.shapeOf ns self)
  let name := mkIdent (owner ++ `shape)
  if ofValue then
    return #[← `(/-- The shape of a value. -/
      def $name:ident $ctx.implicits* : $dom → Shape $alts:matchAlt*), eqs]
  return #[← `(/-- The shape of a cylinder. -/
    def $name:ident $ctx.implicits* : $dom → Shape $alts:matchAlt*), eqs]

def genShapeCylinder (ctx : Ctx) : CommandElabM (Array Command) := do
  let rhs (c : Ctor) (ns : Array Ident) : CommandElabM Term := do
    c.dot (← c.fields.mapIdxM fun i f => match f.kind with
      | .base => return ns[i]!
      | .data => `(Set.univ)
      | .recursive => `(Shape.cylinder $(ns[i]!):ident))
  let alts ← ctx.ctors.mapM fun c => do
    let ns ← c.fieldVars "s"
    matchAlt #[← c.dot (terms (c.keys.map (ns[·]!)))] (← rhs c ns)
  return #[
    ← `(/-- The cylinder of all values of a given shape: `univ` at every data field. -/
      def Shape.cylinder $ctx.implicits* : Shape → $ctx.cyl $alts:matchAlt*),
    ← ctx.eqs (mkIdent `Shape.cylinder_eqs) (fun x => `(Shape.cylinder $ctx.named:namedArgument* $x)) (← `(Shape))
      fun c => do
        let ns ← c.fieldVars "s"
        return (c.keys.map (ns[·]!), ← rhs c ns)]

/-- The condition on the base fields of two `c`-cylinders for them to intersect. -/
def Ctor.cond (c : Ctor) (ns ns' : Array Ident) : CommandElabM (Option Term) := do
  let eqs ← c.bases.mapM fun i => `($(ns[i]!):ident = $(ns'[i]!):ident)
  if eqs.isEmpty then return none
  return some (← conj eqs)

/-- The right-hand side of `Cylinder.inter?` on two `c`-cylinders with fields `ns` and `ns'`. -/
def Ctor.interArm (c : Ctor) (ns ns' : Array Ident) : CommandElabM Term := do
  let rs ← c.vars "r"
  let meet ← c.fields.mapIdxM fun i f => match f.kind with
    | .base => return ns[i]!
    | .data => `($(ns[i]!):ident ∩ $(ns'[i]!):ident)
    | .recursive => return rs[i]!
  let result ← `(some $(← c.dot meet))
  let body ← if c.recs.isEmpty then pure result else do
    let both ← c.recs.mapM fun i => `(Cylinder.inter? $(ns[i]!):ident $(ns'[i]!):ident)
    let somes ← c.recs.mapM fun i => `(some $(rs[i]!):ident)
    let others ← if c.recs.size == 1 then pure #[← `(none)] else c.recs.mapM fun _ => `(_)
    `(match $[$both:term],* with | $somes,* => $result | $others,* => none)
  match ← c.cond ns ns' with
  | none => return body
  | some cond => `(if $cond then $body else none)

def genInter (ctx : Ctx) : CommandElabM Command := do
  let mut alts ← ctx.ctors.mapM fun c => do
    let ns ← c.fieldVars
    let ns' ← ns.mapM fun x => fresh s!"{x.getId.eraseMacroScopes}'"
    matchAlt #[← c.dot (terms ns), ← c.dot (terms ns')] (← c.interArm ns ns')
  if ctx.ctors.size > 1 then alts := alts.push (← matchAlt #[← `(_), ← `(_)] (← `(none)))
  `(open Classical in
    /-- Partial intersection of cylinders: `none` when the intersection is empty. -/
    def Cylinder.inter? $ctx.implicits* : $ctx.cyl → $ctx.cyl → Option $ctx.cyl $alts:matchAlt*)

def Ctor.cover (c : Ctor) (suffix : Name := .anonymous) : Ident := mkIdent (`cover ++ c.short ++ suffix)

/-- `cover.c_univ_eq_range`, with the suffix in the last component. -/
def Ctor.coverRange (c : Ctor) : Ident := mkIdent (`cover ++ .mkSimple (c.raw ++ "_univ_eq_range"))

def Ctor.dataOnly (c : Ctor) : Bool := c.fields.size == 1 && c.kind 0 == .data

def genCoverDef (ctx : Ctx) (c : Ctor) : CommandElabM Command := do
  let cylCtor := mkIdent (`Cylinder ++ c.short)
  if c.dataOnly then
    `(def $(c.cover) $ctx.implicits* (S : Set $(c.fields[0]!.type)) : Set $ctx.ty :=
        Cylinder.flatten ($cylCtor S : $ctx.cyl))
  else
    let args ← c.fields.mapIdxM fun i f => do match f.kind with
      | .base => proj (← `(p)) (pos c.keys i) c.keys.size
      | .recursive => `(Shape.cylinder $(← proj (← `(p)) (pos c.keys i) c.keys.size))
      | .data => `((Set.univ : Set $f.type))
    `(def $(c.cover) $ctx.implicits* (S : Set $(← tupleType (← c.keys.mapM (shapeFieldType c.fields[·]!)))) :
          Set $ctx.ty :=
        ⋃ p ∈ S, Cylinder.flatten ($(Syntax.mkApp cylCtor args) : $ctx.cyl))

def genDecompCell (ctx : Ctx) : CommandElabM (Array Command) := do
  let fs := ctx.perCtor "f"
  let n := quote ctx.ctors.size
  let plain ← do
    let α := ctx.greek "α"
    let cells ← fs.mapM fun (c, f) => `($(mkIdent (c.name ++ `ι)) '' ($f ⁻¹' S))
    let binders ← fs.mapM fun (c, f) => do `(bracketedBinder| ($f : $(← ctx.dom c) → $α))
    `(/-- Per-constructor cells of the `casesOn` preimage decomposition. -/
      def decompCell $ctx.implicits* {$α : Type _} (S : Set $α) $binders* : Fin $n → Set $ctx.ty :=
        ![$cells,*])
  let param ← do
    let (α, β) := ctx.paramVars
    let cells ← fs.mapM fun (c, f) => do
      let args ← (Array.range c.fields.size).mapM (proj (← `(q.2)) · c.fields.size)
      `((fun q : $β × $(← ctx.dom c) => ($(← ctx.apply c args), q.1)) '' ($f ⁻¹' S))
    let binders ← fs.mapM fun (c, f) => do `(bracketedBinder| ($f : $β × $(← ctx.dom c) → $α))
    let vars ← typeVars α β
    `(/-- Per-constructor cells of the parameterised `casesOn` preimage decomposition. -/
      def decompCell_param $ctx.implicits* $vars (S : Set $α) $binders* :
          Fin $n → Set ($ctx.ty × $β) :=
        ![$cells,*])
  return #[plain, param]

def genSingletonCyl (ctx : Ctx) : CommandElabM (Array Command) := do
  let rhs (c : Ctor) (ns : Array Ident) : CommandElabM Term := do
    c.dot (← c.fields.mapIdxM fun i f => match f.kind with
      | .base => return ns[i]!
      | .data => `({$(ns[i]!):term})
      | .recursive => `(singletonCyl $(ns[i]!):ident))
  let alts ← ctx.ctors.mapM fun c => do
    let ns ← c.fieldVars
    matchAlt #[← c.dot (terms ns)] (← rhs c ns)
  return #[
    ← `(/-- The cylinder containing exactly one value. -/
      def singletonCyl $ctx.implicits* : $ctx.ty → $ctx.cyl $alts:matchAlt*),
    ← ctx.eqs (mkIdent `singletonCyl_eqs) (fun x => `(singletonCyl $x)) ctx.ty fun c => do
      let ns ← c.fieldVars
      return (ns, ← rhs c ns)]

/-! ## Generic lemmas -/

def genBasics (ctx : Ctx) : CommandElabM (Array Command) := do
  let alts ← ctx.ctors.mapM fun c => do
    let ns ← c.fieldVars "s"
    let ihs ← c.recs.mapM fun i => fresh s!"ih{i + 1}"
    let leaves ← c.leaves fun i =>
      if c.kind i == .data then `(MeasurableSet.univ) else return ihs[pos c.recs i]!
    inductionAlt c (c.keys.map (ns[·]!) ++ ihs) #[← `(tactic| exact $leaves)]
  let cP := ctx.plain "c"
  return #[
    ← `(/-- The cylinder of a shape has measurable leaves. -/
      theorem Shape.cylinder_hasMeasurableLeaves $ctx.implicits* $ctx.insts* (s : Shape) :
          (s.cylinder $ctx.named:namedArgument*).HasMeasurableLeaves := by
        induction s with $alts:inductionAlt*),
    ← `(/-- Flattened cylinders with measurable leaves are measurable. -/
      @[measurability]
      theorem flatten_measurable $ctx.implicits* $ctx.insts* {$cP : $ctx.cyl}
          (hc : Cylinder.HasMeasurableLeaves $cP) : MeasurableSet (Cylinder.flatten $cP) :=
        Cylinders.flatten_measurable rfl hc)]

def genShapeOfMem (ctx : Ctx) : CommandElabM Command := do
  let alts ← ctx.ctors.mapM fun c => do
    let ns ← c.fieldVars
    let ihs ← c.recs.mapM fun i => fresh s!"ih{i + 1}"
    let ms ← c.sets.mapM fun i => fresh s!"m{i + 1}"
    let destruct ← match ms with
      | #[] => `(tactic| obtain rfl : t = _ := h)
      | #[m] => `(tactic| obtain ⟨_, $m:ident, rfl⟩ := h)
      | ms => `(tactic| obtain ⟨_, $(← tuplePat (← ms.mapM identPat)), rfl⟩ := h)
    let uses ← c.recs.mapIdxM fun j i => `($(ihs[j]!):ident $(ms[pos c.sets i]!):ident)
    inductionAlt c (ns ++ ihs)
      #[destruct, ← simpOnly (#[← `($(ctx.T `shape_eqs)), ← `(Cylinder.shape_eqs)] ++ uses)]
  `(theorem Cylinder.shape_of_mem_flatten $ctx.implicits* {c : $ctx.cyl} {t : $ctx.ty}
        (h : t ∈ Cylinder.flatten c) : $(ctx.T `shape) t = Cylinder.shape c := by
      induction c generalizing t with $alts:inductionAlt*)

def genShapeLemmas (ctx : Ctx) : CommandElabM (Array Command) := do
  let shape := ctx.T `shape
  let simps := #[← `(Shape.cylinder_eqs), ← `(Cylinder.shape_eqs), ← `($(ctx.T `shape_eqs)),
    ← `(Cylinder.flatten_eqs)]
  return #[
    ← `(/-- Flattens of cylinders with different shapes are disjoint. -/
      theorem Cylinder.flatten_disjoint_of_shape_ne $ctx.implicits* {c₁ c₂ : $ctx.cyl}
          (h : Cylinder.shape c₁ ≠ Cylinder.shape c₂) :
          Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ = ∅ :=
        Cylinders.flatten_disjoint_of_shape_ne (cShape := Cylinder.shape)
          (fun {_ _} h => Cylinder.shape_of_mem_flatten h) h),
    ← `(/-- The cylinder of a shape flattens to the values of that shape. -/
      theorem Shape.cylinder_preimage_shape $ctx.implicits* (s : Shape) :
          (s.cylinder $ctx.named:namedArgument*).flatten = $shape ⁻¹' {s} :=
        Cylinders.cylinder_preimage_shape (cShape := Cylinder.shape)
          (fun {_ _} h => Cylinder.shape_of_mem_flatten h)
          (fun s => by induction s <;> simp_all [$[$simps:term],*])
          (fun p => by induction p <;> simp_all [$[$simps:term],*]) s),
    ← `(theorem Shape.mem_cylinder_shape $ctx.implicits* (p : $ctx.ty) :
          p ∈ (($shape p).cylinder $ctx.named:namedArgument*).flatten := by
        rw [Shape.cylinder_preimage_shape]; exact rfl)]

/-! ## Intersections

Two cylinders of different shapes are disjoint; two cylinders of the same shape intersect field by
field. -/

/-- A theorem `∀ c, motive c` by induction, with one lemma `name.k` per constructor `k`, so that
they are elaborated in parallel. `proof k ns` proves `motive (.k ns)`, with the induction
hypotheses `ih<i>`. -/
def Ctx.byConstructor (ctx : Ctx) (name : Name) (binders : Array Binder) (implicit : Bool)
    (motive : Term → CommandElabM Term) (proof : Ctor → Array Ident → CommandElabM (Array Tactic)) :
    CommandElabM (Array Command) := do
  let lemmas ← ctx.ctors.mapM fun k => do
    let ns ← k.fieldVars
    let fields ← k.fields.mapIdxM fun i f => do
      `(bracketedBinder| ($(ns[i]!):ident : $(← ctx.cylFieldType f)))
    let ihs ← k.recs.mapM fun i => do
      `(bracketedBinder| ($(← fresh s!"ih{i + 1}") : $(← motive ns[i]!)))
    let tacs ← proof k ns
    `(open Classical in
      theorem $(mkIdent (name ++ k.short)):ident $(binders ++ fields ++ ihs)* :
          $(← motive (← `(($(← k.dot (terms ns)) : $ctx.cyl)))) := by
        $[$tacs]*)
  let alts ← ctx.ctors.mapM fun k => do
    let ns ← k.fieldVars
    let ihs ← k.recs.mapM fun i => fresh s!"ih{i + 1}"
    inductionAlt k (ns ++ ihs)
      #[← `(tactic| exact $(Syntax.mkApp (mkIdent (name ++ k.short)) (terms (ns ++ ihs))))]
  let c₁ ← if implicit then `(bracketedBinder| {c₁ : $ctx.cyl}) else `(bracketedBinder| (c₁ : $ctx.cyl))
  return lemmas.push (← `(theorem $(mkIdent name):ident $binders* $c₁ : $(← motive (← `(c₁))) := by
    induction c₁ with $alts:inductionAlt*))

/-- Unfolds `Cylinder.inter?` on two `c`-cylinders by `rfl`: its equation lemmas are slow to
generate. -/
def Ctor.unfoldInter (c : Ctor) (ns ns' : Array Ident) : CommandElabM Term := do
  `(show Cylinder.inter? $(← c.dot (terms ns)) $(← c.dot (terms ns')) = $(← c.interArm ns ns') from rfl)

/-- Cases on the base-field condition of `inter?`: `neg` closes the case where the base fields
differ, and otherwise they are substituted. -/
def Ctor.gate (c : Ctor) (ns ns' : Array Ident) (loc : Option Ident) (neg : Tactic) :
    CommandElabM (Array Tactic) := do
  let some cond ← c.cond ns ns' | return #[]
  let rfls ← tuplePat (Array.replicate c.bases.size (← `(rcasesPat| rfl)))
  let loc ← loc.mapM fun h => `(Parser.Tactic.location| at $h:ident)
  return #[← `(tactic| by_cases hb : $cond), ← `(tactic| case neg => rw [ite_eq_right hb] $[$loc]?; $neg),
    ← `(tactic| rw [ite_eq_left hb] $[$loc]?), ← `(tactic| obtain $rfls:rcasesPat := hb)]

/-- Cases on the `inter?` of each recursive field, rewriting `at_ i`; the `none` cases are closed
right away by `close`, so this makes one goal per field rather than 2^fields. -/
def Ctor.splitInters (c : Ctor) (ns ns' : Array Ident) (at_ : Nat → Ident) (close : Tactic)
    (elimNone := false) : CommandElabM (Array Tactic) := do
  c.recs.foldlM (init := #[]) fun tacs i => do
    let (e, r, h) := (← fresh s!"e{i + 1}", ← fresh s!"r{i + 1}", at_ i)
    let split ← if elimNone then
        `(tactic| rcases $e:ident : Cylinder.inter? $(ns[i]!):ident $(ns'[i]!):ident with _ | $r:ident <;>
          rw [$e:ident] at $h:ident <;> simp only [Option.elim] at $h:ident)
      else `(tactic| rcases $e:ident : Cylinder.inter? $(ns[i]!):ident $(ns'[i]!):ident with _ | $r:ident <;>
          rw [$e:ident] at $h:ident)
    return tacs ++ #[split, ← `(tactic| · $close:tactic)]

/-- The function whose image `flatten` takes at `c` (with its base fields fixed), and a proof that
it is injective; `none` when `flatten` gives a singleton. -/
def Ctx.imageFn (ctx : Ctx) (c : Ctor) (ns : Array Ident) : CommandElabM (Option (Term × Tactic)) := do
  let n := c.sets.size
  if n == 0 then return none
  let dom ← tupleType (c.sets.map (ctx.fieldType c.fields[·]!))
  let inj ← injective n
  if c.sets == #[ns.size - 1] then
    return some (← `(($(← ctx.apply c (terms ns.pop)) : $dom → $ctx.ty)), inj)
  let args ← ns.mapIdxM fun i x => do
    if c.sets.contains i then proj (← `(p)) (pos c.sets i) n else return x
  return some (← `((fun p : $dom => $(← ctx.apply c args) : $dom → $ctx.ty)), inj)

def genFlattenInter (ctx : Ctx) : CommandElabM (Array Command) :=
  ctx.byConstructor `Cylinder.flatten_inter ctx.implicits (implicit := false)
    (fun x => `(∀ c₂ : $ctx.cyl,
      Cylinder.flatten $x ∩ Cylinder.flatten c₂ = (Cylinder.inter? $x c₂).elim ∅ Cylinder.flatten))
    fun k ns => do
      let ns' ← ns.mapM fun x => fresh s!"{x.getId.eraseMacroScopes}'"
      let hs ← k.recs.mapM fun i => fresh s!"h{i + 1}"
      let fn ← ctx.imageFn k ns
      let mut lemmas := #[← `(Cylinder.flatten_eqs), ← `(Option.elim), ← `(Set.prod_inter_prod),
        ← `(Set.prod_empty), ← `(Set.empty_prod), ← `(Set.image_empty), ← `(Set.inter_self)] ++ terms hs
      if fn.isSome then lemmas := lemmas.push (← `((Set.image_inter hF).symm))
      let close ← simpOnly lemmas
      let ihs ← k.recs.mapIdxM fun j i => do
        `(tactic| have $(hs[j]!):ident := $(← fresh s!"ih{i + 1}") $(ns'[i]!):ident)
      let injective ← fn.toArray.mapM fun (f, inj) =>
        `(tactic| have hF : Function.Injective $f := by $inj:tactic)
      let disjoint ← `(tactic|
        (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp_all [Cylinder.shape_eqs])]; rfl))
      let diag := ihs ++ injective ++ #[← `(tactic| rw [$(← k.unfoldInter ns ns'):term])] ++
        (← k.gate ns ns' none disjoint) ++
        (← k.splitInters ns ns' (hs[pos k.recs ·]!) close (elimNone := true)) ++ #[close]
      let vars ← ns'.mapM fun x => `(binderIdent| $x:ident)
      return #[← `(tactic| intro c₂), ← `(tactic| cases c₂),
        ← `(tactic| case $k.ident:ident $vars* => $diag*),
        ← `(tactic| all_goals exact Cylinder.flatten_disjoint_of_shape_ne Shape.noConfusion)]

def genHasMeasurableLeavesInter (ctx : Ctx) : CommandElabM (Array Command) :=
  ctx.byConstructor `Cylinder.hasMeasurableLeaves_inter (ctx.implicits ++ ctx.insts) (implicit := true)
    (fun x => `(∀ {c₂ c : $ctx.cyl}, Cylinder.HasMeasurableLeaves $x → c₂.HasMeasurableLeaves →
      Cylinder.inter? $x c₂ = some c → c.HasMeasurableLeaves))
    fun k ns => do
      let ns' ← ns.mapM fun x => fresh s!"{x.getId.eraseMacroScopes}'"
      let (as, bs) := (← k.vars "a", ← k.vars "b")
      let h ← fresh "h"
      let leaves ← k.leaves fun i => do
        if k.kind i == .data then `(MeasurableSet.inter $(as[i]!):ident $(bs[i]!):ident)
        else `(($(← fresh s!"ih{i + 1}") $(as[i]!):ident $(bs[i]!):ident $(← fresh s!"e{i + 1}") :
          Cylinder.HasMeasurableLeaves $(← fresh s!"r{i + 1}")))
      let diag := #[← `(tactic| rw [$(← k.unfoldInter ns ns'):term] at h)] ++
        (← k.obtainLeaves ns as (← fresh "h₁")) ++ (← k.obtainLeaves ns' bs (← fresh "h₂")) ++
        (← k.gate ns ns' h (← `(tactic| cases h))) ++
        (← k.splitInters ns ns' (fun _ => h) (← `(tactic| simp at h))) ++
        #[← `(tactic| try dsimp only at h), ← `(tactic| cases h), ← `(tactic| exact $leaves)]
      let vars ← ns'.mapM fun x => `(binderIdent| $x:ident)
      return #[← `(tactic| intro c₂ c h₁ h₂ h), ← `(tactic| cases c₂),
        ← `(tactic| case $k.ident:ident $vars* => $diag*),
        ← `(tactic| all_goals nomatch h)]

/-- `flatten_isCountablySpanning` needs some cylinder with measurable leaves: the cylinder of the
shape of a constructor without recursive fields, nullary if possible. -/
def genPiSystem (ctx : Ctx) : CommandElabM (Array Command) := do
  let some c := ctx.ctors.find? (·.fields.isEmpty) <|>
      ctx.ctors.find? (·.fields.all fun f => f.kind == .data || f.kind == .base && f.inhabited)
    | throwError "cylinders: `flatten_isCountablySpanning` needs a constructor without recursive \
        fields whose base fields are `Inhabited`"
  let s₀ ← c.dot (← c.bases.mapM fun _ => `(default))
  let gen ← `({S : Set $ctx.ty | ∃ c : $ctx.cyl, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S})
  return #[
    ← `(theorem Cylinder.flatten_inter_some $ctx.implicits* {c₁ c₂ c : $ctx.cyl}
          (h : Cylinder.inter? c₁ c₂ = some c) :
          Cylinder.flatten c = Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ :=
        Cylinders.flatten_inter_some Cylinder.flatten_inter h),
    ← `(/-- The flattened cylinders with measurable leaves form a π-system. -/
      theorem Cylinder.flatten_isPiSystem $ctx.implicits* $ctx.insts* : IsPiSystem $gen :=
        Cylinders.flatten_isPiSystem Cylinder.flatten_inter
          (fun {_ _ _} => Cylinder.hasMeasurableLeaves_inter)),
    ← `(/-- The flattened cylinders with measurable leaves are countably spanning. -/
      theorem Cylinder.flatten_isCountablySpanning $ctx.implicits* $ctx.insts* :
          IsCountablySpanning $gen :=
        Cylinders.flatten_isCountablySpanning Shape.cylinder_hasMeasurableLeaves
          Shape.cylinder_preimage_shape (Shape.cylinder $s₀) (Shape.cylinder_hasMeasurableLeaves $s₀))]

/-! ## Per-constructor measurability -/

/-- `T.c` as a function of a tuple: constant, raw, uncurried, or a tuple lambda. -/
def Ctx.ctorFn (ctx : Ctx) (c : Ctor) : CommandElabM Term := do
  let tys := c.fields.map ctx.fieldType
  match tys with
  | #[] => `(fun _ : Unit => ($(← ctx.apply c #[]) : $ctx.ty))
  | #[a] => `(($(← ctx.apply c #[]) : $a → $ctx.ty))
  | #[a, b] => `(Function.uncurry ($(← ctx.apply c #[]) : $a → $b → $ctx.ty))
  | _ =>
    let args ← (Array.range tys.size).mapM (proj (← `(p)) · tys.size)
    `(fun (p : $(← tupleType tys)) => $(← ctx.apply c args))

/-- `generateFrom 𝓒 = ‹_›`, countably spanning, and π-system lemmas for the generating family of a
field: cylinders (recursive), points (base) or all measurable sets (data); and for a tuple of
fields, the families of rectangles. -/
def fact : Kind → CommandElabM (Term × Term × Term)
  | .recursive => return (← `(rfl), ← `(Cylinder.flatten_isCountablySpanning), ← `(Cylinder.flatten_isPiSystem))
  | .base => return (← `(Cylinders.points_generateFrom), ← `(Cylinders.points_isCountablySpanning),
      ← `(Cylinders.points_isPiSystem))
  | .data => return (← `(MeasurableSpace.generateFrom_measurableSet),
      ← `(isCountablySpanning_measurableSet), ← `(MeasurableSpace.isPiSystem_measurableSet))

def facts : List Kind → CommandElabM (Term × Term × Term)
  | [] => return (← `(rfl), ← `(rfl), ← `(rfl))
  | [k] => fact k
  | k :: ks => do
    let (g, s, p) ← fact k
    let (g', s', p') ← facts ks
    return (← `(generateFrom_eq_prod $g $g' $s $s'), ← `($(s).prod $s'),
      ← `($(p).prod $p'))

/-- Patterns for a set in the generating family of `c`'s fields `is` and its membership, binding each
field's value (or set, or cylinder) to `ns[i]` and its membership to `hs[i]`. -/
def Ctor.rectPattern (c : Ctor) (ns hs : Array Ident) : List Nat → CommandElabM (Pat × Pat)
  | [] => return (← `(rcasesPat| _), ← `(rcasesPat| _))
  | i :: is => do
    let one ← match c.kind i with
      | .recursive => pure (← `(rcasesPat| _), ← `(rcasesPat| ⟨$(ns[i]!):ident, $(hs[i]!):ident, rfl⟩))
      | .data => pure (← identPat ns[i]!, ← identPat hs[i]!)
      | .base => pure (← `(rcasesPat| _), ← identPat hs[i]!)
    if is.isEmpty then return one
    let (a, m) ← c.rectPattern ns hs is
    return (← `(rcasesPat| _), ← tuplePat #[one.1, one.2, a, m, ← `(rcasesPat| rfl)])

/-- `rfl` at the base fields of `c`, and `ms[i]` at the others. -/
def Ctor.rfls (c : Ctor) (ms : Array Ident) : CommandElabM (Array Term × Array Pat) := do
  let is := Array.range c.fields.size
  return (← is.mapM fun i => if c.kind i == .base then `(rfl) else pure (terms ms)[i]!,
    ← is.mapM fun i => if c.kind i == .base then `(rcasesPat| rfl) else identPat ms[i]!)

/-- `cover.c` is measurable, and covers the range of `T.c`. -/
def genCover (ctx : Ctx) (c : Ctor) : CommandElabM (Array Command) := do
  let as ← c.vars "a"
  let a (i : Nat) : Term := (terms as)[i]!
  let key (i : Nat) : CommandElabM Term := do proj (← `(p)) (pos c.keys i) c.keys.size
  let measurable ← if c.dataOnly then
      `(theorem $(c.cover `measurable) $ctx.implicits* $ctx.insts*
          {S : Set $(c.fields[0]!.type)} (hS : MeasurableSet S) :
          MeasurableSet ($(c.cover) S : Set $ctx.ty) :=
        flatten_measurable ($(ctx.plain "c"):ident := ($(← c.dot #[← `(S)]) : $ctx.cyl)) hS)
    else do
      let leaves ← c.leaves fun i => do
        if c.kind i == .data then `(MeasurableSet.univ) else `(Shape.cylinder_hasMeasurableLeaves $(← key i))
      `(theorem $(c.cover `measurable) $ctx.implicits* $ctx.insts*
          (S : Set $(← tupleType (← c.keys.mapM (shapeFieldType c.fields[·]!)))) :
          MeasurableSet ($(c.cover) S : Set $ctx.ty) :=
        .biUnion (Set.to_countable _) fun p _ => flatten_measurable $leaves)
  let intro ← if c.dataOnly then `(tactic| intro h)
    else `(tactic| (intro h; obtain ⟨p, -, h⟩ := Set.mem_iUnion₂.1 h))
  let ofCover ← c.flattenMem tuplePat (← c.sets.mapM (identPat as[·]!))
    (← c.sets.mapM fun _ => `(rcasesPat| -)) (← `(rcasesPat| rfl))
  let value ← anon (← (Array.range c.fields.size).mapM fun i =>
    if c.kind i == .base then key i else pure (a i))
  let ofValue ← tuplePat #[← tuplePat (← as.mapM identPat), ← `(rcasesPat| rfl)]
  let mem ← c.flattenMem anon (c.sets.map a) (← c.sets.mapM fun i => do
    if c.kind i == .data then `(trivial) else `(Shape.mem_cylinder_shape $(a i))) (← `(rfl))
  let inCover ← if c.dataOnly then pure mem else do
    let key ← if c.keys.isEmpty then `(()) else anon (← c.keys.mapM fun i => do
      if c.kind i == .base then pure (a i) else `($(ctx.T `shape) $(a i)))
    `(Set.mem_iUnion₂.2 ⟨$key, trivial, $mem⟩)
  let range ← `(
    theorem $(c.coverRange) $ctx.implicits* :
        $(c.cover) Set.univ = Set.range $(← ctx.uncurried c `ι) := by
      ext t
      constructor
      · $intro:tactic
        obtain $ofCover:rcasesPat := h
        exact ⟨$value, rfl⟩
      · rintro $ofValue:rcasesPat
        exact $inCover)
  return #[measurable, range]

/-- `T.c` is measurable: the preimage of a `c`-cylinder is the product of its leaves, and the
preimage of any other cylinder is empty. -/
def genCtorMeasurable (ctx : Ctx) (c : Ctor) : CommandElabM (Array Command) := do
  let n := c.fields.size
  let ι ← ctx.uncurried c `ι
  let measurable ← `(theorem $(c.lemma `measurable) $ctx.implicits* $ctx.insts* :
      Measurable $(← ctx.ctorFn c) := $(c.lemma `ι.measurable))
  if n == 0 then
    return #[← `(theorem $(c.lemma `ι.measurable) $ctx.implicits* $ctx.insts* :
      Measurable $ι := measurable_const), measurable]
  let (ns, hs, as, bs, ms) := (← c.fieldVars, ← c.vars "h", ← c.vars "a", ← c.vars "b", ← c.vars "m")
  let leaves ← (Array.range n).mapM fun i => match c.kind i with
    | .base => `(MeasurableSet.singleton $(ns[i]!):ident)
    | .data => pure (terms hs)[i]!
    | .recursive => `(flatten_measurable $(hs[i]!):ident)
  let product ← leaves.pop.foldrM (fun a b => `($(a).prod $b)) leaves.back!
  let (rfls, rflPats) ← c.rfls ms
  let toRect ← c.flattenMem tuplePat (← c.sets.mapM (identPat bs[·]!)) (← c.sets.mapM (identPat ms[·]!))
    (← `(rcasesPat| h))
  let ofRect ← c.flattenMem anon (c.sets.map ((terms as)[·]!)) (c.sets.map ((terms ms)[·]!)) (← `(rfl))
  let arm ← inductionAlt c ns <| (← c.obtainLeaves ns hs (← fresh "hS")) ++ #[
    ← `(tactic| convert $product:term using 1),
    ← `(tactic| ext $(← tuplePat (← as.mapM identPat)):rcasesPat),
    ← `(tactic| constructor),
    ← `(tactic|
      · rintro $toRect:rcasesPat
        cases h
        exact $(← anon rfls)),
    ← `(tactic|
      · rintro $(← tuplePat rflPats):rcasesPat
        exact $ofRect)]
  let others ← if ctx.ctors.size == 1 then pure #[] else pure #[← `(Parser.Tactic.inductionAlt|
    | _ => exact Cylinders.measurableSet_of_forall_notMem fun t h =>
        Shape.noConfusion (Cylinder.shape_of_mem_flatten (Set.mem_preimage.1 h)))]
  return #[← `(
    theorem $(c.lemma `ι.measurable) $ctx.implicits* $ctx.insts* : Measurable $ι := by
      apply measurable_generateFrom
      rintro _ ⟨s, hS, rfl⟩
      cases s with $arm:inductionAlt $others:inductionAlt*), measurable]

/-- `T.c` is a measurable embedding: injective and measurable, and the image of a generating set
of the product of its fields is measurable. -/
def genEmbedding (ctx : Ctx) (c : Ctor) : CommandElabM Command := do
  let n := c.fields.size
  let cov ← if c.dataOnly then `($(c.cover `measurable) $ctx.named:namedArgument* MeasurableSet.univ)
    else `($(c.cover `measurable) $ctx.named:namedArgument* Set.univ)
  if n == 0 then
    return ← `(theorem $(c.lemma `measurableEmbedding) $ctx.implicits* $ctx.insts* :
        MeasurableEmbedding $(← ctx.ctorFn c) :=
      .of_measurable_inverse (g := fun _ => ()) measurable_const
        (by have hS := $cov; rw [$(c.coverRange):ident] at hS; exact hS)
        measurable_const fun _ => rfl)
  let (ns, hs, as, ms) := (← c.fieldVars, ← c.vars "h", ← c.vars "a", ← c.vars "m")
  let (g, _, pi) ← facts (c.fields.toList.map (·.kind))
  let (setPat, memPat) ← c.rectPattern ns hs (List.range n)
  let points ← c.bases.flatMapM fun i => do return #[
    ← `(tactic| rcases $(hs[i]!):ident with rfl | ⟨$(ns[i]!):ident, rfl⟩),
    ← `(tactic| · simp only [Set.prod_empty, Set.empty_prod, Set.image_empty, MeasurableSet.empty])]
  let (rfls, rflPats) ← c.rfls ms
  let mem ← c.flattenMem anon (c.sets.map ((terms as)[·]!)) (c.sets.map ((terms ms)[·]!)) (← `(rfl))
  let memPat' ← c.flattenMem tuplePat (← c.sets.mapM (identPat as[·]!)) (← c.sets.mapM (identPat ms[·]!))
    (← `(rcasesPat| rfl))
  let value ← anon (terms ((Array.range n).map fun i => if c.kind i == .base then ns[i]! else as[i]!))
  let ofRect := #[← `(tactic| ext t), ← `(tactic| constructor),
    ← `(tactic|
      · rintro $(← tuplePat #[← tuplePat (← as.mapM identPat), ← tuplePat rflPats, ← `(rcasesPat| rfl)]):rcasesPat
        exact $mem),
    ← `(tactic|
      · rintro $memPat':rcasesPat
        exact ⟨$value, $(← anon rfls), rfl⟩)]
  let basic := #[← `(tactic| rintro $setPat:rcasesPat $memPat:rcasesPat)] ++ points ++
    #[← `(tactic| convert flatten_measurable ($(ctx.plain "c"):ident := ($(← c.dot (terms ns)) : $ctx.cyl))
        $(← c.leaves (pure (terms hs)[·]!)) using 1)] ++ ofRect
  `(theorem $(c.lemma `measurableEmbedding) $ctx.implicits* $ctx.insts* :
      MeasurableEmbedding $(← ctx.ctorFn c) :=
    measurableEmbedding_of_piSystem₁ (f := $(← ctx.uncurried c `ι)) $(c.lemma `ι.inj) $(c.lemma `ι.measurable)
      (h_gen := $(g).symm) (h_pi := $pi) (h_basic := by $[$basic]*)
      (h_cov_meas := $cov) (h_cov_range := $(c.coverRange)))

/-- The projection `T.c.π` is measurable. -/
def genProjMeasurable (ctx : Ctx) (c : Ctor) : CommandElabM (Array Command) := do
  if c.fields.isEmpty then return #[]
  let holes ← anon (Array.replicate c.fields.size (← `(_)))
  return #[← `(theorem $(c.lemma `π.measurable) $ctx.implicits* $ctx.insts* :
      Measurable ($(← ctx.uncurried c `π) : $ctx.ty → Option $(← ctx.dom c)) :=
    Cylinders.proj_measurable $(c.lemma `measurableEmbedding)
      (by
        ext t; constructor
        · rintro hS ⟨_, rfl⟩; cases hS
        · intro hS; cases t <;> first | rfl | exact absurd ⟨$holes, rfl⟩ hS)
      (fun S => by
        ext t; constructor
        · rintro ⟨_, hS, h⟩; cases t <;> cases h; exact ⟨_, hS, rfl⟩
        · rintro ⟨_, hS, rfl⟩; exact ⟨_, hS, rfl⟩))]

def genMeasurability (ctx : Ctx) (c : Ctor) : CommandElabM (Array Command) :=
  return (← genCover ctx c) ++ (← genCtorMeasurable ctx c) ++ #[← genEmbedding ctx c] ++
    (← genProjMeasurable ctx c)

/-! ## `casesOn` decomposition and `measurable_rec` -/

/-- The arm of `T.casesOn` that calls `f` on `c`'s fields as a tuple, after `b` if given. -/
def Ctor.recArm (c : Ctor) (f : Ident) (b : Option Term := none) : CommandElabM Term := do
  let xs ← c.vars "x"
  let args := b.toArray ++ terms xs
  match b, xs.size with
  | none, 0 => `($f ())
  | none, 1 => return f
  | some b, 0 => `($f ($b, ()))
  | _, _ =>
    let tuple ← if h : args.size = 1 then pure args[0] else `(($(args[0]!), $(args[1:].toArray),*))
    `(fun $xs* => $f $tuple)

def genRec (ctx : Ctx) : CommandElabM (Array Command) := do
  let (fs, cs, hs) := (ctx.perCtor "f", ctx.perCtor "c", ctx.perCtor "h")
  let hName (c : Ctor) : Ident := (hs.find? (·.1.name == c.name)).get!.2
  let measurableArg (c : Ctor) := !c.fields.all (·.kind == .base)
  let casesOn (α : Ident) (scrut : Term) (arms : Array Term) : CommandElabM Term :=
    `($(ctx.T `casesOn) (motive := fun _ => $α) $scrut $arms*)
  let hBinders (fs : Array (Ctor × Ident)) : CommandElabM (Array Binder) :=
    fs.mapM fun (c, f) => `(bracketedBinder| ($(hName c) : Measurable $f))
  let fNames := fs.map (·.2)
  -- a value lies in the cell of its constructor, and the cells lie in the preimage
  let wit (c : Ctor) : CommandElabM Term := do match c.fields.size with
    | 0 => `(())
    | 1 => `(_)
    | n => anon (Array.replicate n (← `(_)))
  let inCell (wit : Ctor → CommandElabM Term) : CommandElabM (Array Tactic) :=
    ctx.ctors.mapIdxM fun j c => do `(tactic| · exact ⟨$(quote j), $(← wit c), hx, rfl⟩)
  let ofCell ← `(tactic|
    · rintro ⟨i, hi⟩; fin_cases i <;>
        · obtain ⟨q, hq, hx⟩ := hi; cases hx; exact hq)
  let plain ← do
    let α := ctx.greek "α"
    let fn ← `(fun x : $ctx.ty => $(← casesOn α (← `(x)) (← fs.mapM fun (c, f) => c.recArm f)))
    let fBinders ← fs.mapM fun (c, f) => do `(bracketedBinder| ($f : $(← ctx.dom c) → $α))
    let hBinders ← hBinders (fs.filter (measurableArg ·.1))
    let cells ← inCell wit
    let images ← ctx.ctors.mapM fun c => do
      let h ← if measurableArg c then `($(hName c) hS) else `(MeasurableSet.of_discrete)
      `(tactic| · exact $(c.lemma `measurableEmbedding.measurableSet_image') $h)
    pure #[
      ← `(
        theorem casesOn_preimage_decomp $ctx.implicits* {$α : Type _} (S : Set $α) $fBinders* :
            $fn ⁻¹' S = ⋃ i, decompCell S $fNames* i := by
          ext x
          simp only [Set.mem_preimage, Set.mem_iUnion, decompCell]
          constructor
          · intro hx
            cases x
            $[$cells]*
          $ofCell:tactic),
      ← `(
        theorem measurable_rec $ctx.implicits* $ctx.insts* {$α : Type _} [MeasurableSpace $α]
            $(fBinders ++ hBinders)* :
            Measurable $fn := by
          intro S hS
          rw [casesOn_preimage_decomp]
          refine .iUnion fun i => ?_
          fin_cases i
          $[$images]*)]
  let param ← do
    let (α, β) := ctx.paramVars
    let fn (fs : Array (Ctor × Ident)) : CommandElabM Term := do
      `(fun p : $ctx.ty × $β => $(← casesOn α (← `(p.1)) (← fs.mapM fun (c, f) => do c.recArm f (← `(p.2)))))
    let fBinders (fs : Array (Ctor × Ident)) : CommandElabM (Array Binder) :=
      fs.mapM fun (c, f) => do `(bracketedBinder| ($f : $β × $(← ctx.dom c) → $α))
    let cells ← inCell fun c => do `((y, $(← wit c)))
    let (vars, decompBinders, recBinders) := (← typeVars α β, ← fBinders fs, (← fBinders cs) ++ (← hBinders cs))
    let images ← ctx.ctors.mapM fun c => `(tactic|
      · exact (($(c.lemma `measurableEmbedding).prodMap (.id (α := $β))).comp
          MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' ($(hName c) hS))
    pure #[
      ← `(
        theorem casesOn_preimage_decomp_param $ctx.implicits* $vars (S : Set $α) $decompBinders* :
            $(← fn fs) ⁻¹' S = ⋃ i, decompCell_param S $fNames* i := by
          ext ⟨x, y⟩
          simp only [Set.mem_preimage, Set.mem_iUnion, decompCell_param]
          constructor
          · intro hx
            cases x
            $[$cells]*
          $ofCell:tactic),
      ← `(
        theorem measurable_rec_param $ctx.implicits* $ctx.insts*
            {$α : Type _} [MeasurableSpace $α] {$β : Type _} [MeasurableSpace $β]
            $recBinders* :
            Measurable $(← fn cs) := by
          intro S hS
          rw [casesOn_preimage_decomp_param]
          refine .iUnion fun i => ?_
          fin_cases i
          $[$images]*)]
  return plain ++ param

/-! ## Measurable singletons -/

/-- `singletonCyl` lemmas and the `MeasurableSingletonClass` instance, if every data field has
measurable singletons (given measurable singletons in the parameters). -/
def genSingletons (ctx : Ctx) : CommandElabM (Array Command) := do
  unless ctx.ctors.all (·.fields.all fun f => f.kind != .data || f.singletons) do return #[]
  let mscs ← ctx.spec.params.mapM fun p => `(bracketedBinder| [MeasurableSingletonClass $p])
  let induct (body : Ctor → Array Ident → Array Ident → CommandElabM Tactic) := do
    let alts ← ctx.ctors.mapM fun c => do
      let ns ← c.fieldVars
      let ihs ← c.recs.mapM fun i => fresh s!"ih{i + 1}"
      inductionAlt c (ns ++ ihs) #[← body c ns ihs]
    `(tactic| induction x with $alts:inductionAlt*)
  return #[
    ← `(theorem singletonCyl_flatten $ctx.implicits* (x : $ctx.ty) :
          (singletonCyl x).flatten = {x} := by
        $(← induct fun _ _ ihs => do
          simpOnly (#[← `(singletonCyl_eqs), ← `(Cylinder.flatten_eqs), ← `(Set.singleton_prod_singleton),
            ← `(Set.image_singleton)] ++ terms ihs)):tactic),
    ← `(theorem singletonCyl_hasMeasurableLeaves $ctx.implicits* $ctx.insts* $mscs* (x : $ctx.ty) :
          (singletonCyl x).HasMeasurableLeaves := by
        $(← induct fun c ns ihs => do
          `(tactic| exact $(← c.leaves fun i =>
            if c.kind i == .data then `(MeasurableSet.singleton $(ns[i]!):ident) else return ihs[pos c.recs i]!))):tactic),
    ← `(instance instMeasurableSingletonClass $ctx.implicits* $ctx.insts* $mscs* :
          MeasurableSingletonClass $ctx.ty where
        measurableSet_singleton :=
          Cylinders.measurableSet_singleton rfl singletonCyl_flatten singletonCyl_hasMeasurableLeaves)]

/-! ## Structural recursion -/

/-- `Measurable` of a function of the fields `tys`: the function itself for one field,
`Function.uncurry` for two, a tuple lambda for more. -/
def measurableOf (fn : Ident) (tys : Array Term) : CommandElabM Term := do
  match tys.size with
  | 0 | 1 => `(Measurable $fn)
  | 2 => `(Measurable (Function.uncurry $fn))
  | n => `(Measurable (fun (q : $(← tupleType tys)) =>
      $(Syntax.mkApp fn (← (Array.range n).mapM (proj (← `(q)) · n)))))

/-- Measurability of component `k` of an `n`-tuple, or `none` for the identity. -/
def projMeas (k n : Nat) : CommandElabM (Option Term) := do
  let mut ops := List.replicate k (← `(measurable_snd))
  if k + 1 < n then ops := ops ++ [← `(measurable_fst)]
  ops.foldlM (init := none) fun t op => match t with
    | none => return some op
    | some t => return some (← `($(op).comp $t))

/-- `m ∘ base`, or `base` for the identity. -/
def compose (m : Option Term) (base : Term) : CommandElabM Term :=
  match m with
  | none => return base
  | some m => `($(m).comp $base)

/-- `measurable_struct_rec` (`param := none`), or the `β`-threaded `measurable_struct_rec_param`
(`param := some shift`, with the `shifting` constructors shifting the parameter if `shift`): a
function given by structural recursion is measurable if its arms are. -/
def genStructRec (ctx : Ctx) (param : Option Bool) : CommandElabM Command := do
  let α := ctx.greek "α" [mkIdent `β]
  let β := ctx.greek "β" [α]
  let f := ctx.plain (if param.isSome then "g" else "f")
  let plain (pre : String) (c : Ctor) : Ident := ctx.plain s!"{pre}_{c.raw}"
  let (arm, eqn, hyp, shift, hshift) := (plain "c", plain "eq", plain "h", plain "t", plain "ht")
  let shifts (c : Ctor) := param == some true && ctx.shifting.contains c.short
  let hasHyp (c : Ctor) := param.isSome || c.fields.any (·.kind != .base)
  -- the threaded parameter comes first
  let b ← fresh "b"
  let (pre, bs) := if param.isSome then (#[(β : Term)], #[b]) else (#[], #[])
  let armTys (c : Ctor) : Array Term := pre ++ c.fields.map fun fd => if fd.kind == .recursive then (α : Term) else fd.type
  let arrows (tys : Array Term) : CommandElabM Term := tys.foldrM (fun a b => `($a → $b)) α
  let mut binders := #[← `(bracketedBinder| {$f : $(← arrows (pre.push ctx.ty))})]
  for c in ctx.ctors do
    binders := binders.push (← `(bracketedBinder| {$(arm c) : $(← arrows (armTys c))}))
  for c in ctx.ctors.filter shifts do
    binders := binders.push (← `(bracketedBinder| {$(shift c) : $β → $β}))
  for c in ctx.ctors do
    let xs ← c.vars "x"
    let b' ← if shifts c then `($(shift c) $b) else pure (b : Term)
    let args := (terms xs).mapIdx fun i x =>
      if c.kind i != .recursive then x else Syntax.mkApp f ((if param.isSome then #[b'] else #[]) ++ #[x])
    let eq ← `($(Syntax.mkApp f (terms bs ++ #[← ctx.apply c (terms xs)])) =
      $(Syntax.mkApp (arm c) (terms bs ++ args)))
    let vars := bs ++ xs
    binders := binders.push (← `(bracketedBinder| ($(eqn c) : $(← if vars.isEmpty then pure eq else `(∀ $vars*, $eq)))))
  for c in ctx.ctors.filter hasHyp do
    binders := binders.push (← `(bracketedBinder| ($(hyp c) : $(← measurableOf (arm c) (armTys c)))))
  for c in ctx.ctors.filter shifts do
    binders := binders.push (← `(bracketedBinder| ($(hshift c) : Measurable $(shift c))))
  -- one cell per shape, on which the function is the arm applied to the fields
  let alts ← ctx.ctors.mapM fun c => do
    let n := c.fields.size
    let ss ← c.fieldVars "s"
    let ihs ← c.recs.mapM fun i => fresh s!"ih{i + 1}"
    let vs ← c.vars "b"
    let value ← if n == 0 then `(()) else
      anon (terms ((Array.range n).map fun i => if c.kind i == .base then ss[i]! else vs[i]!))
    let ofShape ← c.flattenMem tuplePat (← c.sets.mapM (identPat vs[·]!))
      (Array.replicate c.sets.size (← `(rcasesPat| _))) (← `(rcasesPat| rfl))
    let inRange ← `(fun p hp => by
      rw [← Set.mem_singleton_iff, ← Set.mem_preimage, ← Shape.cylinder_preimage_shape] at hp
      obtain $ofShape:rcasesPat := hp
      exact ⟨$value, rfl⟩)
    let q ← `(q)
    let field (i : Nat) (fields : Term) : CommandElabM Term := do
      let x ← proj fields i n
      if c.kind i != .recursive then return x
      if param.isNone then `($f $x)
      else if shifts c then `($f ($(shift c) q.1) $x)
      else `($f q.1 $x)
    let G ← if param.isSome then
        `(fun q => $(Syntax.mkApp (arm c) (#[← `(q.1)] ++ (← (Array.range n).mapM (field · (← `(q.2)))))))
      else `(fun q => $(Syntax.mkApp (arm c) (← (Array.range n).mapM (field · q))))
    let eqns ← if param.isSome then
        `(fun b q _ => $(Syntax.mkApp (eqn c) (#[← `(b)] ++ (← (Array.range n).mapM (proj q · n)))))
      else `(fun q _ => $(Syntax.mkApp (eqn c) (← (Array.range n).mapM (proj q · n))))
    -- `G` restricted to the cell is measurable: the arm composed with the fields
    let coe ← `(measurable_subtype_coe)
    let fieldMeasurable (i : Nat) : CommandElabM Term := do
      let pm ← projMeas i n
      if c.kind i != .recursive then
        return ← compose pm (← if param.isSome then `(measurable_snd.comp $coe) else pure coe)
      let inj ← proj (← `(($(mkIdent (`Shape ++ c.short ++ `inj)) hq))) (pos c.keys i) c.keys.size
      let into ← if param.isNone then compose pm (← `(measurable_id))
        else `($(← if shifts c then `($(hshift c).comp measurable_fst) else `(measurable_fst)).prodMk
          $(← compose pm (← `(measurable_snd))))
      `(Cylinders.restrict_comp (Cylinders.restrict_of_cell @$(ihs[pos c.recs i]!):ident) $into
        (fun q hq => $inj))
    let mut ms := #[]
    if param.isSome then ms := ms.push (← `(measurable_fst.comp $coe))
    ms := ms ++ (← (Array.range n).mapM fieldMeasurable)
    let hG ← if hasHyp c then
        `($(hyp c).comp $(← ms.pop.foldrM (fun m acc => `($(m).prodMk $acc)) ms.back!))
      else `(measurable_of_countable _)
    let cell ← if param.isSome then `(Cylinders.cell_param) else `(Cylinders.cell)
    inductionAlt c (c.keys.map (ss[·]!) ++ ihs) #[← `(tactic| intro U hU), ← `(tactic|
      exact $cell (ι := $(← ctx.uncurried c `ι)) $(c.lemma `measurableEmbedding) (hC _) $inRange
        (G := $G) $eqns $hG hU)]
  let name := mkIdent <| match param with
    | none => `measurable_struct_rec
    | some false => `measurable_struct_rec_param
    | some true => `measurable_struct_rec_param_shift
  let paramBinders ← if param.isSome then
      pure #[← `(bracketedBinder| {$β : Type _}), ← `(bracketedBinder| [MeasurableSpace $β])]
    else pure #[]
  let ofCells ← if param.isSome then `(StructRec.measurable_of_cells_param $(ctx.T `shape))
    else `(StructRec.measurable_of_cells $(ctx.T `shape))
  `(theorem $name $ctx.implicits* {$α : Type _} $ctx.insts* [MeasurableSpace $α]
      $(paramBinders ++ binders)* :
      Measurable $(← if param.isSome then `(Function.uncurry $f) else pure f) := by
    apply $ofCells:term
    intro s
    have hC : ∀ s : Shape, MeasurableSet ($(ctx.T `shape) $ctx.named:namedArgument* ⁻¹' {s}) := fun s => by
      rw [← Shape.cylinder_preimage_shape]; exact flatten_measurable (Shape.cylinder_hasMeasurableLeaves s)
    induction s with $alts:inductionAlt*)

/-! ## Assembly -/

/-- Attributes on theorems wait for their proofs, so they come last, when the proofs have been
elaborated in parallel. -/
def genAttributes (ctx : Ctx) : CommandElabM (Array Command) := do
  let cs := ctx.ctors
  -- `fun_prop` does not accept the `casesOn` of a single-constructor type
  let funProp := cs.flatMap (fun c => #[c.lemma `measurable] ++
      if c.fields.isEmpty then #[] else #[c.lemma `π.measurable]) ++
    if cs.size > 1 then #[mkIdent `measurable_rec, mkIdent `measurable_rec_param] else #[]
  return #[
    ← `(attribute [fun_prop] $funProp*),
    ← `(attribute [measurability] $(cs.map (·.cover `measurable))*),
    ← `(attribute [aesop safe apply (rule_sets := [Measurable])] Shape.cylinder_hasMeasurableLeaves),
    ← `(attribute [simp, cylinder_simp] Cylinder.flatten_eqs $(ctx.T `shape_eqs):ident Cylinder.shape_eqs
      Shape.cylinder_eqs),
    ← `(attribute [cylinder_simp] $(cs.map (·.cover))*),
    ← `(attribute [simp] singletonCyl_eqs Shape.cylinder_preimage_shape)]

def genDefs (ctx : Ctx) : CommandElabM (Array Command) := do
  let recursive := ctx.ctors.any (·.fields.any (·.kind == .recursive))
  let variants := if !recursive then #[] else
    #[none, some false] ++ if ctx.shifting.isEmpty then #[] else #[some true]
  let structRec ← variants.mapM (genStructRec ctx)
  let cmds :=
    (← ctx.ctors.mapM (genInj ctx)) ++
    #[← genCylinder ctx, ← genShape ctx] ++ (← genFlatten ctx) ++
    #[← genHasMeasurableLeaves ctx, ← genInstance ctx] ++
    (← genShapeOf ctx true) ++ (← genShapeOf ctx false) ++ (← genShapeCylinder ctx) ++
    #[← genInter ctx] ++ (← ctx.ctors.mapM (genCoverDef ctx)) ++
    (← genDecompCell ctx) ++ (← genSingletonCyl ctx) ++ (← genBasics ctx) ++
    #[← genShapeOfMem ctx] ++ (← genShapeLemmas ctx) ++
    (← genFlattenInter ctx) ++ (← genHasMeasurableLeavesInter ctx) ++ (← genPiSystem ctx) ++
    (← ctx.ctors.flatMapM (genMeasurability ctx)) ++ (← genRec ctx) ++ (← genSingletons ctx) ++
    structRec ++ (← genAttributes ctx)
  return cmds.map (⟨exposeNames ·⟩)

/-! ## Commands -/

def classifyIdent (id : Ident) : CommandElabM Spec :=
  liftTermElabM do classify (← realizeGlobalConstNoOverloadWithInfo id)

/-- Elaborates generated code, without the section variables (which could capture its names), and
without linters (which would be wasted work). -/
def elabGenerated (cmd : Command) : CommandElabM Unit :=
  withScope (fun sc => { sc with
      varDecls := #[], varUIds := #[], opts := sc.opts.setBool `linter.all false }) <|
    elabCommand cmd

elab "#cylinder_classify " T:ident : command => do
  let spec ← classifyIdent T
  let field (f : Field) : CommandElabM String :=
    return s!"({f.name} : {← liftCoreM (PrettyPrinter.ppTerm f.type)}) {f.kind}"
  let lines ← spec.ctors.mapM fun c => do
    let fields ← c.fields.toList.mapM field
    return s!"{c.short}: " ++ if fields.isEmpty then "nullary" else ", ".intercalate fields
  logInfo ("\n".intercalate lines.toList)

syntax "cylinder_defs " ident (&" shifting" (ppSpace ident)+)? : command
syntax "cylinder_defs? " ident (&" shifting" (ppSpace ident)+)? : command

def cylinderDefs (T : Ident) (shifting : Array Ident) (log : Bool) : CommandElabM Unit := do
  let ctx ← Ctx.make (← classifyIdent T) (shifting.toList.map (·.getId))
  for b in ctx.shifting do
    let some c := ctx.ctors.find? (·.short == b)
      | throwError "cylinders: `{b}` is not a constructor"
    unless c.fields.any (·.kind == .recursive) do
      throwError "cylinders: `{b}` has no recursive fields to shift"
  let cmds ← genDefs ctx
  if log then
    let shown ← cmds.mapM fun cmd => liftCoreM (PrettyPrinter.ppCommand ⟨eraseScopes cmd⟩)
    logInfo <| .joinSep (shown.toList.map toMessageData) "\n\n"
  for cmd in cmds do
    elabGenerated cmd
    if (← get).messages.hasErrors then return

end

elab_rules : command
  | `(cylinder_defs $T $[shifting $cs*]?) => cylinderDefs T (cs.getD #[]) (log := false)
  | `(cylinder_defs? $T $[shifting $cs*]?) => cylinderDefs T (cs.getD #[]) (log := true)

end Metrology.CylinderGen
