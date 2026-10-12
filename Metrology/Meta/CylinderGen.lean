module

public meta import Lean

@[expose] public section

open Lean Elab Command Term Meta

/-!
# Cylinder generator

`cylinder_defs T` generates the CoreMeasures cylinder σ-algebra on an inductive `T`
(`STAMPING.md`, §2 items 1–20), as Lean source elaborated in place: `ι.inj`, `Cylinder`, `Shape`,
`flatten`, `HasMeasurableLeaves`, the `MeasurableSpace` instance, the shape maps, `inter?`, covers,
`decompCell(_param)`, `singletonCyl`, and the lemmas up to `flatten_isPiSystem` and
`flatten_isCountablySpanning`.

`cylinder_defs? T` also logs the source. `#cylinder_classify T` shows how each field is classified:
recursive (of type `T`), base (countable with measurable singletons: kept in `Shape`), or data
(a `Set` in `Cylinder`, dropped from `Shape`).
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
  /-- Lean source with full names. -/
  type : String
  deriving Inhabited

structure Ctor where
  name : Name
  /-- Last name component, escaped where needed. -/
  short : String
  raw : String
  fields : Array Field
  deriving Inhabited

structure Spec where
  name : Name
  params : Array String
  ctors : Array Ctor
  deriving Inhabited

/-- Declarations the generator defines, in the current namespace or under `Cylinder`/`Shape`. -/
def generated : List String :=
  ["Cylinder", "Shape", "cover", "singletonCyl", "decompCell", "decompCell_param", "ι", "π",
   "measurable", "measurableEmbedding", "casesOn_preimage_decomp", "casesOn_preimage_decomp_param",
   "measurable_rec", "measurable_rec_param", "singletonCyl_flatten",
   "singletonCyl_hasMeasurableLeaves", "instMeasurableSingletonClass", "measurable_struct_rec",
   "measurable_struct_rec_param", "measurable_struct_rec_param_shift",
   "flatten_measurable", "flatten", "flatten_eqs", "shape_eqs", "cylinder_eqs", "singletonCyl_eqs", "HasMeasurableLeaves", "shape", "inter?", "cylinder",
   "cylinder_hasMeasurableLeaves", "cylinder_preimage_shape", "mem_cylinder_shape", "shape_of_mem_flatten",
   "flatten_disjoint_of_shape_ne", "flatten_inter", "flatten_inter_some",
   "hasMeasurableLeaves_inter", "flatten_isPiSystem", "flatten_isCountablySpanning"]

/-- Global names the generated code refers to (first components). -/
def globals : List String :=
  ["Set", "MeasurableSet", "MeasurableSpace", "Unit", "Function", "Option", "some", "none",
   "Cylinders", "IsPiSystem", "IsCountablySpanning", "Fin", "rfl", "default", "reduceCtorEq", "Bool",
   "Measurable", "MeasurableEmbedding", "Prod", "measurable_const", "measurable_generateFrom",
   "measurableEmbedding_of_piSystem₁", "generateFrom_eq_prod", "isCountablySpanning_measurableSet",
   "MeasurableEquiv", "fin_cases", "MeasurableSingletonClass", "StructRec",
   "measurable_fst", "measurable_snd", "measurable_id", "measurable_subtype_coe",
   "measurable_of_countable",
   "Type", "Prop", "Sort"]

def hasInstance (cls : Name) (args : Array (Option Expr)) : MetaM Bool := do
  try return (← synthInstance? (← mkAppOptM cls args)).isSome catch _ => return false

def classifyField (T : Name) (ty : Expr) : MetaM Kind := do
  if ty.getAppFn.isConstOf T then return .recursive
  if (ty.find? (·.isConstOf T)).isSome then
    throwError "cylinders: field type {ty} contains `{T}` in an unsupported position"
  unless ← hasInstance `MeasurableSpace #[ty] do
    throwError "cylinders: field type {ty} has no `MeasurableSpace` instance"
  if (← hasInstance `Countable #[ty]) && (← hasInstance `MeasurableSingletonClass #[ty, none]) then
    return .base
  return .data

/-- `ty` as Lean source. The generator works on source text, so the text is checked to
elaborate back to `ty`. -/
def typeSource (ty : Expr) : MetaM String := do
  let opts := fun o : Options => o |>.setBool `pp.fullNames true |>.setBool `pp.funBinderTypes true
    |>.setBool `pp.numericTypes true |>.setBool `pp.coercions.types true
  let src := (← withOptions opts (ppExpr ty)).pretty 100000
  let msgs := (← getThe Core.State).messages
  modifyThe Core.State ({ · with messages := {} })
  let ok ← try
      let .ok stx := Parser.runParserCategory (← getEnv) `term src | pure false
      Term.TermElabM.run' <| Term.withoutErrToSorry do
        let ty' ← Term.elabType stx
        Term.synthesizeSyntheticMVarsNoPostponing
        isDefEq ty ty'
    catch _ => pure false
  let ok := ok && !(← getThe Core.State).messages.hasErrors
  modifyThe Core.State ({ · with messages := msgs })
  unless ok do
    throwError "cylinders: cannot reproduce field type {ty} as source (printed as `{src}`)"
  return src

/-- The identifiers in printed source, including the parts of dotted names. -/
def idents (s : String) : List String :=
  let words := (s.map fun c => if isIdRest c || c == '.' then c else ' ').splitOn " "
  words ++ words.flatMap (·.splitOn ".")

def classify (T : Name) : MetaM Spec := do
  let info ← getConstInfoInduct T
  unless info.all.length == 1 do throwError "cylinders: mutual inductive blocks are not supported yet"
  unless info.numNested == 0 do throwError "cylinders: nested inductives are not supported"
  unless info.numIndices == 0 do throwError "cylinders: indexed families are not supported"
  if ← forallTelescope info.type fun _ ty => return ty.isProp then
    throwError "cylinders: `{T}` is a `Prop`"
  forallBoundedTelescope info.type info.numParams fun params _ => do
  let esc (n : Name) := do
    return if ((Parser.getTokenTable (← getEnv)).find? n.toString).isSome then s!"«{n}»" else n.toString
  let names ← params.mapM fun p => do esc (← p.fvarId!.getUserName)
  for p in params, n in names do
    let ty ← whnf (← inferType p)
    unless ty.isSort && ty.sortLevel!.dec.isSome do
      throwError "cylinders: parameter {p} must be a `Type _`, got {ty}"
    if (← p.fvarId!.getUserName).hasMacroScopes then
      throwError "cylinders: parameters must be named"
    unless (← p.fvarId!.getBinderInfo).isExplicit do
      throwError "cylinders: parameter `{n}` must be explicit"
    if (globals ++ generated ++ T.components.map toString).contains n then
      throwError "cylinders: parameter name `{n}` clashes with a name used by the generated code"
  let insts := params.map fun p => (`inst, BinderInfo.instImplicit, fun _ => mkAppM `MeasurableSpace #[p])
  withLocalDecls insts fun _ => do
  -- Field types are printed without the fields in scope, so that a field named like a
  -- parameter does not make the parameter print as inaccessible.
  let lctx ← getLCtx
  let linsts ← getLocalInstances
  let ctors ← info.ctors.toArray.mapM fun c => do
    let raw := c.getString!
    let short ← esc (.mkSimple raw)
    if (globals ++ generated ++ [s!"instMeasurableSpace{T.getString!}"]).contains raw then
      throwError "cylinders: constructor name `{raw}` clashes with a name used by the generated code"
    forallTelescope (← instantiateForall (← getConstInfo c).type params) fun xs _ => do
      let fields ← xs.mapIdxM fun i x => do
        let d ← x.fvarId!.getDecl
        let d := d.setType d.type.cleanupAnnotations
        unless d.binderInfo.isExplicit do
          throwError "cylinders: constructor `{c}` has a non-explicit field `{d.userName}`; \
            only explicit fields are supported"
        if xs[:i].any (d.type.containsFVar ·.fvarId!) then
          throwError "cylinders: dependent field type {d.type} is not supported"
        let type ← withLCtx lctx linsts (typeSource d.type)
        if let some g := generated.find? (idents type).contains then
          throwError "cylinders: field type {d.type} mentions `{g}`, which the generated code defines"
        let mscs := params.map fun p => (`inst, BinderInfo.instImplicit, fun _ =>
          mkAppOptM `MeasurableSingletonClass #[some p, none])
        return { name := d.userName, kind := ← classifyField T d.type, type,
                 inhabited := ← hasInstance `Inhabited #[d.type]
                 singletons := ← withLocalDecls mscs fun _ =>
                   hasInstance `MeasurableSingletonClass #[d.type, none] : Field }
      return { name := c, short, raw, fields }
  for c in ctors do
    if ctors.any (·.raw == c.raw ++ "_univ_eq_range") then
      throwError "cylinders: constructors `{c.raw}` and `{c.raw}_univ_eq_range` would both define \
        `cover.{c.raw}_univ_eq_range`"
  return { name := T, params := names, ctors }

/-! ## Source generation -/

def paren (s : String) : String := if s.contains ' ' then s!"({s})" else s

def app (f : String) (args : Array String) : String := " ".intercalate (f :: args.toList)

/-- `⟨x, y, …⟩`, or just `x` for one item. -/
def anon (xs : Array String) : String := if xs.size == 1 then xs[0]! else "⟨" ++ ", ".intercalate xs.toList ++ "⟩"

/-- `A × B × …`, or `Unit`. -/
def tuple (tys : Array String) : String :=
  if tys.isEmpty then "Unit" else " × ".intercalate (tys.map paren).toList

/-- Component `k` of a right-nested `n`-tuple `p`: `p.1`, `p.2.1`, …, `p.2.….2`. -/
def proj (p : String) (k n : Nat) : String :=
  if n ≤ 1 then p
  else p ++ String.join (List.replicate k ".2") ++ (if k + 1 == n then "" else ".1")

structure Ctx where
  spec : Spec
  /-- Constructors whose recursive fields are under a binder (`cylinder_defs T shifting c …`). -/
  binders : List String := []
  /-- Names that a field's own name may not take as a binder: it would capture them. -/
  avoidOwn : List String
  /-- Names generated locals avoid: also constructor names, which patterns would read as
  constructors. -/
  avoid : List String

def Ctx.ofSpec (spec : Spec) : Ctx :=
  let types := spec.ctors.toList.flatMap fun c => c.fields.toList.map (·.type)
  let avoidOwn := spec.params.toList ++ globals ++ generated ++ (spec.name.toString :: types).flatMap idents
  { spec, avoidOwn, avoid := avoidOwn ++ spec.ctors.toList.map (·.short) }

def Ctx.v (ctx : Ctx) (n : String) (taken : List String := []) : String := Id.run do
  let mut n := n
  while ctx.avoid.contains n || taken.contains n do n := n ++ "'"
  return n

/-- The constructors with their `f_<ctor>` binders for `decompCell(_param)`, pairwise distinct. -/
def Ctx.withF (ctx : Ctx) : List (Ctor × String) :=
  ctx.spec.ctors.toList.zip <| ctx.spec.ctors.toList.foldl (init := []) fun acc c =>
    acc ++ [ctx.v (Name.mkSimple s!"f_{c.raw}").toString acc]

def Ctx.T (ctx : Ctx) : String := ctx.spec.name.toString

/-- `@T.c rT`: with `@`, fields with default values are not filled in when partially applied. -/
def Ctx.ctor (ctx : Ctx) (c : Ctor) : String := app s!"@{c.name}" ctx.spec.params
def Ctx.implicits (ctx : Ctx) : String := " ".intercalate (ctx.spec.params.map (s!"\{{·} : Type _}")).toList
def Ctx.explicits (ctx : Ctx) : String := " ".intercalate (ctx.spec.params.map (s!"({·} : Type _)")).toList
def Ctx.insts (ctx : Ctx) : String := " ".intercalate (ctx.spec.params.map (s!"[MeasurableSpace {·}]")).toList
def Ctx.named (ctx : Ctx) : String := " ".intercalate (ctx.spec.params.map fun p => s!"({p} := {p})").toList
def Ctx.ty (ctx : Ctx) : String := app ctx.T ctx.spec.params
def Ctx.cyl (ctx : Ctx) : String := app "Cylinder" ctx.spec.params

def Ctx.fieldType (ctx : Ctx) (f : Field) : String := if f.kind == .recursive then ctx.ty else f.type

/-- One line per constructor, `  | <line c>`. -/
def Ctx.arms (ctx : Ctx) (line : Ctor → String) : String :=
  String.join (ctx.spec.ctors.toList.map fun c => s!"  | {line c}\n")

/-- Names for `c`'s fields: `x`, `S` or `rec`, numbered by position. With `own`, a base field
keeps its own name where safe, so that named arguments like `(op := op)` work. -/
def Ctx.names (ctx : Ctx) (c : Ctor) (rec := "c") (own := false) : Array String :=
  let gen := c.fields.mapIdx fun i f =>
    ctx.v s!"{match f.kind with | .base => "x" | .data => "S" | .recursive => rec}{i + 1}"
  c.fields.mapIdx fun i f =>
    let o := f.name.toString
    let safe := f.name.isAtomic && !f.name.hasMacroScopes && !ctx.avoidOwn.contains o &&
      !gen.contains o && (c.fields.filter (·.name == f.name)).size == 1
    if own && f.kind == .base && safe then o else gen[i]!

/-- Proof that a function out of an `n`-tuple that applies a constructor is injective. -/
def injProof (n : Nat) : String :=
  let tup := "⟨" ++ ", ".intercalate (List.replicate n "_") ++ "⟩"
  if n ≤ 1 then "intro a b h; cases h; rfl"
  else s!"intro a b h; obtain {tup} := a; obtain {tup} := b; cases h; rfl"

def Ctor.idx (c : Ctor) (p : Kind → Bool) : Array Nat :=
  (Array.range c.fields.size).filter (p c.fields[·]!.kind)

/-- The names of a second cylinder's fields. -/
def Ctx.primed (ctx : Ctx) (ns : Array String) : Array String := ns.map (ctx.v <| · ++ "'")

/-- The induction hypothesis for field `i`. -/
def Ctx.ih (ctx : Ctx) (i : Nat) : String := ctx.v s!"ih{i + 1}"

def Ctor.dot (c : Ctor) (args : Array String) : String := app s!".{c.short}" args

/-- A proof that a `c`-cylinder has measurable leaves, from proofs `t i` for its non-base fields. -/
def Ctor.leaves (c : Ctor) (t : Nat → String) : String :=
  let ts := (c.idx (· != .base)).map t
  if ts.isEmpty then "True.intro"
  else ts.toList.dropLast.foldr (fun a acc => s!"(And.intro {a} {acc})") ts.back!

/-- `obtain` of the measurable leaves `h` of the `c`-cylinder with fields `ns` into `hs` (at the
non-base fields). -/
def Ctor.obtainLeaves (c : Ctor) (ns hs : Array String) (h : String) : List String :=
  let sets := c.idx (· != .base)
  match sets.size with
  | 0 => []
  | 1 => let i := sets[0]!
    [s!"have {hs[i]!} : {if c.fields[i]!.kind == .data then "MeasurableSet" else "Cylinder.HasMeasurableLeaves"} \
      {ns[i]!} := {h}"]
  | _ => [s!"obtain {anon (sets.map (hs[·]!))} := {h}"]

/-- `cover.<c><suffix>`, escaped as one name component. -/
def Ctor.coverName (c : Ctor) (suffix : String) : String :=
  "cover." ++ (Name.mkSimple (c.raw ++ suffix)).toString

def genCylinder (ctx : Ctx) : String :=
  s!"/-- Cylinders over `{ctx.T}`: data fields are replaced by a set of values. -/
inductive Cylinder {ctx.explicits}\n" ++ ctx.arms fun c =>
    let ns := ctx.names c (own := true)
    app c.short <| c.fields.mapIdx fun i f => match f.kind with
      | .base => s!"({ns[i]!} : {f.type})"
      | .data => s!"({ns[i]!} : Set {paren f.type})"
      | .recursive => s!"({ns[i]!} : {ctx.cyl})"

def genShape (ctx : Ctx) : String :=
  s!"/-- Shapes of `{ctx.T}`: data fields are forgotten, so `Shape` is countable. -/
inductive Shape\n" ++ ctx.arms (fun c =>
    let ns := ctx.names c "s" (own := true)
    app c.short <| (c.idx (· != .data)).map fun i =>
      s!"({ns[i]!} : {if c.fields[i]!.kind == .base then c.fields[i]!.type else "Shape"})") ++
  "  deriving Countable\n"

/-- The image of the constructor over the sets of its non-base fields. -/
def image (ctx : Ctx) (c : Ctor) (ns : Array String) (self := "flatten") : String :=
  let sets := c.idx (· != .base)
  let set (i : Nat) := if c.fields[i]!.kind == .recursive then s!"{self} {ns[i]!}" else ns[i]!
  let n := c.fields.size
  if sets.isEmpty then s!"\{{app (ctx.ctor c) ns}}"
  else if sets == #[n - 1] then s!"{app (ctx.ctor c) ns.pop} '' {set (n - 1)}"
  else
    let p := ctx.v "p"
    let args := ns.mapIdx fun i x => match sets.findIdx? (· == i) with
      | some k => proj p k sets.size
      | none => x
    s!"(fun {p} : {tuple (sets.map (ctx.fieldType c.fields[·]!))} => {app (ctx.ctor c) args}) \
      '' ({" ×ˢ ".intercalate (sets.map set).toList})"

/-- The equations of `fn : dom → _` as one conjunction, proved by `rfl`: Lean's own equation
lemmas are slow to generate. `arm c` gives the fields of `c` and the right-hand side. -/
def Ctx.eqs (ctx : Ctx) (name fn dom : String) (arm : Ctor → Array String × String) : String :=
  let parts := ctx.spec.ctors.toList.map fun c =>
    let (xs, rhs) := arm c
    let eq := s!"{fn} ({c.dot xs} : {dom}) = {rhs}"
    if xs.isEmpty then (eq, "rfl")
    else (s!"(∀ {" ".intercalate xs.toList}, {eq})", s!"fun {" ".intercalate (xs.toList.map fun _ => "_")} => rfl")
  s!"theorem {name} {ctx.implicits} :\n    {" ∧\n    ".intercalate (parts.map (·.1))} :=\n  \
    {anon (parts.map (·.2)).toArray}\n"

def genFlatten (ctx : Ctx) : List String :=
  [s!"/-- The set of `{ctx.T}` values described by a cylinder. -/
def Cylinder.flatten {ctx.implicits} : {ctx.cyl} → Set ({ctx.ty})\n" ++
    ctx.arms (fun c => let ns := ctx.names c; s!"{c.dot ns} => {image ctx c ns}"),
   ctx.eqs "Cylinder.flatten_eqs" "Cylinder.flatten" ctx.cyl fun c =>
    let ns := ctx.names c; (ns, image ctx c ns "Cylinder.flatten")]

def genHasMeasurableLeaves (ctx : Ctx) : String :=
  s!"/-- A cylinder has measurable leaves if every set it carries is measurable. -/
def Cylinder.HasMeasurableLeaves {ctx.implicits} {ctx.insts} : {ctx.cyl} → Prop\n" ++ ctx.arms fun c =>
    let ns := ctx.names c
    let conds := (c.idx (· != .base)).map fun i =>
      if c.fields[i]!.kind == .data then s!"MeasurableSet {ns[i]!}" else s!"HasMeasurableLeaves {ns[i]!}"
    s!"{c.dot (c.fields.mapIdx fun i f => if f.kind == .base then "_" else ns[i]!)} => \
      {if conds.isEmpty then "True" else " ∧ ".intercalate conds.toList}"

def genInstance (ctx : Ctx) : String :=
  let c := ctx.v "c"
  s!"instance {(Name.mkSimple s!"instMeasurableSpace{ctx.spec.name.getString!}").toString} {ctx.implicits} {ctx.insts} :
    MeasurableSpace ({ctx.ty}) :=
  .generateFrom <| Cylinder.flatten '' \{ {c} : {ctx.cyl} | {c}.HasMeasurableLeaves }\n"

/-- The shape of a `c`-value or `c`-cylinder with fields `ns`, with `self` the recursive call. -/
def shapeOut (c : Ctor) (ns : Array String) (self : String) : String :=
  c.dot <| (c.idx (· != .data)).map fun i =>
    if c.fields[i]!.kind == .base then ns[i]! else s!"({self} {ns[i]!})"

/-- `T.shape` (`ofValue`) or `Cylinder.shape`: the same arms, on values or on cylinders. -/
def genShapeOf (ctx : Ctx) (ofValue : Bool) : List String :=
  let (name, dom, eqs) := if ofValue then (s!"{ctx.T}.shape", ctx.ty, s!"_root_.{ctx.T}.shape_eqs")
    else ("Cylinder.shape", ctx.cyl, "Cylinder.shape_eqs")
  [(if ofValue then s!"/-- The shape of a `{ctx.T}` value. -/
def _root_.{name} {ctx.implicits} : {dom} → Shape\n"
    else s!"/-- The shape of a cylinder. -/
def {name} {ctx.implicits} : {dom} → Shape\n") ++
    ctx.arms (fun c =>
      let ns := ctx.names c
      s!"{c.dot (c.fields.mapIdx fun i f => if f.kind == .data then "_" else ns[i]!)} => \
        {shapeOut c ns "shape"}"),
   ctx.eqs eqs name dom fun c => let ns := ctx.names c; (ns, shapeOut c ns name)]

def genShapeCylinder (ctx : Ctx) : List String :=
  let out (c : Ctor) (ns : Array String) (self : String) := c.dot <| c.fields.mapIdx fun i f =>
    match f.kind with
    | .base => ns[i]!
    | .data => "Set.univ"
    | .recursive => s!"({self} {ns[i]!})"
  [s!"/-- The cylinder of all values of a given shape: `univ` at every data field. -/
def Shape.cylinder {ctx.implicits} : Shape → {ctx.cyl}\n" ++ ctx.arms (fun c =>
    let ns := ctx.names c "s"
    s!"{c.dot ((c.idx (· != .data)).map (ns[·]!))} => {out c ns "cylinder"}"),
   ctx.eqs "Shape.cylinder_eqs" s!"Shape.cylinder {ctx.named}" "Shape" fun c =>
    let ns := ctx.names c "s"; ((c.idx (· != .data)).map (ns[·]!), out c ns "Shape.cylinder")]

/-- The base-field condition of `inter?` for `c`, if `c` has base fields. -/
def Ctor.cond (c : Ctor) (ns ns' : Array String) : Option String :=
  let eqs := (c.idx (· == .base)).map fun i => s!"{ns[i]!} = {ns'[i]!}"
  if eqs.isEmpty then none else some (" ∧ ".intercalate eqs.toList)

/-- The right-hand side of `Cylinder.inter?` on two `c`-cylinders with fields `ns` and `ns'`. -/
def Ctx.interArm (ctx : Ctx) (c : Ctor) (ns ns' : Array String) : String :=
  let rs := ns.mapIdx fun i _ => ctx.v s!"r{i + 1}"
  let recs := c.idx (· == .recursive)
  let meet := c.fields.mapIdx fun i f => match f.kind with
    | .base => ns[i]!
    | .data => s!"({ns[i]!} ∩ {ns'[i]!})"
    | .recursive => rs[i]!
  let result := s!"some {paren (c.dot meet)}"
  let body := if recs.isEmpty then result else
    let both := recs.map fun i => s!"Cylinder.inter? {ns[i]!} {ns'[i]!}"
    let somes := recs.map (s!"some {rs[·]!}")
    let other := if recs.size == 1 then "none" else ", ".intercalate (recs.toList.map fun _ => "_")
    s!"(match {", ".intercalate both.toList} with \
      | {", ".intercalate somes.toList} => {result} | {other} => none)"
  match c.cond ns ns' with
  | none => body
  | some cond => s!"(if {cond} then {body} else none)"

/-- Unfolds one `Cylinder.inter?` arm by `rfl`: its equation lemmas are slow to generate. -/
def Ctx.unfoldInter (ctx : Ctx) (c : Ctor) (ns ns' : Array String) (at_ : String) : String :=
  s!"rw [show Cylinder.inter? {paren (c.dot ns)} {paren (c.dot ns')} = {ctx.interArm c ns ns'} from rfl]{at_}"

def genInter (ctx : Ctx) : String :=
  s!"open Classical in
/-- Partial intersection of cylinders: `none` when the intersection is empty. -/
def Cylinder.inter? {ctx.implicits} : {ctx.cyl} → {ctx.cyl} → Option ({ctx.cyl})\n" ++
  ctx.arms (fun c =>
    let ns := ctx.names c
    let ns' := ctx.primed ns
    s!"{c.dot ns}, {c.dot ns'} => {ctx.interArm c ns ns'}") ++
  (if ctx.spec.ctors.size > 1 then "  | _, _ => none\n" else "")

def genCover (ctx : Ctx) (c : Ctor) : String :=
  let S := ctx.v "S"
  let hdr := s!"def cover.{c.short} {ctx.implicits}"
  if c.fields.size == 1 && c.fields[0]!.kind == .data then
    s!"{hdr} ({S} : Set {paren c.fields[0]!.type}) : Set ({ctx.ty}) :=
  Cylinder.flatten (Cylinder.{c.short} {S} : {ctx.cyl})\n"
  else
    let keys := c.idx (· != .data)
    let x := if keys.isEmpty then "_" else ctx.v (if keys.size == 1 then "x" else "p")
    let args := c.fields.mapIdx fun i f => match f.kind, keys.findIdx? (· == i) with
      | .base, some k => proj x k keys.size
      | .recursive, some k => s!"{proj x k keys.size}.cylinder"
      | _, _ => s!"(Set.univ : Set {paren f.type})"
    let dom := tuple (keys.map fun i =>
      if c.fields[i]!.kind == .base then c.fields[i]!.type else "Shape")
    s!"{hdr} ({S} : Set {paren dom}) : Set ({ctx.ty}) :=
  ⋃ {x} ∈ {S}, Cylinder.flatten ({app s!"Cylinder.{c.short}" args} : {ctx.cyl})\n"

/-- Type variable names avoiding the parameters: the codomain prefers `α`, the threaded
parameter `β` (`EctxItem`, whose parameter is `α`, gets `γ` and `β`). -/
def Ctx.greek (ctx : Ctx) (pref : String) (taken : List String := []) : String :=
  ((pref :: ["γ", "δ", "ε", "ζ"]).find? fun n => !ctx.avoid.contains n && !taken.contains n).getD
    (ctx.v pref taken)

def Ctx.dom (ctx : Ctx) (c : Ctor) : String := tuple (c.fields.map ctx.fieldType)

def genDecompCell (ctx : Ctx) : String :=
  let a := ctx.greek "α"
  let S := ctx.v "S"
  s!"/-- Per-constructor cells of the `casesOn` preimage decomposition. -/
def decompCell {ctx.implicits} \{{a} : Type _} ({S} : Set {a})
    {" ".intercalate (ctx.withF.map fun (c, f) => s!"({f} : {ctx.dom c} → {a})")} :
    Fin {ctx.spec.ctors.size} → Set ({ctx.ty}) :=
  ![ {"\n   , ".intercalate (ctx.withF.map fun (c, f) => s!"{c.name}.ι '' ({f} ⁻¹' {S})")} ]\n"

def genDecompCellParam (ctx : Ctx) : String :=
  let b := ctx.greek "β"
  let a := ctx.greek "α" [b]
  let S := ctx.v "S"
  let q := ctx.v "q"
  let row : Ctor × String → String := fun (c, f) =>
    let args := (Array.range c.fields.size).map (proj s!"{q}.2" · c.fields.size)
    s!"(fun {q} : {b} × {paren (ctx.dom c)} => ({app (ctx.ctor c) args}, {q}.1)) '' ({f} ⁻¹' {S})"
  s!"/-- Per-constructor cells of the `{b}`-parameterised `casesOn` preimage decomposition. -/
def decompCell_param {ctx.implicits} \{{if a < b then s!"{a} {b}" else s!"{b} {a}"} : Type _} ({S} : Set {a})
    {" ".intercalate (ctx.withF.map fun (c, f) => s!"({f} : {b} × {paren (ctx.dom c)} → {a})")} :
    Fin {ctx.spec.ctors.size} → Set ({ctx.ty} × {b}) :=
  ![ {"\n   , ".intercalate (ctx.withF.map row)} ]\n"

def genSingletonCyl (ctx : Ctx) : List String :=
  let out (c : Ctor) (ns : Array String) := c.dot <| c.fields.mapIdx fun i f => match f.kind with
    | .base => ns[i]!
    | .data => s!"\{{ns[i]!}}"
    | .recursive => s!"(singletonCyl {ns[i]!})"
  [s!"/-- The cylinder containing exactly one value. -/
def singletonCyl {ctx.implicits} : {ctx.ty} → {ctx.cyl}\n" ++
    ctx.arms (fun c => let ns := ctx.names c; s!"{c.dot ns} => {out c ns}"),
   ctx.eqs "singletonCyl_eqs" "singletonCyl" ctx.ty fun c => let ns := ctx.names c; (ns, out c ns)]

def genInj (ctx : Ctx) : List String := ctx.spec.ctors.toList.map fun c =>
  let pf := injProof c.fields.size
  s!"theorem {c.short}.ι.inj {ctx.implicits} :
    Function.Injective {paren (app s!"@{c.name}.ι" ctx.spec.params)} := by {pf}\n"

def genBasics (ctx : Ctx) : List String :=
  let s := ctx.v "s"
  let c := ctx.v "c"
  let hc := ctx.v "hc"
  [s!"/-- The cylinder of a shape has measurable leaves. -/
theorem Shape.cylinder_hasMeasurableLeaves {ctx.implicits} {ctx.insts} ({s} : Shape) :
    ({s}.cylinder {ctx.named}).HasMeasurableLeaves := by
  induction {s} with\n" ++ ctx.arms (fun c =>
    let ns := ctx.names c "s"
    let ihs := (c.idx (· == .recursive)).map ctx.ih
    s!"{app c.short ((c.idx (· != .data)).map (ns[·]!) ++ ihs)} => exact {c.leaves fun i =>
      if c.fields[i]!.kind == .data then "MeasurableSet.univ"
      else ihs[(c.idx (· == .recursive)).findIdx? (· == i) |>.get!]!}"),
  s!"/-- Flattened cylinders with measurable leaves are measurable. -/
@[measurability]
theorem flatten_measurable {ctx.implicits} {ctx.insts} \{{c} : {ctx.cyl}}
    ({hc} : {c}.HasMeasurableLeaves) : MeasurableSet {c}.flatten :=
  Cylinders.flatten_measurable rfl {hc}\n"]

/-- The function whose image `flatten` takes at a constructor (with its base fields fixed), and a
proof that it is injective; `none` when `flatten` gives a singleton. -/
def Ctx.imageFn (ctx : Ctx) (c : Ctor) (ns : Array String) : Option (String × String) :=
  let sets := c.idx (· != .base)
  let dom := tuple (sets.map (ctx.fieldType c.fields[·]!))
  let inj := injProof sets.size
  let p := ctx.v "p"
  let args := ns.mapIdx fun i x => match sets.findIdx? (· == i) with
    | some k => proj p k sets.size
    | none => x
  if sets.isEmpty then none
  else if sets == #[ns.size - 1] then some (s!"({app (ctx.ctor c) ns.pop} : {dom} → {ctx.ty})", inj)
  else some (s!"(fun {p} : {dom} => {app (ctx.ctor c) args} : {dom} → {ctx.ty})", inj)

/-- Case on the `inter?` of each recursive field, rewriting `h<i>` (or `h`); `none` cases are closed
right away by `close`, so this makes one goal per field rather than 2^fields. -/
def Ctx.splitInters (ctx : Ctx) (c : Ctor) (ns ns' : Array String) (at_ : Nat → String)
    (close : String) (simpElim := false) : List String :=
  (c.idx (· == .recursive)).toList.flatMap fun i =>
    let e := ctx.v s!"e{i + 1}"
    [s!"rcases {e} : Cylinder.inter? {ns[i]!} {ns'[i]!} with _ | {ctx.v s!"r{i + 1}"} <;> \
      rw [{e}] at {at_ i}{if simpElim then s!" <;> simp only [Option.elim] at {at_ i}" else ""}",
     s!"· {close}"]

/-- Case on the base-field condition of `inter?`: `neg` closes the case where the base fields
differ; otherwise they are substituted. `at_` is `""` or `" at h"`. -/
def Ctx.gate (ctx : Ctx) (c : Ctor) (ns ns' : Array String) (at_ neg : String) : List String :=
  let hb := ctx.v "hb"
  let n := (c.idx (· == .base)).size
  match c.cond ns ns' with
  | none => []
  | some cond =>
    [s!"by_cases {hb} : {cond}",
     s!"case neg => rw [ite_eq_right {hb}]{at_}; {neg}",
     s!"rw [ite_eq_left {hb}]{at_}",
     s!"obtain {if n == 1 then "rfl" else "⟨" ++ ", ".intercalate (List.replicate n "rfl") ++ "⟩"} := {hb}"]

def genShapeOfMem (ctx : Ctx) : String :=
  let (c, t, h) := (ctx.v "c", ctx.v "t", ctx.v "h")
  s!"theorem Cylinder.shape_of_mem_flatten {ctx.implicits} \{{c} : {ctx.cyl}} \{{t} : {ctx.ty}}
    ({h} : {t} ∈ Cylinder.flatten {c}) : {ctx.T}.shape {t} = Cylinder.shape {c} := by
  induction {c} generalizing {t} with\n" ++ ctx.arms fun k =>
    let ns := ctx.names k
    let ihs := (k.idx (· == .recursive)).map ctx.ih
    let sets := k.idx (· != .base)
    let ms := sets.map (ctx.v s!"m{· + 1}")
    let destruct := if sets.isEmpty then s!"obtain rfl : {t} = _ := {h}"
      else if sets.size == 1 then s!"obtain ⟨_, {ms[0]!}, rfl⟩ := {h}"
      else s!"obtain ⟨_, ⟨{", ".intercalate ms.toList}⟩, rfl⟩ := {h}"
    let uses := (k.idx (· == .recursive)).mapIdx fun j i =>
      s!"{ihs[j]!} {ms[(sets.findIdx? (· == i)).get!]!}"
    s!"{app k.short (ns ++ ihs)} =>\n    {destruct}\n    \
      simp only [{", ".intercalate ([s!"{ctx.T}.shape_eqs", "Cylinder.shape_eqs"] ++ uses.toList)}]"

/-- A theorem about `c₁ : Cylinder` proved by induction on `c₁`, with one lemma `name.<k>` per
constructor `k` (so that they are elaborated in parallel), each casing on `c₂`: `diag k ns ns'`
proves the case where both are built by `k`, and `off` closes the others. `binders` and `stmt`
give the binders after `c₁` and the statement, `ih` the induction hypothesis of a field, and `args`
the arguments after the fields and induction hypotheses. -/
def Ctx.byPairs (ctx : Ctx) (name hdr : String) (c₁ binders stmt ih : String → String)
    (gen args c₂ off : String) (diag : Ctor → Array String → Array String → List String) :
    List String :=
  let x := ctx.v "c₁"
  let lemma (k : Ctor) :=
    let ns := ctx.names k
    let ns' := ctx.primed ns
    let fields := k.fields.mapIdx fun i f => match f.kind with
      | .base => s!"({ns[i]!} : {f.type})"
      | .data => s!"({ns[i]!} : Set {paren f.type})"
      | .recursive => s!"({ns[i]!} : {ctx.cyl})"
    let ihs := (k.idx (· == .recursive)).map fun i => s!"({ctx.ih i} : {ih ns[i]!})"
    let cyl := s!"({k.dot ns} : {ctx.cyl})"
    s!"open Classical in
theorem {name}.{k.short} {hdr} {" ".intercalate (fields ++ ihs).toList} {binders cyl} :
    {stmt cyl} := by
  cases {c₂}
  case {k.short} {" ".intercalate ns'.toList} =>
" ++ String.join ((diag k ns ns').map (s!"    {·}\n")) ++ s!"  {off}\n"
  ctx.spec.ctors.toList.map lemma ++
  [s!"theorem {name} {hdr} {c₁ x} {binders x} : {stmt x} := by
  induction {x} generalizing {gen} with\n" ++ ctx.arms fun k =>
    let ns := ctx.names k
    let ihs := (k.idx (· == .recursive)).map ctx.ih
    s!"{app k.short (ns ++ ihs)} => exact {app s!"{name}.{k.short}" (ns ++ ihs)} {args}"]

def genFlattenInter (ctx : Ctx) : List String :=
  let c₂ := ctx.v "c₂"
  let disjoint (simp : String) := s!"(rw [Cylinder.flatten_disjoint_of_shape_ne (by {simp} [Cylinder.shape_eqs])]; rfl)"
  let stmt (x : String) := s!"Cylinder.flatten {x} ∩ Cylinder.flatten {c₂} = (Cylinder.inter? {x} {c₂}).elim ∅ Cylinder.flatten"
  ctx.byPairs "Cylinder.flatten_inter" ctx.implicits (s!"({·} : {ctx.cyl})") (fun _ => s!"({c₂} : {ctx.cyl})") stmt
    (fun x => s!"∀ {c₂} : {ctx.cyl}, {stmt x}") c₂ c₂ c₂
    "all_goals exact Cylinder.flatten_disjoint_of_shape_ne Shape.noConfusion" fun k ns ns' =>
    let recs := k.idx (· == .recursive)
    let hs := recs.map (ctx.v s!"h{· + 1}")
    let hyp (i : Nat) := hs[(recs.findIdx? (· == i)).get!]!
    let fn := ctx.imageFn k ns
    let hF := ctx.v "hF"
    let close := s!"simp only [Cylinder.flatten_eqs, Option.elim{if fn.isSome then s!", ← Set.image_inter {hF}" else ""}, \
      Set.prod_inter_prod, Set.prod_empty, Set.empty_prod, Set.image_empty, Set.inter_self\
      {String.join (hs.toList.map (", " ++ ·))}]"
    (recs.toList.map fun i => s!"have {hyp i} := {ctx.ih i} {ns'[i]!}") ++
    (fn.toList.map fun (f, inj) => s!"have {hF} : Function.Injective {f} := by {inj}") ++
    [ctx.unfoldInter k ns ns' ""] ++ ctx.gate k ns ns' "" (disjoint "simp_all") ++
    ctx.splitInters k ns ns' hyp close (simpElim := true) ++ [close]

def genHasMeasurableLeavesInter (ctx : Ctx) : List String :=
  let (c₂, c, h₁, h₂, h) := (ctx.v "c₂", ctx.v "c", ctx.v "h₁", ctx.v "h₂", ctx.v "h")
  let hyps (x : String) := s!"{x}.HasMeasurableLeaves → {c₂}.HasMeasurableLeaves → \
    Cylinder.inter? {x} {c₂} = some {c} → {c}.HasMeasurableLeaves"
  ctx.byPairs "Cylinder.hasMeasurableLeaves_inter" s!"{ctx.implicits} {ctx.insts}" (s!"\{{·} : {ctx.cyl}}")
    (fun x => s!"\{{c₂} {c} : {ctx.cyl}} ({h₁} : {x}.HasMeasurableLeaves) \
      ({h₂} : {c₂}.HasMeasurableLeaves) ({h} : Cylinder.inter? {x} {c₂} = some {c})")
    (fun _ => s!"{c}.HasMeasurableLeaves") (fun x => s!"∀ \{{c₂} {c} : {ctx.cyl}}, {hyps x}")
    s!"{c₂} {c}" s!"{h₁} {h₂} {h}" c₂ s!"all_goals nomatch {h}" fun k ns ns' =>
    let (as, bs) := (ns.mapIdx fun i _ => ctx.v s!"a{i + 1}", ns.mapIdx fun i _ => ctx.v s!"b{i + 1}")
    [ctx.unfoldInter k ns ns' s!" at {h}"] ++ k.obtainLeaves ns as h₁ ++ k.obtainLeaves ns' bs h₂ ++
    ctx.gate k ns ns' s!" at {h}" s!"cases {h}" ++
    ctx.splitInters k ns ns' (fun _ => h) s!"simp at {h}" ++
    [s!"(try dsimp only at {h}); cases {h}",
     s!"exact {k.leaves fun i => if k.fields[i]!.kind == .data then s!"(MeasurableSet.inter {as[i]!} {bs[i]!})"
       else s!"({ctx.ih i} {as[i]!} {bs[i]!} {ctx.v s!"e{i + 1}"} : \
         Cylinder.HasMeasurableLeaves {ctx.v s!"r{i + 1}"})"}"]

def genShapeLemmas (ctx : Ctx) : List String :=
  let simps := s!"Shape.cylinder_eqs, Cylinder.shape_eqs, {ctx.T}.shape_eqs, Cylinder.flatten_eqs"
  let (c₁, c₂, h, s, p) := (ctx.v "c₁", ctx.v "c₂", ctx.v "h", ctx.v "s", ctx.v "p")
  [s!"/-- Flattens of cylinders with different shapes are disjoint. -/
theorem Cylinder.flatten_disjoint_of_shape_ne {ctx.implicits} \{{c₁} {c₂} : {ctx.cyl}}
    ({h} : Cylinder.shape {c₁} ≠ Cylinder.shape {c₂}) :
    Cylinder.flatten {c₁} ∩ Cylinder.flatten {c₂} = ∅ :=
  Cylinders.flatten_disjoint_of_shape_ne (cShape := Cylinder.shape)
    (fun \{_ _} {h} => Cylinder.shape_of_mem_flatten {h}) {h}\n",
  s!"/-- The cylinder of a shape flattens to the values of that shape. -/
theorem Shape.cylinder_preimage_shape {ctx.implicits} ({s} : Shape) :
    ({s}.cylinder {ctx.named}).flatten = {ctx.T}.shape ⁻¹' \{{s}} :=
  Cylinders.cylinder_preimage_shape (cShape := Cylinder.shape)
    (fun \{_ _} {h} => Cylinder.shape_of_mem_flatten {h})
    (fun {s} => by induction {s} <;> simp_all [{simps}])
    (fun {p} => by induction {p} <;> simp_all [{simps}]) {s}\n",
  s!"theorem Shape.mem_cylinder_shape {ctx.implicits} ({p} : {ctx.ty}) :
    {p} ∈ (({ctx.T}.shape {p}).cylinder {ctx.named}).flatten := by
  rw [Shape.cylinder_preimage_shape]; exact rfl\n"]

def genPiSystem (ctx : Ctx) : Except String (List String) := do
  -- `flatten_isCountablySpanning` needs some cylinder with measurable leaves: the cylinder of
  -- the shape of a constructor without recursive fields, nullary if possible.
  let some c := ctx.spec.ctors.find? (·.fields.isEmpty) <|>
      ctx.spec.ctors.find? (·.fields.all fun f => f.kind == .data || f.kind == .base && f.inhabited)
    | throw "cylinders: `flatten_isCountablySpanning` needs a constructor without recursive fields \
        whose base fields are `Inhabited`"
  let s₀ := paren (c.dot ((c.idx (· == .base)).map fun _ => "default"))
  let (c₁, c₂, c, h, S) := (ctx.v "c₁", ctx.v "c₂", ctx.v "c", ctx.v "h", ctx.v "S")
  let gen := s!"\{{S} : Set ({ctx.ty}) | ∃ {c} : {ctx.cyl}, {c}.HasMeasurableLeaves ∧ Cylinder.flatten {c} = {S}}"
  return [s!"theorem Cylinder.flatten_inter_some {ctx.implicits} \{{c₁} {c₂} {c} : {ctx.cyl}}
    ({h} : Cylinder.inter? {c₁} {c₂} = some {c}) :
    Cylinder.flatten {c} = Cylinder.flatten {c₁} ∩ Cylinder.flatten {c₂} :=
  Cylinders.flatten_inter_some Cylinder.flatten_inter {h}\n",
  s!"/-- The flattened cylinders with measurable leaves form a π-system. -/
theorem Cylinder.flatten_isPiSystem {ctx.implicits} {ctx.insts} :
    IsPiSystem ({gen}) :=
  Cylinders.flatten_isPiSystem Cylinder.flatten_inter
    (fun \{_ _ _} => Cylinder.hasMeasurableLeaves_inter)\n",
  s!"/-- The flattened cylinders with measurable leaves are countably spanning. -/
theorem Cylinder.flatten_isCountablySpanning {ctx.implicits} {ctx.insts} :
    IsCountablySpanning ({gen}) :=
  Cylinders.flatten_isCountablySpanning Shape.cylinder_hasMeasurableLeaves
    Shape.cylinder_preimage_shape (Shape.cylinder {s₀}) (Shape.cylinder_hasMeasurableLeaves {s₀})\n"]

/-! ## Per-constructor measurability -/

/-- The function `T.c` as it appears in the statements of `c.measurable` and
`c.measurableEmbedding`: constant, raw, uncurried, or a tuple lambda. -/
def Ctx.ctorFn (ctx : Ctx) (c : Ctor) : String :=
  let ctor := ctx.ctor c
  let tys := c.fields.map (paren ∘ ctx.fieldType)
  match c.fields.size with
  | 0 => s!"(fun _ : Unit => ({ctor} : {ctx.ty}))"
  | 1 => s!"({ctor} : {tys[0]!} → {ctx.ty})"
  | 2 => s!"(Function.uncurry ({ctor} : {tys[0]!} → {tys[1]!} → {ctx.ty}))"
  | n =>
    let p := ctx.v "p"
    s!"(fun ({p} : {tuple (c.fields.map ctx.fieldType)}) => {app ctor ((Array.range n).map (proj p · n))})"

/-- `generateFrom 𝓒 = ‹_›`, countably spanning, and π-system lemmas for the generating family of a
field: cylinders (recursive), points (base) or all measurable sets (data). For a tuple of fields,
the families of rectangles. -/
def fact : Kind → String × String × String
  | .recursive => ("rfl", "Cylinder.flatten_isCountablySpanning", "Cylinder.flatten_isPiSystem")
  | .base => ("Cylinders.points_generateFrom", "Cylinders.points_isCountablySpanning",
      "Cylinders.points_isPiSystem")
  | .data => ("MeasurableSpace.generateFrom_measurableSet", "isCountablySpanning_measurableSet",
      "MeasurableSpace.isPiSystem_measurableSet")

def facts : List Kind → String × String × String
  | [] => ("", "", "")
  | [k] => fact k
  | k :: ks =>
    let (g, s, p) := fact k
    let (g', s', p') := facts ks
    (s!"(generateFrom_eq_prod {g} {g'} {s} {s'})", s!"({s}.prod {s'})", s!"({p}.prod {p'})")

/-- `rintro` patterns `(set, membership)` for a rectangle of generating sets of fields `is`,
binding each field's value (or set, or cylinder) to `ns[i]` and its membership to `hs[i]`. -/
def rectPattern (c : Ctor) (ns hs : Array String) : List Nat → String × String
  | [] => ("", "")
  | i :: is =>
    let one := match c.fields[i]!.kind with
      | .recursive => ("_", s!"⟨{ns[i]!}, {hs[i]!}, rfl⟩")
      | .data => (ns[i]!, hs[i]!)
      | .base => ("_", hs[i]!)
    if is.isEmpty then one
    else let (a, m) := rectPattern c ns hs is; ("_", s!"⟨{one.1}, {one.2}, {a}, {m}, rfl⟩")


/-- Membership in `flatten` of a `c`-cylinder, as a pattern or a term: the values `vs` of the
non-base fields and their memberships `ms`. -/
def Ctor.flattenMem (c : Ctor) (vs ms : Array String) (eq := "rfl") : String :=
  match (c.idx (· != .base)).size with
  | 0 => eq
  | 1 => s!"⟨{vs[0]!}, {ms[0]!}, {eq}⟩"
  | _ => s!"⟨{anon vs}, {anon ms}, {eq}⟩"

def genMeasurability (ctx : Ctx) (c : Ctor) : List String :=
  let ns := ctx.names c
  let hs := ns.mapIdx fun i _ => ctx.v s!"h{i + 1}"
  let n := c.fields.size
  let ι := paren (app s!"@{c.name}.ι" ctx.spec.params)
  let dataOnly := n == 1 && c.fields[0]!.kind == .data
  let (t, S, hS, s, h) := (ctx.v "t", ctx.v "S", ctx.v "hS", ctx.v "s", ctx.v "h")
  let leaves := c.leaves (hs[·]!)
  let prodMeas := " ".intercalate <| c.fields.toList.mapIdx fun i f =>
    let m := match f.kind with
      | .base => s!"(MeasurableSet.singleton {ns[i]!})"
      | .data => hs[i]!
      | .recursive => s!"(flatten_measurable {hs[i]!})"
    if i + 1 == n then m ++ String.join (List.replicate (n - 1) ")") else s!"({m}.prod"
  let (g, _, pi) := facts (c.fields.toList.map (·.kind))
  -- `T.c.ι '' rectangle = flatten cylinder`, by rebuilding memberships in both directions
  let as := ns.mapIdx fun i _ => ctx.v s!"a{i + 1}"
  let ns2 := ns.mapIdx fun i _ => ctx.v s!"b{i + 1}"
  let ms := ns.mapIdx fun i _ => ctx.v s!"m{i + 1}"
  let sets := c.idx (· != .base)
  let rect := s!"ext {t}; constructor
      · rintro ⟨{anon as}, {anon (c.fields.mapIdx fun i f => if f.kind == .base then "rfl" else ms[i]!)}, rfl⟩
        exact {c.flattenMem (sets.map (as[·]!)) (sets.map (ms[·]!))}
      · rintro {c.flattenMem (sets.map (as[·]!)) (sets.map (ms[·]!))}
        exact ⟨{anon (c.fields.mapIdx fun i f => if f.kind == .base then ns[i]! else as[i]!)}, \
               {anon (c.fields.mapIdx fun i f => if f.kind == .base then "rfl" else ms[i]!)}, rfl⟩"
  let keys := c.idx (· != .data)
  let p := ctx.v "p"
  let arg (f : Nat → String) := if n == 0 then "⟨⟩" else anon ((Array.range n).map f)
  let key := if keys.isEmpty then "()" else anon (keys.map fun i =>
    if c.fields[i]!.kind == .base then as[i]! else s!"{ctx.T}.shape {as[i]!}")
  let cov := if dataOnly then s!"cover.{c.short}.measurable {ctx.named} MeasurableSet.univ"
    else s!"cover.{c.short}.measurable {ctx.named} Set.univ"
  [if dataOnly then
    s!"theorem cover.{c.short}.measurable {ctx.implicits} {ctx.insts}
    \{{S} : Set {paren c.fields[0]!.type}} ({hS} : MeasurableSet {S}) :
    MeasurableSet (cover.{c.short} {S} : Set ({ctx.ty})) :=
  flatten_measurable ({ctx.v "c"} := ({c.dot #[S]} : {ctx.cyl})) {hS}\n"
  else
    s!"theorem cover.{c.short}.measurable {ctx.implicits} {ctx.insts}
    ({S} : Set {paren (tuple ((c.idx (· != .data)).map fun i =>
      if c.fields[i]!.kind == .base then c.fields[i]!.type else "Shape"))}) :
    MeasurableSet (cover.{c.short} {S} : Set ({ctx.ty})) :=
  .biUnion (Set.to_countable _) fun {p} _ => flatten_measurable {c.leaves fun i =>
    if c.fields[i]!.kind == .data then "MeasurableSet.univ"
    else s!"(Shape.cylinder_hasMeasurableLeaves {proj p ((keys.findIdx? (· == i)).get!) keys.size})"}\n",
  s!"theorem {c.coverName "_univ_eq_range"} {ctx.implicits} :
    cover.{c.short} (Set.univ) = Set.range {ι} := by
  ext {t}; constructor
  · {if dataOnly then s!"intro {h}" else s!"intro {h}; obtain ⟨{p}, -, {h}⟩ := Set.mem_iUnion₂.1 {h}"}
    obtain {c.flattenMem (sets.map (as[·]!)) (sets.map fun _ => "-")} := {h}
    exact ⟨{arg fun i => if c.fields[i]!.kind == .base then proj p ((keys.findIdx? (· == i)).get!) keys.size else as[i]!}, rfl⟩
  · rintro ⟨{arg (as[·]!)}, rfl⟩
    exact {if dataOnly then "" else s!"Set.mem_iUnion₂.2 ⟨{key}, trivial, "}{c.flattenMem (sets.map (as[·]!)) (sets.map fun i =>
      if c.fields[i]!.kind == .data then "trivial" else s!"Shape.mem_cylinder_shape {as[i]!}")}{if dataOnly then "" else "⟩"}\n",
  if n == 0 then
    s!"theorem {c.short}.ι.measurable {ctx.implicits} {ctx.insts} :
    Measurable {ι} := measurable_const\n"
  else
    s!"theorem {c.short}.ι.measurable {ctx.implicits} {ctx.insts} :
    Measurable {ι} := by
  apply measurable_generateFrom
  rintro _ ⟨{s}, {hS}, rfl⟩
  cases {s} with
  | {app c.short ns} =>{String.join (c.obtainLeaves ns hs hS |>.map (s!"\n    " ++ ·))}
    convert {prodMeas} using 1
    ext {anon as}; constructor
    · rintro {c.flattenMem (sets.map (ns2[·]!)) (sets.map (ms[·]!)) h}; cases {h}
      exact {anon (c.fields.mapIdx fun i f => if f.kind == .base then "rfl" else ms[i]!)}
    · rintro {anon (c.fields.mapIdx fun i f => if f.kind == .base then "rfl" else ms[i]!)}
      exact {c.flattenMem (sets.map (as[·]!)) (sets.map (ms[·]!))}{
  if ctx.spec.ctors.size > 1 then s!"\n  | _ => exact Cylinders.measurableSet_of_forall_notMem fun {t} {h} =>
    Shape.noConfusion (Cylinder.shape_of_mem_flatten (Set.mem_preimage.1 {h}))" else ""}\n",
  s!"theorem {c.short}.measurable {ctx.implicits} {ctx.insts} :
    Measurable {ctx.ctorFn c} := {c.short}.ι.measurable\n",
  if n == 0 then
    s!"theorem {c.short}.measurableEmbedding {ctx.implicits} {ctx.insts} :
    MeasurableEmbedding {ctx.ctorFn c} :=
  .of_measurable_inverse (g := fun _ => ()) measurable_const
    (by have {hS} := {cov}; rw [{c.coverName "_univ_eq_range"}] at {hS}; exact {hS})
    measurable_const fun _ => rfl\n"
  else
    s!"theorem {c.short}.measurableEmbedding {ctx.implicits} {ctx.insts} :
    MeasurableEmbedding {ctx.ctorFn c} :=
  measurableEmbedding_of_piSystem₁ (f := {ι}) {c.short}.ι.inj {c.short}.ι.measurable
    (h_gen := {g}.symm) (h_pi := {pi})
    (h_basic := by
      rintro {let (a, m) := rectPattern c ns hs (List.range n); s!"{a} {m}"}{String.join <|
        (c.idx (· == .base)).toList.map fun i => s!"
      rcases {hs[i]!} with rfl | ⟨{ns[i]!}, rfl⟩
      · simp only [Set.prod_empty, Set.empty_prod, Set.image_empty, MeasurableSet.empty]"}
      convert flatten_measurable ({ctx.v "c"} := ({c.dot ns} : {ctx.cyl})) {leaves} using 1
      {rect})
    (h_cov_meas := {cov}) (h_cov_range := {c.coverName "_univ_eq_range"})\n"] ++
  (if n == 0 then [] else
    [s!"theorem {c.short}.π.measurable {ctx.implicits} {ctx.insts} :
    Measurable ({app s!"@{c.name}.π" ctx.spec.params} : {ctx.ty} → Option {paren (ctx.dom c)}) :=
  Cylinders.proj_measurable {c.short}.measurableEmbedding
    (by
      ext {t}; constructor
      · rintro {hS} ⟨_, rfl⟩; cases {hS}
      · intro {hS}; cases {t} <;> first | rfl | exact absurd ⟨{anon (ns.map fun _ => "_")}, rfl⟩ {hS})
    (fun {S} => by
      ext {t}; constructor
      · rintro ⟨_, {hS}, {h}⟩; cases {t} <;> cases {h}; exact ⟨_, {hS}, rfl⟩
      · rintro ⟨_, {hS}, rfl⟩; exact ⟨_, {hS}, rfl⟩)\n"])

/-! ## `casesOn` decomposition and `measurable_rec` -/

/-- The arm of `T.casesOn` that calls `f` on the constructor's fields as a tuple (with the
parameter `b` first if given). -/
def Ctx.recArm (ctx : Ctx) (c : Ctor) (f : String) (b : Option String := none) : String :=
  let xs := (Array.range c.fields.size).map fun i => ctx.v s!"x{i + 1}"
  let args := b.toList.toArray ++ xs
  match b, c.fields.size with
  | none, 0 => s!"({f} ())"
  | none, 1 => f
  | some b, 0 => s!"({f} ({b}, ()))"
  | _, _ => s!"(fun {" ".intercalate xs.toList} => {f} {paren ("(" ++ ", ".intercalate args.toList ++ ")")})"

def genRec (ctx : Ctx) : List String :=
  let (a, (pa, pb)) := (ctx.greek "α", (ctx.greek "α" [ctx.greek "β"], ctx.greek "β"))
  let (S, hS, x, y, i, hi, q, hq, hx, p) :=
    (ctx.v "S", ctx.v "hS", ctx.v "x", ctx.v "y", ctx.v "i", ctx.v "hi", ctx.v "q", ctx.v "hq",
     ctx.v "hx", ctx.v "p")
  let fs := ctx.withF
  let cs := fs.map fun (c, _) => (c, ctx.v (Name.mkSimple s!"c_{c.raw}").toString)
  let hName (c : Ctor) := ctx.v (Name.mkSimple s!"h_{c.raw}").toString
  let wit (c : Ctor) := match c.fields.size with | 0 => "()" | 1 => "_" | n => anon (Array.replicate n "_")
  let casesOn (scrut : String) (arms : List String) (cod : String) :=
    s!"{ctx.T}.casesOn (motive := fun _ => {cod}) {scrut}\n        {"\n        ".intercalate arms}"
  let fArgs (dom : Ctor → String) := " ".intercalate (fs.map fun (c, f) => s!"({f} : {dom c})")
  let forward (k : Nat × Ctor → String) := String.join <| (List.range fs.length).zip (fs.map (·.1))
    |>.map fun (j, c) => s!"\n    · exact ⟨{j}, {k (j, c)}, {hx}, rfl⟩"
  let backward := s!"· rintro ⟨{i}, {hi}⟩; fin_cases {i} <;>
      · obtain ⟨{q}, {hq}, {hx}⟩ := {hi}; cases {hx}; exact {hq}"
  let thrBinders := if pa < pb then s!"\{{pa} {pb} : Type _}" else s!"\{{pb} {pa} : Type _}"
  [s!"theorem casesOn_preimage_decomp {ctx.implicits} \{{a} : Type _} ({S} : Set {a})
    {fArgs fun c => s!"{ctx.dom c} → {a}"} :
    (fun {x} : {ctx.ty} => {casesOn x (fs.map fun (c, f) => ctx.recArm c f) a}) ⁻¹' {S}
      = ⋃ {i}, decompCell {S} {" ".intercalate (fs.map (·.2))} {i} := by
  ext {x}
  simp only [Set.mem_preimage, Set.mem_iUnion, decompCell]
  constructor
  · intro {hx}; cases {x}{forward fun (_, c) => wit c}
  {backward}\n",
  s!"theorem measurable_rec {ctx.implicits} {ctx.insts} \{{a} : Type _} [MeasurableSpace {a}]
    {fArgs fun c => s!"{ctx.dom c} → {a}"}
    {" ".intercalate <| fs.filterMap fun (c, f) =>
      if c.fields.all (·.kind == .base) then none else some s!"({hName c} : Measurable {f})"} :
    Measurable (fun {x} : {ctx.ty} => {casesOn x (fs.map fun (c, f) => ctx.recArm c f) a}) := by
  intro {S} {hS}
  rw [casesOn_preimage_decomp]
  refine .iUnion fun {i} => ?_
  fin_cases {i}{String.join <| fs.map fun (c, _) =>
    s!"\n  · exact {c.short}.measurableEmbedding.measurableSet_image' \
      {if c.fields.all (·.kind == .base) then "(MeasurableSet.of_discrete)" else s!"({hName c} {hS})"}"}\n",
  s!"theorem casesOn_preimage_decomp_param {ctx.implicits} {thrBinders} ({S} : Set {pa})
    {fArgs fun c => s!"{pb} × {paren (ctx.dom c)} → {pa}"} :
    (fun {p} : {ctx.ty} × {pb} => {casesOn s!"{p}.1" (fs.map fun (c, f) => ctx.recArm c f s!"{p}.2") pa}) ⁻¹' {S}
      = ⋃ {i}, decompCell_param {S} {" ".intercalate (fs.map (·.2))} {i} := by
  ext ⟨{x}, {y}⟩
  simp only [Set.mem_preimage, Set.mem_iUnion, decompCell_param]
  constructor
  · intro {hx}; cases {x}{forward fun (_, c) => s!"({y}, {wit c})"}
  {backward}\n",
  s!"theorem measurable_rec_param {ctx.implicits} {ctx.insts}
    \{{pa} : Type _} [MeasurableSpace {pa}] \{{pb} : Type _} [MeasurableSpace {pb}]
    {" ".intercalate (cs.map fun (c, f) => s!"({f} : {pb} × {paren (ctx.dom c)} → {pa})")}
    {" ".intercalate (cs.map fun (c, f) => s!"({hName c} : Measurable {f})")} :
    Measurable (fun {p} : {ctx.ty} × {pb} => {casesOn s!"{p}.1" (cs.map fun (c, f) => ctx.recArm c f s!"{p}.2") pa}) := by
  intro {S} {hS}
  rw [casesOn_preimage_decomp_param]
  refine .iUnion fun {i} => ?_
  fin_cases {i}{String.join <| cs.map fun (c, _) =>
    s!"\n  · exact (({c.short}.measurableEmbedding.prodMap (.id (α := {pb}))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' ({hName c} {hS})"}\n"]

/-! ## Measurable singletons -/

/-- `singletonCyl` lemmas and the `MeasurableSingletonClass` instance, if every data field has
measurable singletons (given measurable singletons in the parameters). -/
def genSingletons (ctx : Ctx) : List String :=
  let (x, ok) := (ctx.v "x", ctx.spec.ctors.all (·.fields.all fun f => f.kind != .data || f.singletons))
  let mscs := " ".intercalate (ctx.spec.params.map (s!"[MeasurableSingletonClass {·}]")).toList
  let induct (body : Ctor → Array String → Array String → String) := s!"induction {x} with\n" ++
    ctx.arms fun c =>
      let ns := ctx.names c
      let ihs := (c.idx (· == .recursive)).map ctx.ih
      s!"{app c.short (ns ++ ihs)} => {body c ns ihs}"
  if !ok then [] else
  [s!"theorem singletonCyl_flatten {ctx.implicits} ({x} : {ctx.ty}) :
    (singletonCyl {x}).flatten = \{{x}} := by
  {induct fun _ _ ihs => s!"simp only [singletonCyl_eqs, Cylinder.flatten_eqs, Set.singleton_prod_singleton, \
    Set.image_singleton{String.join (ihs.toList.map (", " ++ ·))}]"}",
  s!"theorem singletonCyl_hasMeasurableLeaves {ctx.implicits} {ctx.insts} {mscs} ({x} : {ctx.ty}) :
    (singletonCyl {x}).HasMeasurableLeaves := by
  {induct fun c ns ihs => s!"exact {c.leaves fun i =>
      if c.fields[i]!.kind == .data then s!"(MeasurableSet.singleton {ns[i]!})"
      else ihs[(c.idx (· == .recursive)).findIdx? (· == i) |>.get!]!}"}",
  s!"instance instMeasurableSingletonClass {ctx.implicits} {ctx.insts} {mscs} :
    MeasurableSingletonClass ({ctx.ty}) where
  measurableSet_singleton :=
    Cylinders.measurableSet_singleton rfl singletonCyl_flatten singletonCyl_hasMeasurableLeaves\n"]

/-! ## Structural recursion -/

/-- `Measurable` of a function of the fields `tys`: the function itself for one field,
`Function.uncurry` for two, a tuple lambda for more. -/
def Ctx.measurableOf (ctx : Ctx) (fn : String) (tys : Array String) : String :=
  match tys.size with
  | 0 | 1 => s!"Measurable {fn}"
  | 2 => s!"Measurable (Function.uncurry {fn})"
  | n =>
    let q := ctx.v "q"
    s!"Measurable (fun ({q} : {tuple tys}) => {app fn ((Array.range n).map (proj q · n))})"

/-- Measurability of `fun a => a.2.….1` (component `k` of an `n`-tuple). -/
def projMeas (k n : Nat) : String :=
  let ops := List.replicate k "snd" ++ (if k + 1 < n then ["fst"] else [])
  ops.foldl (init := "measurable_id") fun t op =>
    if t == "measurable_id" then s!"measurable_{op}" else s!"measurable_{op}.comp ({t})"

/-- `measurable_struct_rec` (`param := none`), or the `β`-threaded `measurable_struct_rec_param`
(`param := some shift`, with binder constructors shifting the parameter if `shift`). -/
def genStructRec (ctx : Ctx) (param : Option Bool) : String :=
  let a := ctx.greek "α" ["β"]
  let b := ctx.greek "β" [a]
  let (f, bv, U, hU, p, hp, hC, s, q, hq) := (ctx.v (if param.isSome then "g" else "f"), ctx.v "b",
    ctx.v "U", ctx.v "hU", ctx.v "p", ctx.v "hp", ctx.v "hC", ctx.v "s", ctx.v "q", ctx.v "hq")
  let nm (pre : String) (c : Ctor) := ctx.v (Name.mkSimple s!"{pre}_{c.raw}").toString
  let shifts (c : Ctor) := param == some true && ctx.binders.contains c.raw
  let cs := ctx.spec.ctors.toList
  let fieldTys (c : Ctor) := c.fields.map fun fd => if fd.kind == .recursive then a else fd.type
  let pre := if param.isSome then [b] else []
  let hasH (c : Ctor) := param.isSome || c.fields.any (·.kind != .base)
  let binders :=
    [s!"\{{f} : {if param.isSome then s!"{b} → " else ""}{ctx.ty} → {a}}"] ++
    cs.map (fun c => s!"\{{nm "c" c} : {" → ".intercalate ((pre ++ (fieldTys c).toList.map paren) ++ [a])}}") ++
    (cs.filter shifts).map (fun c => s!"\{{nm "t" c} : {b} → {b}}") ++
    cs.map (fun c =>
      let xs := (Array.range c.fields.size).map fun i => ctx.v s!"x{i + 1}"
      let bb := if shifts c then s!"({nm "t" c} {bv})" else bv
      let lhs := app f (pre.toArray.map (fun _ => bv) ++ #[paren (app (ctx.ctor c) xs)])
      let rhs := app (nm "c" c) (pre.toArray.map (fun _ => bv) ++ c.fields.mapIdx fun i fd =>
        if fd.kind == .recursive then paren (app f ((if param.isSome then #[bb] else #[]) ++ #[xs[i]!])) else xs[i]!)
      let vars := pre.toArray.map (fun _ => bv) ++ xs
      s!"({nm "eq" c} : {if vars.isEmpty then "" else s!"∀ {" ".intercalate vars.toList}, "}{lhs} = {rhs})") ++
    (cs.filter hasH).map (fun c => s!"({nm "h" c} : {ctx.measurableOf (nm "c" c) (pre.toArray ++ fieldTys c)})") ++
    (cs.filter shifts).map (fun c => s!"({nm "ht" c} : Measurable {nm "t" c})")
  let arm (c : Ctor) : String :=
    let n := c.fields.size
    let xs := ctx.names c "s"
    let ihs := (c.idx (· == .recursive)).map ctx.ih
    let bs := (Array.range n).map fun i => ctx.v s!"b{i + 1}"
    let sets := c.idx (· != .base)
    let shapeIdx := c.idx (· != .data)
    let tuple := anon (c.fields.mapIdx fun i fd => if fd.kind == .base then xs[i]! else bs[i]!)
    let cover := s!"(fun {p} {hp} => by
        rw [← Set.mem_singleton_iff, ← Set.mem_preimage, ← Shape.cylinder_preimage_shape] at {hp}
        obtain {c.flattenMem (sets.map (bs[·]!)) (sets.map fun _ => "_")} := {hp}
        exact ⟨{if n == 0 then "()" else tuple}, rfl⟩)"
    let ι := app s!"@{c.name}.ι" ctx.spec.params
    let comp (i : Nat) (arg : String) :=
      if c.fields[i]!.kind == .recursive then
        paren (app f ((if param.isSome then #[if shifts c then s!"({nm "t" c} {q}.1)" else s!"{q}.1"] else #[]) ++ #[proj arg i n]))
      else proj arg i n
    let G := if param.isSome then
        s!"fun {q} => {app (nm "c" c) (#[s!"{q}.1"] ++ (Array.range n).map (comp · s!"{q}.2"))}"
      else s!"fun {q} => {app (nm "c" c) ((Array.range n).map (comp · q))}"
    let eqArg := if param.isSome then
        s!"fun {bv} {q} _ => {app (nm "eq" c) (#[bv] ++ (Array.range n).map (proj q · n))}"
      else s!"fun {q} _ => {app (nm "eq" c) ((Array.range n).map (proj q · n))}"
    -- measurability of the restricted `G`: `h_c` composed with the fields' measurability
    let coe := "measurable_subtype_coe"
    let fieldMeas (i : Nat) : String :=
      let pm := projMeas i n
      if c.fields[i]!.kind == .recursive then
        let j := (shapeIdx.findIdx? (· == i)).get!
        let inj := proj s!"(Shape.{c.short}.inj {hq})" j shapeIdx.size
        let into := if param.isSome then
            s!"(({if shifts c then s!"{nm "ht" c}.comp measurable_fst" else "measurable_fst"}).prodMk \
              ({if pm == "measurable_id" then "measurable_snd" else s!"({pm}).comp measurable_snd"}))"
          else paren pm
        s!"(Cylinders.restrict_comp (Cylinders.restrict_of_cell @{ihs[(c.idx (· == .recursive)).findIdx? (· == i) |>.get!]!}) \
          {into} (fun {q} {hq} => {inj}))"
      else
        let base := if param.isSome then s!"(measurable_snd.comp {coe})" else coe
        if pm == "measurable_id" then base else s!"(({pm}).comp {base})"
    let ms := (if param.isSome then #[s!"(measurable_fst.comp {coe})"] else #[]) ++
      (Array.range n).map fieldMeas
    let chain := ms.toList.dropLast.foldr (init := ms.back?.getD "") fun m acc => s!"({m}.prodMk {acc})"
    let hG := if hasH c then s!"({nm "h" c}.comp {chain})" else "(measurable_of_countable _)"
    s!"{app c.short ((c.idx (· != .data)).map (xs[·]!) ++ ihs)} =>
    intro {U} {hU}
    exact Cylinders.{if param.isSome then "cell_param" else "cell"} (ι := {ι}) {c.short}.measurableEmbedding ({hC} _)
      {cover}
      (G := {G}) ({eqArg})
      {hG} {hU}"
  let name := match param with
    | none => "measurable_struct_rec" | some false => "measurable_struct_rec_param"
    | some true => "measurable_struct_rec_param_shift"
  s!"theorem {name} {ctx.implicits} \{{a} : Type _} {ctx.insts} [MeasurableSpace {a}]\
    {if param.isSome then s!" \{{b} : Type _} [MeasurableSpace {b}]" else ""}
    {"\n    ".intercalate binders} :
    Measurable {if param.isSome then s!"(Function.uncurry {f})" else f} := by
  apply _root_.StructRec.{if param.isSome then "measurable_of_cells_param" else "measurable_of_cells"} {ctx.T}.shape
  intro {s}
  have {hC} : ∀ {s} : Shape, MeasurableSet ({ctx.T}.shape {ctx.named} ⁻¹' \{{s}}) := fun {s} => by
    rw [← Shape.cylinder_preimage_shape]; exact flatten_measurable (Shape.cylinder_hasMeasurableLeaves {s})
  induction {s} with\n" ++ String.join (cs.map fun c => s!"  | {arm c}\n")

/-- Attributes on theorems wait for their proofs, so they come last, when the proofs have been
elaborated in parallel. -/
def genAttributes (ctx : Ctx) : List String :=
  let cs := ctx.spec.ctors.toList
  -- `fun_prop` does not accept the `casesOn` of a single-constructor type
  let funProp := cs.flatMap (fun c => [s!"{c.short}.measurable"] ++
      if c.fields.isEmpty then [] else [s!"{c.short}.π.measurable"]) ++
    if cs.length > 1 then ["measurable_rec", "measurable_rec_param"] else []
  [s!"attribute [fun_prop] {" ".intercalate funProp}\n",
   s!"attribute [measurability] {" ".intercalate (cs.map (s!"cover.{·.short}.measurable"))}\n",
   "attribute [aesop safe apply (rule_sets := [Measurable])] Shape.cylinder_hasMeasurableLeaves\n",
   s!"attribute [simp, cylinder_simp] Cylinder.flatten_eqs {ctx.T}.shape_eqs Cylinder.shape_eqs \
     Shape.cylinder_eqs\n",
   s!"attribute [cylinder_simp] {" ".intercalate (cs.map (s!"cover.{·.short}"))}\n",
   "attribute [simp] singletonCyl_eqs Shape.cylinder_preimage_shape\n"]

def genDefs (ctx : Ctx) : Except String (List String) := do
  -- the case splits over pairs of constructors grow quadratically
  let n := ctx.spec.ctors.size
  let big (cmd : String) := if n ≤ 30 then cmd
    else s!"set_option maxHeartbeats {200000 * (n * n / 900 + 1)} in\n{cmd}"
  return genInj ctx ++
    [genCylinder ctx, big (genShape ctx)] ++ genFlatten ctx ++ [genHasMeasurableLeaves ctx, genInstance ctx] ++
    genShapeOf ctx true ++ genShapeOf ctx false ++ genShapeCylinder ctx ++ [genInter ctx] ++
    ctx.spec.ctors.toList.map (genCover ctx) ++
    [genDecompCell ctx, genDecompCellParam ctx] ++ genSingletonCyl ctx ++ genBasics ctx ++
    [genShapeOfMem ctx] ++ genShapeLemmas ctx ++
    genFlattenInter ctx ++ genHasMeasurableLeavesInter ctx ++ (← genPiSystem ctx) ++
    ctx.spec.ctors.toList.flatMap (genMeasurability ctx) ++ genRec ctx ++ genSingletons ctx ++
    (if ctx.spec.ctors.all (·.fields.all (·.kind != .recursive)) then [] else
      [genStructRec ctx none, genStructRec ctx (some false)] ++
      (if ctx.binders.isEmpty then [] else [genStructRec ctx (some true)])) ++
    genAttributes ctx

/-! ## Commands -/

def classifyIdent (id : Ident) : CommandElabM Spec :=
  liftTermElabM do classify (← realizeGlobalConstNoOverloadWithInfo id)

/-- Parse and elaborate generated source, reporting errors at `ref`. -/
def elabSource (ref : Syntax) (src : String) : CommandElabM Unit := do
  let rec setInfo : Syntax → Syntax
    | .node _ k args => .node (.fromRef ref) k (args.map setInfo)
    | .atom _ v => .atom (.fromRef ref) v
    | .ident _ raw v pre => .ident (.fromRef ref) raw v pre
    | .missing => .missing
  match Parser.runParserCategory (← getEnv) `command src with
  | .ok stx =>
    -- section variables would be in scope of the generated code, and could capture its names;
    -- linting generated code is wasted work
    withScope (fun sc => { sc with
        varDecls := #[], varUIds := #[], opts := sc.opts.setBool (Name.mkSimple "linter" |>.str "all") false }) <|
      withRef ref <| elabCommand (setInfo stx)
  | .error e => throwErrorAt ref "cylinders: generated code does not parse: {e}\n{src}"

end

syntax (name := cylinderClassify) "#cylinder_classify " ident : command

@[command_elab cylinderClassify]
meta def elabCylinderClassify : CommandElab := fun stx => do
  let spec ← classifyIdent ⟨stx[1]⟩
  logInfo <| "\n".intercalate <| spec.ctors.toList.map fun c =>
    s!"{c.short}: " ++ if c.fields.isEmpty then "nullary" else
      ", ".intercalate (c.fields.toList.map fun f => s!"({f.name} : {f.type}) {f.kind}")

syntax (name := cylinderCmd) ("cylinder_defs " <|> "cylinder_defs? ") ident
  (&" shifting" (ppSpace ident)+)? : command

@[command_elab cylinderCmd]
meta def elabCylinderCmd : CommandElab := fun stx => do
  let binders := stx[2].getArgs.toList.drop 1 |>.flatMap (·.getArgs.toList) |>.map (·.getId.toString (escape := false))
  let ctx := { Ctx.ofSpec (← classifyIdent ⟨stx[1]⟩) with binders }
  for b in binders do
    let some c := ctx.spec.ctors.find? (·.raw == b)
      | throwErrorAt stx "cylinders: `{b}` is not a constructor"
    unless c.fields.any (·.kind == .recursive) do
      throwErrorAt stx "cylinders: `{b}` has no recursive fields to shift"
  let srcs ← match genDefs ctx with
    | .ok srcs => pure srcs
    | .error e => throwErrorAt stx e
  -- the generated code refers to globals unqualified, so they must mean the same here as at the root
  let used := (srcs.flatMap fun src => (idents src).filter fun n => globals.contains (n.splitOn ".")[0]!)
    ++ globals ++ ["Set.to_countable", "MeasurableSet.biUnion"]
  for g in used.eraseDups do
    let g := g.toName
    let resolve (r : List (Name × List String)) := (r.filter (·.2.isEmpty)).map (·.1) |>.eraseDups
    let here := resolve (← resolveGlobalName g)
    if here != resolve (ResolveName.resolveGlobalName (← getEnv) {} .anonymous [] g) then
      throwErrorAt stx "cylinders: `{g}` refers to {here} here, but the generated code needs the \
        global `{g}`"
  if (stx.getHead?.map (·.getAtomVal)) == some "cylinder_defs?" then
    logInfoAt stx ("\n".intercalate srcs)
  for src in srcs do
    elabSource stx src
    if (← get).messages.hasErrors then return

end Metrology.CylinderGen
