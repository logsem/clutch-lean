module

public meta import Lean
public meta import Lean.Meta.Constructions.CtorIdx
public meta import Lean.Meta.Constructions.CtorElim
public meta import Metrology.Meta.Projections
public meta import Metrology.ProbLang.CoreMeasures.CylinderGen.Fibers
public import Metrology.ProbLang.CoreMeasures.Shapes

@[expose] public section

open Lean Elab Command Meta Metrology.Meta

/-!
# Measurable structure on inductive types

`deriving instance MeasurableSpace for T` makes an inductive type `T` a measurable space, and
proves measurable its constructors and the functions defined on it by cases or by structural
recursion.

A value of `T` is its *shape* (its constructors and its countable, *base*, fields) together with its
*leaves* (its other, *data*, fields), so `T ≃ Σ s : T.Shape, T.Leaves s`, and `T` gets the
σ-algebra of that sum. Every term is built as an `Expr` (with the builders of
`CylinderGen/Ctx.lean`), and every proof instantiates lemmas of `Shapes.lean`. In order, it
declares:

1. `T.Shape`, with the constructions of an `inductive` and `Countable`, and `T.Leaves s`, with its
   σ-algebra;
2. `T.toSigma`, `T.ofSigma`, their inverse laws `T.ofSigma_toSigma` and `T.toSigma_ofSigma`,
   `T.equivSigma`, the σ-algebra on `T` (the comap of `toSigma`), `T.measurableEquiv`, and
   `T.shape`, with a `simp` lemma `T.shape_c` per constructor `c`;
3. for each constructor `c`: `c.measurableEmbedding`, `c.ι.measurable`, `c.measurable`, `c.ι.inj`,
   where `c.ι` and `c.π` (constructor and projection of the tuple of fields) are as declared by
   `@[constructors, uncurriedProjections]`, and declared here unless `T` has them;
4. `T.measurable_cases` and `T.measurable_struct_rec` (for functions by cases, and by structural
   recursion), their `_param` variants, which thread a parameter, `T.measurable_casesOn(_param)`
   (for functions by `T.casesOn`), and `c.π.measurable`;
5. `MeasurableSingletonClass T`, when the leaves have measurable singletons.

`T.measurable_struct_rec(_param)` exist when `T` has recursive fields, and `c.π.measurable` when
`c` has fields. `c.measurable`, `c.π.measurable` and, when `T` has several constructors,
`T.measurable_casesOn(_param)` are `fun_prop` lemmas.
`#cylinder_classify T` shows how it classifies the fields.
-/

namespace Metrology.CylinderGen

meta section

/-! ## 1. Shapes and leaves -/

/-- Declares `name` by `mk`, unless it exists; then it must have type `type`. -/
def declareUnlessExists (name : Name) (type : MetaM Expr) (mk : MetaM Unit) : MetaM Unit := do
  let some info := (← getEnv).find? name | mk
  unless ← isDefEq info.type (← type) do
    throwError "cylinders: `{name}` exists, and its type is not {← type}"

/-- `c.ι` and `c.π`, for the constructors `c` of `I`, unless they exist, as from `@[constructors]`
and `@[uncurriedProjections]`. -/
def addUncurried (I : Name) : MetaM Unit := do
  forEachCtor I fun c => do
    declareUnlessExists (c.name ++ `ι) (ctorUncurriedType c) (mkCtorUncurried c)
    if c.numFields > 0 then declareUnlessExists (c.name ++ `π) (ctorProjType c) (mkCtorProj c)

/-- `T.Shape`: for each constructor of `T`, a constructor with its base fields, and with shapes for
its recursive fields. It gets the constructions of an `inductive` declaration, and `ι` and `π`. -/
def Ctx.addShape (ctx : Ctx) : MetaM Unit := do
  let name := ctx.T ++ `Shape
  ensureFresh name
  let ctors ← ctx.ctors.mapM fun c => do
    let args := c.fields.filter (·.indexed) |>.map fun f =>
      (f.name, fun _ => pure (if f.kind == .base then f.type else mkConst name))
    let type ← withLocalDeclsD args (mkForallFVars · (mkConst name))
    return { name := ctx.shapeCtor c, type }
  let baseTys := ctx.ctors.flatMap fun c => (c.fields.filter (·.kind == .base)).map (·.type)
  let level ← baseTys.foldlM (init := Level.one) fun l ty => return mkLevelMax' l (← getLevel ty)
  addDecl <| .inductDecl [] 0 [{ name, type := .sort level, ctors := ctors.toList }] false
  compileDecls #[name]
  -- what `inductive` adds (core's `mkAuxConstructions`, with `sizeOf` and injectivity)
  mkRecOn name; mkCasesOn name; mkCtorIdx name; mkCtorElim name; Lean.mkNoConfusion name
  mkBelow name; mkBRecOn name; mkSizeOfInstances name; mkInjectiveTheorems name
  addUncurried name

/-- `T.Leaves s`: the leaves of the values of shape `s`. -/
def Ctx.addLeaves (ctx : Ctx) : MetaM Unit := do
  let type ← mkArrow ctx.shape (.sort ctx.w.succ)
  let value ← withLocalDeclD `s ctx.shape fun s => do
    let motive ← mkLambdaFVars #[s] (.sort ctx.w.succ)
    let leaves ← ctx.recurseShape motive s fun _ slots => ctx.leavesTy slots fun _ ih => ih
    mkLambdaFVars #[s] leaves
  ctx.declare (ctx.T ++ `Leaves) type value (isDef := true)

/-- Declares `T.Leaves.name : ∀ s, cls (T.Leaves s)`, assembled from the instances for products,
under the instance `binders`. -/
def Ctx.addLeavesInstance (ctx : Ctx) (name : Name) (cls : Expr → MetaM Expr)
    (binders : Array Expr := #[]) : MetaM Unit := do
  let (type, value) ← withLocalDeclD `s ctx.shape fun s => do
    let motive ← mkLambdaFVars #[s] (← cls (ctx.leaves s))
    -- the motive at the recursive fields, a local instance, gives `cls (T.Leaves s)` there
    let value ← ctx.recurseShape motive s fun _ slots => do
      synthInstance (← cls (← ctx.leavesTy slots))
    return (← mkForallFVars #[s] (← cls (ctx.leaves s)), ← mkLambdaFVars #[s] value)
  ctx.declareInstance (ctx.T ++ `Leaves ++ name) type value (binders := binders)

/-! ## 2. The equivalence with the sum over shapes -/

/-- A function of `p : Σ s, T.Leaves s`, by induction on the shape `p.1`, of type
`motiveAt s v`, and given by `arm c slots vs` on the leaves `v` of shape `c slots`, whose components
are `vs`. -/
def Ctx.sigmaRec (ctx : Ctx) (motiveAt : Expr → Expr → MetaM Expr)
    (arm : Ctor → Array ShapeSlot → Array Expr → MetaM Expr) : MetaM Expr := do
  withLocalDeclD `p (← ctx.sigma) fun p => do
    let motive ← withLocalDeclD `s ctx.shape fun s => do
      mkLambdaFVars #[s] (← withLocalDeclD `v (ctx.leaves s) fun v => do
        mkForallFVars #[v] (← motiveAt s v))
    let f ← ctx.recurseShape motive (← mkAppM ``Sigma.fst #[p]) fun c slots => do
      withLocalDeclD `v (← ctx.leavesTy slots) fun v => do
        let vs ← (Array.range slots.size).mapM (mkNestedProdProj v · slots.size)
        mkLambdaFVars #[v] (← arm c slots vs)
    mkLambdaFVars #[p] (mkApp f (← mkAppM ``Sigma.snd #[p]))

/-- `⟨c args, (leaves)⟩`, from what each field contributes: its argument of the shape constructor,
if any (base and recursive fields), and its leaves. -/
def Ctx.sigmaOf (ctx : Ctx) (c : Ctor) (parts : Array (Option Expr × Expr)) : MetaM Expr := do
  let leaves ← mkNestedProdValue (parts.map (·.2)).toList ctx.unit
  ctx.sigmaMk (ctx.shapeOf c (parts.filterMap (·.1))) leaves

/-- What a recursive field contributes, from the `⟨shape, leaves⟩` `E` of its value. -/
def recursivePart (E : Expr) : MetaM (Option Expr × Expr) :=
  return (← mkAppM ``Sigma.fst #[E], ← mkAppM ``Sigma.snd #[E])

/-- `T.toSigma (c xs) = ⟨c (base fields, shapes of recursive fields), (leaves of the fields)⟩`. -/
def Ctx.addToSigma (ctx : Ctx) : MetaM Unit := do
  let σ ← ctx.sigma
  let value ← withLocalDeclD `x ctx.ty fun x => do
    mkLambdaFVars #[x] (← ctx.recurse (← mkLambdaFVars #[x] σ) x fun c slots => do
      ctx.sigmaOf c (← slots.mapM fun
        | .base x => pure (some x, ctx.unit)
        | .data x => return (none, ← ctx.up x)
        | .recursive _ ih => recursivePart ih))
  ctx.declare (ctx.T ++ `toSigma) (← mkArrow ctx.ty σ) value (isDef := true)

/-- `T.ofSigma ⟨c xs, v⟩ = c (base fields, leaves of `v`, `ofSigma` of the recursive fields)`. -/
def Ctx.addOfSigma (ctx : Ctx) : MetaM Unit := do
  let value ← ctx.sigmaRec (fun _ _ => pure ctx.ty) fun c slots vs => do
    let fields ← (slots.zip vs).mapM fun
      | (.base x, _) => pure x
      | (.leaf _, vi) => mkAppM ``ULift.down #[vi]
      | (.recursive _ ih, vi) => pure (mkApp ih vi)
    return mkAppN (ctx.const c.name) fields
  ctx.declare (ctx.T ++ `ofSigma) (← inferType value) value (isDef := true)

/-- `T.ofSigma_toSigma : ofSigma (toSigma x) = x`, by induction on `x`: a congruence per
constructor. -/
def Ctx.addLeftInverse (ctx : Ctx) : MetaM Unit := do
  let proof ← withLocalDeclD `x ctx.ty fun x => do
    let roundTrip := mkApp (ctx.member `ofSigma) (mkApp (ctx.member `toSigma) x)
    let motive ← mkLambdaFVars #[x] (← mkEq roundTrip x)
    mkLambdaFVars #[x] (← ctx.recurse motive x fun c slots => do
      slots.foldlM (init := ← mkEqRefl (ctx.const c.name)) fun h slot => match slot with
        | .base x | .data x => mkCongrFun h x
        | .recursive _ ih => mkCongr h ih)
  ctx.declare (ctx.T ++ `ofSigma_toSigma) (← inferType proof) proof

/-- `T.toSigma_ofSigma : toSigma (ofSigma ⟨s, v⟩) = ⟨s, v⟩`, by induction on `s`: both sides are
`G` of the values at the recursive fields, on which the motive gives a congruence. -/
def Ctx.addRightInverse (ctx : Ctx) : MetaM Unit := do
  let σ ← ctx.sigma
  let roundTrip (s v : Expr) : MetaM Expr := do
    let sv ← ctx.sigmaMk s v
    mkEq (mkApp (ctx.member `toSigma) (mkApp (ctx.member `ofSigma) sv)) sv
  let proof ← ctx.sigmaRec roundTrip fun c slots vs => do
    let ihs := (slots.zip vs).filterMap fun
      | (.recursive _ ih, vi) => some (mkApp ih vi)
      | _ => none
    -- `G Es = ⟨c (base fields, shapes of Es), (leaves of v, leaves of Es)⟩`
    let G ← withLocalDeclsDND (ihs.map fun _ => (`E, σ)) fun Es => do
      let mut (rest, parts) := (Es.toList, #[])
      for slot in slots, vi in vs do
        match slot with
        | .base x => parts := parts.push (some x, ctx.unit)
        | .leaf _ => parts := parts.push (none, vi)
        | .recursive .. =>
          let E :: rest' := rest | unreachable!
          rest := rest'
          parts := parts.push (← recursivePart E)
      mkLambdaFVars Es (← ctx.sigmaOf c parts)
    ihs.foldlM mkCongr (← mkEqRefl G)
  ctx.declare (ctx.T ++ `toSigma_ofSigma) (← inferType proof) proof

/-- `T.toSigma` and `T.ofSigma`, their inverse laws, and `T.equivSigma : T ≃ Σ s, T.Leaves s`,
the σ-algebra on `T` (the comap of `toSigma`), and `T.measurableEquiv`. -/
def Ctx.addEquiv (ctx : Ctx) : MetaM Unit := do
  ctx.addToSigma
  ctx.addOfSigma
  ctx.addLeftInverse
  ctx.addRightInverse
  let toSigma := ctx.member `toSigma
  let equiv ← mkAppM ``Equiv.mk
    #[toSigma, ctx.member `ofSigma, ctx.member `ofSigma_toSigma, ctx.member `toSigma_ofSigma]
  ctx.declare (ctx.T ++ `equivSigma) (← inferType equiv) equiv (isDef := true)
  let sigmaInst ← synthInstance (← mkAppM ``MeasurableSpace #[← ctx.sigma])
  let inst ← mkAppM ``MeasurableSpace.comap #[toSigma, sigmaInst]
  ctx.declareInstance (ctx.T ++ `instMeasurableSpace) (← inferType inst) inst
  let e ← mkAppM ``Shapes.measurableEquiv #[ctx.member `equivSigma,
    ← mkEqRefl (ctx.member `instMeasurableSpace (insts := true))]
  ctx.declare (ctx.T ++ `measurableEquiv) (← inferType e) e (insts := true) (isDef := true)

/-- `T.shape x`, the shape of `x`, with a `simp` equation `T.shape_c` per constructor. -/
def Ctx.addShapeFn (ctx : Ctx) : MetaM Unit := do
  let value ← withLocalDeclD `x ctx.ty fun x => do
    mkLambdaFVars #[x] (← mkAppM ``Sigma.fst #[mkApp (ctx.member `toSigma) x])
  ctx.declare (ctx.T ++ `shape) (← mkArrow ctx.ty ctx.shape) value (isDef := true)
  for c in ctx.ctors do
    ctx.withFields c fun xs => do
      let shape (x : Expr) := mkApp (ctx.member `shape) x
      let args := (c.fields.zip xs).filterMap fun (f, x) => match f.kind with
        | .base => some x
        | .data => none
        | .recursive => some (shape x)
      let lhs := shape (mkAppN (ctx.const c.name) xs)
      let name := ctx.T ++ c.named "shape"
      let type ← mkForallFVars xs (← mkEq lhs (ctx.shapeOf c args))
      ctx.declare name type (← mkLambdaFVars xs (← mkEqRefl lhs))
      addSimpTheorem simpExtension name (post := true) (inv := false) .global (eval_prio default)

/-! ## 3. Constructors -/

/-- The type `A ≃ᵐ B`. -/
def measurableEquivTy (A B : Expr) : MetaM Expr := mkAppOptM ``MeasurableEquiv #[A, B, none, none]

/-- The splitting of a field into a shape index and leaves: all index (`Shapes.point`) for a base
field, all leaves (`Shapes.leaf`) for a data field, and `T.measurableEquiv` for a recursive one.
`instantiateFor` fixes their universes from the goal, so as not to depend on their order. -/
def Ctx.fieldEquiv (ctx : Ctx) (f : Field) : MetaM Expr := do
  match f.kind with
  | .base =>
    let sigma ← mkAppM ``Sigma #[.lam `_ f.type ctx.punit .default]
    instantiateFor ``Shapes.point (← measurableEquivTy f.type sigma)
  | .data => instantiateFor ``Shapes.leaf (← measurableEquivTy f.type (← ctx.ulift f.type))
  | .recursive => pure ctx.equiv

/-- Splits the tuple of fields of `c` into a shape index and leaves: `A ≃ᵐ Σ κ, …`, with `true`,
or `A ≃ᵐ …` if no field is indexed. -/
def Ctx.splitFields (ctx : Ctx) (c : Ctor) : MetaM (Expr × Bool) := do
  if c.fields.isEmpty then
    return (← instantiateFor ``Shapes.unit (← measurableEquivTy (mkConst ``Unit) ctx.punit), false)
  let pieces ← c.fields.mapM fun f => return (← ctx.fieldEquiv f, f.indexed)
  pieces.pop.foldrM (init := pieces.back!) fun (e, i) (e', i') => do
    let pair := match i, i' with
      | true, true => ``Shapes.pair
      | false, true => ``Shapes.leafPair
      | true, false => ``Shapes.pairLeaf
      | false, false => ``MeasurableEquiv.prodCongr
    return (← mkAppM pair #[e, e'], i || i')

/-- `fun a => rfl : ∀ a, lhs a = lhs a`, for `a` in the domain of the function `ι`. -/
def reflOn (ι : Expr) (lhs : Expr → MetaM Expr) : MetaM Expr := do
  withLocalDeclD `a (← inferType ι).bindingDomain! fun a => do
    mkLambdaFVars #[a] (← mkEqRefl (← lhs a))

/-- `c.measurableEmbedding`, from the splitting of its fields, and `c.ι.measurable`,
`c.measurable` and `c.ι.inj`. -/
def Ctx.addConstructor (ctx : Ctx) (c : Ctor) : MetaM Unit := do
  let ι := ctx.const (c.name ++ `ι)
  let some_ (a : Expr) := mkAppM ``Option.some #[a]
  let (g, indexed) ← ctx.splitFields c
  let h ← reflOn ι fun a => mkAppM ``DFunLike.coe #[ctx.equiv, mkApp ι a]
  let embedding ← if indexed then do
      let (sι, sπ) := (mkConst (ctx.shapeCtor c ++ `ι), mkConst (ctx.shapeCtor c ++ `π))
      let inj ← mkAppM ``Shapes.injective_of_proj #[sι, sπ, ← reflOn sι some_]
      mkAppM ``Shapes.measurableEmbedding #[ctx.equiv, inj, g, h]
    else
      mkAppM ``Shapes.measurableEmbedding_leaves #[ctx.equiv, mkConst (ctx.shapeCtor c), g, h]
  let ctorFn ← uncurryN (ctx.const c.name) (c.fields.map ctx.fieldType)
  ctx.declare (c.name ++ `measurableEmbedding) (← mkAppM ``MeasurableEmbedding #[ctorFn]) embedding
    (insts := true)
  let measurable ← mkAppM ``MeasurableEmbedding.measurable
    #[ctx.const (c.name ++ `measurableEmbedding) (insts := true)]
  ctx.declare (c.name ++ `ι ++ `measurable) (← mkAppM ``Measurable #[ι]) measurable (insts := true)
  -- a nullary constructor is a constant, which `fun_prop` handles already
  ctx.declare (c.name ++ `measurable) (← mkAppM ``Measurable #[ctorFn]) measurable (insts := true)
    (funProp := !c.fields.isEmpty)
  -- by `π` rather than the embedding, so that it needs no measurable spaces
  let inj ← if c.fields.isEmpty then mkAppM ``Function.injective_of_subsingleton #[ι]
    else mkAppM ``Shapes.injective_of_proj #[ι, ctx.const (c.name ++ `π), ← reflOn ι some_]
  ctx.declare (c.name ++ `ι ++ `inj) (← mkAppM ``Function.Injective #[ι]) inj

/-! ## 4. Functions by cases and by structural recursion

All of them are measurable by `fiberProof` (`CylinderGen/Fibers.lean`). -/

/-- Runs `k` with `b : β` if `β?` is some `β`. -/
def withParam [Inhabited α] (β? : Option Expr) (k : Array Expr → MetaM α) : MetaM α :=
  withLocalDecls (β?.toArray.map fun β => decl `b .default (pure β)) k

/-- Runs `k bs xs` with the parameter `bs` (as `withParam`) and the fields `xs` of `c`. -/
def Ctx.withArgs [Inhabited α] (ctx : Ctx) (β? : Option Expr) (c : Ctor)
    (k : Array Expr → Array Expr → MetaM α) : MetaM α :=
  withParam β? fun bs => ctx.withFields c (k bs)

/-- Runs `k` with `α : Type u` and `[MeasurableSpace α]`, and with `param` also `β : Type v` and
`[MeasurableSpace β]` (as `βs`), named apart from the parameters of `T`. -/
def Ctx.withTypeVars [Inhabited α] (ctx : Ctx) (param : Bool)
    (k : Expr → Expr → Array Expr → MetaM α) : MetaM α := do
  let params ← ctx.params.toList.mapM (·.fvarId!.getUserName)
  let (a, u) := (fresh `α params, fresh `u ctx.levelParams)
  let (b, v) := (fresh `β (a :: params), fresh `v (u :: ctx.levelParams))
  let withType (name u : Name) (k : Expr → Expr → MetaM α) : MetaM α :=
    withLocalDecl name .implicit (.sort (.succ (.param u))) fun t => do
      withLocalDecl `inst .instImplicit (← mkAppM ``MeasurableSpace #[t]) (k t)
  withType a u fun tα iα =>
    if param then withType b v fun tβ iβ => k tα iα #[tβ, iβ] else k tα iα #[]

/-- The constructors whose arm needs a measurability hypothesis: all of them with a parameter, and
otherwise those with a field that is not base (the other arms are constant). -/
def Ctx.measured (ctx : Ctx) (param : Bool) : Array Ctor :=
  ctx.ctors.filter fun c => param || c.fields.any (·.kind != .base)

/-- `∀ b xs, f b (T.c xs) = arm b args`, with the parameter `b : β` if `β?`, where `args` are the
fields, or with `recursive`, `f (t b)` at the recursive fields, for the shift `t` if `shift?`. -/
def Ctx.eqType (ctx : Ctx) (c : Ctor) (recursive : Bool) (f arm : Expr) (β? shift? : Option Expr) :
    MetaM Expr :=
  ctx.withArgs β? c fun bs xs => do
    let b := match shift? with | some t => bs.map (mkApp t) | none => bs
    let args := (c.fields.zip xs).map fun (fd, x) =>
      if fd.callsF recursive then mkAppN f (b.push x) else x
    let lhs := mkAppN f (bs.push (mkAppN (ctx.const c.name) xs))
    mkForallFVars (bs ++ xs) (← mkEq lhs (mkAppN arm (bs ++ args)))

/-- `T.measurable_cases` (or with `recursive`, `T.measurable_struct_rec`; with `param`, their
`_param` variants): a function given by its equations on the constructors is measurable if its
arms are. The arms of `measurable_struct_rec` take the function at the recursive fields, and
those of `measurable_cases` the fields themselves. With `param`, the function takes a parameter,
which a recursive call may change by a shift `t_c` (by default `id`). -/
def Ctx.addRecursion (ctx : Ctx) (recursive param : Bool) : MetaM Unit := do
  let name := ctx.T ++ match recursive, param with
    | false, false => `measurable_cases
    | false, true => `measurable_cases_param
    | true, false => `measurable_struct_rec
    | true, true => `measurable_struct_rec_param
  let shifted := if recursive && param then ctx.ctors.filter (·.isRecursive) else #[]
  let measured := ctx.measured param
  ctx.withTypeVars param fun α iα βs => do
  let β? := βs[0]?
  let armTys (c : Ctor) := β?.toArray ++ c.fields.map fun fd =>
    if fd.callsF recursive then α else ctx.fieldType fd
  -- `t_c : β → β := id`
  let shiftTy ← β?.mapM fun β => do
    mkAppM ``optParam #[← mkArrow β β, ← withLocalDeclD `b β fun b => mkLambdaFVars #[b] b]
  -- the binders, in the order of the statement
  withLocalDecl `f .implicit (← mkArrowN (β?.toArray.push ctx.ty) α) fun f => do
  let armDecls := ctx.ctors.map fun c => decl (c.named "c") .implicit (mkArrowN (armTys c) α)
  withLocalDecls armDecls fun arms => do
  let shiftDecls := shifted.filterMap fun c => shiftTy.map (decl (c.named "t") .default <| pure ·)
  withLocalDecls shiftDecls fun ts => do
  let tOf := ctx.spread shifted ts
  let eqDecls := ctx.ctors.map fun c =>
    decl (c.named "eq") .default
      (ctx.eqType c recursive f arms[c.idx]! (β? := β?) (shift? := tOf[c.idx]!))
  withLocalDecls eqDecls fun eqs => do
  let hDecls := measured.map fun c =>
    decl (c.named "h") .default do mkAppM ``Measurable #[← uncurryN arms[c.idx]! (armTys c)]
  withLocalDecls hDecls fun hs => do
  let htDecls := (shifted.zip ts).map fun (c, t) =>
    decl (c.named "ht") .default (mkAppM ``Measurable #[t])
  withLocalDecls htDecls fun hts => do
  let proof ← ctx.fiberProof
    { recursive, f, β?, arms := ctx.mkArms arms eqs measured hs shifted (ts.zip hts) }
  let conclusion ← mkAppM ``Measurable #[← if param then mkAppM ``Function.uncurry #[f] else pure f]
  ctx.declare name conclusion proof (insts := true)
    (binders := #[α, iα] ++ βs ++ #[f] ++ arms ++ ts ++ eqs ++ hs ++ hts)

/-- `fun b x => T.casesOn x (arms[c] b …)`: the function by cases (with a parameter, if `β?`) whose
arm for `c` is `arms[c]` applied to the parameter and the fields. -/
def Ctx.casesOnFn (ctx : Ctx) (α : Expr) (β? : Option Expr) (arms : Array Expr) : MetaM Expr :=
  withParam β? fun bs => withLocalDeclD `x ctx.ty fun x => do
    let alts ← ctx.ctors.mapM fun c => ctx.withFields c fun xs => do
      mkLambdaFVars xs (mkAppN arms[c.idx]! (bs ++ xs)).headBeta
    mkLambdaFVars (bs.push x) (← mkCasesOnConst ctx.T ctx.levels ctx.params α x alts)

/-- From `h : Measurable (uncurry g)`, for `g : β → T → α`, the statement and proof of
`Measurable fun p : T × β => g p.2 p.1`: the value first, so that `fun_prop` matches
`T.casesOn p.1 …`. -/
def Ctx.measurableSwapped (ctx : Ctx) (β g h : Expr) : MetaM (Expr × Expr) := do
  withLocalDeclD `p (← mkAppM ``Prod #[ctx.ty, β]) fun p => do
    let swapFn ← mkLambdaFVars #[p] (← mkAppM ``Prod.swap #[p])
    let swap ← instantiateFor ``measurable_swap (← mkAppM ``Measurable #[swapFn])
    let fn ← mkLambdaFVars #[p] (mkApp2 g (← mkAppM ``Prod.snd #[p]) (← mkAppM ``Prod.fst #[p]))
    return (← mkAppM ``Measurable #[fn], ← mkAppM ``Measurable.comp #[h, swap])

/-- `T.measurable_casesOn` (`T.measurable_casesOn_param`): a function by `T.casesOn` is measurable
if its arms `c_c`, as functions of the tuple `(b, x₁, …)` of the parameter and the fields, are. -/
def Ctx.addCasesOn (ctx : Ctx) (param : Bool) : MetaM Unit := do
  let name := ctx.T ++ if param then `measurable_casesOn_param else `measurable_casesOn
  let measured := ctx.measured param
  ctx.withTypeVars param fun α iα βs => do
  let β? := βs[0]?
  let argTys (c : Ctor) := β?.toArray ++ c.fields.map ctx.fieldType
  let cDecls := ctx.ctors.map fun c =>
    decl (c.named "c") .default do mkArrow (← mkNestedProdType (argTys c).toList) α
  withLocalDecls cDecls fun cs => do
  let hDecls := measured.map fun c =>
    decl (c.named "h") .default (mkAppM ``Measurable #[cs[c.idx]!])
  withLocalDecls hDecls fun hs => do
  -- the arm of `c` as `fiberProof` takes it: `b xs ↦ c_c (b, xs)`
  let arms ← ctx.ctors.mapM fun c => ctx.withArgs β? c fun bs xs => do
    mkLambdaFVars (bs ++ xs) (mkApp cs[c.idx]! (← mkNestedProdValue (bs ++ xs).toList))
  let cases ← ctx.casesOnFn α β? arms
  let eqs ← ctx.ctors.mapM fun c => ctx.withArgs β? c fun bs xs => do
    mkLambdaFVars (bs ++ xs) (← mkEqRefl (mkAppN cases (bs.push (mkAppN (ctx.const c.name) xs))))
  let proof ← ctx.fiberProof
    { recursive := false, f := cases, β?, arms := ctx.mkArms arms eqs measured hs }
  let (type, proof) ← match β? with
    | none => pure (← mkAppM ``Measurable #[cases], proof)
    | some β => ctx.measurableSwapped β cases proof
  -- `fun_prop` does not accept the `casesOn` of a single-constructor type
  ctx.declare name type proof (insts := true) (binders := #[α, iα] ++ βs ++ cs ++ hs)
    (funProp := ctx.ctors.size > 1)

/-- `c.π.measurable`: the projection on constructor `c` is `T.casesOn` with arms `some` on `c` and
`none` elsewhere, as functions of the tuple of the fields, so it is measurable by
`T.measurable_casesOn`. -/
def Ctx.addProjection (ctx : Ctx) (c : Ctor) : MetaM Unit := do
  let π := ctx.const (c.name ++ `π)
  let τ ← mkNestedProdType (c.fields.map ctx.fieldType).toList
  let α ← mkAppM ``Option #[τ]
  let arms ← ctx.ctors.mapM fun d => do
    if d.idx == c.idx then return mkApp (mkConst ``Option.some [← getDecLevel τ]) τ
    withLocalDeclD `x (← mkNestedProdType (d.fields.map ctx.fieldType).toList) fun x => do
      mkLambdaFVars #[x] (← mkNone τ)
  let hyps ← (ctx.measured false).mapM fun d => do
    let goal ← mkAppM ``Measurable #[arms[d.idx]!]
    instantiateFor (if d.idx == c.idx then ``measurable_some else ``measurable_const) goal
  -- `measurable_casesOn`, with its arguments in order and the instance on `α` synthesized
  let args := (ctx.params ++ ctx.insts ++ #[α]).map some ++ #[none] ++ (arms ++ hyps).map some
  let proof ← mkAppOptM (ctx.T ++ `measurable_casesOn) args
  ctx.declare (c.name ++ `π ++ `measurable) (← mkAppM ``Measurable #[π]) proof (insts := true)
    (funProp := true)

/-! ## 5. Measurable singletons -/

/-- `MeasurableSingletonClass T`, given measurable singletons in the parameters that occur in data
fields, if the data fields have them. -/
def Ctx.addSingletons (ctx : Ctx) : MetaM Unit := do
  let msc (ty : Expr) := mkAppOptM ``MeasurableSingletonClass #[ty, none]
  let dataTys : Array Expr :=
    ctx.ctors.flatMap fun c => (c.fields.filter (·.kind == .data)).map (·.type)
  let used := ctx.params.filter fun p => dataTys.any fun ty => ty.containsFVar p.fvarId!
  withLocalDecls (used.map fun p => decl `inst .instImplicit (msc p)) fun mscs => do
    unless ← dataTys.allM fun ty => hasInstance ``MeasurableSingletonClass #[some ty, none] do
      return
    ctx.addLeavesInstance `instMeasurableSingletonClass msc mscs
    let inst ← mkAppM ``Shapes.measurableSingletonClass #[ctx.equiv]
    ctx.declareInstance (ctx.T ++ `instMeasurableSingletonClass) (← inferType inst) inst
      (binders := mscs)

/-! ## The deriving handler -/

/-- Generates the declarations of the module docstring for `T`. The `Countable` deriving handler is
a command, so it runs between two passes, each reading `T` into a `Ctx` of its own local context. -/
def generate (T : Name) : CommandElabM Unit := withExporting do
  liftTermElabM <| withCtx T (·.addShape)
  applyDerivingHandlers ``Countable #[T ++ `Shape]
  liftTermElabM <| withCtx T fun ctx => do
    ctx.addLeaves
    ctx.addLeavesInstance `instMeasurableSpace fun ty => mkAppM ``MeasurableSpace #[ty]
    ctx.addEquiv
    ctx.addShapeFn
    addUncurried ctx.T
    for c in ctx.ctors do ctx.addConstructor c
    for param in [false, true] do
      ctx.addRecursion false param
      if ctx.ctors.any (·.isRecursive) then ctx.addRecursion true param
      ctx.addCasesOn param
    for c in ctx.ctors do if !c.fields.isEmpty then ctx.addProjection c
    ctx.addSingletons

initialize registerDerivingHandler ``MeasurableSpace fun Ts => do
  Ts.forM generate
  return true

elab "#cylinder_classify " id:ident : command => liftTermElabM do
  withCtx (← realizeGlobalConstNoOverloadWithInfo id) fun ctx => do
    -- strings, so that a constructor's line does not wrap
    let lines ← ctx.ctors.toList.mapM fun c => do
      let fields ← c.fields.toList.mapM fun f => return s!"({f.name} : {← ppExpr f.type}) {f.kind}"
      return s!"{c.short}: " ++ if fields.isEmpty then "nullary" else ", ".intercalate fields
    logInfo ("\n".intercalate lines)

end

end Metrology.CylinderGen
