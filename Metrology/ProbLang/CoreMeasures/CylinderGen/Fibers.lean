module

public meta import Metrology.ProbLang.CoreMeasures.CylinderGen.Ctx
public import Metrology.ProbLang.CoreMeasures.Shapes

/-! # The measurability of functions on `T`, fiber by fiber

`fiberProof` proves them measurable from their equations on the constructors. -/

@[expose] public section

open Lean Meta Metrology.Meta

namespace Metrology.CylinderGen

meta section

/-! ## Measurability of terms

Each helper returns a term and a proof that it is measurable in some variable. -/

/-- `measurable_id'` for the variable `v`: `Measurable fun v => v`. -/
def measurableId (v : Expr) : MetaM Expr := do
  instantiateFor ``measurable_id' (← mkAppM ``Measurable #[← mkLambdaFVars #[v] v])

/-- `t.1` (with `fst`) or `t.2`, and its measurability in some variable, from that of `t` (`ht`). -/
def measurableProj (fst : Bool) (t ht : Expr) : MetaM (Expr × Expr) := do
  let (f, thm) := if fst then (``Prod.fst, ``Measurable.fst) else (``Prod.snd, ``Measurable.snd)
  return (← mkAppM f #[t], ← mkAppM thm #[ht])

/-- Component `i` of a right-nested `n`-tuple `p`, which is measurable in some variable by `hp`, and
its measurability. -/
def measurableNestedProj (p hp : Expr) (i n : Nat) : MetaM (Expr × Expr) :=
  (nestedProdPath i n).foldlM (init := (p, hp)) fun (t, h) f => measurableProj f t h

/-- `t.down`, and its measurability in some variable, from that of `t` (`ht`). -/
def measurableDown (t ht : Expr) : MetaM (Expr × Expr) := do
  let down ← withLocalDeclD `y (← inferType t) fun y => do
    mkLambdaFVars #[y] (← mkAppM ``ULift.down #[y])
  let hdown ← instantiateFor ``measurable_down (← mkAppM ``Measurable #[down])
  return (← mkAppM ``ULift.down #[t], ← mkAppM ``Measurable.comp #[hdown, ht])

/-! ## The function and its arms -/

/-- The equation of a function `f` on constructor `c`, with its arm, the proof `hyp?` that the arm
is measurable (if not constant), and the shift `shift?` at recursive calls. -/
structure Arm where
  /-- The arm, applied to the parameter and the arguments. -/
  arm : Expr
  /-- The equation of `f` on the constructor. -/
  eq : Expr
  /-- The proof that the arm is measurable, if it is not constant. -/
  hyp? : Option Expr
  /-- The shift `t_c` of the parameter at recursive calls, with its measurability. -/
  shift? : Option (Expr × Expr) := none
  deriving Inhabited

variable (ctx : Ctx)

/-- `xs`, which belong to the constructors `cs` in order, as an array indexed by constructor. -/
def Ctx.spread (cs : Array Ctor) (xs : Array α) : Array (Option α) :=
  ctx.ctors.map fun c => (cs.findIdx? (·.idx == c.idx)).bind (xs[·]?)

/-- The arms of the constructors, from their `arms` and equations `eqs`, the hypotheses `hs` of
the constructors `measured`, and the shifts of the constructors `shifted`. -/
def Ctx.mkArms (arms eqs : Array Expr) (measured : Array Ctor) (hs : Array Expr)
    (shifted : Array Ctor := #[]) (shifts : Array (Expr × Expr) := #[]) : Array Arm :=
  let (hOf, shiftOf) := (ctx.spread measured hs, ctx.spread shifted shifts)
  ctx.ctors.map fun c =>
    { arm := arms[c.idx]!, eq := eqs[c.idx]!, hyp? := hOf[c.idx]!, shift? := shiftOf[c.idx]! }

/-- A function `f` on `T` (with `β?`, `f : β → T → α`) given by its equations, one `Arm` per
constructor. -/
structure Recursion where
  /-- Structural recursion: the arms take `f` at recursive fields (else: by cases, the arms take
  the fields). -/
  structural : Bool
  /-- The function. -/
  f : Expr
  /-- The type of the parameter, if `f : β → T → α`. -/
  β? : Option Expr
  /-- One per constructor, indexed by `Ctor.idx`. -/
  arms : Array Arm

/-! ## Measurability on the leaves of one shape -/

/-- The domain of the function on the leaves `leaves` of a shape: `β × leaves` with a parameter. -/
def Recursion.domain (r : Recursion) (leaves : Expr) : MetaM Expr :=
  match r.β? with
  | none => pure leaves
  | some β => mkAppM ``Prod #[β, leaves]

variable (r : Recursion)

/-- An argument of an arm on the leaves of a shape: as the equation takes it, as the arm takes it,
and a proof that the latter is measurable in the leaves. -/
structure Arg where
  /-- The argument as the equation takes it. -/
  field : Expr
  /-- The argument as the arm takes it. -/
  arm : Expr
  /-- The proof that `arm` is measurable in the leaves. -/
  measurable : Expr
  deriving Inhabited

/-- `ctx.equiv.symm ⟨s, v⟩`: the value of shape `s` with leaves `v`. -/
def Ctx.ofLeaves (s v : Expr) : MetaM Expr := do
  mkAppM ``DFunLike.coe #[← mkAppM ``MeasurableEquiv.symm #[ctx.equiv], ← ctx.sigmaMk s v]

/-- `fun v => f (ctx.equiv.symm ⟨s, v⟩)`, or with a parameter
`fun p => f p.1 (ctx.equiv.symm ⟨s, p.2⟩)`: the function on the leaves of shape `s`. -/
def Ctx.onLeaves (s : Expr) : MetaM Expr := do
  withLocalDeclD `v (← r.domain (ctx.leaves s)) fun v => do
    let value ← match r.β? with
      | none => pure (mkApp r.f (← ctx.ofLeaves s v))
      | some _ => do
        let x ← ctx.ofLeaves s (← mkAppM ``Prod.snd #[v])
        pure (mkApp2 r.f (← mkAppM ``Prod.fst #[v]) x)
    mkLambdaFVars #[v] value

/-- The argument of an arm at a recursive field of value `x := ctx.equiv.symm ⟨s, vi⟩`, where `vi`
is measurable by `hvi`: `x` for a function by cases, and `f x` (or `f (shift b) x`) for a structural
recursion, measurable by the motive `ih`. -/
def Ctx.recursiveArg (shift? : Option (Expr × Expr)) (b? : Option Arg)
    (s ih vi hvi : Expr) : MetaM Arg := do
  let x ← ctx.ofLeaves s vi
  if !r.structural then
    let hsymm ← mkAppM ``Shapes.measurable_symm_mk #[ctx.equiv, s]
    return { field := x, arm := x, measurable := ← mkAppM ``Measurable.comp #[hsymm, hvi] }
  match b? with
  | none =>
    return { field := x, arm := mkApp r.f x, measurable := ← mkAppM ``Measurable.comp #[ih, hvi] }
  | some b =>
    let (b', hb') ← match shift? with
      | some (t, ht) => pure (mkApp t b.arm, ← mkAppM ``Measurable.comp #[ht, b.measurable])
      | none => pure (b.arm, b.measurable)
    let hpair ← mkAppM ``Measurable.prodMk #[hb', hvi]
    return { field := x, arm := mkApp2 r.f b' x
             measurable := ← mkAppM ``Measurable.comp #[ih, hpair] }

/-- The arguments of `arm` on the leaves `lv` of shape `c slots`, which are measurable in `v` (by
`hv`) by `hlv`; with a parameter, the parameter (`v.1`) first. -/
def Ctx.argsOnLeaves (arm : Arm) (slots : Array ShapeSlot)
    (v hv lv hlv : Expr) : MetaM (Array Arg) := do
  let param ← r.β?.mapM fun _ => do
    let (b, hb) ← measurableProj true v hv
    return { field := b, arm := b, measurable := hb : Arg }
  let fields ← slots.mapIdxM fun i slot => do
    match slot with
    | .base x =>
      let hx ← instantiateFor ``measurable_const (← mkAppM ``Measurable #[← mkLambdaFVars #[v] x])
      return { field := x, arm := x, measurable := hx : Arg }
    | .leaf _ =>
      let (vi, hvi) ← measurableNestedProj lv hlv i slots.size
      let (x, hx) ← measurableDown vi hvi
      return { field := x, arm := x, measurable := hx }
    | .recursive s ih =>
      let (vi, hvi) ← measurableNestedProj lv hlv i slots.size
      ctx.recursiveArg r arm.shift? param s ih vi hvi
  return param.toArray ++ fields

/-- On the leaves `v` of shape `c slots`, the function is the arm of `c` applied to its arguments,
which is measurable by its `hyp?`. -/
def Ctx.fiberArm (c : Ctor) (slots : Array ShapeSlot) : MetaM Expr := do
  withLocalDeclD `v (← r.domain (← ctx.leavesTy slots)) fun v => do
  let hv ← measurableId v
  let (lv, hlv) ← match r.β? with
    | none => pure (v, hv)
    | some _ => measurableProj false v hv
  let arm := r.arms[c.idx]!
  let args ← ctx.argsOnLeaves r arm slots v hv lv hlv
  let G ← mkLambdaFVars #[v] (mkAppN arm.arm (args.map (·.arm)))
  let hG ← match arm.hyp? with
    | some h => do
      -- an arm with a hypothesis has an argument: the parameter, or a field that is not base
      let tuple ← args.pop.foldrM (init := args.back!.measurable) fun a hb =>
        mkAppM ``Measurable.prodMk #[a.measurable, hb]
      mkAppM ``Measurable.comp #[h, tuple]
    | none => instantiateFor ``measurable_const (← mkAppM ``Measurable #[G])
  let F ← ctx.onLeaves r (ctx.shapeOf c (slots.filterMap ShapeSlot.shapeArg?))
  let eq ← mkLambdaFVars #[v] (mkAppN arm.eq (args.map (·.field)))
  mkAppM ``Shapes.measurable_of_eq #[F, G, eq, hG]

/-! ## The proof over all shapes -/

/-- `Measurable f` (or `Measurable (uncurry f)`), from its measurability on the leaves of every
shape, by induction on shapes. -/
def Ctx.fiberProof : MetaM Expr := do
  -- its induction hypothesis at recursive fields is the `ih` of `Ctx.recursiveArg`
  let motive ← withLocalDeclD `s ctx.shape fun s => do
    mkLambdaFVars #[s] (← mkAppM ``Measurable #[← ctx.onLeaves r s])
  let fibers ← withLocalDeclD `s ctx.shape fun s => do
    mkLambdaFVars #[s] (← ctx.recurseShape motive s (ctx.fiberArm r))
  let thm :=
    if r.β?.isSome then ``Shapes.measurable_uncurry_of_fibers else ``Shapes.measurable_of_fibers
  mkAppM thm #[ctx.equiv, r.f, fibers]

end

end Metrology.CylinderGen
