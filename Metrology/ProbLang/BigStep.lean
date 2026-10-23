module

public import Metrology.ProbLang.Syntax.HeapArray

@[expose] public section

/-! # Big-step evaluation for ProbLang

Generic over the effects `EvalOps`, so one evaluator serves both the measure semantics
(`measureOps`, `BigStepEquiv.lean`) and the interpreter (`ioOps`, `Interp/BigStepIO.lean`).
-/

namespace ProbLang

/-- The effects the big-step evaluator needs from its result type `M`. -/
structure EvalOps (rT : Type _) (M : Type _) where
  /-- Finish with a final configuration. -/
  ret : Cfg rT → M
  /-- Run a computation and pass its final configuration to the continuation. -/
  bind : M → (Cfg rT → M) → M
  /-- Get stuck, or `fail`. The measure semantics discards the message. -/
  stuck : String → M
  /-- `Cfg.uniform`: a uniform integer in `[0, z)` (`-1` if `z ≤ 0`); the state is kept. -/
  uniform : Int → State rT → M
  /-- `Cfg.uniformReal`: a real sampled from the unit interval; the state is kept. -/
  uniformReal : State rT → M

variable {rT : Type _} [ProbLangℝ rT] {M : Type _}

/-- Evaluates subterms right to left (the order of `Exp.decompItem`), then takes the
corresponding `headStep`. -/
@[specialize]
def bigStepF (m : EvalOps rT M) (eval : Cfg rT → M) : Cfg rT → M
  -- Stuck terms.
  | ⟨.bvar _, _⟩ => m.stuck "unbound de Bruijn index"
  | ⟨.fvar _, _⟩ => m.stuck "free variable"
  | ⟨.fail, _⟩ => m.stuck "fail"
  -- Values. A `lam` or `fix` is a value only when it is locally closed.
  | ⟨.lit b, σ⟩ => m.ret ⟨.lit b, σ⟩
  | ⟨.lam e, σ⟩ => if (Exp.lam e).isValue then m.ret ⟨.lam e, σ⟩ else m.stuck "open lam"
  | ⟨.fix e, σ⟩ => if (Exp.fix e).isValue then m.ret ⟨.fix e, σ⟩ else m.stuck "open fix"
  | ⟨.pair e1 e2, σ⟩ =>
    m.bind (eval ⟨e2, σ⟩) fun ⟨v2, σ⟩ =>
    m.bind (eval ⟨e1, σ⟩) fun ⟨v1, σ⟩ =>
    m.ret ⟨.pair v1 v2, σ⟩
  | ⟨.inl e, σ⟩ =>
    m.bind (eval ⟨e, σ⟩) fun ⟨v, σ⟩ =>
    m.ret ⟨.inl v, σ⟩
  | ⟨.inr e, σ⟩ =>
    m.bind (eval ⟨e, σ⟩) fun ⟨v, σ⟩ =>
    m.ret ⟨.inr v, σ⟩
  -- Functions.
  | ⟨.app e1 e2, σ⟩ =>
    m.bind (eval ⟨e2, σ⟩) fun ⟨v2, σ⟩ =>
    m.bind (eval ⟨e1, σ⟩) fun ⟨v1, σ⟩ =>
    match v1 with
    | .lam e => eval ⟨Exp.open' e v2, σ⟩
    | .fix e => eval ⟨.app (Exp.open' e (.fix e)) v2, σ⟩
    | _ => m.stuck "app: not a function"
  -- Operators.
  | ⟨.unop op e, σ⟩ =>
    m.bind (eval ⟨e, σ⟩) fun ⟨v, σ⟩ =>
    match op.eval v with
    | some v' => m.ret ⟨v', σ⟩
    | none => m.stuck "unop: ill-typed operand"
  | ⟨.binop op e1 e2, σ⟩ =>
    m.bind (eval ⟨e2, σ⟩) fun ⟨v2, σ⟩ =>
    m.bind (eval ⟨e1, σ⟩) fun ⟨v1, σ⟩ =>
    match op.eval v1 v2 with
    | some v => m.ret ⟨v, σ⟩
    | none => m.stuck "binop: ill-typed operands"
  | ⟨.cond ec et ef, σ⟩ =>
    m.bind (eval ⟨ec, σ⟩) fun ⟨vc, σ⟩ =>
    match vc with
    | .lit (.bool true) => eval ⟨et, σ⟩
    | .lit (.bool false) => eval ⟨ef, σ⟩
    | _ => m.stuck "if: not a boolean"
  -- Eliminators.
  | ⟨.fst e, σ⟩ =>
    m.bind (eval ⟨e, σ⟩) fun ⟨v, σ⟩ =>
    match v with
    | .pair v1 _ => m.ret ⟨v1, σ⟩
    | _ => m.stuck "fst: not a pair"
  | ⟨.snd e, σ⟩ =>
    m.bind (eval ⟨e, σ⟩) fun ⟨v, σ⟩ =>
    match v with
    | .pair _ v2 => m.ret ⟨v2, σ⟩
    | _ => m.stuck "snd: not a pair"
  | ⟨.case ec el er, σ⟩ =>
    m.bind (eval ⟨ec, σ⟩) fun ⟨vc, σ⟩ =>
    match vc with
    | .inl v => eval ⟨.app el v, σ⟩
    | .inr v => eval ⟨.app er v, σ⟩
    | _ => m.stuck "case: not a sum"
  | ⟨.scrut e p, σ⟩ =>
    m.bind (eval ⟨e, σ⟩) fun ⟨v, σ⟩ =>
    match p.tryMatch v with
    | some bindings => m.ret ⟨.inl bindings, σ⟩
    | none => m.ret ⟨.inr (.lit .unit), σ⟩
  -- Heap.
  | ⟨.alloc e, σ⟩ =>
    m.bind (eval ⟨e, σ⟩) fun ⟨v, σ⟩ =>
    match v.toVal? with
    | some v =>
      let ℓ := σ.heap.fresh
      m.ret ⟨.lit (.loc ℓ), σ.update_heap fun t => t.insert ℓ v⟩
    | none => m.stuck "alloc: not a value"
  | ⟨.allocN en ev, σ⟩ =>
    m.bind (eval ⟨ev, σ⟩) fun ⟨v, σ⟩ =>
    m.bind (eval ⟨en, σ⟩) fun ⟨en, σ⟩ =>
    match en, v.toVal? with
    | .lit (.int n), some v =>
      if 0 < n then
        m.ret ⟨.lit (.loc σ.heap.fresh), σ.update_heap (fun h => LocHeap.allocN h v n.toNat)⟩
      else m.stuck "allocN: nonpositive length"
    | _, _ => m.stuck "allocN: invalid operands"
  | ⟨.load e, σ⟩ =>
    m.bind (eval ⟨e, σ⟩) fun ⟨v, σ⟩ =>
    match v with
    | .lit (.loc ℓ) =>
      match σ.heap[ℓ]? with
      | some v => m.ret ⟨.ofVal v, σ⟩
      | none => m.stuck "load: dangling location"
    | _ => m.stuck "load: not a location"
  | ⟨.store e1 e2, σ⟩ =>
    m.bind (eval ⟨e2, σ⟩) fun ⟨v2, σ⟩ =>
    m.bind (eval ⟨e1, σ⟩) fun ⟨v1, σ⟩ =>
    match v1, v2.toVal? with
    | .lit (.loc ℓ), some v =>
      match σ.heap[ℓ]? with
      | some _ => m.ret ⟨.lit .unit, σ.update_heap fun t => t.insert ℓ v⟩
      | none => m.stuck "store: dangling location"
    | _, _ => m.stuck "store: not a location"
  -- Sampling.
  | ⟨.tape e, σ⟩ =>
    m.bind (eval ⟨e, σ⟩) fun ⟨v, σ⟩ =>
    match v with
    | .lit (.int z) =>
      let α := σ.tapes.fresh
      m.ret ⟨.lit (.lbl α), σ.update_tapes fun t => t.insert α (.empty z)⟩
    | _ => m.stuck "tape: not an integer"
  | ⟨.rand e1 e2, σ⟩ =>
    m.bind (eval ⟨e2, σ⟩) fun ⟨v2, σ⟩ =>
    m.bind (eval ⟨e1, σ⟩) fun ⟨v1, σ⟩ =>
    match v1, v2 with
    | .lit (.int z), .lit .unit => m.uniform z σ
    | .lit (.int z), .lit (.lbl α) =>
      match σ.tapes[α]? with
      | none => m.stuck "rand: dangling tape"
      | some ⟨bound, ns⟩ =>
        if bound = z then
          match ns with
          | [] => m.uniform z σ
          | n :: ns => m.ret ⟨.lit (.int n), σ.update_tapes fun t => t.insert α ⟨bound, ns⟩⟩
        else m.uniform z σ
    | _, _ => m.stuck "rand: ill-typed operands"
  | ⟨.urand, σ⟩ => m.uniformReal σ

end ProbLang
