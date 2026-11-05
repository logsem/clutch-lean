module

public import Metrology.ProbLang.Syntax.HeapArray

@[expose] public section

/-! # Big-step evaluation for ProbLang

One evaluator, generic over `EvalOps`, serves the measure semantics and the interpreter. -/

namespace ProbLang

/-- The effects the big-step evaluator needs from its result type `M`. -/
structure EvalOps (rT : Type _) (M : Type _) where
  /-- Finish with a final configuration. -/
  ret : Cfg rT → M
  /-- Run a computation and pass its final configuration to the continuation. -/
  bind : M → (Cfg rT → M) → M
  /-- Get stuck with a message ignored by the measure semantics. -/
  stuck : String → M
  /-- `Cfg.uniform`: a uniform integer in `[0, z)` (`-1` if `z ≤ 0`); the state is kept. -/
  uniform : Int → State rT → M
  /-- `Cfg.uniformReal`: a real sampled from the unit interval; the state is kept. -/
  uniformReal : State rT → M
  /-- `Cfg.sample`: a value drawn from the distribution named `n` at an argument; the state is
  kept. -/
  sample : ℕ → Val rT → State rT → M
  /-- `Cfg.test`: a test `k` at an argument of the random variable at a label. -/
  test : ℕ → Val rT → Lbl → State rT → M

variable {rT : Type _} [ProbLangℝ rT] {M : Type _}

/-- Evaluates subterms right to left (the order of `Exp.decompItem`), then takes the
corresponding `headStep`. -/
@[specialize]
def bigStepF [DecidableEq rT] (m : EvalOps rT M) (eval : Cfg rT → M) : Cfg rT → M
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
      m.ret ⟨.lit (.loc ℓ), σ.updateHeap fun t => t.insert ℓ v⟩
    | none => m.stuck "alloc: not a value"
  | ⟨.allocN en ev, σ⟩ =>
    m.bind (eval ⟨ev, σ⟩) fun ⟨v, σ⟩ =>
    m.bind (eval ⟨en, σ⟩) fun ⟨en, σ⟩ =>
    match en, v.toVal? with
    | .lit (.int n), some v =>
      if 0 < n then
        m.ret ⟨.lit (.loc σ.heap.fresh), σ.updateHeap (fun h => LocHeap.allocN h v n.toNat)⟩
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
      | some _ => m.ret ⟨.lit .unit, σ.updateHeap fun t => t.insert ℓ v⟩
      | none => m.stuck "store: dangling location"
    | _, _ => m.stuck "store: not a location"
  -- Sampling.
  | ⟨.tape n e, σ⟩ =>
    m.bind (eval ⟨e, σ⟩) fun ⟨v, σ⟩ =>
    match v.toVal? with
    | some v =>
      let α := σ.tapes.fresh
      m.ret ⟨.lit (.lbl α), σ.updateTapes fun t => t.insert α (.empty n v)⟩
    | none => m.stuck "tape: not a value"
  | ⟨.sample n e et, σ⟩ =>
    m.bind (eval ⟨et, σ⟩) fun ⟨vt, σ⟩ =>
    m.bind (eval ⟨e, σ⟩) fun ⟨ve, σ⟩ =>
    match ve.toVal?, vt with
    | some v, .lit .unit => m.sample n v σ
    | some v, .lit (.lbl α) =>
      match σ.tapes[α]? with
      | none => m.stuck "sample: dangling tape"
      | some t =>
        if t.name = n ∧ t.arg = v then
          let σ' := σ.updateTapes fun ts => ts.insert α t.shift
          match t.head? with
          | none => m.sample n v σ'
          | some w => m.ret ⟨.ofVal w, σ'⟩
        else m.sample n v σ
    | _, _ => m.stuck "sample: ill-typed operands"
  -- Foreign calls: no foreign code, so stuck once the argument is a value.
  | ⟨.ffi e, σ⟩ =>
    m.bind (eval ⟨e, σ⟩) fun _ => m.stuck "ffi: no foreign code"
  -- Random variables.
  | ⟨.randvar n e, σ⟩ =>
    m.bind (eval ⟨e, σ⟩) fun ⟨v, σ⟩ =>
    match v.toVal? with
    | some v =>
      let l := σ.rvs.fresh
      m.ret ⟨.lit (.lbl l), σ.updateRvs fun t => t.insert l (RvCell.fresh n v)⟩
    | none => m.stuck "randvar: not a value"
  | ⟨.test k e1 e2, σ⟩ =>
    m.bind (eval ⟨e2, σ⟩) fun ⟨v2, σ⟩ =>
    m.bind (eval ⟨e1, σ⟩) fun ⟨v1, σ⟩ =>
    match v1, v2.toVal? with
    | .lit (.lbl l), some a => m.test k a l σ
    | _, _ => m.stuck "test: not a label"

end ProbLang
