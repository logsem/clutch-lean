module

public import Metrology.ProbLang.Syntax.HeapArray

/-! # An environment machine for ProbLang

A substitution-free evaluator with closures and first-order `Frame` continuations, taking the
same steps as `bigStepF`; `EnvStepEquiv.lean` proves it equals `bigStep` under readback (`rb`).
-/

@[expose] public section

namespace ProbLang

variable {rT : Type _}

/-- Runtime values, where a closure `clo env body` stands for `lam body` with its free de Bruijn
indices bound to `env`, and `fixClo` likewise for `fix`. -/
inductive RVal (rT : Type _) where
  | lit (b : BaseLit rT)
  | clo (env : List (RVal rT)) (body : Exp rT)
  | fixClo (env : List (RVal rT)) (body : Exp rT)
  | pair (v1 v2 : RVal rT)
  | inl (v : RVal rT)
  | inr (v : RVal rT)
  deriving Inhabited

/-- Environments: the value of de Bruijn index `i` is the `i`-th entry. -/
abbrev Env (rT : Type _) := List (RVal rT)

/-- A final configuration of the machine. -/
structure RCfg (rT : Type _) where
  /-- The returned value. -/
  val : RVal rT
  /-- The final state. -/
  state : State rT

/-- A pending evaluation-context item: what remains to do with the value of the subterm being
evaluated, where frames holding an `env` still have subterms to evaluate under it. -/
inductive Frame (rT : Type _) where
  | pairR (env : Env rT) (e1 : Exp rT)
  | pairL (v2 : RVal rT)
  | inl
  | inr
  | appR (env : Env rT) (e1 : Exp rT)
  | appL (v2 : RVal rT)
  /-- Apply the value to `v`. -/
  | applyTo (v : RVal rT)
  | unop (op : UnOp)
  | binopR (op : BinOp) (env : Env rT) (e1 : Exp rT)
  | binopL (op : BinOp) (v2 : RVal rT)
  | cond (env : Env rT) (et ef : Exp rT)
  | fst
  | snd
  | case (env : Env rT) (el er : Exp rT)
  | scrut (p : Pat rT)
  | alloc
  | load
  | storeR (env : Env rT) (e1 : Exp rT)
  | storeL (v2 : RVal rT)
  | tape (n : ℕ)
  | sampleR (n : ℕ) (env : Env rT) (e1 : Exp rT)
  | sampleL (n : ℕ) (v2 : RVal rT)
  | allocNR (env : Env rT) (en : Exp rT)
  | allocNL (v : RVal rT)
  | ffi
  | randvar (n : ℕ)
  | testR (k : ℕ) (env : Env rT) (e1 : Exp rT)
  | testL (k : ℕ) (v2 : RVal rT)

/-- A configuration of the machine: a call of the evaluator. -/
inductive EnvCfg (rT : Type _) where
  | eval (env : Env rT) (e : Exp rT) (σ : State rT)
  | apply (f v : RVal rT) (σ : State rT)
  /-- Resume the frame `f` with the value `v` of the subterm it was waiting for. -/
  | resume (f : Frame rT) (v : RVal rT) (σ : State rT)

/-- The operations a machine step may take, where proofs use `Step` data (`stepOps`) and the
interpreter its own loop. -/
structure StepOps (rT : Type _) (α : Type _) where
  /-- Return the value `v` with state `σ`. -/
  ret : RVal rT → State rT → α
  /-- Continue by evaluating `e` under `env` (a tail call). -/
  eval : Env rT → Exp rT → State rT → α
  /-- Evaluate `e` under `env`, then resume the frame with its value. -/
  evalThen : Env rT → Exp rT → State rT → Frame rT → α
  /-- Continue by applying a function value (a tail call). -/
  apply : RVal rT → RVal rT → State rT → α
  /-- Get stuck, or `fail`. -/
  stuck : String → α
  /-- Return `lit (int n)` for `n` uniform in `[0, z)`, or `n = -1` when `z ≤ 0`. -/
  uniform : Int → State rT → α
  /-- Return `lit (real r)` for `r` drawn from `LawfulProbLangℝ.unifUnit`. -/
  uniformReal : State rT → α
  /-- Return a value drawn from the distribution named `n` at the argument `v`. -/
  sample : ℕ → Val rT → State rT → α
  /-- Return the result of test `k` at the argument `a` of the random variable at label `l`. -/
  test : ℕ → Val rT → Lbl → State rT → α

/-- A machine step as data: the `StepOps` whose operations are constructors. -/
inductive Step (rT : Type _) where
  | ret (v : RVal rT) (σ : State rT)
  | eval (env : Env rT) (e : Exp rT) (σ : State rT)
  | evalThen (env : Env rT) (e : Exp rT) (σ : State rT) (f : Frame rT)
  | apply (f v : RVal rT) (σ : State rT)
  | stuck (msg : String)
  | uniform (z : Int) (σ : State rT)
  | uniformReal (σ : State rT)
  | sample (n : ℕ) (v : Val rT) (σ : State rT)
  | test (k : ℕ) (a : Val rT) (l : Lbl) (σ : State rT)

/-- The `StepOps` whose operations are the `Step` constructors. -/
def stepOps : StepOps rT (Step rT) :=
  ⟨.ret, .eval, .evalThen, .apply, .stuck, .uniform, .uniformReal, .sample, .test⟩

/-! ## Readback -/

/-- Substitute `vs` for the de Bruijn indices `k, k+1, …` of `e`. -/
def Exp.substEnv (k : Nat) (vs : List (Exp rT)) : Exp rT → Exp rT
  | .bvar j => if k ≤ j then (vs[j - k]?).getD (.bvar j) else .bvar j
  | .fvar x => .fvar x
  | .lit b => .lit b
  | .lam e => .lam (substEnv (k+1) vs e)
  | .fix e => .fix (substEnv (k+1) vs e)
  | .app e1 e2 => .app (substEnv k vs e1) (substEnv k vs e2)
  | .unop op e => .unop op (substEnv k vs e)
  | .binop op e1 e2 => .binop op (substEnv k vs e1) (substEnv k vs e2)
  | .cond ec et ef => .cond (substEnv k vs ec) (substEnv k vs et) (substEnv k vs ef)
  | .pair e1 e2 => .pair (substEnv k vs e1) (substEnv k vs e2)
  | .fst e => .fst (substEnv k vs e)
  | .snd e => .snd (substEnv k vs e)
  | .inl e => .inl (substEnv k vs e)
  | .inr e => .inr (substEnv k vs e)
  | .case ec el er => .case (substEnv k vs ec) (substEnv k vs el) (substEnv k vs er)
  | .alloc e => .alloc (substEnv k vs e)
  | .load e => .load (substEnv k vs e)
  | .store e1 e2 => .store (substEnv k vs e1) (substEnv k vs e2)
  | .allocN e1 e2 => .allocN (substEnv k vs e1) (substEnv k vs e2)
  | .tape n e => .tape n (substEnv k vs e)
  | .fail => .fail
  | .ffi e => .ffi (substEnv k vs e)
  | .sample n e et => .sample n (substEnv k vs e) (substEnv k vs et)
  | .scrut e p => .scrut (substEnv k vs e) p
  | .randvar n e => .randvar n (substEnv k vs e)
  | .test k' e1 e2 => .test k' (substEnv k vs e1) (substEnv k vs e2)

mutual
/-- Read a runtime value back as an expression. -/
def RVal.rb : RVal rT → Exp rT
  | .lit b => .lit b
  | .clo env body => .lam (body.substEnv 1 (RVal.rbEnv env))
  | .fixClo env body => .fix (body.substEnv 1 (RVal.rbEnv env))
  | .pair v1 v2 => .pair v1.rb v2.rb
  | .inl v => .inl v.rb
  | .inr v => .inr v.rb

/-- Read an environment back as a list of expressions. -/
def RVal.rbEnv : List (RVal rT) → List (Exp rT)
  | [] => []
  | v :: vs => v.rb :: RVal.rbEnv vs
end

/-- Read a final configuration back as a `Cfg`. -/
def RCfg.rb (r : RCfg rT) : Cfg rT := ⟨r.val.rb, r.state⟩

/-- Plug an expression into the hole of a frame, reading the frame back. -/
def Frame.fill : Frame rT → Exp rT → Exp rT
  | .pairR env e1, e => .pair (e1.substEnv 0 (RVal.rbEnv env)) e
  | .pairL v2, e => .pair e v2.rb
  | .inl, e => .inl e
  | .inr, e => .inr e
  | .appR env e1, e => .app (e1.substEnv 0 (RVal.rbEnv env)) e
  | .appL v2, e => .app e v2.rb
  | .applyTo v, e => .app e v.rb
  | .unop op, e => .unop op e
  | .binopR op env e1, e => .binop op (e1.substEnv 0 (RVal.rbEnv env)) e
  | .binopL op v2, e => .binop op e v2.rb
  | .cond env et ef, e =>
    .cond e (et.substEnv 0 (RVal.rbEnv env)) (ef.substEnv 0 (RVal.rbEnv env))
  | .fst, e => .fst e
  | .snd, e => .snd e
  | .case env el er, e =>
    .case e (el.substEnv 0 (RVal.rbEnv env)) (er.substEnv 0 (RVal.rbEnv env))
  | .scrut p, e => .scrut e p
  | .alloc, e => .alloc e
  | .load, e => .load e
  | .storeR env e1, e => .store (e1.substEnv 0 (RVal.rbEnv env)) e
  | .allocNR env e1, e => .allocN (e1.substEnv 0 (RVal.rbEnv env)) e
  | .storeL v2, e => .store e v2.rb
  | .allocNL v2, e => .allocN e v2.rb
  | .tape n, e => .tape n e
  | .sampleR n env e1, e => .sample n (e1.substEnv 0 (RVal.rbEnv env)) e
  | .sampleL n v2, e => .sample n e v2.rb
  | .ffi, e => .ffi e
  | .randvar n, e => .randvar n e
  | .testR k env e1, e => .test k (e1.substEnv 0 (RVal.rbEnv env)) e
  | .testL k v2, e => .test k e v2.rb

/-- Read a machine configuration back as a `Cfg`. -/
def EnvCfg.rb : EnvCfg rT → Cfg rT
  | .eval env e σ => ⟨e.substEnv 0 (RVal.rbEnv env), σ⟩
  | .apply f v σ => ⟨.app f.rb v.rb, σ⟩
  | .resume f v σ => ⟨f.fill v.rb, σ⟩

/-- Convert a value expression into a runtime value (with empty closure environments). -/
def RVal.ofExp : Exp rT → RVal rT
  | .lit b => .lit b
  | .lam body => .clo [] body
  | .fix body => .fixClo [] body
  | .pair e1 e2 => .pair (ofExp e1) (ofExp e2)
  | .inl e => .inl (ofExp e)
  | .inr e => .inr (ofExp e)
  | _ => .lit .unit

/-- `Pat.tryMatch` on runtime values. -/
def Pat.tryMatchR [BEq (BaseLit rT)] : Pat rT → RVal rT → Option (RVal rT)
  | .wildcard, v => some v
  | .lit b, .lit b' => if b == b' then some (.lit .unit) else none
  | .pair p1 p2, .pair v1 v2 => do
      let b1 ← p1.tryMatchR v1
      let b2 ← p2.tryMatchR v2
      return .pair b1 b2
  | .inl p, .inl v => p.tryMatchR v
  | .inr p, .inr v => p.tryMatchR v
  | _, _ => none

/-! ## The machine -/

variable [ProbLangℝ rT] [DecidableEq rT] {α : Type _}

/-- Resume a frame with the value of its subterm: evaluate the frame's next subterm, or
take the head step once every subterm is a value. -/
@[inline] def resumeK (k : StepOps rT α) : Frame rT → RVal rT → State rT → α
  | .pairR env e1, v2, σ => k.evalThen env e1 σ (.pairL v2)
  | .pairL v2, v1, σ => k.ret (.pair v1 v2) σ
  | .inl, v, σ => k.ret (.inl v) σ
  | .inr, v, σ => k.ret (.inr v) σ
  | .appR env e1, v2, σ => k.evalThen env e1 σ (.appL v2)
  | .appL v2, v1, σ => k.apply v1 v2 σ
  | .applyTo v, f, σ => k.apply f v σ
  | .unop op, v, σ =>
    match op.eval v.rb with
    | some v' => k.ret (.ofExp v') σ
    | none => k.stuck "unop: ill-typed operand"
  | .binopR op env e1, v2, σ => k.evalThen env e1 σ (.binopL op v2)
  | .binopL op v2, v1, σ =>
    match op.eval v1.rb v2.rb with
    | some v => k.ret (.ofExp v) σ
    | none => k.stuck "binop: ill-typed operands"
  | .cond env et ef, vc, σ =>
    match vc with
    | .lit (.bool true) => k.eval env et σ
    | .lit (.bool false) => k.eval env ef σ
    | _ => k.stuck "if: not a boolean"
  | .fst, v, σ =>
    match v with
    | .pair v1 _ => k.ret v1 σ
    | _ => k.stuck "fst: not a pair"
  | .snd, v, σ =>
    match v with
    | .pair _ v2 => k.ret v2 σ
    | _ => k.stuck "snd: not a pair"
  | .case env el er, vc, σ =>
    match vc with
    | .inl v => k.evalThen env el σ (.applyTo v)
    | .inr v => k.evalThen env er σ (.applyTo v)
    | _ => k.stuck "case: not a sum"
  | .scrut p, v, σ =>
    match p.tryMatchR v with
    | some bindings => k.ret (.inl bindings) σ
    | none => k.ret (.inr (.lit .unit)) σ
  | .alloc, v, σ =>
    match v.rb.toVal? with
    | some v =>
      let ℓ := σ.heap.fresh
      k.ret (.lit (.loc ℓ)) (σ.updateHeap fun t => t.insert ℓ v)
    | none => k.stuck "alloc: not a value"
  | .allocNR env en, v, σ => k.evalThen env en σ (.allocNL v)
  | .allocNL v, en, σ =>
    match en, v.rb.toVal? with
    | .lit (.int n), some v =>
      if 0 < n then
        k.ret (.lit (.loc σ.heap.fresh)) (σ.updateHeap (fun h => LocHeap.allocN h v n.toNat))
      else k.stuck "allocN: nonpositive length"
    | _, _ => k.stuck "allocN: invalid operands"
  | .load, v, σ =>
    match v with
    | .lit (.loc ℓ) =>
      match σ.heap[ℓ]? with
      | some v => k.ret (.ofExp v.1) σ
      | none => k.stuck "load: dangling location"
    | _ => k.stuck "load: not a location"
  | .storeR env e1, v2, σ => k.evalThen env e1 σ (.storeL v2)
  | .storeL v2, v1, σ =>
    match v1, v2.rb.toVal? with
    | .lit (.loc ℓ), some v =>
      match σ.heap[ℓ]? with
      | some _ => k.ret (.lit .unit) (σ.updateHeap fun t => t.insert ℓ v)
      | none => k.stuck "store: dangling location"
    | _, _ => k.stuck "store: not a location"
  | .tape n, v, σ =>
    match v.rb.toVal? with
    | some v =>
      let α := σ.tapes.fresh
      k.ret (.lit (.lbl α)) (σ.updateTapes fun t => t.insert α (.empty n v))
    | none => k.stuck "tape: not a value"
  | .sampleR n env e1, v2, σ => k.evalThen env e1 σ (.sampleL n v2)
  | .sampleL n v2, v1, σ =>
    match v1.rb.toVal?, v2 with
    | some v, .lit .unit => k.sample n v σ
    | some v, .lit (.lbl α) =>
      match σ.tapes[α]? with
      | none => k.stuck "sample: dangling tape"
      | some t =>
        if t.name = n ∧ t.arg = v then
          let σ' := σ.updateTapes fun ts => ts.insert α t.shift
          match t.head? with
          | none => k.sample n v σ'
          | some w => k.ret (.ofExp w.1) σ'
        else k.sample n v σ
    | _, _ => k.stuck "sample: ill-typed operands"
  | .ffi, _, _ => k.stuck "ffi: no foreign code"
  | .randvar n, v, σ =>
    match v.rb.toVal? with
    | some v =>
      let l := σ.rvs.fresh
      k.ret (.lit (.lbl l)) (σ.updateRvs fun t => t.insert l (RvCell.fresh n v))
    | none => k.stuck "randvar: not a value"
  | .testR k' env e1, v2, σ => k.evalThen env e1 σ (.testL k' v2)
  | .testL k' v2, v1, σ =>
    match v1, v2.rb.toVal? with
    | .lit (.lbl l), some a => k.test k' a l σ
    | _, _ => k.stuck "test: not a label"

/-- Start evaluating `e` under `env`: return it if it is a value former with nothing to
evaluate, or evaluate its rightmost subterm under the matching frame. -/
@[inline] def evalK (k : StepOps rT α) (env : Env rT) : Exp rT → State rT → α
  | .bvar j, σ =>
    match env[j]? with
    | some v => k.ret v σ
    | none => k.stuck "unbound de Bruijn index"
  | .fvar _, _ => k.stuck "free variable"
  | .fail, _ => k.stuck "fail"
  | .lit b, σ => k.ret (.lit b) σ
  | .lam body, σ => k.ret (.clo env body) σ
  | .fix body, σ => k.ret (.fixClo env body) σ
  | .pair e1 e2, σ => k.evalThen env e2 σ (.pairR env e1)
  | .inl e, σ => k.evalThen env e σ .inl
  | .inr e, σ => k.evalThen env e σ .inr
  | .app e1 e2, σ => k.evalThen env e2 σ (.appR env e1)
  | .unop op e, σ => k.evalThen env e σ (.unop op)
  | .binop op e1 e2, σ => k.evalThen env e2 σ (.binopR op env e1)
  | .cond ec et ef, σ => k.evalThen env ec σ (.cond env et ef)
  | .fst e, σ => k.evalThen env e σ .fst
  | .snd e, σ => k.evalThen env e σ .snd
  | .case ec el er, σ => k.evalThen env ec σ (.case env el er)
  | .scrut e p, σ => k.evalThen env e σ (.scrut p)
  | .alloc e, σ => k.evalThen env e σ .alloc
  | .load e, σ => k.evalThen env e σ .load
  | .store e1 e2, σ => k.evalThen env e2 σ (.storeR env e1)
  | .allocN e1 e2, σ => k.evalThen env e2 σ (.allocNR env e1)
  | .tape n e, σ => k.evalThen env e σ (.tape n)
  | .ffi e, σ => k.evalThen env e σ .ffi
  | .sample n e et, σ => k.evalThen env et σ (.sampleR n env e)
  | .randvar n e, σ => k.evalThen env e σ (.randvar n)
  | .test k' e1 e2, σ => k.evalThen env e2 σ (.testR k' env e1)

/-- Apply the function value `f` to `v` through the operations `k`. -/
@[inline] def applyK (k : StepOps rT α) : RVal rT → RVal rT → State rT → α
  | .clo env body, v, σ => k.eval (v :: env) body σ
  | f@(.fixClo env body), v, σ => k.evalThen (f :: env) body σ (.applyTo v)
  | _, _, _ => k.stuck "app: not a function"

/-- One step of the environment machine. -/
def envStep : EnvCfg rT → Step rT
  | .eval env e σ => evalK stepOps env e σ
  | .apply f v σ => applyK stepOps f v σ
  | .resume f v σ => resumeK stepOps f v σ

end ProbLang
