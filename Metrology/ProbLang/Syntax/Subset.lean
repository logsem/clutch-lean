module

public meta import Lean.Elab.Command
public meta import Lean.Elab.Term
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.Meta.Settings

/-! # Syntactic subsets of ProbLang

Feature sets, membership of expressions in the subset they allow, its closure lemmas, and the
`subset` clause of the `problang` panel. -/

@[expose] public section

namespace ProbLang

variable {rT : Type _}

/-! ## Samplers -/

/-- Whether the expression may draw from a non-discrete distribution family. -/
def Exp.isSampler : Exp rT → Bool
  | .sample n _ _ => n != unifIntName
  | _ => false

/-- The expression may draw from a non-discrete distribution family. -/
abbrev Exp.IsSampler (e : Exp rT) : Prop := e.isSampler = true

@[simp] theorem Exp.isSampler_urand : (Exp.urand : Exp rT).IsSampler := rfl

@[simp] theorem Exp.isSampler_sample {n : ℕ} (hn : n ≠ unifIntName) (e et : Exp rT) :
    (Exp.sample n e et).IsSampler := by
  simp [Exp.IsSampler, Exp.isSampler, bne_iff_ne, hn]

@[simp] theorem Exp.not_isSampler_rand (e et : Exp rT) : ¬(Exp.rand e et).IsSampler := by
  simp [Exp.IsSampler, Exp.isSampler, unifIntName]

/-! ## Features and membership -/

/-- The optional features of ProbLang, which a syntactic subset may leave out. -/
inductive Feature
  /-- Continuous sampling, `urand`. -/
  | urand
  /-- Tape allocation and tape reads. -/
  | tape
  /-- Sampling from a user distribution family. -/
  | sample
  /-- Foreign calls `ffi e` and foreign code handles `#code n`. -/
  | ffi
  /-- Random variables, `randvar n e` and `test k ec ea`. -/
  | randvar
  deriving DecidableEq, Repr

/-- A syntactic subset of ProbLang, given by the features it allows. -/
abbrev Features := Feature → Bool

/-- The subset allowing every feature: full ProbLang. -/
def Features.all : Features := fun _ => true

/-- The subset allowing every feature except those listed. -/
def Features.without (l : List Feature) : Features := fun f => !l.contains f

section Membership

variable (F : Features)

/-- Whether a distribution family is available in the subset. -/
def Features.allowsFamily (n : ℕ) : Bool :=
  if n = unifIntName then true else if n = unifRealName then F .urand else F .sample

/-- Whether a sampler's tape argument is fresh-draw syntax or requires tapes. -/
def Features.allowsTapeArg : Exp rT → Bool
  | .lit .unit => true
  | _ => F .tape

/-- Enabling tapes permits every tape argument. -/
theorem Features.allowsTapeArg_of_tape (e : Exp rT) (h : F .tape = true) :
    F.allowsTapeArg e = true := by
  cases e <;> try exact h
  case lit b => cases b <;> first | rfl | exact h

/-- A non-value tape argument requires the tape feature. -/
theorem Features.allowsTapeArg_eq_tape (e : Exp rT) (he : ¬e.isValue) :
    F.allowsTapeArg e = F .tape := by
  cases e <;> try rfl
  case lit => exact (he ⟨.lit⟩).elim

/-- Opening an allowed tape argument keeps it allowed. -/
theorem Features.allowsTapeArg_openRec {e s : Exp rT} (h : F.allowsTapeArg e = true) (i : ℕ) :
    F.allowsTapeArg (Exp.openRec i s e) = true := by
  cases e <;> simp_all [Features.allowsTapeArg, Exp.openRec]
  case bvar =>
    split <;> simp_all

/-- Every construct of the expression is allowed by `F`. -/
def Exp.inSubset : Exp rT → Bool
  | .tape _ e => F .tape && e.inSubset
  | .sample n e et =>
      F.allowsFamily n && F.allowsTapeArg et && e.inSubset && et.inSubset
  | .ffi e => F .ffi && e.inSubset
  | .lit (.code _) => F .ffi
  | .randvar _ e => F .randvar && e.inSubset
  | .test _ e1 e2 => F .randvar && e1.inSubset && e2.inSubset
  | .bvar _ | .fvar _ | .lit _ | .fail => true
  | .lam e | .fix e | .unop _ e | .fst e | .snd e | .inl e | .inr e | .alloc e | .load e
  | .scrut e _ => e.inSubset
  | .app e1 e2 | .binop _ e1 e2 | .pair e1 e2 | .store e1 e2 | .allocN e1 e2 =>
      e1.inSubset && e2.inSubset
  | .cond e0 e1 e2 | .case e0 e1 e2 => e0.inSubset && e1.inSubset && e2.inSubset

/-- The expression lies in the syntactic subset `F`. -/
abbrev Exp.InSubset (e : Exp rT) : Prop := e.inSubset F = true

/-- The value lies in the syntactic subset `F`. -/
abbrev Val.InSubset (v : Val rT) : Prop := v.1.InSubset F

/-- Every frame of the context lies in the syntactic subset `F`. -/
def Ectx.InSubset (K : Ectx rT) : Prop :=
  ∀ Ki ∈ K, (Ki.fillItem (.fvar (.internal 0))).InSubset F

/-- Every value stored in the heap or tapes lies in the syntactic subset `F`. -/
def State.InSubset (σ : State rT) : Prop :=
  (∀ (ℓ : Loc) (v : Val rT), σ.heap[ℓ]? = some v → v.InSubset F) ∧
    ∀ (α : Lbl) (t : Tape rT), σ.tapes[α]? = some t →
      t.arg.InSubset F ∧ ∀ k w, t.presamples k = some w → w.InSubset F

/-- The expression and the heap of the configuration lie in the syntactic subset `F`. -/
def Cfg.InSubset (ρ : Cfg rT) : Prop :=
  ρ.expr.InSubset F ∧ ρ.state.InSubset F

end Membership

/-! ## Syntactic closure -/

variable {F : Features}

/-- Filling an allowed frame with an allowed expression stays in the subset. -/
theorem EctxItem.inSubset_fillItem_mpr (Ki : EctxItem rT) (e : Exp rT)
    (h : (Ki.fillItem (.fvar (.internal 0))).InSubset F ∧ e.InSubset F) :
    (Ki.fillItem e).InSubset F := by
  cases Ki <;>
    simp_all [Exp.InSubset, Exp.inSubset, and_comm, and_left_comm]
  case sampleR =>
    apply Features.allowsTapeArg_of_tape
    simpa [Features.allowsTapeArg] using h.2.2.2

/-- A frame filled with a non-value lies in a subset exactly when the frame and term do. -/
theorem EctxItem.inSubset_fillItem (Ki : EctxItem rT) (e : Exp rT) (he : ¬e.isValue) :
    (Ki.fillItem e).InSubset F ↔
      (Ki.fillItem (.fvar (.internal 0))).InSubset F ∧ e.InSubset F := by
  cases Ki <;>
    simp_all [Exp.InSubset, Exp.inSubset, and_comm, and_assoc, and_left_comm]
  case sampleR =>
    rw [Features.allowsTapeArg_eq_tape F e he]
    simp [Features.allowsTapeArg]

/-- Filling an allowed context with an allowed expression stays in the subset. -/
theorem Ectx.inSubset_fill_mpr (K : Ectx rT) (e : Exp rT) :
    K.InSubset F ∧ e.InSubset F → (K.fill e).InSubset F := by
  induction K generalizing e with
  | nil => simp [Ectx.InSubset, Ectx.fill]
  | cons Ki K ih =>
    rintro ⟨hK, he⟩
    apply ih
    refine ⟨?_, EctxItem.inSubset_fillItem_mpr Ki e ⟨hK Ki (by simp), he⟩⟩
    intro Kj hKj
    exact hK Kj (by simp [hKj])

/-- A context filled with a non-value lies in a subset exactly when both parts do. -/
theorem Ectx.inSubset_fill (K : Ectx rT) (e : Exp rT) (he : ¬e.isValue) :
    (K.fill e).InSubset F ↔ K.InSubset F ∧ e.InSubset F := by
  induction K generalizing e with
  | nil => simp [Ectx.InSubset, Ectx.fill]
  | cons Ki K ih =>
    rw [show Ectx.fill (Ki :: K) e = Ectx.fill K (Ki.fillItem e) from rfl,
      ih (Ki.fillItem e) (EctxItem.fillItem_noVal he), EctxItem.inSubset_fillItem Ki e he]
    simp only [Ectx.InSubset, List.mem_cons, forall_eq_or_imp]
    tauto

namespace Exp.InSubset

variable {e : Exp rT} (h : e.InSubset F)
include h

/-- Outside a subset allowing `urand` and user families, an expression is no sampler. -/
theorem not_isSampler (hu : F .urand = false) (hs : F .sample = false) :
    ¬ e.IsSampler := by
  cases e <;>
    simp_all [Exp.InSubset, inSubset, isSampler, Features.allowsFamily, unifIntName,
      unifRealName]

/-- Outside a subset allowing tapes, an expression is no tape allocation. -/
theorem ne_tape (hF : F .tape = false) (n : ℕ) (e' : Exp rT) : e ≠ .tape n e' := by
  rintro rfl
  simp_all [Exp.InSubset, inSubset]

/-- Outside a subset allowing foreign calls, an expression is no foreign call. -/
theorem ne_ffi (hF : F .ffi = false) : ∀ e', e ≠ .ffi e' := by
  rintro e' rfl
  simp_all [Exp.InSubset, inSubset]

/-- Outside a subset allowing random variables, an expression is no `randvar`. -/
theorem ne_randvar (hF : F .randvar = false) : ∀ n e', e ≠ .randvar n e' := by
  rintro n e' rfl
  simp_all [Exp.InSubset, inSubset]

/-- Outside a subset allowing random variables, an expression is no `test`. -/
theorem ne_test (hF : F .randvar = false) : ∀ k e1 e2, e ≠ .test k e1 e2 := by
  rintro k e1 e2 rfl
  simp_all [Exp.InSubset, inSubset]

/-- Opening with a term of the subset stays in the subset. -/
theorem openRec {s : Exp rT} (hs : s.InSubset F) (i : Nat) : (Exp.openRec i s e).InSubset F := by
  induction e generalizing i with
  | bvar j =>
    simp only [Exp.openRec]
    split <;> simp_all [Exp.InSubset, inSubset]
  | sample n e et ihe ihet =>
      simp_all [Exp.InSubset, inSubset, Exp.openRec, Features.allowsTapeArg_openRec]
  | _ => simp_all [Exp.InSubset, inSubset, Exp.openRec]

/-- `open'` with a term of the subset stays in the subset. -/
theorem open' {s : Exp rT} (hs : s.InSubset F) : (Exp.open' e s).InSubset F :=
  h.openRec hs 0

/-- The evaluation context and the redex of an expression in a subset lie in the subset. -/
theorem decomp : e.decomp.1.InSubset F ∧ e.decomp.2.InSubset F := by
  rcases hd : e.decomp with ⟨K, e'⟩
  have hfill : K.fill e' = e := Exp.decomp_fill hd
  by_cases hv : e'.isValue
  · have hK : K = [] := Exp.decomp_val_empty hd hv
    subst K
    have heq : e' = e := by simpa [Ectx.fill] using hfill
    rw [heq]
    simpa [Ectx.InSubset] using h
  · rw [← hfill, Ectx.inSubset_fill K e' hv] at h
    exact h

/-- Outside a subset allowing `urand` and user families, the redex is no sampler. -/
theorem decomp_snd_not_isSampler (hu : F .urand = false) (hs : F .sample = false) :
    ¬ e.decomp.2.IsSampler :=
  h.decomp.2.not_isSampler hu hs

end Exp.InSubset

section WithRealParam

variable [ProbLangℝ rT]

/-- The result of a unary operator lies in every subset. -/
theorem UnOp.inSubset_eval {op : UnOp} {v e : Exp rT} (h : op.eval v = some e) :
    e.InSubset F := by
  unfold UnOp.eval at h
  split at h <;> cases h <;> rfl

/-- The result of a binary operator lies in every subset. -/
theorem BinOp.inSubset_eval {op : BinOp} {v1 v2 e : Exp rT} (h : op.eval v1 v2 = some e) :
    e.InSubset F := by
  unfold BinOp.eval at h
  split at h <;> cases h <;> rfl

/-- The bindings of a successful match of a term in a subset lie in the subset. -/
theorem Pat.inSubset_tryMatch {p : Pat rT} {e b : Exp rT} (he : e.InSubset F)
    (h : p.tryMatch e = some b) : b.InSubset F := by
  induction p generalizing e b with
  | wildcard => cases h; exact he
  | lit l =>
    cases e <;> simp only [Pat.tryMatch, reduceCtorEq] at h
    split at h <;> cases h
    rfl
  | pair p1 p2 ih1 ih2 =>
    cases e <;> simp only [Pat.tryMatch, reduceCtorEq] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b1, h1, b2, h2, rfl⟩ := h
    simp only [Exp.InSubset, Exp.inSubset, Bool.and_eq_true] at he ⊢
    exact ⟨ih1 he.1 h1, ih2 he.2 h2⟩
  | inl p ih | inr p ih =>
    cases e <;> simp only [Pat.tryMatch, reduceCtorEq] at h
    exact ih (by simpa [Exp.InSubset, Exp.inSubset] using he) h

end WithRealParam

/-! ## The `subset` clause of the `problang` panel -/

open Lean Elab Command Term Metrology.Settings

/-- The section's feature set, from the panel's `subset` clause, or `Features.all`. -/
elab "subset%" : term => do
  let F ← match ← getSetting? `subset with
    | some F => pure F
    | none => `(Features.all)
  elabTerm F (some (mkConst ``Features))

/-- `subset -f₁ … -fₙ`: the section's subset leaves out the features `fᵢ`. -/
syntax (name := subsetOpt) &"subset" (ppSpace "-" noWs rawIdent)* : problang_opt

/-- Elaborates the `subset` clause, checking that each name is a `Feature`. -/
elab_rules : command
  | `(problang_clause $c) => do
    unless c.raw.isOfKind ``subsetOpt do throwUnsupportedSyntax
    let feats ← c.raw[1].getArgs.mapM fun arg => do
      let f : Ident := ⟨arg[1]⟩
      let n := ``Feature ++ f.getId
      unless (← getEnv).contains n do
        throwErrorAt f "unknown ProbLang feature `{f.getId}`"
      return mkIdentFrom f n
    let F ← `(Features.without [$feats,*])
    runTermElabM fun _ => discard <| elabTerm F (some (mkConst ``Features))
    setSetting `subset F

/-! ## Side-condition tactics -/

/-- Proves `e.InSubset F` at a concrete program, from hypotheses for its free parts. -/
syntax "in_subset" : tactic

macro_rules
  | `(tactic| in_subset) => `(tactic| first
      | assumption
      | rfl
      | (simp only [Exp.InSubset, Exp.inSubset, Val.InSubset, Exp.ofVal, Bool.and_eq_true] at *
         simp_all))

/-- Discharges `¬ e.IsSampler` and `¬ e.decomp.2.IsSampler` from a subset hypothesis and the panel's
`subset` clause. -/
syntax "subset_side" : tactic

open Exp.InSubset in
macro_rules
  | `(tactic| subset_side) => `(tactic| first
      | exact not_isSampler (F := subset%) (by in_subset) rfl rfl
      | exact decomp_snd_not_isSampler (F := subset%) (by in_subset) rfl rfl)

/-- Discharges ProbLang side conditions such as `¬ e.IsSampler`, from a subset hypothesis or by
computation; later layers extend it by `macro_rules` that try `subset_side` first. -/
syntax "problang_side" : tactic

macro_rules | `(tactic| problang_side) => `(tactic| first | subset_side | nofun)

end ProbLang
