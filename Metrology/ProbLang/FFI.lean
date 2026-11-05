module

public import Metrology.ProbLang.CoreMeasures

/-! # Foreign calls

`ffi e` runs foreign code on the value of `e` and the heap; `ProbLangFFI rT` says what each call
does, and `ProbLangFFI.Stuck` says that every call is stuck. -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace ProbLang

open Val

variable {rT : Type _}

/-- What a foreign step hands back to ProbLang, besides the new heap. -/
inductive FFIOutcome (rT : Type _)
  /-- Return the value `v`. -/
  | ret (v : Val rT)
  /-- Call `f` on `a`, then resume foreign code with the pair of the resume token `r` and the
  result. -/
  | call (f a r : Val rT)
  /-- Step to `fail`. -/
  | fail

namespace FFIOutcome

/-- An outcome as a sum, which gives it its σ-algebra. -/
def toSum : FFIOutcome rT → Val rT ⊕ (Val rT × Val rT × Val rT) ⊕ Unit
  | ret v => .inl v
  | call f a r => .inr (.inl (f, a, r))
  | fail => .inr (.inr ())

/-- `toSum` is injective. -/
theorem toSum_injective : Function.Injective (toSum (rT := rT)) := by
  rintro (_ | _ | _) (_ | _ | _) h <;> simp_all [toSum]

/-- The expression ProbLang continues with after the outcome. -/
def toExp : FFIOutcome rT → Exp rT
  | ret v => v.fst
  | call f a r => .ffi (.pair r.fst (.app f.fst a.fst))
  | fail => .fail

variable [MeasurableSpace rT]

/-- The σ-algebra of outcomes: the pullback of the sum σ-algebra along `toSum`. -/
instance instMeasurableSpace : MeasurableSpace (FFIOutcome rT) :=
  MeasurableSpace.comap toSum inferInstance

/-- `toSum` is measurable. -/
theorem measurable_toSum : Measurable (toSum (rT := rT)) :=
  comap_measurable _

/-- A map into outcomes is measurable when its `toSum` image is. -/
theorem measurable_of_toSum {X : Type _} [MeasurableSpace X] {f : X → FFIOutcome rT}
    (hf : Measurable fun x => (f x).toSum) : Measurable f :=
  measurable_comap_iff.mpr hf

/-- `ret` is measurable. -/
theorem ret.measurable : Measurable (ret : Val rT → FFIOutcome rT) :=
  measurable_of_toSum measurable_inl

/-- `call` is measurable in the function, the argument and the resume token. -/
theorem call.measurable :
    Measurable (fun p : Val rT × Val rT × Val rT => call p.1 p.2.1 p.2.2) :=
  measurable_of_toSum (measurable_inr.comp measurable_inl)

/-- `toExp` is measurable. -/
theorem toExp.measurable : Measurable (toExp (rT := rT)) := by
  have hcall : Measurable fun p : Val rT × Val rT × Val rT =>
      Exp.ffi (.pair p.2.2.fst (.app p.1.fst p.2.1.fst)) :=
    Exp.ffi.measurable.comp (Exp.pair.measurable.comp
      ((fst.measurable.comp (measurable_snd.comp measurable_snd)).prodMk
        (Exp.app.measurable.comp ((fst.measurable.comp measurable_fst).prodMk
          (fst.measurable.comp (measurable_fst.comp measurable_snd))))))
  have h : toExp (rT := rT) =
      Sum.elim fst (Sum.elim (fun p => .ffi (.pair p.2.2.fst (.app p.1.fst p.2.1.fst)))
        fun _ => .fail) ∘
        toSum := by
    funext o; cases o <;> rfl
  rw [h]
  exact (fst.measurable.sumElim (hcall.sumElim measurable_const)).comp measurable_toSum

end FFIOutcome

/-- The code handle and the argument of a call value `(#code n, a)`. -/
def Val.codeArg? (v : Val rT) : Option (ℕ × Val rT) :=
  (Exp.pair.π v.fst).bind fun p => ((Exp.lit.π p.1).bind BaseLit.code.π).bind fun n =>
    p.2.toVal?.map (n, ·)

@[simp] theorem Val.codeArg?_pair_code (n : ℕ) (a : Val rT) :
    ((code n).pair a).codeArg? = some (n, a) := by
  simp [codeArg?]

variable [MeasurableSpace rT]

/-- `Val.codeArg?` is measurable. -/
theorem Val.codeArg?.measurable :
    Measurable (codeArg? (rT := rT)) := by
  have hn : Measurable fun p : Exp rT × Exp rT => (Exp.lit.π p.1).bind BaseLit.code.π :=
    Option.measurable_bind_param (Exp.lit.π.measurable.comp measurable_fst)
      (BaseLit.code.π.measurable.comp measurable_snd)
  have harg : Measurable fun q : (Exp rT × Exp rT) × ℕ => q.1.2.toVal?.map (q.2, ·) :=
    measurable_from_prod_countable_left fun n =>
      (measurable_const.prodMk measurable_id).option_map.comp
        (Exp.toVal_question.measurable.comp measurable_snd)
  exact Option.measurable_bind_param (Exp.pair.π.measurable.comp fst.measurable)
    (Option.measurable_bind_param (hn.comp measurable_snd) (harg.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))

/-- The meaning of `ffi`: a measurable partial map from the argument and the heap to an outcome
and a new heap, where `none` means stuck. -/
class ProbLangFFI (rT : Type _) [MeasurableSpace rT] where
  /-- The step `ffi` takes. -/
  ffi : Val rT × LocHeap (Val rT) → Option (FFIOutcome rT × LocHeap (Val rT))
  /-- The step is measurable. -/
  measurable_ffi : Measurable ffi

/-- The foreign code where every call is stuck. -/
@[instance_reducible]
def ProbLangFFI.stuck : ProbLangFFI rT where
  ffi _ := Option.none
  measurable_ffi := measurable_const

/-- The foreign code that runs `step n` on a call `(#code n, a)` and is stuck on any other
argument. -/
@[instance_reducible]
def ProbLangFFI.ofCode
    (step : ℕ → Val rT × LocHeap (Val rT) → Option (FFIOutcome rT × LocHeap (Val rT)))
    (hstep : ∀ n, Measurable (step n) := by fun_prop) : ProbLangFFI rT where
  ffi x := x.1.codeArg?.bind fun p => step p.1 (p.2, x.2)
  measurable_ffi := by
    have hg : Measurable fun q : ℕ × (Val rT × LocHeap (Val rT)) => step q.1 q.2 :=
      measurable_from_prod_countable_right hstep
    exact Option.measurable_bind_param (codeArg?.measurable.comp measurable_fst)
      (hg.comp ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_snd.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst))))

/-- `ProbLangFFI.ofCode` runs `step n` on a call `(#code n, a)`. -/
@[simp] theorem ProbLangFFI.ofCode_ffi
    {step : ℕ → Val rT × LocHeap (Val rT) → Option (FFIOutcome rT × LocHeap (Val rT))}
    {hstep : ∀ n, Measurable (step n)} (n : ℕ) (a : Val rT) (h : LocHeap (Val rT)) :
    (ofCode step hstep).ffi ((code n).pair a, h) = step n (a, h) := by
  change ((code n).pair a).codeArg?.bind (fun p => step p.1 (p.2, h)) = _
  simp

/-- Every foreign call is stuck. -/
class ProbLangFFI.Stuck (rT : Type _) [MeasurableSpace rT] [ProbLangFFI rT] : Prop where
  /-- Every foreign step is stuck. -/
  ffi_eq_none (x : Val rT × LocHeap (Val rT)) : ProbLangFFI.ffi x = Option.none

attribute [simp] ProbLangFFI.Stuck.ffi_eq_none

/-- In `ProbLangFFI.stuck`, every foreign call is stuck. -/
instance : @ProbLangFFI.Stuck rT _ ProbLangFFI.stuck :=
  @ProbLangFFI.Stuck.mk rT _ ProbLangFFI.stuck fun _ => rfl

end ProbLang
