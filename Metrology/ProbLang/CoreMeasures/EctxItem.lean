module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.Val
public import Metrology.ProbLang.CoreMeasures.Cylinders

meta import Metrology.Meta
meta import Metrology.ProbLang.CoreMeasures.CylinderGen

@[expose] public section

-- TODO move this to the semantics file once we have that.

noncomputable section ProbLangMeasures

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

/-! # Measure space on evaluation-context items -/

namespace ProbLang.EctxItem

/-! `cylinder_defs` generates the cylinder σ-algebra, measurable constructors, embeddings and
projections, and the `casesOn` keystones `measurable_rec` / `measurable_rec_param`. -/

cylinder_defs EctxItem

/-! ### Smoke tests

`EctxItem` is not recursive, so each test goes through `measurable_rec` or `measurable_rec_param`
and exercises all 21 constructor slots. -/

/-- Discrete codomain. -/
@[simp] def tagDepth : EctxItem α → Nat
  | .appL _    => 0
  | .appR _    => 1
  | .unop _    => 2
  | .binopL _ _ => 3
  | .binopR _ _ => 4
  | .condC _ _ => 5
  | .pairL _   => 6
  | .pairR _   => 7
  | .fst       => 8
  | .snd       => 9
  | .inl       => 10
  | .inr       => 11
  | .case _ _  => 12
  | .alloc     => 13
  | .load      => 14
  | .storeL _  => 15
  | .storeR _  => 16
  | .tape      => 17
  | .randL _   => 18
  | .randR _   => 19
  | .scrut _   => 20

theorem tagDepth.measurable [MeasurableSpace α] :
    Measurable (tagDepth : EctxItem α → Nat) := by
  have heq : (tagDepth : EctxItem α → Nat)
    = (fun K : EctxItem α => EctxItem.casesOn (motive := fun _ => Nat) K
        (fun _ => 0) (fun _ => 1) (fun _ => 2)
        (fun _ _ => 3) (fun _ _ => 4) (fun _ _ => 5)
        (fun _ => 6) (fun _ => 7)
        8 9 10 11 (fun _ _ => 12) 13 14
        (fun _ => 15) (fun _ => 16) 17 (fun _ => 18) (fun _ => 19) (fun _ => 20)) := by
    funext K; cases K <;> rfl
  rw [heq]
  apply measurable_rec
    (f_appL := fun _ => 0) (f_appR := fun _ => 1) (f_unop := fun _ => 2)
    (f_binopL := fun _ => 3) (f_binopR := fun _ => 4) (f_condC := fun _ => 5)
    (f_pairL := fun _ => 6) (f_pairR := fun _ => 7)
    (f_fst := fun _ => 8) (f_snd := fun _ => 9) (f_inl := fun _ => 10) (f_inr := fun _ => 11)
    (f_case := fun _ => 12) (f_alloc := fun _ => 13) (f_load := fun _ => 14)
    (f_storeL := fun _ => 15) (f_storeR := fun _ => 16) (f_tape := fun _ => 17)
    (f_randL := fun _ => 18) (f_randR := fun _ => 19) (f_scrut := fun _ => 20)
  all_goals fun_prop

/-- Depends on whether a constructor carries a payload. -/
@[simp] def countLeaves : EctxItem α → Nat
  | .appL _    => 1
  | .appR _    => 1
  | .unop _    => 1
  | .binopL _ _ => 1
  | .binopR _ _ => 1
  | .condC _ _ => 1
  | .pairL _   => 1
  | .pairR _   => 1
  | .fst       => 0
  | .snd       => 0
  | .inl       => 0
  | .inr       => 0
  | .case _ _  => 1
  | .alloc     => 0
  | .load      => 0
  | .storeL _  => 1
  | .storeR _  => 1
  | .tape      => 0
  | .randL _   => 1
  | .randR _   => 1
  | .scrut _   => 1

theorem countLeaves.measurable [MeasurableSpace α] :
    Measurable (countLeaves : EctxItem α → Nat) := by
  have heq : (countLeaves : EctxItem α → Nat)
    = (fun K : EctxItem α => EctxItem.casesOn (motive := fun _ => Nat) K
        (fun _ => 1) (fun _ => 1) (fun _ => 1)
        (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1)
        (fun _ => 1) (fun _ => 1)
        0 0 0 0 (fun _ _ => 1) 0 0
        (fun _ => 1) (fun _ => 1) 0 (fun _ => 1) (fun _ => 1) (fun _ => 1)) := by
    funext K; cases K <;> rfl
  rw [heq]
  apply measurable_rec
    (f_appL := fun _ => 1) (f_appR := fun _ => 1) (f_unop := fun _ => 1)
    (f_binopL := fun _ => 1) (f_binopR := fun _ => 1) (f_condC := fun _ => 1)
    (f_pairL := fun _ => 1) (f_pairR := fun _ => 1)
    (f_fst := fun _ => 0) (f_snd := fun _ => 0) (f_inl := fun _ => 0) (f_inr := fun _ => 0)
    (f_case := fun _ => 1) (f_alloc := fun _ => 0) (f_load := fun _ => 0)
    (f_storeL := fun _ => 1) (f_storeR := fun _ => 1) (f_tape := fun _ => 0)
    (f_randL := fun _ => 1) (f_randR := fun _ => 1) (f_scrut := fun _ => 1)
  all_goals fun_prop

/-- Non-discrete codomain; only `appR` transforms its payload. -/
@[simp] def endoMap : EctxItem α → EctxItem α
  | .appL v    => .appL v
  | .appR e    => .appR (Exp.fst e)
  | .unop u    => .unop u
  | .binopL op v => .binopL op v
  | .binopR op e => .binopR op e
  | .condC e1 e2 => .condC e1 e2
  | .pairL v   => .pairL v
  | .pairR e   => .pairR e
  | .fst       => .fst
  | .snd       => .snd
  | .inl       => .inl
  | .inr       => .inr
  | .case e1 e2 => .case e1 e2
  | .alloc     => .alloc
  | .load      => .load
  | .storeL v  => .storeL v
  | .storeR e  => .storeR e
  | .tape      => .tape
  | .randL v   => .randL v
  | .randR e   => .randR e
  | .scrut p   => .scrut p

theorem endoMap.measurable [MeasurableSpace α] :
    Measurable (endoMap : EctxItem α → EctxItem α) := by
  have heq : (endoMap : EctxItem α → EctxItem α)
    = (fun K : EctxItem α => EctxItem.casesOn (motive := fun _ => EctxItem α) K
        EctxItem.appL (fun e => EctxItem.appR (Exp.fst e)) EctxItem.unop
        EctxItem.binopL EctxItem.binopR EctxItem.condC
        EctxItem.pairL EctxItem.pairR
        EctxItem.fst EctxItem.snd EctxItem.inl EctxItem.inr
        EctxItem.case EctxItem.alloc EctxItem.load
        EctxItem.storeL EctxItem.storeR EctxItem.tape
        EctxItem.randL EctxItem.randR EctxItem.scrut) := by
    funext K; cases K <;> rfl
  rw [heq]
  apply measurable_rec
    (f_appL := EctxItem.appL) (f_appR := fun e => EctxItem.appR (Exp.fst e))
    (f_unop := EctxItem.unop)
    (f_binopL := fun q : BinOp × Val α => EctxItem.binopL q.1 q.2)
    (f_binopR := fun q : BinOp × Exp α => EctxItem.binopR q.1 q.2)
    (f_condC := fun q : Exp α × Exp α => EctxItem.condC q.1 q.2)
    (f_pairL := EctxItem.pairL) (f_pairR := EctxItem.pairR)
    (f_fst := fun _ => EctxItem.fst) (f_snd := fun _ => EctxItem.snd)
    (f_inl := fun _ => EctxItem.inl) (f_inr := fun _ => EctxItem.inr)
    (f_case := fun q : Exp α × Exp α => EctxItem.case q.1 q.2)
    (f_alloc := fun _ => EctxItem.alloc) (f_load := fun _ => EctxItem.load)
    (f_storeL := EctxItem.storeL) (f_storeR := EctxItem.storeR)
    (f_tape := fun _ => EctxItem.tape)
    (f_randL := EctxItem.randL) (f_randR := EctxItem.randR)
    (f_scrut := EctxItem.scrut)
  all_goals fun_prop

/-- Threads a parameter through `measurable_rec_param`. -/
@[simp] def addAcc : Nat → EctxItem α → Nat
  | acc, .appL _    => acc + 1
  | acc, .appR _    => acc + 1
  | acc, _          => acc

theorem addAcc.measurable [MeasurableSpace α] :
    Measurable (fun p : EctxItem α × Nat => addAcc p.2 p.1) := by
  have heq : (fun p : EctxItem α × Nat => addAcc p.2 p.1)
    = (fun p : EctxItem α × Nat => EctxItem.casesOn (motive := fun _ => Nat) p.1
        (fun _ => p.2 + 1) (fun _ => p.2 + 1) (fun _ => p.2)
        (fun _ _ => p.2) (fun _ _ => p.2) (fun _ _ => p.2)
        (fun _ => p.2) (fun _ => p.2)
        p.2 p.2 p.2 p.2 (fun _ _ => p.2) p.2 p.2
        (fun _ => p.2) (fun _ => p.2) p.2 (fun _ => p.2) (fun _ => p.2) (fun _ => p.2)) := by
    funext ⟨K, _⟩; cases K <;> rfl
  rw [heq]
  apply measurable_rec_param
    (c_appL := fun q : Nat × Val α => q.1 + 1) (c_appR := fun q : Nat × Exp α => q.1 + 1)
    (c_unop := fun q : Nat × UnOp => q.1)
    (c_binopL := fun q : Nat × BinOp × Val α => q.1)
    (c_binopR := fun q : Nat × BinOp × Exp α => q.1)
    (c_condC := fun q : Nat × Exp α × Exp α => q.1)
    (c_pairL := fun q : Nat × Val α => q.1) (c_pairR := fun q : Nat × Exp α => q.1)
    (c_fst := fun q : Nat × Unit => q.1) (c_snd := fun q : Nat × Unit => q.1)
    (c_inl := fun q : Nat × Unit => q.1) (c_inr := fun q : Nat × Unit => q.1)
    (c_case := fun q : Nat × Exp α × Exp α => q.1)
    (c_alloc := fun q : Nat × Unit => q.1) (c_load := fun q : Nat × Unit => q.1)
    (c_storeL := fun q : Nat × Val α => q.1) (c_storeR := fun q : Nat × Exp α => q.1)
    (c_tape := fun q : Nat × Unit => q.1)
    (c_randL := fun q : Nat × Val α => q.1) (c_randR := fun q : Nat × Exp α => q.1)
    (c_scrut := fun q : Nat × Pat α => q.1)
  all_goals fun_prop
