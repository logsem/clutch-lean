module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.BaseLit
public import Metrology.ProbLang.CoreMeasures.Exp
public import Metrology.ProbLang.CoreMeasures.Pat
public import Metrology.ProbLang.CoreMeasures.EctxItem
public import Metrology.ProbLang.CoreMeasures.Shapes

meta import Metrology.Meta

@[expose] public section

/-! # Smoke tests for the `CoreMeasures` σ-algebras

Synthetic functions on `BaseLit`, `Exp`, `Pat` and `EctxItem` whose measurability exercises every
constructor slot of the generated `casesOn` keystones. -/

noncomputable section ProbLangMeasures

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

namespace ProbLang.BaseLit

variable {rT : Type _}

/-! ## Smoke tests: each one exercises every constructor slot of a keystone. -/

/-- The index of the constructor. -/
@[simp] def tagDepth : BaseLit rT → Nat
  | .int _  => 0
  | .bool _ => 1
  | .unit   => 2
  | .loc _  => 3
  | .lbl _  => 4
  | .real _ => 5

theorem tagDepth.measurable [MeasurableSpace rT] [Inhabited rT] :
    Measurable (tagDepth : BaseLit rT → Nat) := by
  have heq : (tagDepth : BaseLit rT → Nat)
    = (fun b : BaseLit rT =>
        BaseLit.casesOn (motive := fun _ => Nat) b
          (fun _ => 0) (fun _ => 1) 2 (fun _ => 3) (fun _ => 4) (fun _ => 5)) := by
    funext b; cases b <;> rfl
  rw [heq]
  apply measurable_casesOn
    (c_int := fun _ => 0) (c_bool := fun _ => 1)
    (c_unit := fun _ => 2) (c_loc := fun _ => 3) (c_lbl := fun _ => 4)
    (c_real := fun _ => 5)
  fun_prop

/-- Depends on the `int` and `real` payloads. -/
@[simp] def countLeaves (g : rT → Int) : BaseLit rT → Int
  | .real r => g r
  | .int n  => n
  | _       => 0

theorem countLeaves.measurable [MeasurableSpace rT] [Inhabited rT] (g : rT → Int)
    (hg : Measurable g) :
    Measurable (countLeaves g : BaseLit rT → Int) := by
  have heq : (countLeaves g : BaseLit rT → Int)
    = (fun b : BaseLit rT =>
        BaseLit.casesOn (motive := fun _ => Int) b
          (fun n => n) (fun _ => 0) 0 (fun _ => 0) (fun _ => 0) g) := by
    funext b; cases b <;> rfl
  rw [heq]
  apply measurable_casesOn
    (c_int := fun n => n) (c_bool := fun _ => 0)
    (c_unit := fun _ => 0) (c_loc := fun _ => 0) (c_lbl := fun _ => 0)
    (c_real := g)
  exact hg

/-- Non-discrete codomain. -/
@[simp] def endoMap : BaseLit rT → BaseLit rT
  | .int z  => .int z
  | .bool b => .bool b
  | .unit   => .unit
  | .loc l  => .loc l
  | .lbl l  => .lbl l
  | .real r => .real r

theorem endoMap.measurable [MeasurableSpace rT] [Inhabited rT] :
    Measurable (endoMap : BaseLit rT → BaseLit rT) := by
  have heq : (endoMap : BaseLit rT → BaseLit rT)
    = (fun b : BaseLit rT =>
        BaseLit.casesOn (motive := fun _ => BaseLit rT) b
          BaseLit.int BaseLit.bool BaseLit.unit BaseLit.loc BaseLit.lbl BaseLit.real) := by
    funext b; cases b <;> rfl
  rw [heq]
  apply measurable_casesOn
    (c_int := BaseLit.int) (c_bool := BaseLit.bool)
    (c_unit := fun _ => BaseLit.unit) (c_loc := BaseLit.loc) (c_lbl := BaseLit.lbl)
    (c_real := BaseLit.real)
  exact real.measurable

/-- Threads an accumulator through `measurable_casesOn_param`. -/
@[simp] def addAcc : Int → BaseLit rT → Int
  | acc, .int n  => acc + n
  | acc, _       => acc

theorem addAcc.measurable [MeasurableSpace rT] [Inhabited rT] :
    Measurable (fun p : BaseLit rT × Int => addAcc p.2 p.1) := by
  have heq : (fun p : BaseLit rT × Int => addAcc p.2 p.1)
    = (fun p : BaseLit rT × Int =>
        BaseLit.casesOn (motive := fun _ => Int) p.1
          (fun z => (fun q : Int × Int => q.1 + q.2) (p.2, z))
          (fun b => (fun q : Int × Bool => q.1) (p.2, b))
          ((fun q : Int => q) p.2)
          (fun l => (fun q : Int × Loc => q.1) (p.2, l))
          (fun l => (fun q : Int × Lbl => q.1) (p.2, l))
          (fun r => (fun q : Int × rT => q.1) (p.2, r))) := by
    funext p; obtain ⟨b, x⟩ := p; cases b <;> rfl
  rw [heq]
  apply measurable_casesOn_param
    (c_int := fun q : Int × Int => q.1 + q.2)
    (c_bool := fun q : Int × Bool => q.1)
    (c_unit := fun q : Int => q)
    (c_loc := fun q : Int × Loc => q.1)
    (c_lbl := fun q : Int × Lbl => q.1)
    (c_real := fun q : Int × rT => q.1)
  all_goals fun_prop

end BaseLit
end ProbLang

namespace ProbLang.Exp

variable {rT : Type _}

/-! ### Synthetic smoke-test battery -/

/-- Discrete codomain. -/
@[simp] def tagDepth : Exp rT → Nat
  | .bvar _        => 0
  | .fvar _        => 0
  | .lit _         => 0
  | .lam e         => tagDepth e + 1
  | .fix e         => tagDepth e + 1
  | .app e1 e2     => max (tagDepth e1) (tagDepth e2) + 1
  | .unop _ e      => tagDepth e + 1
  | .binop _ e1 e2 => max (tagDepth e1) (tagDepth e2) + 1
  | .cond ec et ef => max (max (tagDepth ec) (tagDepth et)) (tagDepth ef) + 1
  | .pair e1 e2    => max (tagDepth e1) (tagDepth e2) + 1
  | .fst e         => tagDepth e + 1
  | .snd e         => tagDepth e + 1
  | .inl e         => tagDepth e + 1
  | .inr e         => tagDepth e + 1
  | .case ec el er => max (max (tagDepth ec) (tagDepth el)) (tagDepth er) + 1
  | .alloc e       => tagDepth e + 1
  | .load e        => tagDepth e + 1
  | .store e1 e2   => max (tagDepth e1) (tagDepth e2) + 1
  | .tape e        => tagDepth e + 1
  | .rand e1 e2    => max (tagDepth e1) (tagDepth e2) + 1
  | .fail          => 0
  | .urand         => 0
  | .scrut e _     => tagDepth e + 1

theorem tagDepth.measurable [MeasurableSpace rT] :
    Measurable (tagDepth : Exp rT → Nat) := by
  apply measurable_struct_rec (f := tagDepth)
    (c_bvar := fun _ => 0) (c_fvar := fun _ => 0) (c_lit := fun _ => 0)
    (c_lam := (· + 1)) (c_fix := (· + 1))
    (c_app := fun n1 n2 => max n1 n2 + 1)
    (c_unop := fun _ n => n + 1)
    (c_binop := fun _ n1 n2 => max n1 n2 + 1)
    (c_cond := fun n1 n2 n3 => max (max n1 n2) n3 + 1)
    (c_pair := fun n1 n2 => max n1 n2 + 1) (c_fst := (· + 1)) (c_snd := (· + 1))
    (c_inl := (· + 1)) (c_inr := (· + 1))
    (c_case := fun n1 n2 n3 => max (max n1 n2) n3 + 1)
    (c_alloc := (· + 1)) (c_load := (· + 1)) (c_store := fun n1 n2 => max n1 n2 + 1)
    (c_tape := (· + 1)) (c_rand := fun n1 n2 => max n1 n2 + 1)
    (c_fail := 0)
    (c_urand := 0)
    (c_scrut := fun n _ => n + 1)
  all_goals first | (intros; rfl) | fun_prop

/-- Depends on the data leaves `lit` and `scrut`. -/
@[simp] def countLeaves : Exp rT → Nat
  | .bvar _        => 0
  | .fvar _        => 0
  | .lit _         => 1
  | .lam e         => countLeaves e
  | .fix e         => countLeaves e
  | .app e1 e2     => countLeaves e1 + countLeaves e2
  | .unop _ e      => countLeaves e
  | .binop _ e1 e2 => countLeaves e1 + countLeaves e2
  | .cond ec et ef => countLeaves ec + countLeaves et + countLeaves ef
  | .pair e1 e2    => countLeaves e1 + countLeaves e2
  | .fst e         => countLeaves e
  | .snd e         => countLeaves e
  | .inl e         => countLeaves e
  | .inr e         => countLeaves e
  | .case ec el er => countLeaves ec + countLeaves el + countLeaves er
  | .alloc e       => countLeaves e
  | .load e        => countLeaves e
  | .store e1 e2   => countLeaves e1 + countLeaves e2
  | .tape e        => countLeaves e
  | .rand e1 e2    => countLeaves e1 + countLeaves e2
  | .fail          => 0
  | .urand         => 0
  | .scrut e _     => countLeaves e + 1

theorem countLeaves.measurable [MeasurableSpace rT] :
    Measurable (countLeaves : Exp rT → Nat) := by
  apply measurable_struct_rec (f := countLeaves)
    (c_bvar := fun _ => 0) (c_fvar := fun _ => 0) (c_lit := fun _ => 1)
    (c_lam := id) (c_fix := id)
    (c_app := (· + ·))
    (c_unop := fun _ n => n)
    (c_binop := fun _ n1 n2 => n1 + n2)
    (c_cond := fun n1 n2 n3 => n1 + n2 + n3)
    (c_pair := (· + ·)) (c_fst := id) (c_snd := id)
    (c_inl := id) (c_inr := id)
    (c_case := fun n1 n2 n3 => n1 + n2 + n3)
    (c_alloc := id) (c_load := id) (c_store := (· + ·))
    (c_tape := id) (c_rand := (· + ·))
    (c_fail := 0)
    (c_urand := 0)
    (c_scrut := fun n _ => n + 1)
  all_goals first | (intros; rfl) | fun_prop

/-- Non-discrete codomain. -/
@[simp] def endoMap : Exp rT → Exp rT
  | .bvar n        => .bvar n
  | .fvar x        => .fvar x
  | .lit b         => .lit b
  | .lam e         => .lam (.lam (endoMap e))
  | .fix e         => .fix (endoMap e)
  | .app e1 e2     => .app (endoMap e1) (endoMap e2)
  | .unop u e      => .unop u (endoMap e)
  | .binop b e1 e2 => .binop b (endoMap e1) (endoMap e2)
  | .cond ec et ef => .cond (endoMap ec) (endoMap et) (endoMap ef)
  | .pair e1 e2    => .pair (endoMap e1) (endoMap e2)
  | .fst e         => .fst (endoMap e)
  | .snd e         => .snd (endoMap e)
  | .inl e         => .inl (endoMap e)
  | .inr e         => .inr (endoMap e)
  | .case ec el er => .case (endoMap ec) (endoMap el) (endoMap er)
  | .alloc e       => .alloc (endoMap e)
  | .load e        => .load (endoMap e)
  | .store e1 e2   => .store (endoMap e1) (endoMap e2)
  | .tape e        => .tape (endoMap e)
  | .rand e1 e2    => .rand (endoMap e1) (endoMap e2)
  | .fail          => .fail
  | .urand         => .urand
  | .scrut e p     => .scrut (endoMap e) p

theorem endoMap.measurable [MeasurableSpace rT] :
    Measurable (endoMap : Exp rT → Exp rT) := by
  apply measurable_struct_rec (f := endoMap)
    (c_bvar := Exp.bvar) (c_fvar := Exp.fvar) (c_lit := Exp.lit)
    (c_lam := fun e => .lam (.lam e)) (c_fix := Exp.fix)
    (c_app := fun e1 e2 => .app e1 e2)
    (c_unop := fun u e => .unop u e)
    (c_binop := fun b e1 e2 => .binop b e1 e2)
    (c_cond := fun ec et ef => .cond ec et ef)
    (c_pair := fun e1 e2 => .pair e1 e2) (c_fst := Exp.fst) (c_snd := Exp.snd)
    (c_inl := Exp.inl) (c_inr := Exp.inr)
    (c_case := fun ec el er => .case ec el er)
    (c_alloc := Exp.alloc) (c_load := Exp.load) (c_store := fun e1 e2 => .store e1 e2)
    (c_tape := Exp.tape) (c_rand := fun e1 e2 => .rand e1 e2)
    (c_fail := .fail)
    (c_urand := .urand)
    (c_scrut := fun e p => .scrut e p)
  all_goals first | (intros; rfl) | fun_prop

/-- Threads a parameter, used at the `bvar` leaf. -/
@[simp] def addAcc : Nat → Exp rT → Nat
  | acc, .bvar n        => acc + n
  | acc, .fvar _        => acc
  | acc, .lit _         => acc
  | acc, .lam e         => addAcc acc e
  | acc, .fix e         => addAcc acc e
  | acc, .app e1 e2     => addAcc acc e1 + addAcc acc e2
  | acc, .unop _ e      => addAcc acc e
  | acc, .binop _ e1 e2 => addAcc acc e1 + addAcc acc e2
  | acc, .cond ec et ef => addAcc acc ec + addAcc acc et + addAcc acc ef
  | acc, .pair e1 e2    => addAcc acc e1 + addAcc acc e2
  | acc, .fst e         => addAcc acc e
  | acc, .snd e         => addAcc acc e
  | acc, .inl e         => addAcc acc e
  | acc, .inr e         => addAcc acc e
  | acc, .case ec el er => addAcc acc ec + addAcc acc el + addAcc acc er
  | acc, .alloc e       => addAcc acc e
  | acc, .load e        => addAcc acc e
  | acc, .store e1 e2   => addAcc acc e1 + addAcc acc e2
  | acc, .tape e        => addAcc acc e
  | acc, .rand e1 e2    => addAcc acc e1 + addAcc acc e2
  | acc, .fail          => acc
  | acc, .urand         => acc
  | acc, .scrut e _     => addAcc acc e

theorem addAcc.measurable [MeasurableSpace rT] :
    Measurable (Function.uncurry (addAcc : Nat → Exp rT → Nat)) := by
  apply measurable_struct_rec_param (f := addAcc)
    (c_bvar := fun acc n => acc + n) (c_fvar := fun acc _ => acc)
    (c_lit := fun acc _ => acc)
    (c_lam := fun _ n => n) (c_fix := fun _ n => n)
    (c_app := fun _ n1 n2 => n1 + n2)
    (c_unop := fun _ _ n => n)
    (c_binop := fun _ _ n1 n2 => n1 + n2)
    (c_cond := fun _ n1 n2 n3 => n1 + n2 + n3)
    (c_pair := fun _ n1 n2 => n1 + n2) (c_fst := fun _ n => n) (c_snd := fun _ n => n)
    (c_inl := fun _ n => n) (c_inr := fun _ n => n)
    (c_case := fun _ n1 n2 n3 => n1 + n2 + n3)
    (c_alloc := fun _ n => n) (c_load := fun _ n => n) (c_store := fun _ n1 n2 => n1 + n2)
    (c_tape := fun _ n => n) (c_rand := fun _ n1 n2 => n1 + n2)
    (c_fail := fun acc => acc)
    (c_urand := fun acc => acc)
    (c_scrut := fun _ n _ => n)
  all_goals first | (intros; rfl) | fun_prop

end Exp
end ProbLang

namespace ProbLang.Pat

variable {rT : Type _}

/-! ### Synthetic smoke-test battery -/

/-- Discrete codomain. -/
@[simp] def tagDepth : Pat rT → Nat
  | .wildcard   => 0
  | .lit _      => 0
  | .pair p1 p2 => max (tagDepth p1) (tagDepth p2) + 1
  | .inl p      => tagDepth p + 1
  | .inr p      => tagDepth p + 1

theorem tagDepth.measurable [MeasurableSpace rT] :
    Measurable (tagDepth : Pat rT → Nat) := by
  apply measurable_struct_rec (f := tagDepth)
    (c_wildcard := 0)
    (c_lit := fun _ => 0)
    (c_pair := fun n1 n2 => max n1 n2 + 1)
    (c_inl := (· + 1))
    (c_inr := (· + 1))
  all_goals first | (intros; rfl) | fun_prop

/-- Depends on the data leaf `lit`. -/
@[simp] def countLeaves : Pat rT → Nat
  | .wildcard   => 0
  | .lit _      => 1
  | .pair p1 p2 => countLeaves p1 + countLeaves p2
  | .inl p      => countLeaves p
  | .inr p      => countLeaves p

theorem countLeaves.measurable [MeasurableSpace rT] :
    Measurable (countLeaves : Pat rT → Nat) := by
  apply measurable_struct_rec (f := countLeaves)
    (c_wildcard := 0)
    (c_lit := fun _ => 1)
    (c_pair := (· + ·))
    (c_inl := id)
    (c_inr := id)
  all_goals first | (intros; rfl) | fun_prop

/-- Non-discrete codomain. -/
@[simp] def endoMap : Pat rT → Pat rT
  | .wildcard   => .wildcard
  | .lit b      => .lit b
  | .pair p1 p2 => .pair (endoMap p1) (endoMap p2)
  | .inl p      => .inl (.inl (endoMap p))
  | .inr p      => .inr (.inr (endoMap p))

theorem endoMap.measurable [MeasurableSpace rT] :
    Measurable (endoMap : Pat rT → Pat rT) := by
  apply measurable_struct_rec (f := endoMap)
    (c_wildcard := .wildcard)
    (c_lit := Pat.lit)
    (c_pair := fun p1 p2 => .pair p1 p2)
    (c_inl := fun p => .inl (.inl p))
    (c_inr := fun p => .inr (.inr p))
  all_goals first | (intros; rfl) | fun_prop

/-- Threads a parameter through every recursive call. -/
@[simp] def addAcc : Nat → Pat rT → Nat
  | acc, .wildcard   => acc
  | acc, .lit _      => acc
  | acc, .pair p1 p2 => addAcc acc p1 + addAcc acc p2
  | acc, .inl p      => addAcc acc p
  | acc, .inr p      => addAcc acc p

theorem addAcc.measurable [MeasurableSpace rT] :
    Measurable (Function.uncurry (addAcc : Nat → Pat rT → Nat)) := by
  apply measurable_struct_rec_param (f := addAcc)
    (c_wildcard := fun acc => acc)
    (c_lit := fun acc _ => acc)
    (c_pair := fun _ n1 n2 => n1 + n2)
    (c_inl := fun _ n => n)
    (c_inr := fun _ n => n)
  all_goals first | (intros; rfl) | fun_prop

end Pat
end ProbLang

namespace ProbLang.EctxItem

variable {rT : Type _}
variable {α : Type _}

/-! ### Smoke tests

`EctxItem` is not recursive, so each test goes through `measurable_casesOn` or
`measurable_casesOn_param` and exercises all 21 constructor slots. -/

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
  apply measurable_casesOn
    (c_appL := fun _ => 0) (c_appR := fun _ => 1) (c_unop := fun _ => 2)
    (c_binopL := fun _ => 3) (c_binopR := fun _ => 4) (c_condC := fun _ => 5)
    (c_pairL := fun _ => 6) (c_pairR := fun _ => 7)
    (c_fst := fun _ => 8) (c_snd := fun _ => 9) (c_inl := fun _ => 10) (c_inr := fun _ => 11)
    (c_case := fun _ => 12) (c_alloc := fun _ => 13) (c_load := fun _ => 14)
    (c_storeL := fun _ => 15) (c_storeR := fun _ => 16) (c_tape := fun _ => 17)
    (c_randL := fun _ => 18) (c_randR := fun _ => 19) (c_scrut := fun _ => 20)
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
  apply measurable_casesOn
    (c_appL := fun _ => 1) (c_appR := fun _ => 1) (c_unop := fun _ => 1)
    (c_binopL := fun _ => 1) (c_binopR := fun _ => 1) (c_condC := fun _ => 1)
    (c_pairL := fun _ => 1) (c_pairR := fun _ => 1)
    (c_fst := fun _ => 0) (c_snd := fun _ => 0) (c_inl := fun _ => 0) (c_inr := fun _ => 0)
    (c_case := fun _ => 1) (c_alloc := fun _ => 0) (c_load := fun _ => 0)
    (c_storeL := fun _ => 1) (c_storeR := fun _ => 1) (c_tape := fun _ => 0)
    (c_randL := fun _ => 1) (c_randR := fun _ => 1) (c_scrut := fun _ => 1)
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
  apply measurable_casesOn
    (c_appL := EctxItem.appL) (c_appR := fun e => EctxItem.appR (Exp.fst e))
    (c_unop := EctxItem.unop)
    (c_binopL := fun q : BinOp × Val α => EctxItem.binopL q.1 q.2)
    (c_binopR := fun q : BinOp × Exp α => EctxItem.binopR q.1 q.2)
    (c_condC := fun q : Exp α × Exp α => EctxItem.condC q.1 q.2)
    (c_pairL := EctxItem.pairL) (c_pairR := EctxItem.pairR)
    (c_fst := fun _ => EctxItem.fst) (c_snd := fun _ => EctxItem.snd)
    (c_inl := fun _ => EctxItem.inl) (c_inr := fun _ => EctxItem.inr)
    (c_case := fun q : Exp α × Exp α => EctxItem.case q.1 q.2)
    (c_alloc := fun _ => EctxItem.alloc) (c_load := fun _ => EctxItem.load)
    (c_storeL := EctxItem.storeL) (c_storeR := EctxItem.storeR)
    (c_tape := fun _ => EctxItem.tape)
    (c_randL := EctxItem.randL) (c_randR := EctxItem.randR)
    (c_scrut := EctxItem.scrut)
  all_goals fun_prop

/-- Threads a parameter through `measurable_casesOn_param`. -/
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
  apply measurable_casesOn_param
    (c_appL := fun q : Nat × Val α => q.1 + 1) (c_appR := fun q : Nat × Exp α => q.1 + 1)
    (c_unop := fun q : Nat × UnOp => q.1)
    (c_binopL := fun q : Nat × BinOp × Val α => q.1)
    (c_binopR := fun q : Nat × BinOp × Exp α => q.1)
    (c_condC := fun q : Nat × Exp α × Exp α => q.1)
    (c_pairL := fun q : Nat × Val α => q.1) (c_pairR := fun q : Nat × Exp α => q.1)
    (c_fst := fun q : Nat => q) (c_snd := fun q : Nat => q)
    (c_inl := fun q : Nat => q) (c_inr := fun q : Nat => q)
    (c_case := fun q : Nat × Exp α × Exp α => q.1)
    (c_alloc := fun q : Nat => q) (c_load := fun q : Nat => q)
    (c_storeL := fun q : Nat × Val α => q.1) (c_storeR := fun q : Nat × Exp α => q.1)
    (c_tape := fun q : Nat => q)
    (c_randL := fun q : Nat × Val α => q.1) (c_randR := fun q : Nat × Exp α => q.1)
    (c_scrut := fun q : Nat × Pat α => q.1)
  all_goals fun_prop

end EctxItem
end ProbLang

end ProbLangMeasures
