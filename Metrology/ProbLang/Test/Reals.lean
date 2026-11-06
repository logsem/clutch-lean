module

public import Metrology.ProbLang.Reals
public import Metrology.ProbLang.Syntax.Notation
public import Metrology.ProbLang.Syntax.Types

/-! # Tests for the real operators

Notation, typing and evaluation at `ℝ`, including the total conventions at domain boundaries. -/

@[expose] public section

open ProbLang Exp ProbLangℝ

/-! ## Notation -/

example (r : ℝ) : (pl(floor(#real r)) : Exp ℝ) = .unop .floor (.lit (.real r)) := rfl
example : (pl(#pi) : Exp ℝ) = .lit (.real realPi) := rfl
example (r : ℝ) :
    (pl(ceil(#real r)) : Exp ℝ) = .unop .minus (.unop .floor (.unop .minus (.lit (.real r)))) :=
  rfl
example (x y : ℝ) : (pl(pow(#real x, #real y)) : Exp ℝ) =
    .unop .exp (.binop .mult (.lit (.real y)) (.unop .log (.lit (.real x)))) := rfl

/-! ## Typing -/

example (r : ℝ) : Typed Tctx.empty (pl(floor(#real r)) : Exp ℝ) .int :=
  .unop_real .lit_real rfl
example (r : ℝ) :
    Typed Tctx.empty (pl(atan(sin(cos(exp(sqrt(log(#real r))))))) : Exp ℝ) .real := by
  repeat (first | exact .lit_real | refine .unop_real ?_ rfl)
example (a b : ℝ) : Typed Tctx.empty (pl(#real a * #real b - #real a / #real b) : Exp ℝ) .real :=
  .binop_real (.binop_real .lit_real .lit_real rfl) (.binop_real .lit_real .lit_real rfl) rfl
-- The real functions take no integer operands, and real `%` stays untyped.
example : UnOp.intResTy .floor = none ∧ UnOp.intResTy .log = none := ⟨rfl, rfl⟩
example : BinOp.realResTy .mod = none := rfl

/-! ## Evaluation at `ℝ` -/

/-- `floor` rounds toward `-∞` on negative inputs. -/
example : UnOp.eval .floor (.lit (.real (-2.5 : ℝ))) = some (.lit (.int (-3))) := by
  norm_num [UnOp.eval, Int.floor_eq_iff]
example : UnOp.eval .floor (.lit (.real (-3 : ℝ))) = some (.lit (.int (-3))) := by
  norm_num [UnOp.eval, Int.floor_eq_iff]
example : realCeil (-2.5 : ℝ) = -2 := by norm_num [Int.ceil_eq_iff]
-- Integer operands are stuck, as are mixed int/real binary operands.
example : UnOp.eval .floor (.lit (.int 2) : Exp ℝ) = none := rfl
example : BinOp.eval .mult (.lit (.int 2)) (.lit (.real (3 : ℝ))) = none := rfl
example : BinOp.eval .minus (.lit (.real (5 : ℝ))) (.lit (.real 2)) = some (.lit (.real 3)) := by
  norm_num [BinOp.eval]
example :
    BinOp.eval .div (.lit (.real (1 : ℝ))) (.lit (.real 4)) = some (.lit (.real (1 / 4))) := by
  simp [BinOp.eval]

/-! ## Domain boundaries at `ℝ` -/

example : BinOp.eval .div (.lit (.real (1 : ℝ))) (.lit (.real 0)) = some (.lit (.real 0)) := by
  simp [BinOp.eval]
example : UnOp.eval .log (.lit (.real (0 : ℝ))) = some (.lit (.real 0)) := by simp [UnOp.eval]
example : UnOp.eval .log (.lit (.real (-1 : ℝ))) = some (.lit (.real 0)) := by simp [UnOp.eval]
example : UnOp.eval .sqrt (.lit (.real (-4 : ℝ))) = some (.lit (.real 0)) := by
  simp [UnOp.eval, realSqrt_of_neg_real (show (-4 : ℝ) < 0 by norm_num)]
example (y : ℝ) : realPow 0 y = 1 := realPow_zero_real y
example : realPow (4 : ℝ) (1 / 2) = 2 := by
  rw [realPow_real_of_pos (by norm_num), ← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
