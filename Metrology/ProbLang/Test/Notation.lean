module

public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.Syntax.Notation
public import Metrology.ProbLang.Discrete

@[expose] public section

open ProbLang Exp Ty

/-! # Tests for the LN surface-syntax elaborator -/

/-- Check that a ProbLang expression elaborates to the expected AST. -/
macro "#elabpl " lhs:term:max ppLine "#expect " rhs:term : command =>
  `(example : ($lhs : Exp Int) = $rhs := by rfl)

/-- As `#elabpl`, for `Ty`. -/
macro "#elabpl_ty " lhs:term:max ppLine "#expect " rhs:term : command =>
  `(example : $lhs = $rhs := by rfl)

/-- As `#elabpl`, for `Pat Int`. -/
macro "#elabpl_pat " lhs:term:max ppLine "#expect " rhs:term : command =>
  `(example : ($lhs : Pat Int) = $rhs := by rfl)

/-! ## Reserved-keyword errors -/

/-- error: 'fst' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(fst) : Exp Int)
/-- error: 'snd' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(snd) : Exp Int)
/-- error: 'inl' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(inl) : Exp Int)
/-- error: 'inr' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(inr) : Exp Int)
/-- error: 'alloc' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(alloc) : Exp Int)
/-- error: 'rand' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(rand) : Exp Int)
/-- error: 'fst' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(fun fst, x) : Exp Int)
/-- error: 'inl' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(fun inl, x) : Exp Int)
/-- error: 'rand' is a reserved keyword in ProbLang and cannot be used as an identifier -/
#guard_msgs (error) in #check (pl(rec f rand := x) : Exp Int)

variable (e e1 e2 : Exp Int)

/-! ## Literals -/

#elabpl pl(#(.int 1))
#expect lit (.int 1)

#elabpl pl(#1)
#expect lit (.int 1)

#elabpl pl(#true)
#expect lit (.bool true)

#elabpl pl(#false)
#expect lit (.bool false)

#elabpl pl(#.unit)
#expect lit .unit

/-! ## Free variables — atoms are the identifier string -/

#elabpl pl(x)
#expect .fvar "x"

#elabpl pl(x + y)
#expect binop .plus (.fvar "x") (.fvar "y")

-- Same identifier → same atom.
#elabpl pl(x + x)
#expect binop .plus (.fvar "x") (.fvar "x")

-- Different identifier → different atom.
example : (pl(x) : Exp Int) ≠ pl(y) := by
  intro h
  injection h with h'
  injection h' with h''
  exact (by decide : "x" ≠ "y") h''

/-! ## Arithmetic and precedence -/

#elabpl pl(#1 + #2)
#expect binop .plus (lit (.int 1)) (lit (.int 2))

#elabpl pl(#1 + #2 * #3)
#expect binop .plus (lit (.int 1)) (binop .mult (lit (.int 2)) (lit (.int 3)))

#elabpl pl(#1 + #2 + #3)
#expect binop .plus (binop .plus (lit (.int 1)) (lit (.int 2))) (lit (.int 3))

#elabpl pl((#1 + #2) * #3)
#expect binop .mult (binop .plus (lit (.int 1)) (lit (.int 2))) (lit (.int 3))

#elabpl pl(#1 - #2 - #3)
#expect binop .minus (binop .minus (lit (.int 1)) (lit (.int 2))) (lit (.int 3))

#elabpl pl(#1 - #2 * #3)
#expect binop .minus (lit (.int 1)) (binop .mult (lit (.int 2)) (lit (.int 3)))

/-! ## Unary operators -/

#elabpl pl(~x)
#expect unop .neg (.fvar "x")

#elabpl pl(-x)
#expect unop .minus (.fvar "x")

#elabpl pl(-x + y)
#expect binop .plus (unop .minus (.fvar "x")) (.fvar "y")

#elabpl pl(~~x)
#expect unop .neg (unop .neg (.fvar "x"))

#elabpl pl(-(x + y))
#expect unop .minus (binop .plus (.fvar "x") (.fvar "y"))

/-! ## Booleans and comparisons -/

#elabpl pl(~x && y)
#expect binop .and (unop .neg (.fvar "x")) (.fvar "y")

#elabpl pl(x && y || z)
#expect binop .or (binop .and (.fvar "x") (.fvar "y")) (.fvar "z")

#elabpl pl(x && y ^^ z)
#expect binop .xor (binop .and (.fvar "x") (.fvar "y")) (.fvar "z")

#elabpl pl(x ^^ y || z)
#expect binop .or (binop .xor (.fvar "x") (.fvar "y")) (.fvar "z")

#elabpl pl(x + y = z)
#expect binop .eq (binop .plus (.fvar "x") (.fvar "y")) (.fvar "z")

#elabpl pl(x = y = z)
#expect binop .eq (.fvar "x") (binop .eq (.fvar "y") (.fvar "z"))

#elabpl pl(x && y = z)
#expect binop .eq (binop .and (.fvar "x") (.fvar "y")) (.fvar "z")

#elabpl pl(x || y = z)
#expect binop .eq (binop .or (.fvar "x") (.fvar "y")) (.fvar "z")

#elabpl pl(~(x = y))
#expect unop .neg (binop .eq (.fvar "x") (.fvar "y"))

/-! ## Load and store interact with precedence -/

#elabpl pl(!x)
#expect load (.fvar "x")

#elabpl pl(!x + #1)
#expect binop .plus (load (.fvar "x")) (lit (.int 1))

#elabpl pl(!x * y)
#expect binop .mult (load (.fvar "x")) (.fvar "y")

#elabpl pl(!(!x))
#expect load (load (.fvar "x"))

#elabpl pl(x ← y)
#expect store (.fvar "x") (.fvar "y")

#elabpl pl(x ← alloc(y))
#expect store (.fvar "x") (alloc (.fvar "y"))

#elabpl pl(fst(p) ← x)
#expect store (fst (.fvar "p")) (.fvar "x")

#elabpl pl(p ← f x)
#expect store (.fvar "p") (app (.fvar "f") (.fvar "x"))

/-! ## Conditionals -/

#elabpl pl(if x then y else z)
#expect cond (.fvar "x") (.fvar "y") (.fvar "z")

#elabpl pl(if x then y + z else w)
#expect cond (.fvar "x") (binop .plus (.fvar "y") (.fvar "z")) (.fvar "w")

#elabpl pl(if x && y then z else w)
#expect cond (binop .and (.fvar "x") (.fvar "y")) (.fvar "z") (.fvar "w")

#elabpl pl(if (if b then x else y) then z else w)
#expect cond (cond (.fvar "b") (.fvar "x") (.fvar "y")) (.fvar "z") (.fvar "w")

#elabpl pl(if x then (if y then a else b) else c)
#expect cond (.fvar "x") (cond (.fvar "y") (.fvar "a") (.fvar "b")) (.fvar "c")

/-! ## Pairs and sums -/

#elabpl pl((x, y))
#expect pair (.fvar "x") (.fvar "y")

#elabpl pl((x, y, z))
#expect pair (.fvar "x") (pair (.fvar "y") (.fvar "z"))

#elabpl pl((a, b, c, d))
#expect pair (.fvar "a") (pair (.fvar "b") (pair (.fvar "c") (.fvar "d")))

#elabpl pl(fst(x))
#expect fst (.fvar "x")

#elabpl pl(snd(x))
#expect snd (.fvar "x")

#elabpl pl(snd((x, y)))
#expect snd (pair (.fvar "x") (.fvar "y"))

#elabpl pl(fst(snd((x, (y, z)))))
#expect fst (snd (pair (.fvar "x") (pair (.fvar "y") (.fvar "z"))))

#elabpl pl(inl(x))
#expect inl (.fvar "x")

#elabpl pl(inr(x))
#expect inr (.fvar "x")

#elabpl pl((inl(x), inr(y)))
#expect pair (inl (.fvar "x")) (inr (.fvar "y"))

#elabpl pl(inl(if b then x else y))
#expect inl (cond (.fvar "b") (.fvar "x") (.fvar "y"))

/-! ## Heap, random, failure -/

#elabpl pl(alloc(#0))
#expect alloc (lit (.int 0))

#elabpl pl(alloc(alloc(x)))
#expect alloc (alloc (.fvar "x"))

#elabpl pl(tape(#10))
#expect .tape (lit (.int 10))

#elabpl pl(rand(#10, #.unit))
#expect rand (lit (.int 10)) (lit .unit)

#elabpl pl(rand(tape(n), #.unit))
#expect rand (.tape (.fvar "n")) (lit .unit)

#elabpl pl(fail)
#expect Exp.fail

#elabpl pl(assert(b))
#expect cond (.fvar "b") (lit .unit) Exp.fail

/-! ## Application — left-associative, tighter than operators -/

#elabpl pl(f x y)
#expect app (app (.fvar "f") (.fvar "x")) (.fvar "y")

#elabpl pl(f x + g y)
#expect binop .plus (app (.fvar "f") (.fvar "x")) (app (.fvar "g") (.fvar "y"))

#elabpl pl(f x * g y)
#expect binop .mult (app (.fvar "f") (.fvar "x")) (app (.fvar "g") (.fvar "y"))

#elabpl pl(#0 x)
#expect app (lit (.int 0)) (.fvar "x")

#elabpl pl(fst(p) x)
#expect app (fst (.fvar "p")) (.fvar "x")

#elabpl pl((!f) x)
#expect app (load (.fvar "f")) (.fvar "x")

#elabpl pl(fst(f x))
#expect fst (app (.fvar "f") (.fvar "x"))

/-! ## Types -/

#elabpl_ty pl_ty(int)
#expect Ty.int

#elabpl_ty pl_ty(bool)
#expect Ty.bool

#elabpl_ty pl_ty(unit)
#expect Ty.unit

#elabpl_ty pl_ty(int × bool)
#expect Ty.prod .int .bool

#elabpl_ty pl_ty(int + bool)
#expect Ty.sum .int .bool

#elabpl_ty pl_ty(int → bool)
#expect Ty.arrow .int .bool

#elabpl_ty pl_ty(ref(int))
#expect Ty.ref .int

#elabpl_ty pl_ty(tape)
#expect Ty.tape

#elabpl_ty pl_ty(int × bool × unit)
#expect Ty.prod .int (.prod .bool .unit)

#elabpl_ty pl_ty(int → bool → unit)
#expect Ty.arrow .int (.arrow .bool .unit)

#elabpl_ty pl_ty(int + bool + unit)
#expect Ty.sum .int (.sum .bool .unit)

#elabpl_ty pl_ty(int × bool + unit)
#expect Ty.sum (.prod .int .bool) .unit

#elabpl_ty pl_ty(int × bool → unit)
#expect Ty.arrow (.prod .int .bool) .unit

#elabpl_ty pl_ty(int × (bool + unit))
#expect Ty.prod .int (.sum .bool .unit)

#elabpl_ty pl_ty(int + bool → unit)
#expect Ty.arrow (.sum .int .bool) .unit

#elabpl_ty pl_ty(ref(int) × ref(bool))
#expect Ty.prod (.ref .int) (.ref .bool)

#elabpl_ty pl_ty(ref(ref(int)))
#expect Ty.ref (.ref .int)

#elabpl_ty pl_ty(ref(int × bool))
#expect Ty.ref (.prod .int .bool)

/-! ## Type annotations (phantom) -/

#elabpl pl((x : int))
#expect Exp.annotated .int (.fvar "x")

#elabpl pl((#1 : int))
#expect Exp.annotated .int (lit (.int 1))

#elabpl pl((x + y : int))
#expect Exp.annotated .int (binop .plus (.fvar "x") (.fvar "y"))

#elabpl pl((x : int → bool))
#expect Exp.annotated (.arrow .int .bool) (.fvar "x")

#elabpl pl((x : int × bool))
#expect Exp.annotated (.prod .int .bool) (.fvar "x")

#elabpl pl(((x : int) : int))
#expect Exp.annotated .int (Exp.annotated .int (.fvar "x"))

#elabpl pl(alloc((#0 : int)))
#expect alloc (Exp.annotated .int (lit (.int 0)))

#elabpl pl(!(r : ref(int)))
#expect load (Exp.annotated (.ref .int) (.fvar "r"))

#elabpl pl(fst(((#1, #2) : int × int)))
#expect fst (Exp.annotated (.prod .int .int) (pair (lit (.int 1)) (lit (.int 2))))

/-! ## Scrut -/

#elabpl pl(scrut x with y)
#expect Exp.scrut (.fvar "x") Pat.wildcard

#elabpl pl(scrut inl(#1) with inl(x))
#expect Exp.scrut (inl (lit (.int 1))) (.inl .wildcard)

#elabpl pl(scrut (x, y) with (a, b))
#expect Exp.scrut (pair (.fvar "x") (.fvar "y")) (.pair .wildcard .wildcard)

-- `scrut x with (y : int)` is untested: annotated patterns hit the same elaborator dispatch
-- issue as `pl_pat((y : int))`.

/-! ## Patterns -/

#elabpl_pat pl_pat(_)
#expect Pat.wildcard

#elabpl_pat pl_pat(x)
#expect Pat.wildcard

#elabpl_pat pl_pat(# .unit)
#expect Pat.lit .unit

#elabpl_pat pl_pat(#(.int 1))
#expect Pat.lit (.int 1)

#elabpl_pat pl_pat((x, y))
#expect Pat.pair .wildcard .wildcard

#elabpl_pat pl_pat(inl(x))
#expect Pat.inl .wildcard

#elabpl_pat pl_pat(inr(x))
#expect Pat.inr .wildcard

#elabpl_pat pl_pat(inl((x, y)))
#expect Pat.inl (Pat.pair .wildcard .wildcard)

#elabpl_pat pl_pat((inl(x), inr(y)))
#expect Pat.pair (Pat.inl .wildcard) (Pat.inr .wildcard)

/-! ## Escape hatch — `{t}` (brace-delimited) and `&t` (atomic, HeapLang-style) -/

#elabpl pl({e})
#expect e

#elabpl pl({e1} + {e2})
#expect binop .plus e1 e2

-- `&t` is the terser escape for an atomic term; agrees with `{t}`.
#elabpl pl(&e)
#expect e

#elabpl pl(&e1 + &e2)
#expect binop .plus e1 e2

-- Compound escaped terms still need the brace form (or parens around `&`).
#elabpl pl(&(e1) + {binop .plus e1 e2})
#expect binop .plus e1 (binop .plus e1 e2)

/-! ## Delaboration round-trips -/

example : (pl% x + #1 : Exp Int) = pl(x + #1) := rfl
example : (pl% f x : Exp Int) = pl(f x) := rfl
example : (pl% if x then y else z : Exp Int) = pl(if x then y else z) := rfl
example : (pl_ty% int × bool) = pl_ty(int × bool) := rfl
example : (pl_pat% (x, y) : Pat Int) = pl_pat((x, y)) := rfl

/-! ### Expressions -/

/-- info: pl(#1) : Exp ℤ -/
#guard_msgs in #check (pl(#1) : Exp Int)

/-- info: pl(#true) : Exp ℤ -/
#guard_msgs in #check (pl(#true) : Exp Int)

/-- info: pl(#false) : Exp ℤ -/
#guard_msgs in #check (pl(#false) : Exp Int)

/-- info: pl(x) : Exp ℤ -/
#guard_msgs in #check (pl(x) : Exp Int)

/-- info: pl(x + #1) : Exp ℤ -/
#guard_msgs in #check (pl(x + #1) : Exp Int)

/-- info: pl(x - y) : Exp ℤ -/
#guard_msgs in #check (pl(x - y) : Exp Int)

/-- info: pl(x * y) : Exp ℤ -/
#guard_msgs in #check (pl(x * y) : Exp Int)

/-- info: pl(x + y * z) : Exp ℤ -/
#guard_msgs in #check (pl(x + y * z) : Exp Int)

/-- info: pl((x + y) * z) : Exp ℤ -/
#guard_msgs in #check (pl((x + y) * z) : Exp Int)

/-- info: pl(x && y || z) : Exp ℤ -/
#guard_msgs in #check (pl(x && y || z) : Exp Int)

/-- info: pl(x ^^ y) : Exp ℤ -/
#guard_msgs in #check (pl(x ^^ y) : Exp Int)

/-- info: pl(x = y) : Exp ℤ -/
#guard_msgs in #check (pl(x = y) : Exp Int)

/-- info: pl(~x) : Exp ℤ -/
#guard_msgs in #check (pl(~x) : Exp Int)

/-- info: pl(-x) : Exp ℤ -/
#guard_msgs in #check (pl(-x) : Exp Int)

/-- info: pl(!x) : Exp ℤ -/
#guard_msgs in #check (pl(!x) : Exp Int)

/-- info: pl(if x then y else z) : Exp ℤ -/
#guard_msgs in #check (pl(if x then y else z) : Exp Int)

/-- info: pl((x, y)) : Exp ℤ -/
#guard_msgs in #check (pl((x, y)) : Exp Int)

/-- info: pl((x, y, z)) : Exp ℤ -/
#guard_msgs in #check (pl((x, y, z)) : Exp Int)

/-- info: pl(fst(x)) : Exp ℤ -/
#guard_msgs in #check (pl(fst(x)) : Exp Int)

/-- info: pl(snd(x)) : Exp ℤ -/
#guard_msgs in #check (pl(snd(x)) : Exp Int)

/-- info: pl(inl(x)) : Exp ℤ -/
#guard_msgs in #check (pl(inl(x)) : Exp Int)

/-- info: pl(inr(x)) : Exp ℤ -/
#guard_msgs in #check (pl(inr(x)) : Exp Int)

/-- info: pl(alloc(#0)) : Exp ℤ -/
#guard_msgs in #check (pl(alloc(#0)) : Exp Int)

/-- info: pl(alloc(x)) : Exp ℤ -/
#guard_msgs in #check (pl(alloc(x)) : Exp Int)

/-- info: pl(x ← y) : Exp ℤ -/
#guard_msgs in #check (pl(x ← y) : Exp Int)

/-- info: pl(tape(#10)) : Exp ℤ -/
#guard_msgs in #check (pl(tape(#10)) : Exp Int)

/-- info: pl(rand(#10, #())) : Exp ℤ -/
#guard_msgs in #check (pl(rand(#10, #.unit)) : Exp Int)

/-- info: pl(fail) : Exp ℤ -/
#guard_msgs in #check (pl(fail) : Exp Int)

/-- info: pl(scrut x with _) : Exp ℤ -/
#guard_msgs in #check (pl(scrut x with y) : Exp Int)

/-- info: pl(scrut inl(x) with inl(_)) : Exp ℤ -/
#guard_msgs in #check (pl(scrut inl(x) with inl(y)) : Exp Int)

/-- info: pl(f x y) : Exp ℤ -/
#guard_msgs in #check (pl(f x y) : Exp Int)

/-! ### Types -/

-- `int × bool + unit` would reparse as a sum, so the parentheses must stay.
/-- info: pl_ty(int × (bool + unit)) : Ty -/
#guard_msgs in #check (pl_ty(int × (bool + unit)))

/-- info: pl_ty(int × bool → unit) : Ty -/
#guard_msgs in #check (pl_ty(int × bool → unit))

/-- info: pl_ty(int + bool → unit) : Ty -/
#guard_msgs in #check (pl_ty(int + bool → unit))

/-- info: pl_ty(int) : Ty -/
#guard_msgs in #check (pl_ty(int))

/-- info: pl_ty(bool) : Ty -/
#guard_msgs in #check (pl_ty(bool))

/-- info: pl_ty(unit) : Ty -/
#guard_msgs in #check (pl_ty(unit))

/-- info: pl_ty(int × bool) : Ty -/
#guard_msgs in #check (pl_ty(int × bool))

/-- info: pl_ty(int + bool) : Ty -/
#guard_msgs in #check (pl_ty(int + bool))

/-- info: pl_ty(int → bool) : Ty -/
#guard_msgs in #check (pl_ty(int → bool))

/-- info: pl_ty(ref(int)) : Ty -/
#guard_msgs in #check (pl_ty(ref(int)))

/-- info: pl_ty(tape) : Ty -/
#guard_msgs in #check (pl_ty(tape))

/-- info: pl_ty(ref(int → bool)) : Ty -/
#guard_msgs in #check (pl_ty(ref(int → bool)))

/-! ### Patterns: identifiers delaborate to `_` -/

/-- info: pl_pat(_) : Pat ℤ -/
#guard_msgs in #check (pl_pat(_) : Pat Int)

/-- info: pl_pat(_) : Pat ℤ -/
#guard_msgs in #check (pl_pat(x) : Pat Int)

/-- info: pl_pat((_, _)) : Pat ℤ -/
#guard_msgs in #check (pl_pat((x, y)) : Pat Int)

/-- info: pl_pat(inl(_)) : Pat ℤ -/
#guard_msgs in #check (pl_pat(inl(x)) : Pat Int)

/-- info: pl_pat(inr(_)) : Pat ℤ -/
#guard_msgs in #check (pl_pat(inr(x)) : Pat Int)

-- TODO: annotation delab under `pp.problang.annot` prints `annotated pl_ty(int) pl(x)`; once it
-- prints `pl((x : int))`, test it here (hidden by default, shown with `pp.problang.annot 2`).
