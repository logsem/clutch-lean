import Metrology.ProbLang.Interp.BigStepIO
import Metrology.ProbLang.Discrete
import Metrology.ProbLang.Syntax.Notation

open ProbLang ProbLang.Interp MeasureTheory

/-! # Tests for the big-step ProbLang interpreter (`Interp.run`)

Each test runs a program and compares its value against an expected `Exp`; a failing
test throws an `IO` error naming it. The tests run at elaboration time, so compiling this
file runs them.

Ported from the test suite of the old context-decomposing interpreter. Where that interpreter departed from the
formal semantics, the tests now follow the semantics: `rand(z, ())` samples `[0, z)` and
returns `-1` when `z ≤ 0`, and tapes are supported. -/

/-- Run a closed program from the empty state on the environment machine. -/
private def runTest (prog : Exp Float) : IO (Exp Float × State Float) := do
  let r ← run (.eval [] prog default)
  return (r.val.rb, r.state)

/-- Run a closed program from the empty state on the reference substitution evaluator. -/
private def runTestSubst (prog : Exp Float) : IO (Exp Float × State Float) := do
  let ⟨v, σ⟩ ← runSubst ⟨prog, default⟩
  return (v, σ)

/-- Both engines return `expected`. -/
private def check (name : String) (prog : Exp Float) (expected : Exp Float) : IO Unit := do
  for (engine, runner) in [("env", runTest), ("subst", runTestSubst)] do
    let v ← runner prog
    if v.1 != expected then
      throw (IO.userError s!"FAIL [{name}, {engine}]: got {repr v.1}, expected {repr expected}")

/-- Both engines raise an error. -/
private def checkError (name : String) (prog : Exp Float) : IO Unit := do
  for (engine, runner) in [("env", runTest), ("subst", runTestSubst)] do
    match ← (runner prog |>.toBaseIO) with
    | .ok v => throw (IO.userError s!"FAIL [{name}, {engine}]: expected error, got {repr v.1}")
    | .error _ => pure ()

-- ---------------------------------------------------------------------------
-- Literals
-- ---------------------------------------------------------------------------

#eval check "int literal"
  pl(#1)
  pl(#1)
#eval check "bool literal"
  pl(#true)
  pl(#true)
#eval check "unit literal"
  pl(#.unit)
  pl(#.unit)

-- ---------------------------------------------------------------------------
-- Arithmetic and boolean operators
-- ---------------------------------------------------------------------------

#eval check "1 + 2 = 3"
  pl(#1 + #2)
  pl(#3)
#eval check "5 - 3 = 2"
  pl(#5 - #3)
  pl(#2)
#eval check "3 * 4 = 12"
  pl(#3 * #4)
  pl(#12)
#eval check "neg"
  pl(- #5)
  pl(#(.int (-5)))
#eval check "not true"
  pl(~ #true)
  pl(#false)
#eval check "and"
  pl(#true && #false)
  pl(#false)
#eval check "or"
  pl(#false || #true)
  pl(#true)
#eval check "xor"
  pl(#true ^^ #true)
  pl(#false)
#eval check "eq ints"
  pl(#3 = #3)
  pl(#true)
#eval check "neq ints"
  pl(#3 = #4)
  pl(#false)

-- ---------------------------------------------------------------------------
-- Context decomposition: the redex is found deep inside a larger expression.
-- These specifically exercise `primStep`'s use of `Exp.decomp`.
-- ---------------------------------------------------------------------------

-- Redex in the right argument of binop
#eval check "binop: redex in right arg"
  pl(#1 + fst((#2, #3)))
  pl(#3)

-- Redex in the left argument of binop (right is already a value)
#eval check "binop: redex in left arg"
  pl(fst((#1, #2)) + fst((#3, #4)))
  pl(#4)

-- Nested: fst inside the argument of snd
#eval check "snd of nested fst"
  pl(snd((fst((#1, #2)), #3)))
  pl(#3)

-- Redex under inl / inr
#eval check "inl of redex"
  pl(inl(#1 + #2))
  pl(inl(#3))
#eval check "inr of redex"
  pl(inr(#3 * #4))
  pl(inr(#12))

-- Condition expression contains a redex
#eval check "redex in condition"
  pl(if fst((#true, #false)) then #1 else #2)
  pl(#1)

-- ---------------------------------------------------------------------------
-- Conditionals
-- ---------------------------------------------------------------------------

#eval check "if true"
  pl(if #true  then #1 else #2)
  pl(#1)
#eval check "if false"
  pl(if #false then #1 else #2)
  pl(#2)

-- ---------------------------------------------------------------------------
-- Functions and let
-- ---------------------------------------------------------------------------

#eval check "identity"
  pl((fun x, x) #42)
  pl(#42)
#eval check "let"
  pl(let x := #7; x + #3)
  pl(#10)
#eval check "closure"
  pl((fun x y, x + y) #3 #4)
  pl(#7)

-- ---------------------------------------------------------------------------
-- Recursion: factorial 5 = 120
-- ---------------------------------------------------------------------------

private def factExp : Exp Float := pl(rec fact n := if n = #0 then #1 else n * fact (n - #1))

#eval check "factorial 5"
  pl({factExp} #5)
  pl(#120)

-- ---------------------------------------------------------------------------
-- Pairs
-- ---------------------------------------------------------------------------

#eval check "fst"
  pl(fst((#1, #2)))
  pl(#1)
#eval check "snd"
  pl(snd((#1, #2)))
  pl(#2)

#eval check "let pair"
  pl(let a := #10; let b := #20; a + b)
  pl(#30)

-- ---------------------------------------------------------------------------
-- Sums
-- ---------------------------------------------------------------------------

-- case with inl/inr patterns
#eval check "case inl"
  pl(case inl(#1) | inl(x) => x + #10 | inr(y) => #0)
  pl(#11)

#eval check "case inr"
  pl(case inr(#2) | inl(_) => #0 | inr(y) => y + #20)
  pl(#22)

-- case with a non-value scrutinee (redex inside scrutinee)
#eval check "case: scrutinee is redex"
  pl(case inl(#1 + #2) | inl(x) => x | inr(_) => #0)
  pl(#3)

-- single-arm case (fails if no match)
#eval check "case single arm inl"
  pl(case inl(#5) | inl(x) => x)
  pl(#5)

#eval checkError "case single arm fail"
  pl(case inr(#5) | inl(x) => x)

-- let! destructuring
#eval check "let! pair"
  pl(let! (x, y) := (#1, #2); x + y)
  pl(#3)

#eval check "let! inl"
  pl(let! inl(x) := inl(#7); x + #3)
  pl(#10)

#eval checkError "let! inl mismatch"
  pl(let! inl(x) := inr(#7); x)

-- case with wildcard fallback
#eval check "case wildcard fallback"
  pl(case #1 | #(.int 0) => #100 | _ => #200)
  pl(#200)

-- case with literal match
#eval check "case literal match"
  pl(case #1 | #(.int 1) => #100 | _ => #200)
  pl(#100)

-- nested pair destructuring
#eval check "let! nested pair"
  pl(let! (x, (y, z)) := (#1, (#2, #3)); x + y + z)
  pl(#6)

-- ---------------------------------------------------------------------------
-- Heap
-- ---------------------------------------------------------------------------

#eval check "alloc/load"
  pl(let r := alloc(#0); !r)
  pl(#0)

#eval check "alloc/store/load"
  pl(let r := alloc(#0); r ← #42; !r)
  pl(#42)

#eval check "two refs"
  pl(let r1 := alloc(#1); let r2 := alloc(#2); !r1 + !r2)
  pl(#3)

-- ---------------------------------------------------------------------------
-- Failure
-- ---------------------------------------------------------------------------

#eval checkError "fail"
  pl(fail)
#eval checkError "assert false"
  pl(assert(#false))
#eval checkError "rand with dangling tape label"
  pl(rand(#5, #(BaseLit.lbl (0 : Int))))

#eval check "assert true"
  pl(assert(#true))
  pl(#.unit)

-- ---------------------------------------------------------------------------
-- Rand: `rand(z, ())` is uniform on [0, z), as in `Cfg.uniform`.
-- ---------------------------------------------------------------------------

#eval do
  let v ← runTest pl(rand(#6, #.unit))
  match v.1 with
  | .lit (.int n) =>
    if n < 0 then
      throw (IO.userError s!"FAIL [rand range]: got {n}, expected ≥ 0")
    if n ≥ 6 then
      throw (IO.userError s!"FAIL [rand range]: got {n}, expected < 6")
  | e => throw (IO.userError s!"FAIL [rand type]: got {repr e}")

-- ---------------------------------------------------------------------------
-- Type errors in operators (should all be stuck)
-- ---------------------------------------------------------------------------

#eval checkError "add bool + int"
  pl(#true + #1)
#eval checkError "add int + bool"
  pl(#1 + #true)
#eval checkError "add unit + unit"
  pl(#.unit + #.unit)
#eval checkError "mult bool"
  pl(#true * #false)
#eval checkError "minus bools"
  pl(#true - #false)
#eval checkError "and int"
  pl(#1 && #2)
#eval checkError "or int"
  pl(#1 || #2)
#eval checkError "xor int"
  pl(#1 ^^ #2)
#eval checkError "neg int"
  pl(~ #5)
#eval checkError "negate bool"
  pl(- #true)

-- ---------------------------------------------------------------------------
-- Projection errors
-- ---------------------------------------------------------------------------

#eval checkError "fst of non-pair"
  pl(fst(#1))
#eval checkError "snd of non-pair"
  pl(snd(#true))
#eval checkError "fst of inl"
  pl(fst(inl(#1)))

-- ---------------------------------------------------------------------------
-- Conditional errors
-- ---------------------------------------------------------------------------

#eval checkError "if int"
  pl(if #1 then #2 else #3)
#eval checkError "if unit"
  pl(if #.unit then #1 else #2)

-- ---------------------------------------------------------------------------
-- Application errors
-- ---------------------------------------------------------------------------

#eval checkError "apply literal"
  pl(#1 #2)
#eval checkError "apply pair"
  pl((#1, #2) #3)

-- ---------------------------------------------------------------------------
-- Arithmetic edge cases
-- ---------------------------------------------------------------------------

#eval check "0 - 1 = -1"
  pl(#0 - #1)
  pl(#(.int (-1)))
#eval check "neg 0"
  pl(- #0)
  pl(#0)
#eval check "neg neg"
  pl(- (- #5))
  pl(#5)
#eval check "not false"
  pl(~ #false)
  pl(#true)
#eval check "not not"
  pl(~ (~ #true))
  pl(#true)
#eval check "0 * anything"
  pl(#0 * #999)
  pl(#0)
#eval check "eq bools"
  pl(#true = #true)
  pl(#true)
#eval check "neq bools"
  pl(#true = #false)
  pl(#false)
#eval check "eq unit"
  pl(#.unit = #.unit)
  pl(#true)
#eval check "xor ff"
  pl(#false ^^ #false)
  pl(#false)
#eval check "xor tf"
  pl(#true ^^ #false)
  pl(#true)
#eval check "and tt"
  pl(#true && #true)
  pl(#true)
#eval check "or ff"
  pl(#false || #false)
  pl(#false)

-- ---------------------------------------------------------------------------
-- Deep context decomposition stress tests
-- ---------------------------------------------------------------------------

-- snd then fst of nested pairs
#eval check "deep decomp 1"
  pl(snd((#99, fst((#42, #0)))))
  pl(#42)

-- Redex buried inside a pair value position
#eval check "pair with redex in both"
  pl(fst((#1 + #2, #3 + #4)))
  pl(#3)

-- Redex in condition, then in branch result
#eval check "nested cond"
  pl(if #true then (if #false then #1 else #2) else #3)
  pl(#2)

-- Chained lets
#eval check "chained lets"
  pl(let a := #1; let b := a + #2; let c := b + #3; c + #4)
  pl(#10)

-- ---------------------------------------------------------------------------
-- Higher-order functions
-- ---------------------------------------------------------------------------

-- Function returning a function
#eval check "higher-order: return fn"
  pl((fun x, (fun y, x + y)) #10 #20)
  pl(#30)

-- Function as argument (apply twice)
#eval check "apply twice"
  pl(let f := (fun x, x + #1); f (f #0))
  pl(#2)

-- Recursive: sum 1..10 = 55
private def sumExp : Exp Float := pl(rec sum n := if n = #0 then #0 else n + sum (n - #1))
#eval check "sum 1..10"
  pl({sumExp} #10)
  pl(#55)

-- Mutual recursion via pairs: is_even/is_odd
private def isEvenOdd : Exp Float :=
  pl(rec eo n := if n = #0 then (#true, #false) else (snd(eo (n - #1)), fst(eo (n - #1))))
#eval check "is_even 4"
  pl(fst({isEvenOdd} #4))
  pl(#true)
#eval check "is_odd 4"
  pl(snd({isEvenOdd} #4))
  pl(#false)
#eval check "is_even 3"
  pl(fst({isEvenOdd} #3))
  pl(#false)
#eval check "is_odd 3"
  pl(snd({isEvenOdd} #3))
  pl(#true)

-- ---------------------------------------------------------------------------
-- Heap: aliasing, multiple stores, store-after-store
-- ---------------------------------------------------------------------------

-- Store twice to same ref
#eval check "store twice"
  pl(let r := alloc(#0); r ← #1; r ← #2; !r)
  pl(#2)

-- Two refs: store to one doesn't affect the other
#eval check "heap isolation"
  pl(let r1 := alloc(#10); let r2 := alloc(#20); r1 ← #99; !r2)
  pl(#20)

-- Load after alloc without store (alloc initializes)
#eval check "alloc initializes"
  pl(let r := alloc(#7); !r)
  pl(#7)

-- Store a pair in a ref
#eval check "store pair in ref"
  pl(let r := alloc((#1, #2)); fst(!r))
  pl(#1)

-- Store a function in a ref and call it
#eval check "store fn in ref"
  pl(let r := alloc((fun x, x + #1)); (!r) #41)
  pl(#42)

-- Heap with computation in stored value
#eval check "store computed value"
  pl(let r := alloc(#0); r ← (#3 + #4); !r)
  pl(#7)

-- ---------------------------------------------------------------------------
-- Sum/case edge cases
-- ---------------------------------------------------------------------------

-- case with computation in both branches
#eval check "case inl: branch computes"
  pl(case inl(#5) | inl(x) => x * x | inr(y) => y + y)
  pl(#25)

-- Nested case
#eval check "nested case"
  pl(case inl(inr(#7))
     | inl(inner) => (case inner | inl(_) => #0 | inr(z) => z)
     | inr(_) => #99)
  pl(#7)

-- let! with inr
#eval check "let! inr"
  pl(let! inr(y) := inr(#42); y)
  pl(#42)

#eval checkError "let! inr mismatch"
  pl(let! inr(y) := inl(#42); y)

-- let! pair where scrutinee needs evaluation first
#eval check "let! pair with redex scrutinee"
  pl(let p := (#1 + #2, #3 + #4); let! (a, b) := p; a + b)
  pl(#10)

-- ---------------------------------------------------------------------------
-- Sequencing and unit
-- ---------------------------------------------------------------------------

#eval check "sequence"
  pl(let _ := #.unit; #42)
  pl(#42)

-- Assert then continue
#eval check "assert then compute"
  pl(let _ := assert(#true); #1 + #2)
  pl(#3)

-- Multiple asserts
#eval check "multi assert"
  pl(let _ := assert(#true); let _ := assert(#true); #.unit)
  pl(#.unit)

-- ---------------------------------------------------------------------------
-- Rand edge cases
-- ---------------------------------------------------------------------------

-- A non-positive bound returns the sentinel `-1` (`Cfg.uniform`).
#eval check "rand 0 bound"
  pl(rand(#0, #.unit))
  pl(#(.int (-1)))
#eval check "rand negative"
  pl(rand(#(.int (-5)), #.unit))
  pl(#(.int (-1)))

-- rand(1, unit) is always 0
#eval check "rand 1"
  pl(rand(#1, #.unit))
  pl(#0)

-- ---------------------------------------------------------------------------
-- Fail propagation through contexts
-- ---------------------------------------------------------------------------

#eval checkError "fail in binop left"
  pl(fail + #1)
#eval checkError "fail in binop right"
  pl(#1 + fail)
#eval checkError "fail in fst"
  pl(fst(fail))
#eval checkError "fail in snd"
  pl(snd(fail))
#eval checkError "fail in inl"
  pl(inl(fail))
#eval checkError "fail in cond"
  pl(if fail then #1 else #2)
#eval checkError "fail in alloc"
  pl(alloc(fail))
#eval checkError "fail in pair left"
  pl((fail, #1))
-- Note: (v, fail) only fails if the pair is forced; as a value it's fine.
-- But since fail is not a value, decomp should find it.
#eval checkError "fail in pair right"
  pl((#1, fail))
#eval checkError "fail in store loc"
  pl(fail ← #1)
#eval checkError "fail in store val"
  pl(let r := alloc(#0); r ← fail)
#eval checkError "fail in load"
  pl(!fail)
#eval checkError "fail in rand bound"
  pl(rand(fail, #.unit))
#eval checkError "fail in rand tape"
  pl(rand(#5, fail))
#eval checkError "fail in app fn"
  pl(fail #1)
#eval checkError "fail in case scrutinee"
  pl(case fail | inl(x) => x | inr(y) => y)
#eval checkError "fail in scrut"
  pl(case scrut fail with x | inl(b) => b | inr(_) => #0)

-- ---------------------------------------------------------------------------
-- Annotations (decomp through EctxItem.annot, preserved in result)
-- ---------------------------------------------------------------------------

-- annot on a value: annotation is stripped during evaluation
#eval check "annot value"
  pl((#42 : int))
  pl(#42)

-- annot on a redex: reduces under annotation, then strips it
#eval check "annot redex"
  pl((#1 + #2 : int))
  pl(#3)

-- nested annot: both annotations stripped
#eval check "annot nested"
  pl(((#3 * #4 : int) : int))
  pl(#12)

-- annot on a pair: annotation stripped, fst works
#eval check "annot pair"
  pl(fst(((#1, #2) : int × int)))
  pl(#1)

-- annot on function result
#eval check "annot fn result"
  pl(((fun x, x + #1) #9 : int))
  pl(#10)

-- ---------------------------------------------------------------------------
-- Raw scrut (pattern matching primitive)
-- ---------------------------------------------------------------------------

-- scrut match success: returns inl(bindings)
#eval check "scrut var match"
  pl(case scrut #42 with x | inl(b) => b | inr(_) => #0)
  pl(#42)

-- scrut literal match: returns inl(unit)
#eval check "scrut lit match"
  pl(case scrut #1 with #(.int 1) | inl(_) => #99 | inr(_) => #0)
  pl(#99)

-- scrut literal mismatch: returns inr(unit)
#eval check "scrut lit mismatch"
  pl(case scrut #1 with #(.int 2) | inl(_) => #99 | inr(_) => #0)
  pl(#0)

-- scrut pair match
#eval check "scrut pair match"
  pl(case scrut (#1, #2) with (x, y) | inl(b) => fst(b) + snd(b) | inr(_) => #0)
  pl(#3)

-- scrut inl match
#eval check "scrut inl match"
  pl(case scrut inl(#5) with inl(x) | inl(b) => b | inr(_) => #0)
  pl(#5)

-- scrut inl on inr: mismatch
#eval check "scrut inl on inr mismatch"
  pl(case scrut inr(#5) with inl(x) | inl(_) => #99 | inr(_) => #0)
  pl(#0)

-- ---------------------------------------------------------------------------
-- Heap errors (segfault)
-- ---------------------------------------------------------------------------

-- Load from a fabricated location (not allocated)
#eval checkError "segfault load"
  pl(!#(.loc 999))

-- Store to a fabricated location
#eval checkError "segfault store"
  pl(#(.loc 999) ← #1)

-- ---------------------------------------------------------------------------
-- Equality across types
-- ---------------------------------------------------------------------------

#eval check "eq int vs int diff"
  pl(#0 = #1)
  pl(#false)
#eval check "eq bool vs bool same"
  pl(#true = #true)
  pl(#true)
#eval check "eq unit vs unit"
  pl(#.unit = #.unit)
  pl(#true)

-- Cross-type equality: int vs bool (BaseLit.int ≠ BaseLit.bool via DecidableEq)
#eval check "eq int vs bool"
  pl(#1 = #true)
  pl(#false)
#eval check "eq bool vs int"
  pl(#false = #0)
  pl(#false)
#eval check "eq unit vs int"
  pl(#.unit = #1)
  pl(#false)

-- ---------------------------------------------------------------------------
-- Variable shadowing
-- ---------------------------------------------------------------------------

#eval check "shadow let"
  pl(let x := #1; let x := #2; x)
  pl(#2)

#eval check "shadow let uses inner"
  pl(let x := #1; let x := x + #10; x)
  pl(#11)

#eval check "shadow fn param"
  pl((fun x, (fun x, x)) #1 #2)
  pl(#2)

#eval check "shadow rec"
  pl(let x := #100; (fun x, x + #1) #5)
  pl(#6)

-- ---------------------------------------------------------------------------
-- Letrec as value
-- ---------------------------------------------------------------------------

-- A bare letrec (not applied) is a value
#eval check "letrec is value"
  pl(rec f x := x)
  pl(rec f x := x)

-- Letrec stored in a let, then applied
#eval check "letrec in let"
  pl(let f := rec g x := x + #1; f #9)
  pl(#10)

-- Letrec in a pair
#eval check "letrec in pair"
  pl(fst((rec f x := x, #99)))
  pl(rec f x := x)

-- ---------------------------------------------------------------------------
-- Anonymous binder edge cases
-- ---------------------------------------------------------------------------

#eval check "anon binder"
  pl((fun _, #42) #0)
  pl(#42)

#eval check "anon binder ignores arg"
  pl((fun _, #1 + #2) #999)
  pl(#3)

-- ---------------------------------------------------------------------------
-- Deep nested values
-- ---------------------------------------------------------------------------

#eval check "pair of pairs"
  pl(fst(snd((#1, (#2, #3)))))
  pl(#2)

#eval check "inl of inr"
  pl(case inl(inr(#7)) | inl(x) => x | inr(_) => #0)
  pl(inr(#7))

#eval check "deeply nested pair"
  pl(fst(snd(snd((#1, (#2, (#3, #4)))))))
  pl(#3)

-- ---------------------------------------------------------------------------
-- Multi-arm case (3+ arms, exercises scrutinize chain)
-- ---------------------------------------------------------------------------

#eval check "3-arm case: first match"
  pl(case #1 | #(.int 1) => #10 | #(.int 2) => #20 | _ => #30)
  pl(#10)

#eval check "3-arm case: second match"
  pl(case #2 | #(.int 1) => #10 | #(.int 2) => #20 | _ => #30)
  pl(#20)

#eval check "3-arm case: fallthrough"
  pl(case #3 | #(.int 1) => #10 | #(.int 2) => #20 | _ => #30)
  pl(#30)

#eval check "4-arm case"
  pl(case #3 | #(.int 1) => #10 | #(.int 2) => #20 | #(.int 3) => #30 | _ => #40)
  pl(#30)

-- ---------------------------------------------------------------------------
-- Deeply nested pattern matching
-- ---------------------------------------------------------------------------

-- let! on nested pair: ((1, 2), (3, 4))
#eval check "let! nested pair of pairs"
  pl(let! ((a, b), (c, d)) := ((#1, #2), (#3, #4)); a + b + c + d)
  pl(#10)

-- case on inl(inl(x))
#eval check "case inl(inl(...))"
  pl(case inl(#5)
     | inl(x) => (case x | #(.int 5) => #100 | _ => #0)
     | inr(_) => #0)
  pl(#100)

-- let! inl of a pair
#eval check "let! inl pair"
  pl(let! inl((x, y)) := inl((#3, #7)); x + y)
  pl(#10)

-- let! inr of a pair
#eval check "let! inr pair"
  pl(let! inr((x, y)) := inr((#10, #20)); x * y)
  pl(#200)

-- Nested case: match on sum, then destructure the payload
#eval check "nested case then let!"
  pl(case inl((#1, #2))
     | inl(p) => (let! (a, b) := p; a + b)
     | inr(_) => #0)
  pl(#3)

-- Triple-nested pair destructuring
#eval check "let! triple nested"
  pl(let! (a, (b, (c, d))) := (#1, (#2, (#3, #4))); a + b + c + d)
  pl(#10)

-- case where first arm fails, second has nested match
#eval check "case fallthrough to nested"
  pl(case inr((#5, #6))
     | inl(_) => #0
     | inr(p) => (let! (x, y) := p; x + y))
  pl(#11)

-- Matching literal inside a pair
#eval check "let! pair with literal check"
  pl(let! (#(.int 1), x) := (#1, #42); x)
  pl(#42)

-- Matching literal inside a pair: mismatch
#eval checkError "let! pair literal mismatch"
  pl(let! (#(.int 99), x) := (#1, #42); x)

-- Deeply nested inl/inr
#eval check "case deeply nested sums"
  pl(case inl(inr(inl(#7)))
     | inl(a) => (case a
       | inr(b) => (case b | inl(c) => c | inr(_) => #0)
       | inl(_) => #0)
     | inr(_) => #0)
  pl(#7)

-- Pattern match then compute with matched values
#eval check "match and compute"
  pl(case inl((#3, #4))
     | inl(p) => (let! (x, y) := p; x * y + #1)
     | inr(_) => #0)
  pl(#13)

-- 5-arm case: exercise long scrutinize chain
#eval check "5-arm case"
  pl(case #4
     | #(.int 1) => #10
     | #(.int 2) => #20
     | #(.int 3) => #30
     | #(.int 4) => #40
     | _ => #50)
  pl(#40)

-- case on pair values (not sum)
#eval check "case on pair"
  pl(case (#1, #2)
     | (#(.int 1), #(.int 2)) => #100
     | _ => #0)
  pl(#100)

#eval check "case on pair mismatch"
  pl(case (#1, #3)
     | (#(.int 1), #(.int 2)) => #100
     | _ => #0)
  pl(#0)

-- ---------------------------------------------------------------------------
-- Rand with computed bound
-- ---------------------------------------------------------------------------

#eval do
  let v ← runTest pl(rand(#3 + #3, #.unit))
  match v.1 with
  | .lit (.int n) =>
    if n < 0 || n ≥ 6 then
      throw (IO.userError s!"FAIL [rand computed bound]: got {n}, expected 0..5")
  | e => throw (IO.userError s!"FAIL [rand computed bound type]: got {repr e}")

-- ---------------------------------------------------------------------------
-- checkError with substring matching
-- ---------------------------------------------------------------------------

private def String.hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- Like `checkError` but also checks the error message contains `needle`. -/
private def checkErrorMsg (name : String) (prog : Exp Float) (needle : String) : IO Unit := do
  for (engine, runner) in [("env", runTest), ("subst", runTestSubst)] do
    match ← (runner prog |>.toBaseIO) with
    | .ok v =>
      throw (IO.userError s!"FAIL [{name}, {engine}]: expected error, got {repr v.1}")
    | .error e =>
      let msg := toString e
      if !msg.hasSubstr needle then
        throw (IO.userError
          s!"FAIL [{name}, {engine}]: expected error containing \"{needle}\", got \"{msg}\"")

-- ---------------------------------------------------------------------------
-- Application errors: non-function stuck cases
-- ---------------------------------------------------------------------------

#eval checkErrorMsg "apply inl"
  pl(inl(#1) #2)
  "stuck"
#eval checkErrorMsg "apply inr"
  pl(inr(#1) #2)
  "stuck"
#eval checkErrorMsg "apply loc"
  pl(#(.loc 1) #2)
  "stuck"

-- ---------------------------------------------------------------------------
-- Raw case on non-sum scrutinee (stuck)
-- ---------------------------------------------------------------------------

-- The notation `case e | ...` desugars through scrut, but raw .case only
-- handles inl/inr.  Build a raw .case with a literal scrutinee directly.
-- Under LN: each branch is a `lam` whose body uses `bvar 0`.
#eval checkErrorMsg "raw case on int"
  (Exp.case (.lit (.int 5)) (.lam (.bvar 0)) (.lam (.bvar 0)))
  "stuck"

-- ---------------------------------------------------------------------------
-- Free variable / open term (stuck)
-- ---------------------------------------------------------------------------

#eval checkErrorMsg "free variable"
  (.binop .plus (.fvar "unbound_x") (.lit (.int 1)))
  "stuck"

-- ---------------------------------------------------------------------------
-- Substitution: capture avoidance
-- ---------------------------------------------------------------------------

-- Inner letrec parameter `x` shadows the outer `let x := #100`.
-- The body `x + #1` should use the letrec's parameter, not the outer binding.
#eval check "subst capture avoidance"
  pl(let x := #100; (rec f x := x + #1) #5)
  pl(#6)

-- Letrec where the self-reference name `f` shadows an outer `let f`.
#eval check "subst capture avoidance rec name"
  pl(let f := #999; (rec f x := if x = #0 then #1 else x * f (x - #1)) #3)
  pl(#6)

-- ---------------------------------------------------------------------------
-- Letrec: self-reference vs parameter name collision
-- ---------------------------------------------------------------------------

-- `rec f f := f` — under LN with counter-based atoms, the two `f` binders
-- get distinct atoms (no shadowing pathology). Inner `f` (the parameter)
-- shadows the outer (recursive self) lexically: body `f` refers to the
-- innermost `f`, which is the parameter. So `(rec f f := f) #42` reduces:
-- app (fix (lam body)) #42 → app (open body fix-self) #42 →
-- (lam body') #42 → open body' #42 = #42.
#eval check "rec f f name collision"
  pl((rec f f := f) #42)
  pl(#42)

-- ---------------------------------------------------------------------------
-- Typed binders
-- ---------------------------------------------------------------------------

#eval check "typed binder fn"
  pl((fun (x : int), x + #1) #9)
  pl(#10)

#eval check "typed binder let"
  pl(let (x : int) := #5; x * #2)
  pl(#10)

#eval check "typed binder rec"
  pl((rec f (n : int) := if n = #0 then #1 else n * f (n - #1)) #4)
  pl(#24)

-- ---------------------------------------------------------------------------
-- Evaluation order with side effects (right-to-left decomp)
-- ---------------------------------------------------------------------------

-- `bump` increments a ref and returns the new value.  In `bump - bump`,
-- right-to-left decomp means the right `bump` fires first (→ 1), then the
-- left (→ 2), so the result is 2 - 1 = 1.  Left-to-right would give
-- 1 - 2 = -1.
#eval check "eval order: binop right before left"
  pl(let r := alloc(#0);
     let bump := rec g _ := (let v := !r + #1; r ← v; v);
     bump #.unit - bump #.unit)
  pl(#1)

-- Same idea for pairs: right side of pair evaluates first.
-- fst((bump, bump)) with right-first: right=1, left=2, fst=2.
#eval check "eval order: pair right before left"
  pl(let r := alloc(#0);
     let bump := rec g _ := (let v := !r + #1; r ← v; v);
     fst((bump #.unit, bump #.unit)))
  pl(#2)

-- ---------------------------------------------------------------------------
-- Store return value
-- ---------------------------------------------------------------------------

#eval check "store returns unit"
  pl(let r := alloc(#0); r ← #42)
  pl(#.unit)

-- ---------------------------------------------------------------------------
-- Rand with both arguments needing reduction
-- ---------------------------------------------------------------------------

-- Both bound (#2 + #1 = 3) and tape arg (if #true then #.unit else #.unit)
-- need evaluation before rand fires.
#eval do
  let v ← runTest pl(rand(#2 + #1, if #true then #.unit else #.unit))
  match v.1 with
  | .lit (.int n) =>
    if n < 0 || n ≥ 3 then
      throw (IO.userError s!"FAIL [rand both redex]: got {n}, expected 0..2")
  | e => throw (IO.userError s!"FAIL [rand both redex type]: got {repr e}")

-- (Pat.annot removed: pattern annotations are now discarded at elaboration,
-- so `Pat.tryMatch` has no annot case. Previous tests targeting this
-- behaviour have been deleted.)

-- ---------------------------------------------------------------------------
-- Multi-arm case with variable-binding pattern in non-first arm
-- ---------------------------------------------------------------------------

-- First arm is a literal (no binding), second arm binds a variable via inl
#eval check "case: var binding in second arm"
  pl(case inl(#7)
     | #(.int 99) => #0
     | inl(x) => x + #1
     | _ => #0)
  pl(#8)

-- Third arm binds
#eval check "case: var binding in third arm"
  pl(case (#5, #6)
     | #(.int 0) => #0
     | inl(_) => #0
     | (x, y) => x + y)
  pl(#11)

-- ---------------------------------------------------------------------------
-- Equality on locations and labels
-- ---------------------------------------------------------------------------

#eval check "eq loc same"
  pl(#(.loc 1) = #(.loc 1))
  pl(#true)
#eval check "eq loc diff"
  pl(#(.loc 1) = #(.loc 2))
  pl(#false)
#eval check "eq lbl same"
  pl(#(.lbl 1) = #(.lbl 1))
  pl(#true)
#eval check "eq lbl diff"
  pl(#(.lbl 1) = #(.lbl 2))
  pl(#false)
#eval check "eq loc vs int"
  pl(#(.loc 1) = #1)
  pl(#false)

-- ---------------------------------------------------------------------------
-- Assert with a redex condition
-- ---------------------------------------------------------------------------

#eval check "assert redex true"
  pl(assert(#1 = #1))
  pl(#.unit)

#eval checkError "assert redex false"
  pl(assert(#1 = #2))

-- ---------------------------------------------------------------------------
-- App with non-value function (decomp through appR)
-- ---------------------------------------------------------------------------

-- Function position is a redex: `if` selects which function to apply
#eval check "app: redex in fn position"
  pl((if #true then (fun x, x + #1) else (fun x, x)) #5)
  pl(#6)

-- Function comes from fst of a pair
#eval check "app: fst as fn"
  pl(fst(((fun x, x * #2), #0)) #7)
  pl(#14)

-- ---------------------------------------------------------------------------
-- Scrut with non-value scrutinee (decomp through scrut context)
-- ---------------------------------------------------------------------------

#eval check "scrut: non-value scrutinee"
  pl(case scrut (#1 + #2) with x | inl(b) => b | inr(_) => #0)
  pl(#3)

#eval check "scrut: scrutinee needs multi-step reduction"
  pl(case scrut (fst((#10, #20))) with #(.int 10) | inl(_) => #99 | inr(_) => #0)
  pl(#99)

-- ---------------------------------------------------------------------------
-- Binder.anon rec name doesn't block substitution
-- ---------------------------------------------------------------------------

-- `fun x, ...` desugars to `rec _ x := ...`.  The anon rec name should NOT
-- block substitution of free variables in the body.
#eval check "anon rec name allows subst"
  pl(let y := #10; (fun x, x + y) #5)
  pl(#15)

-- Nested: outer variable captured through two anonymous rec binders
#eval check "anon rec name nested"
  pl(let z := #3; (fun x, (fun y, x + y + z)) #1 #2)
  pl(#6)

-- ---------------------------------------------------------------------------
-- Equality on compound values gets stuck
-- ---------------------------------------------------------------------------

-- eq works on BaseLit and on .inl/.inr of literals; pairs and functions still stuck.
#eval checkErrorMsg "eq on pairs stuck"
  pl((#1, #2) = (#1, #2))
  "stuck"
-- eq on inl of literals is now supported (matches Rocq's vals_compare_safe).
#eval checkErrorMsg "eq on fn stuck"
  pl((fun x, x) = (fun x, x))
  "stuck"

-- ---------------------------------------------------------------------------
-- Partial application
-- ---------------------------------------------------------------------------

-- `fun x y, x + y` desugars to nested letrecs.  Applying one argument
-- should return a closure (letrec value), which can then be applied.
#eval check "partial application"
  pl(let f := (fun x y, x + y) #3; f #4)
  pl(#7)

#eval check "partial application: stored and reused"
  pl(let add3 := (fun x y, x + y) #3; let a := add3 #10; let b := add3 #20; a + b)
  pl(#36)

-- ---------------------------------------------------------------------------
-- Tapes
-- ---------------------------------------------------------------------------

-- The first tape of the empty state gets label 1.
#eval check "tape"
  pl(tape(#10))
  pl(#(.lbl 1))

-- An empty tape samples fresh, in range.
#eval do
  let v ← runTest pl(let t := tape(#4); rand(#4, t))
  match v.1 with
  | .lit (.int n) =>
    if n < 0 || n ≥ 4 then
      throw (IO.userError s!"FAIL [rand empty tape]: got {n}, expected 0..3")
  | e => throw (IO.userError s!"FAIL [rand empty tape type]: got {repr e}")

-- Presampled values are consumed in order.
#eval do
  let σ : State Float := default
  let t : Tape := ⟨5, [⟨3, by decide⟩, ⟨1, by decide⟩]⟩
  let σ := σ.updateTapes (·.insert 7 t)
  let prog : Exp Float := pl(let a := rand(#5, #(.lbl 7)); let b := rand(#5, #(.lbl 7)); (a, b))
  let r ← run (.eval [] prog σ)
  let (v, σ') := (r.val.rb, r.state)
  if v != pl((#3, #1)) then
    throw (IO.userError s!"FAIL [presampled tape]: got {repr v}")
  if (σ'.tapes[(7 : Int)]?.map fun (t : Tape) => t.presamples.length) != some 0 then
    throw (IO.userError "FAIL [presampled tape]: tape not drained")

-- ---------------------------------------------------------------------------
-- Continuous sampling
-- ---------------------------------------------------------------------------

-- `urand` lands in [0, 1).
#eval do
  let v ← runTest pl(urand)
  match v.1 with
  | .lit (.real r) =>
    if !(0 ≤ r && r < 1) then
      throw (IO.userError s!"FAIL [urand range]: got {r}, expected a value in [0, 1)")
  | e => throw (IO.userError s!"FAIL [urand type]: got {repr e}")

-- ---------------------------------------------------------------------------
-- Real operators
-- ---------------------------------------------------------------------------

#eval check "real 2.5 * 4 = 10" pl(#real 2.5 * #real 4) pl(#real 10)
#eval check "real 1 / 4 = 0.25" pl(#real 1 / #real 4) pl(#real 0.25)
#eval check "real 5 - 2 = 3" pl(#real 5 - #real 2) pl(#real 3)
#eval check "floor 2.5 = 2" pl(floor(#real 2.5)) pl(#2)
#eval check "floor -2.5 = -3" pl(floor(#real (-2.5))) pl(#(-3))
#eval check "floor -3 = -3" pl(floor(#real (-3))) pl(#(-3))
#eval check "floor 2^60" pl(floor(#real 1152921504606846976.0)) pl(#1152921504606846976)
#eval check "floor -2^60 - 2^8" pl(floor(#real (-1152921504606847232.0)))
  pl(#(-1152921504606847232))
#eval check "ceil -2.5 = -2" pl(ceil(#real (-2.5))) pl(#(-2))
#eval check "ceil 2.5 = 3" pl(ceil(#real 2.5)) pl(#3)
#eval check "log 1 = 0" pl(log(#real 1)) pl(#real 0)
#eval check "exp 0 = 1" pl(exp(#real 0)) pl(#real 1)
#eval check "sqrt 9 = 3" pl(sqrt(#real 9)) pl(#real 3)
#eval check "sin 0 = 0" pl(sin(#real 0)) pl(#real 0)
#eval check "cos 0 = 1" pl(cos(#real 0)) pl(#real 1)
#eval check "atan 0 = 0" pl(atan(#real 0)) pl(#real 0)
#eval check "tan 0 = 0" pl(tan(#real 0)) pl(#real 0)
#eval check "4 atan 1 = pi" pl(#real 4 * atan(#real 1)) pl(#pi)
#eval check "pow 2 10 = 1024" pl(floor(pow(#real 2, #real 10) + #real 0.5)) pl(#1024)
-- Integer operands and mixed operands are stuck.
#eval checkError "floor of int" pl(floor(#2))
#eval checkError "log of int" pl(log(#2))
#eval checkError "real times int" pl(#real 2 * #3)
#eval checkError "real mod" pl(#real 5 % #real 2)

/-- Both engines return a real literal satisfying `p`. -/
private def checkReal (name : String) (prog : Exp Float) (p : Float → Bool) : IO Unit := do
  for (engine, runner) in [("env", runTest), ("subst", runTestSubst)] do
    match (← runner prog).1 with
    | .lit (.real r) =>
      if !p r then throw (IO.userError s!"FAIL [{name}, {engine}]: got {r}")
    | e => throw (IO.userError s!"FAIL [{name}, {engine}]: got {repr e}")

-- Runtime domain failures: IEEE results flow on instead of the ℝ model's total conventions.
#eval checkReal "log 0 = -inf" pl(log(#real 0)) fun r => r.isInf && r < 0
#eval checkReal "log -1 = NaN" pl(log(#real (-1))) Float.isNaN
#eval checkReal "sqrt -1 = NaN" pl(sqrt(#real (-1))) Float.isNaN
#eval checkReal "1 / 0 = inf" pl(#real 1 / #real 0) Float.isInf
-- The ℝ model has `pow(0, y) = 1` via `log 0 = 0`; at runtime `exp (3 * -∞) = 0`.
#eval check "pow 0 3 = 0 at runtime" pl(pow(#real 0, #real 3)) pl(#real 0)
#eval check "floor NaN = 0" pl(floor(sqrt(#real (-1)))) pl(#0)

def main : IO Unit :=
  IO.println "All big-step interpreter tests passed."
