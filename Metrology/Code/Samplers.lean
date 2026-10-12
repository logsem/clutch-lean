module

public import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # Sampler programs

Specified in `TotalEris/Examples/Samplers` at `rT = ℝ`; generic in the reals so that
`#sample` can also run them at `rT = Float`. -/

namespace ProbLang
namespace TotalEris
namespace Examples

/-! ## Bernoulli iteration -/

@[pl_fold]
def GeometricTrial {rT : Type _} : Exp rT := pl%
  rec geo trial N := if trial #.unit then geo trial (N + #1) else N

@[pl_fold]
def IterTrial {rT : Type _} : Exp rT := pl%
  rec iter b k :=
    if k = #0 then #true
    else if b #.unit then iter b (k - #1) else #false

/-! ## Continuous-uniform trials -/

@[pl_fold]
def DecrTrial {rT : Type _} : Exp rT := pl%
  rec trial N x :=
    let y := urand;
    if y < x then trial (N + #1) y else N

@[pl_fold]
def LeHalf {rT : Type _} [ProbLangℝ rT] : Exp rT :=
  pl% fun x, x <= #(.real (ProbLangℝ.realOfRat (1 / 2)))

@[pl_fold]
def FairCoin {rT : Type _} [ProbLangℝ rT] : Exp rT := pl%
  fun _u,
    let u := urand;
    &LeHalf u

@[pl_fold]
def BNEHalf {rT : Type _} [ProbLangℝ rT] : Exp rT := pl%
  fun _u,
    let x := urand;
    if &LeHalf x then
      let y := &DecrTrial #0 x;
      (y % #2 = #1)
    else #true

@[pl_fold]
def NegExp {rT : Type _} : Exp rT := pl%
  rec trial L :=
    let x := urand;
    let y := &DecrTrial #0 x;
    if (y % #2 = #0) then (L, x) else trial (L + #1)

/-! ## Index selector -/

@[pl_fold]
def C {rT : Type _} : Exp rT := pl%
  fun m, let v := rand(m + #2, #.unit); if v = #0 then #0 else if v = #1 then #1 else #2

@[pl_fold]
def Bii {rT : Type _} : Exp rT := pl%
  fun k, fun x,
    let f := &C (#2 * k);
    let r := urand;
    if f = #0 then #true else (if f = #1 then (x < r) else #false)

@[pl_fold]
def S {rT : Type _} : Exp rT := pl%
  rec trial k x y N :=
    let z := urand;
    if y < z then N else (if &Bii k x then N else trial k x z (N + #1))

@[pl_fold]
def S0 {rT : Type _} : Exp rT := pl%
  fun k, fun x,
    let z := urand;
    if x < z then #0 else (if &Bii k x then #0 else &S k x z #1)

@[pl_fold]
def B {rT : Type _} : Exp rT := pl%
  fun k, fun x, (&S0 k x % #2 = #0)

/-! ## Gaussian -/

@[pl_fold]
def G1 {rT : Type _} [ProbLangℝ rT] : Exp rT := pl%
  rec trial u :=
    let k := &GeometricTrial &BNEHalf #0;
    if &IterTrial &BNEHalf (k * (k - #1)) then k else trial #.unit

@[pl_fold]
def G2 {rT : Type _} [ProbLangℝ rT] : Exp rT := pl%
  rec trial u :=
    let k := &G1 #.unit;
    let x := urand;
    if &IterTrial (fun _u, &B k x) (k + #1) then (x, k) else trial #.unit

@[pl_fold]
def Gauss {rT : Type _} [ProbLangℝ rT] : Exp rT := pl%
  fun _u,
    let p := &G2 #.unit;
    let y := fst(p) + toReal(snd(p));
    let b := &FairCoin #.unit;
    if b then -y else y

end Examples
end TotalEris
end ProbLang
