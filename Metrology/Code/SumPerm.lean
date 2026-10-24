module

public import Metrology.Code.Switching
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! # The sum of two random permutations

Dai, Hoang and Tessaro's `XOR2` (ePrint 2017/537, App. A) with `+ mod N` for `⊕`: two lazy random
permutations of `{0, …, N-1}`, queried at most `Q` times by an adversary. A fresh query
allocates one tape per permutation before drawing from either, so a proof can presample both draws
in one step. -/

namespace ProbLang

variable {rT : Type _}

namespace SumPerm

open Switching

variable (N : Int)

/-- Draw from tape `α` an element of the list in cell `fv`, remove it, and return it. -/
@[pl_fold] def drawFresh : Exp rT := pl%
  fun fv α,
    let n := rand(&listLength (!fv), α);
    case! (&listRemoveNth (!fv) n)
    | inl(_u) => #0 -- unreachable: `n` is in range
    | inr(p) => (fv ← snd(p); fst(p))

/-- The sum mod `N` of two lazily sampled random permutations of `{0, …, N-1}`, memoised per
input. -/
def sumPerm : Exp rT := pl%
  -- `.1`: the expression of the list value
  let fv₁ := alloc({(intListVal ((List.range N.toNat).map Int.ofNat)).1});
  let fv₂ := alloc({(intListVal ((List.range N.toNat).map Int.ofNat)).1});
  let m := &initMap #();
  fun x,
    case! (&getMap m x)
    | inl(_u) =>
      (let α := tape(&listLength (!fv₁));
       let β := tape(&listLength (!fv₂));
       let a := &drawFresh fv₁ α;
       let b := &drawFresh fv₂ β;
       let y := (a + b) % #N;
       &setMap m x y;
       y)
    | inr(y) => y

/-- Forward at most `q` calls to `f` as `inr (f x)`, then answer `inl ()`. -/
@[pl_fold] def bounded : Exp rT := pl%
  fun q f,
    let c := alloc(#0);
    fun x, if !c < q then (c ← !c + #1; inr(f x)) else inl(#())

/-- The real PRF game: the adversary `A` gets `Q` queries to `sumPerm N`. -/
def realGame (Q : Int) (A : Exp rT) : Exp rT := pl% {A} (&bounded #Q {sumPerm N})

/-- The ideal PRF game: the adversary `A` gets `Q` queries to a random function. -/
def idealGame (Q : Int) (A : Exp rT) : Exp rT := pl% {A} (&bounded #Q {randomFunction N})

end SumPerm
end ProbLang
