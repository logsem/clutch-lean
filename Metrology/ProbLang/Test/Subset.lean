module

public import Metrology.ProbLang.Subset
public import Metrology.ProbLang.Syntax.Notation
public import Metrology.Code.Coins

/-! # Tests for syntactic subsets and the `problang` panel -/

@[expose] public section

namespace ProbLang

open Exp Features

section

problang
  reals rT
  subset -urand -tape -sample

variable [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]

/-! ## Membership by computation -/

example : (pl(let x := rand(#2, #()); x + #1) : Exp).InSubset subset% := by in_subset

example : TotalEris.Examples.heads.InSubset (rT := rT) subset% := by in_subset

example : ¬ (pl(let x := urand; x) : Exp).InSubset subset% := by
  simp [inSubset, without, Features.allowsFamily, Features.allowsTapeArg, unifIntName,
    unifRealName]

example : ¬ (pl(let α := tape(#3); rand(#3, α)) : Exp).InSubset subset% := by
  simp [inSubset, without]

/-! ## Side conditions from a subset hypothesis -/

example (f g : Exp) (hf : f.InSubset subset%) (hg : g.InSubset subset%) :
    ¬ pl({f} {g}).decomp.2.IsSampler := by
  problang_side

example (e : Exp) (σ : State) (he : e.InSubset subset%) : IsAtomicSupport (primStep ⟨e, σ⟩) :=
  primStep_atomic e σ

end

section

problang
  reals rT
  subset -urand -sample

variable [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]

/-! ## Without samplers -/

example : ¬ (pl(sample(2, #1)) : Exp).InSubset subset% := by
  simp [inSubset, without, Features.allowsFamily, Features.allowsTapeArg, unifIntName,
    unifRealName]

example : (pl(sample(0, #1)) : Exp).InSubset subset% := by in_subset

example (e : Exp) (he : e.InSubset subset%) : ¬ e.decomp.2.IsSampler := by
  problang_side

example (e : Exp) (σ : State) (he : e.InSubset subset%) : IsAtomicSupport (primStep ⟨e, σ⟩) :=
  primStep_atomic e σ

end

section

problang
  reals rT
  subset -tape

/-! ## Random variables without tapes -/

example : (pl(let x := randvar(0, #1); test(0, x, #2)) : Exp).InSubset subset% := by in_subset

example (l : Lbl) : (Exp.lit (.lbl l) : Exp).InSubset subset% := rfl

example : ¬ (pl(let α := tape(#3); rand(#3, α)) : Exp).InSubset subset% := by
  simp [inSubset, without]

end

section

problang
  reals := Int
  subset -urand

example : (pl(let α := tape(#3); rand(#3, α)) : Exp).InSubset subset% := by in_subset

end

/-- error: unknown ProbLang feature `foo` -/
#guard_msgs in
problang
  subset -foo

/--
error: could not synthesize default value for parameter 'rT' using tactics
---
error: no `reals` setting: write the argument, or set `reals` in a `problang` panel
-/
#guard_msgs in
example (e : Exp) : e = e := rfl

section

problang
  reals := Int

/--
error: Type mismatch
  e
has type
  Exp Bool
but is expected to have type
  Exp ℤ
-/
#guard_msgs in
example (e : Exp Bool) : True := by
  have := (e : Exp)
  trivial

-- autoParams run after default instances, so a bare numeral keeps `ℕ`; see `Metrology.Settings`
/-- info: pl(#3) : Exp ℕ -/
#guard_msgs in
#check (Exp.lit (.real 3) : Exp)

/-- info: pl(#3) : Exp ℤ -/
#guard_msgs in
#check (Exp.lit (.real (3 : rt%)) : Exp)

/-- info: pl(#3) : Exp ℤ -/
#guard_msgs in
#check pl(#real 3)

end

end ProbLang
