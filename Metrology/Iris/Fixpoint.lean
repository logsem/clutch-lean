module

public import Iris.BI.Lib.Fixpoint

/-!
# Fixpoint and discrete-OFE lemmas

Non-expansiveness of least fixpoints and of functions out of discrete OFEs.
-/

@[expose] public section

open Iris Iris.BI OFE

/-- Pointwise-close functors have close least fixpoints. -/
theorem least_fixpoint_ne_outer {PROP : Type _} [BI PROP] {A : Type _} [OFE A]
    {F1 F2 : (A → PROP) → (A → PROP)} {n : Nat} (HF : ∀ Φ x, F1 Φ x ≡{n}≡ F2 Φ x)
    {x1 x2 : A} (Hx : x1 ≡{n}≡ x2) : bi_least_fixpoint F1 x1 ≡{n}≡ bi_least_fixpoint F2 x2 :=
  -- `bi_least_fixpoint F x = ∀ Φ, □ (∀ y, F Φ y -∗ Φ y) -∗ Φ x`: apply `ne` to each connective
  forall_ne fun _ =>
    wand_ne.ne (intuitionistically_ne.ne (forall_ne fun _ => wand_ne.ne (HF _ _) .rfl))
      (NonExpansive.ne Hx)

/-- Every function out of a discrete OFE is non-expansive. -/
theorem nonExpansive_of_discrete_leibniz {T : Type _} [OFE T] [Discrete T]
    {P : Type _} [OFE P] (f : T → P) : NonExpansive f :=
  ⟨fun _ _ _ hd => .of_eq (congrArg f (Discrete.discrete hd))⟩
