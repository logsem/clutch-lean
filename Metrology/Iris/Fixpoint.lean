module

public import Iris.BI.Lib.Fixpoint

@[expose] public section

/-! # Shared `bi_least_fixpoint` utilities -/

open Iris Iris.BI OFE

theorem least_fixpoint_ne_outer {PROP : Type _} [BI PROP] {A : Type _} [OFE A]
    {F1 F2 : (A → PROP) → (A → PROP)} {n : Nat} (HF : ∀ Φ x, F1 Φ x ≡{n}≡ F2 Φ x)
    {x1 x2 : A} (Hx : x1 ≡{n}≡ x2) : bi_least_fixpoint F1 x1 ≡{n}≡ bi_least_fixpoint F2 x2 :=
  forall_ne fun _ =>
    wand_ne.ne (intuitionistically_ne.ne (forall_ne fun _ => wand_ne.ne (HF _ _) .rfl))
      (NonExpansive.ne Hx)

theorem nonExpansive_of_discrete_leibniz {T : Type _} [COFE T] [OFE.Discrete T]
    {P : Type _} [OFE P] (f : T → P) : NonExpansive f :=
  ⟨fun _ _ _ hd => .of_eq (congrArg f (OFE.Discrete.discrete hd))⟩

theorem eq_of_dist_discrete_leibniz {T : Type _} [COFE T] [OFE.Discrete T]
    {n : Nat} {x y : T} (hd : x ≡{n}≡ y) : x = y :=
  OFE.Discrete.discrete hd
