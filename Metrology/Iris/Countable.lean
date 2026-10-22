module

public import Iris.Std.Positives

/-! # Countable pairs

A `Pos.Countable` instance for products, used to index invariant namespaces. -/

@[expose] public section

open Std Iris.Std

/-- Pairs encode by flattening the encodings of their components. -/
instance posCountable_prod {A B : Type} [Pos.Countable A] [Pos.Countable B] :
    Pos.Countable (A × B) where
  encode p := Pos.flatten [Pos.Countable.encode p.1, Pos.Countable.encode p.2]
  decode p := match Pos.unflatten p with
    | some [a, b] =>
      (Pos.Countable.decode a).bind fun x =>
      (Pos.Countable.decode b).bind fun y =>
      some (x, y)
    | _ => none
  decode_encode p := by
    show (match Pos.unflatten
        (Pos.flatten [Pos.Countable.encode p.1, Pos.Countable.encode p.2]) with
      | _ => _) = _
    rw [Pos.unflatten_flatten]
    show Option.bind (Pos.Countable.decode (Pos.Countable.encode p.1)) _ = _
    rw [Pos.Countable.decode_encode]
    show Option.bind (Pos.Countable.decode (Pos.Countable.encode p.2)) _ = _
    rw [Pos.Countable.decode_encode]
    rfl
