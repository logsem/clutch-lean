module

public import Metrology.Micrometer.AppWeakestpre
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.ProbLang.Syntax.LocallyClosed
public import Iris.Instances.Lib.NaInvariants
public import Iris.Instances.Lib.Invariants

/-! # Countable namespace indices

`Pos.Countable` instances for `Nat`, `Int` and products, used to index invariant namespaces. -/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS

namespace ProbLang

theorem Pos.toNat_succ (p : Pos) : p.succ.toNat = p.toNat + 1 := by
  induction p with
  | xH => rfl
  | xI p ih => show 2 * p.succ.toNat = _; rw [ih]; simp [Pos.toNat]; ring
  | xO p => show 2 * p.toNat + 1 = _; simp [Pos.toNat]

theorem Pos.toNat_ofNat (n : Nat) : (Pos.ofNat n).toNat = n + 1 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [Pos.ofNat, Pos.toNat_succ, ih]

/-- Naturals encode as positive numbers by successor. -/
instance posCountable_nat : Pos.Countable Nat where
  encode n := Pos.ofNat n
  decode p := some (p.toNat - 1)
  decode_encode n := by simp [Pos.toNat_ofNat]

/-- Encode `Int` into `Nat` via the standard zigzag: `n ≥ 0 ↦ 2n`, `n < 0 ↦ -2n - 1`. -/
instance posCountable_int : Pos.Countable Int where
  encode z :=
    Pos.Countable.encode (A := Nat)
      (if 0 ≤ z then 2 * z.toNat else 2 * (-z - 1).toNat + 1)
  decode p := (Pos.Countable.decode (A := Nat) p).bind fun k =>
    some (if k % 2 = 0 then (k / 2 : Int) else -((k - 1) / 2 : Int) - 1)
  decode_encode z := by
    rw [Pos.Countable.decode_encode, Option.bind_some]
    by_cases hz : 0 ≤ z
    · rw [ite_eq_left hz, ite_eq_left (Nat.mul_mod_right 2 _)]
      push_cast
      rw [Int.mul_ediv_cancel_left _ (by decide), Int.toNat_of_nonneg hz]
    · have hmod : (2 * (-z - 1).toNat + 1) % 2 ≠ 0 := by omega
      have := Int.toNat_of_nonneg (show 0 ≤ -z - 1 by omega)
      rw [ite_eq_right hz, ite_eq_right hmod]
      congr 1
      omega

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
