import Metrology.Micrometer.UnifInt

/-! # Byte XOR and the exact one-time-pad coupling -/

namespace MetrologyAsm.OTP

open MeasureTheory GradedLifting ProbLang

/-- XOR two integers as bytes and expose the unsigned result as a logical integer. -/
def byteXor (message key : Int) : Int :=
  ((BitVec.ofInt 8 message) ^^^ (BitVec.ofInt 8 key)).toNat

/-- The XOR result is always a representable unsigned byte. -/
theorem byteXor_range (message key : Int) :
    0 ≤ byteXor message key ∧ byteXor message key < 256 := by
  have h := ((BitVec.ofInt 8 message) ^^^ (BitVec.ofInt 8 key)).isLt
  exact ⟨Int.natCast_nonneg _, by simp only [byteXor]; omega⟩

/-- Applying the same byte mask twice recovers the original key. -/
theorem byteXor_involutive (message key : Int) (hk : 0 ≤ key ∧ key < 256) :
    byteXor message (byteXor message key) = key := by
  simp only [byteXor, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  norm_num
  rw [Int.emod_eq_of_lt hk.1 hk.2]
  omega

/-- The machine's doubleword XOR agrees with byte encryption on representable byte inputs. -/
theorem byteXor_word64 (message key : Int) (hm : 0 ≤ message ∧ message < 256)
    (hk : 0 ≤ key ∧ key < 256) :
    BitVec.ofInt 64 (byteXor message key) = BitVec.ofInt 64 message ^^^ BitVec.ofInt 64 key := by
  have hc := byteXor_range message key
  have hm64 : message < (2 ^ 64 : Nat) := by omega
  have hk64 : key < (2 ^ 64 : Nat) := by omega
  have hc64 : byteXor message key < (2 ^ 64 : Nat) := by omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_xor, BitVec.toNat_ofInt]
  rw [Int.emod_eq_of_lt hc.1 hc64, Int.emod_eq_of_lt hm.1 hm64,
    Int.emod_eq_of_lt hk.1 hk64]
  simp only [byteXor, Int.toNat_natCast, BitVec.toNat_xor, BitVec.toNat_ofInt]
  norm_num
  rw [Int.emod_eq_of_lt hm.1 hm.2, Int.emod_eq_of_lt hk.1 hk.2]

/-- Masking by a fixed message is a bijection of the byte interval. -/
theorem byteXor_bij (message output : Int) (h0 : 0 ≤ output) (h256 : output < 256) :
    ∃! key : Int, (0 ≤ key ∧ key < 256) ∧ byteXor message key = output := by
  refine ⟨byteXor message output, ⟨byteXor_range _ _, byteXor_involutive _ _ ⟨h0, h256⟩⟩, ?_⟩
  rintro key ⟨hk, heq⟩
  calc
    key = byteXor message (byteXor message key) := (byteXor_involutive _ _ hk).symm
    _ = byteXor message output := congrArg (byteXor message) heq

/-- XOR masking preserves the exact uniform byte measure. -/
theorem byteXor_uniform (message : Int) :
    (unifInt 256 (by norm_num)).map (byteXor message) = unifInt 256 (by norm_num) := by
  apply unifInt_map_bijOn (by norm_num) (byteXor message)
  · exact fun _ _ _ => byteXor_range _ _
  · exact byteXor_bij message

/-- Couple a uniform key with an ideal uniform ciphertext at zero cost. -/
theorem byteXor_coupling {B : Type} [Zero B] [Add B] [Preorder B] [OrderTop B]
    {L : GradedLifting.{0} B} [L.IsLawful] [L.IsReflexive] [L.IsSupportLocal] (message : Int) :
    L.Rel 0 (fun key ciphertext => 0 ≤ key ∧ key < 256 ∧ ciphertext = byteXor message key)
      (unifInt 256 (by norm_num)) (unifInt 256 (by norm_num)) := by
  apply unifInt_rel_bij L (by norm_num) (byteXor message)
  · exact fun _ _ _ => byteXor_range _ _
  · exact byteXor_bij message

end MetrologyAsm.OTP
