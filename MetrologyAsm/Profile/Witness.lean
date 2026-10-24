import MetrologyAsm.Profile.Initial

/-! # Consistency of the user-mode profile -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions
open Sail
open Vector (replicate)
open List (foldl_cons mem_cons)

/-- Canonical values witnessing the user-mode register constraints. -/
noncomputable def profileDefault : (r : Register) → RegisterType r
  | .hart_state => .HART_ACTIVE ()
  | .cur_privilege => .User
  | .misa => 0x8000000000141100#64
  | .mstatus => 2#64 <<< 32 ||| 2#64 <<< 34
  | .satp => 0#64
  | .mseccfg => 0#64
  | .menvcfg => 0#64
  | .senvcfg => 0#64
  | .mie => 0#64
  | .mcountinhibit => 4#32
  | .elp => 0#1
  | .fcsr => 0#32
  | .mtvec => 0#64
  | .stvec => 0#64
  | .htif_tohost_base => none
  | .pmpcfg_n => (replicate 64 0#8).set 0 0x0f#8
  | .pmpaddr_n => (replicate 64 0#64).set 0 0x40000000#64
  | .pma_regions => [userRamRegion]
  | r => defaultRegister r

set_option maxRecDepth 100000 in
/-- Every generated register occurs in the finite register enumeration. -/
theorem allRegisters_complete (r : Register) : r ∈ allRegisters := by
  cases r <;> simp [allRegisters]

set_option maxRecDepth 100000 in
/-- Every canonical register value satisfies its user-mode policy. -/
theorem profileDefault_policy (r : Register) : userRegPolicy r (profileDefault r) := by
  cases r <;> simp only [profileDefault, userRegPolicy]
  all_goals first | exact ⟨[], rfl⟩ | decide +kernel

/-- Inserting each listed register returns its assigned value at every listed key. -/
theorem get?_foldRegisters (f : (r : Register) → RegisterType r) (xs : List Register)
    (m : Std.ExtDHashMap Register RegisterType) (r : Register) :
    (xs.foldl (fun m q => m.insert q (f q)) m).get? r =
      if r ∈ xs then some (f r) else m.get? r := by
  induction xs generalizing m with
  | nil => rfl
  | cons q xs ih =>
    rw [foldl_cons, ih]
    by_cases hx : r ∈ xs
    · simp [hx, mem_cons]
    · by_cases hq : q = r
      · subst q
        simp [hx]
      · simp [hx, mem_cons, Std.ExtDHashMap.get?_insert, hq, Ne.symm hq]

/-- A machine state witnessing consistency of the user-mode register profile. -/
noncomputable def profileWitness : Mach := fillRegisters profileDefault

/-- The user-mode register profile has a concrete inhabitant. -/
theorem profileWitness_config : UserConfig profileWitness := by
  constructor
  intro r
  refine ⟨profileDefault r, ?_, profileDefault_policy r⟩
  simp only [profileWitness, fillRegisters]
  rw [get?_foldRegisters]
  simp [allRegisters_complete]

/-- Install consecutive image bytes into a finite Sail byte memory. -/
def witnessImageBytes : List UInt8 → Nat → Std.ExtHashMap Nat (BitVec 8) →
    Std.ExtHashMap Nat (BitVec 8)
  | [], _, mem => mem
  | byte :: bytes, base, mem =>
    (witnessImageBytes bytes (base + 1) mem).insert base (BitVec.ofNat 8 byte.toNat)

/-- Every installed image byte is available at its consecutive physical address. -/
theorem witnessImageBytes_get (bytes : List UInt8) (base : Nat)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (i : Nat) (byte : UInt8)
    (hi : bytes[i]? = some byte) :
    (witnessImageBytes bytes base mem).get? (base + i) = some (BitVec.ofNat 8 byte.toNat) := by
  induction bytes generalizing base i with
  | nil => simp at hi
  | cons head bytes ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst byte
      simp [witnessImageBytes]
    | succ i =>
      have hne : base ≠ base + (i + 1) := by omega
      have htail := ih (base + 1) i (by simpa using hi)
      simpa [witnessImageBytes, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert,
        hne, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htail

/-- Installing consecutive image bytes preserves every memory address outside their interval. -/
theorem witnessImageBytes_get_outside (bytes : List UInt8) (base : Nat)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (address : Nat)
    (hout : address < base ∨ base + bytes.length ≤ address) :
    (witnessImageBytes bytes base mem).get? address = mem.get? address := by
  induction bytes generalizing base with
  | nil => rfl
  | cons byte bytes ih =>
    have hne : base ≠ address := by simp only [List.length_cons] at hout; omega
    rw [witnessImageBytes]
    simpa [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert, hne] using
      ih (base + 1) (by simp only [List.length_cons] at hout; omega)

end MetrologyAsm
