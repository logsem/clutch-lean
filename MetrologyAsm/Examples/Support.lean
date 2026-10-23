import MetrologyAsm.ABI.Interface
import MetrologyAsm.Profile.Witness

/-! # Shared concrete placements and states for assembly examples -/

set_option maxRecDepth 100000

namespace MetrologyAsm

open ProbLang ProbLang.Asm RiscvZkvm.Sail.Functions
open Sail.ConcurrencyInterfaceV1

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

/-- A concrete aligned placement for two distinct logical cells. -/
def witnessPlacement (l : Loc) : Placement where
  addr k := if k = l then 0x80001000#64 else 0x80001008#64
  codeBase := 0x80000000#64
  importAddr _ := 0x80005000#64
  retAddr := 0x80002000#64

/-- The witness's active register state keeps the formal profile and installs the ABI bindings. -/
noncomputable def witnessRegisters : Mach :=
  let s := profileWitness
  let regs := s.regs.insert Register.PC 0x80000000#64
  let regs := regs.insert .x1 0x80002000#64
  let regs := regs.insert .x2 0x80004000#64
  let regs := regs.insert .x10 0x80001000#64
  let regs := regs.insert .x11 0x80001008#64
  let regs := regs.insert .mtvec 0x80003000#64
  let regs := regs.insert .stvec 0x80003000#64
  { s with regs }

/-- The witness's register installation satisfies the complete open user profile. -/
theorem witnessRegisters_config : UserConfig witnessRegisters := by
  exact (((((((profileWitness_config.insert .PC _ trivial).insert .x1 _ trivial).insert
    .x2 _ trivial).insert .x10 _ trivial).insert .x11 _ trivial).insert .mtvec _
    (by simp only [userRegPolicy]; decide +kernel)).insert .stvec _
    (by simp only [userRegPolicy]; decide +kernel))

end MetrologyAsm
