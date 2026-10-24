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

end MetrologyAsm
