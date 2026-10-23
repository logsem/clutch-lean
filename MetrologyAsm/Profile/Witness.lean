import MetrologyAsm.Profile.Initial

/-! # Consistency of the user-mode profile -/

set_option maxRecDepth 100000

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions
open Sail
open Std.ExtDHashMap

/-- Canonical values witnessing the user-mode register constraints. -/
noncomputable def profileDefault : (r : Register) → RegisterType r
  | .hart_state => .HART_ACTIVE ()
  | .cur_privilege => .User
  | .misa => 0x8000000000141100#64
  | .mstatus => 0xA00000000#64
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
  | .pmpcfg_n => (Vector.replicate 64 0#8).set 0 0x0f#8
  | .pmpaddr_n => (Vector.replicate 64 0#64).set 0 0x40000000#64
  | .pma_regions => [userRamRegion]
  | r => defaultRegister r

/-- Every generated register occurs in the finite register enumeration. -/
theorem allRegisters_complete (r : Register) : r ∈ allRegisters := by
  cases r <;> simp [allRegisters]

/-- Every canonical register value satisfies its user-mode policy. -/
theorem profileDefault_policy (r : Register) : userRegPolicy r (profileDefault r) := by
  cases r <;> simp [profileDefault, userRegPolicy]
  all_goals decide +kernel

/-- Inserting each listed register returns its assigned value at every listed key. -/
theorem get?_foldRegisters (f : (r : Register) → RegisterType r) (xs : List Register)
    (m : Std.ExtDHashMap Register RegisterType) (r : Register) :
    (xs.foldl (fun m q => insert m q (f q)) m).get? r =
      if r ∈ xs then some (f r) else m.get? r := by
  induction xs generalizing m with
  | nil => rfl
  | cons q xs ih =>
    rw [List.foldl_cons, ih]
    by_cases hx : r ∈ xs
    · simp [hx, List.mem_cons]
    · by_cases hq : q = r
      · subst q
        simp [hx]
      · simp [hx, List.mem_cons, get?_insert, hq, Ne.symm hq]

/-- A machine state witnessing consistency of the user-mode register profile. -/
noncomputable def profileWitness : Mach :=
  { (default : Mach) with
    regs := allRegisters.foldl (fun m r => insert m r (profileDefault r)) default }

/-- The user-mode register profile has a concrete inhabitant. -/
theorem profileWitness_config : UserConfig profileWitness := by
  constructor
  intro r
  refine ⟨profileDefault r, ?_, profileDefault_policy r⟩
  change (allRegisters.foldl (fun m r => insert m r (profileDefault r)) default).get? r = _
  rw [get?_foldRegisters]
  simp [allRegisters_complete]

end MetrologyAsm
