import MetrologyAsm.Examples.OTP.Layout
import MetrologyAsm.Examples.OTP.Steps

/-! # Machine state effects used in the compiled OTP execution -/

namespace MetrologyAsm.OTP

open Sail

/-- Commit a register-writing instruction at a compiled word index. -/
def registerState (s : Mach) (base : BitVec 64) (index : Nat) (destination : Register)
    (value : RegisterType destination) : Mach :=
  commitState (registerBodyState s (codePC base index) destination value) (codePC base (index + 1))

/-- A permitted register write and sequential commit retain the configured user profile. -/
theorem _root_.MetrologyAsm.UserConfig.otpRegisterState {s : Mach} (h : UserConfig s)
    (base : BitVec 64) (index : Nat) (destination : Register) (value : RegisterType destination)
    (hpolicy : userRegPolicy destination value) :
    UserConfig (registerState s base index destination value) :=
  (h.registerBodyState (codePC base index) destination value hpolicy).insert .PC _ trivial

/-- Commit a doubleword store at a compiled instruction index. -/
def storeState (s : Mach) (base : BitVec 64) (index : Nat) (address value : BitVec 64) : Mach :=
  commitState (storeBodyState s (codePC base index) address value) (codePC base (index + 1))

/-- A scratch store and sequential commit retain the configured user profile. -/
theorem _root_.MetrologyAsm.UserConfig.otpStoreState {s : Mach} (h : UserConfig s)
    (base : BitVec 64) (index : Nat) (address value : BitVec 64) :
    UserConfig (storeState s base index address value) :=
  ((h.counterState.sequentialState _).write64State address value).insert .PC _ trivial

end MetrologyAsm.OTP
