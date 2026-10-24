import MetrologyAsm.Profile.Config
import MetrologyAsm.Sail.RegisterRules

/-! # Sail reductions for the user-mode profile -/

namespace MetrologyAsm

open RiscvZkvm.Sail.Functions
open Sail

namespace UserConfig

variable {s : Mach} (h : UserConfig s)

include h

/-- Supervisor-mode support is enabled in the user-mode profile. -/
theorem enabled_S :
    runSail (currentlyEnabled .Ext_S) s = some (true, s) := by
  obtain ⟨misa, hmisa, hp⟩ := h.regs .misa
  simp only [userRegPolicy] at hp
  obtain ⟨_, _, _, _, hS, _⟩ := hp
  simp only [runSail, currentlyEnabled, bind, EStateM.bind, readReg_eq hmisa, pure, EStateM.pure,
    hartSupports, hS, BEq.rfl, Bool.and_self]
  all_goals rfl

/-- The configured misa register has the compressed bit clear. -/
theorem misa_C : ∃ misa, s.regs.get? Register.misa = some misa ∧ _get_Misa_C misa = 0#1 := by
  obtain ⟨misa, hmisa, hp⟩ := h.regs .misa
  exact ⟨misa, hmisa, hp.2.2.2.2.2⟩

/-- Compressed instructions are disabled in the user-mode profile. -/
theorem disabled_C :
    runSail (currentlyEnabled .Ext_C) s = some (false, s) := by
  obtain ⟨misa, hmisa, hC⟩ := h.misa_C
  simp only [runSail, currentlyEnabled, bind, EStateM.bind, readReg_eq hmisa, pure, EStateM.pure,
    hartSupports, Bool.false_and, Bool.false_or, Bool.and_self, Bool.true_or, Bool.and_true,
    Bool.true_and, hC, BitVec.reduceBEq, Bool.and_false]
  all_goals rfl

/-- The compressed base extension is disabled in the user-mode profile. -/
theorem disabled_Zca :
    runSail (currentlyEnabled .Ext_Zca) s = some (false, s) := by
  obtain ⟨misa, hmisa, hC⟩ := h.misa_C
  simp only [runSail, currentlyEnabled, bind, EStateM.bind, readReg_eq hmisa, pure, EStateM.pure,
    hartSupports, Bool.false_and, Bool.false_or, Bool.and_self, Bool.true_or, Bool.and_true,
    Bool.true_and, hC, BitVec.reduceBEq, Bool.and_false, Option.some.injEq, Prod.mk.injEq,
    and_true]
  all_goals rfl

/-- With MPRV clear, the effective privilege of every access is User. -/
theorem effectivePrivilege_user (access : MemoryAccessType mem_payload)
    {m : BitVec 64} (hm : s.regs.get? Register.mstatus = some m) :
    runSail (effectivePrivilege access m .User) s = some (.User, s) := by
  obtain ⟨v, hv, hp⟩ := h.regs .mstatus
  have heq : v = m := Option.some.inj (hv.symm.trans hm)
  subst v
  simp only [userRegPolicy] at hp
  simp [runSail, effectivePrivilege, hp.2.2, pure, EStateM.pure]

/-- Supervisor translation queries use the configured 64-bit architecture. -/
theorem architecture_supervisor :
    runSail (architecture .Supervisor) s = some (.RV64, s) := by
  obtain ⟨m, hm, hp⟩ := h.regs .mstatus
  simp only [userRegPolicy] at hp
  simp [runSail, architecture, readReg_eq hm, hp.1, architecture_bits_backwards,
    bind, EStateM.bind, pure, EStateM.pure]

/-- User arithmetic uses the configured 64-bit architecture. -/
theorem architecture_user :
    runSail (architecture .User) s = some (.RV64, s) := by
  obtain ⟨m, hm, hp⟩ := h.regs .mstatus
  simp only [userRegPolicy] at hp
  simp [runSail, architecture, readReg_eq hm, hp.2.1, architecture_bits_backwards,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Configured user code never takes the 32-bit address-arithmetic path. -/
theorem in32BitMode_false :
    runSail (in32BitMode ()) s = some (false, s) := by
  have harch := (runSail_eq_some_iff _ _ _ _).mp h.architecture_user
  simp only [runSail, in32BitMode, bind, EStateM.bind, readReg_eq h.privilege, harch, pure,
    EStateM.pure, Option.some.injEq, Prod.mk.injEq, and_true]
  rfl

/-- User addresses use bare physical translation. -/
theorem translationMode_user :
    runSail (translationMode .User) s = some (.Bare, s) := by
  obtain ⟨satp, hsatp, hp⟩ := h.regs .satp
  have harch := (runSail_eq_some_iff _ _ _ _).mp h.architecture_supervisor
  simp only [userRegPolicy] at hp
  simp [runSail, translationMode, harch, readReg_eq hsatp, hp,
    bind, EStateM.bind, pure, EStateM.pure, assert, PreSail.assert,
    satpMode_of_bits, show (Privilege.User == Privilege.Machine) = false from rfl,
    RiscvZkvm.Sail.Functions.xlen, Mk_Satp64]

/-- Reading senvcfg returns its register value and leaves the state unchanged. -/
theorem read_senvcfg_eq {v : BitVec 64}
    (hv : s.regs.get? Register.senvcfg = some v) :
    runSail (read_senvcfg ()) s = some (v, s) := by
  obtain ⟨m, hm, hmp⟩ := h.regs .menvcfg
  obtain ⟨w, hw, hwp⟩ := h.regs .senvcfg
  have heq : w = v := Option.some.inj (hw.symm.trans hv)
  subst w
  simp only [userRegPolicy] at hmp hwp
  have hupdate : _update_SEnvcfg_SSE v 0#1 = v := by
    rw [← hwp.2.2]
    exact update_senvcfg_sse_self v
  simp [runSail, read_senvcfg, readReg_eq hv, readReg_eq hm, hmp.2.2, hwp.2.2,
    hupdate, bind, EStateM.bind, pure, EStateM.pure]

/-- Pointer masking is disabled at user privilege. -/
theorem get_pmm_user :
    runSail (get_pmm .User) s = some (.PMM_Disabled, s) := by
  obtain ⟨v, hv, hp⟩ := h.regs .senvcfg
  have hread := (runSail_eq_some_iff _ _ _ _).mp (h.read_senvcfg_eq hv)
  have hS := (runSail_eq_some_iff _ _ _ _).mp h.enabled_S
  simp only [userRegPolicy] at hp
  simp [runSail, get_pmm, hread, hS, hp.1, pmm_mode_backwards,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Every user access has zero pointer-mask length. -/
theorem get_pmlen_user (access : MemoryAccessType mem_payload) :
    runSail (get_pmlen access .User) s = some (0, s) := by
  obtain ⟨m, hm⟩ := h.present .mstatus
  have hpmm := (runSail_eq_some_iff _ _ _ _).mp h.get_pmm_user
  have happ : ∃ b, is_pmm_applicable access .User s = .ok b s := by
    simp [is_pmm_applicable, readReg_eq hm, bind, EStateM.bind, pure, EStateM.pure]
  obtain ⟨b, hb⟩ := happ
  cases b <;> simp [runSail, get_pmlen, hb, hpmm,
    bind, EStateM.bind, pure, EStateM.pure]

/-- The effective user address is unchanged by privilege, translation, or pointer masking. -/
theorem transform_effective_address_user (a : virtaddr)
    (access : MemoryAccessType mem_payload) :
    runSail (transform_effective_address a access) s = some (a, s) := by
  obtain ⟨m, hm⟩ := h.present .mstatus
  have heff := (runSail_eq_some_iff _ _ _ _).mp (h.effectivePrivilege_user access hm)
  have hlen := (runSail_eq_some_iff _ _ _ _).mp (h.get_pmlen_user access)
  have hmode := (runSail_eq_some_iff _ _ _ _).mp h.translationMode_user
  cases a
  simp [runSail, transform_effective_address, readReg_eq hm, readReg_eq h.privilege,
    heff, hlen, hmode, bind, EStateM.bind, pure, EStateM.pure, pm_transform_PA,
    RiscvZkvm.Sail.Functions.xlen, zero_extend, Sail.BitVec.zeroExtend,
    extract_full_address, show (SATPMode.Bare == SATPMode.Bare) = true from rfl]

/-- User execution does not enable landing-pad enforcement. -/
theorem get_xLPE_user :
    runSail (get_xLPE .User) s = some (false, s) := by
  obtain ⟨v, hv, hp⟩ := h.regs .senvcfg
  have hread := (runSail_eq_some_iff _ _ _ _).mp (h.read_senvcfg_eq hv)
  have hS := (runSail_eq_some_iff _ _ _ _).mp h.enabled_S
  simp only [userRegPolicy] at hp
  simp [runSail, get_xLPE, hread, hS, hp.2.1, bool_bit_backwards,
    bind, EStateM.bind, pure, EStateM.pure]

/-- The control-flow landing-pad extension is disabled for configured user execution. -/
theorem disabled_Zicfilp :
    runSail (currentlyEnabled .Ext_Zicfilp) s = some (false, s) := by
  have hlpe := (runSail_eq_some_iff _ _ _ _).mp h.get_xLPE_user
  simp [runSail, currentlyEnabled, hartSupports, readReg_eq h.privilege, hlpe,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Updating landing-pad state is inert in the configured profile. -/
theorem update_elp_state_eq (rs1 : regidx) :
    runSail (update_elp_state rs1) s = some ((), s) := by
  have hcf := (runSail_eq_some_iff _ _ _ _).mp h.disabled_Zicfilp
  simp [runSail, update_elp_state, hcf, bind, EStateM.bind, pure, EStateM.pure]

/-- Reading mip succeeds and leaves the state unchanged. -/
theorem read_mip_exists :
    ∃ v, read_mip .IncludePlatformInterrupts s = .ok v s := by
  obtain ⟨mip, hmip⟩ := h.present .mip
  obtain ⟨mei, hmei⟩ := h.present .sig_meip
  obtain ⟨sei, hsei⟩ := h.present .sig_seip
  have hS := (runSail_eq_some_iff _ _ _ _).mp h.enabled_S
  simp [read_mip, external_interrupts_pending, readReg_eq hmip, readReg_eq hmei,
    readReg_eq hsei, hS, bind, EStateM.bind, pure, EStateM.pure]

/-- Masked interrupts cannot become pending, even when external signals are asserted. -/
theorem getPendingSet_none :
    runSail (getPendingSet .User) s = some (none, s) := by
  obtain ⟨deleg, hdeleg⟩ := h.present .mideleg
  obtain ⟨status, hstatus⟩ := h.present .mstatus
  obtain ⟨ie, hie, hiep⟩ := h.regs .mie
  simp only [userRegPolicy] at hiep
  subst ie
  obtain ⟨ip, hip⟩ := h.read_mip_exists
  have hS := (runSail_eq_some_iff _ _ _ _).mp h.enabled_S
  simp [runSail, getPendingSet, hS, readReg_eq hdeleg, readReg_eq hstatus,
    readReg_eq hie, hip, bind, EStateM.bind, pure, EStateM.pure, zeros]

/-- Configured user execution dispatches no interrupt. -/
theorem dispatchInterrupt_none :
    runSail (dispatchInterrupt .User) s = some (none, s) := by
  have hpending := (runSail_eq_some_iff _ _ _ _).mp h.getPendingSet_none
  simp [runSail, dispatchInterrupt, hpending, bind, EStateM.bind, pure, EStateM.pure]

/-- Bare user translation preserves ordinary addresses and the whole machine state. -/
theorem translateAddr_user (a : BitVec 64)
    (access : MemoryAccessType mem_payload)
    (hshadow : is_shadow_stack_access access s = .ok false s) :
    runSail (translateAddr (.Virtaddr a) access) s =
      some (.Ok (.Physaddr a, .PBMT_PMA, ()), s) := by
  obtain ⟨m, hm⟩ := h.present .mstatus
  have heff := (runSail_eq_some_iff _ _ _ _).mp (h.effectivePrivilege_user access hm)
  have hmode := (runSail_eq_some_iff _ _ _ _).mp h.translationMode_user
  simp [runSail, translateAddr, readReg_eq hm, readReg_eq h.privilege, heff, hmode,
    hshadow, SailME.run, PreSail.PreSailME.run, bind, EStateM.bind, EStateM.map,
    pure, EStateM.pure, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.lift, ExceptT.pure, MonadLift.monadLift, monadLift, liftM, Functor.map,
    bits_of_virtaddr, zero_extend, Sail.BitVec.zeroExtend, init_ext_ptw,
    show (SATPMode.Bare == SATPMode.Bare) = true from rfl]

end UserConfig

end MetrologyAsm
