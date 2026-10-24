import MetrologyAsm.Examples.OTP.Prefix
import MetrologyAsm.Examples.OTP.Continuation
import MetrologyAsm.Examples.OTP.ImageBridge

/-! # Compiled OTP entry execution derived from the actual ABI and relocated source -/

namespace MetrologyAsm.OTP

open ProbLang ProbLang.Asm Sail
open _root_.BitVec (ofInt)

section

variable (ι : Placement) (s : Mach) (message : Int) (pad : Loc)

/-- Collect the call inputs from the frame registers and the placement. -/
def entryInputs : CallInputs :=
  ⟨ι.codeBase, (s.regs.get? .x2).getD 0, ι.addr pad, ofInt 64 message, ι.retAddr,
    (s.regs.get? .x8).getD 0, (s.regs.get? .x9).getD 0, ι.importAddr "randombytes"⟩

/-- The complete register profile makes the recovered original frame registers genuine bindings. -/
theorem entryInputs_registers (h : UserConfig s) :
    let a := entryInputs ι s message pad
    s.regs.get? .x2 = some a.sp ∧ s.regs.get? .x8 = some a.savedS0 ∧
      s.regs.get? .x9 = some a.savedS1 := by
  obtain ⟨sp, hsp⟩ := h.present .x2
  obtain ⟨s0, hs0⟩ := h.present .x8
  obtain ⟨s1, hs1⟩ := h.present .x9
  simp [entryInputs, hsp, hs0, hs1]

/-- Recovering the original stack binding retains the layout derived from all ABI facets. -/
theorem entryInputs_layout
    (heap : LocHeap BoundaryValue) (h : RVCompat ι otpCode (otpArgs message pad) heap s) :
    let a := entryInputs ι s message pad
    RawLayout a.base a.sp a.pad a.callback a.ret := by
  obtain ⟨sp, hsp, layout⟩ := rawLayout_of_RVCompat ι s message pad heap h
  simpa [entryInputs, hsp] using layout

/-- The compiled OTP entry reaches randombytes under the universal ABI facets. -/
theorem entry_runsTo_call
    (heap : LocHeap BoundaryValue) (h : RVCompat ι otpCode (otpArgs message pad) heap s) :
    RunsTo (codeRange ι otpCode) (fun t => t = (entryInputs ι s message pad).paused s) s := by
  have layout := entryInputs_layout ι s message pad heap h
  obtain ⟨_, _, hargs, hcode, himports, ⟨hra, -, -, -, -⟩, _, hconfig, _⟩ := h
  obtain ⟨hsp, hs0, hs1⟩ := entryInputs_registers ι s message pad hconfig
  have hpc := (codeImage_facts ι s message pad hcode).2.2
  have hmessage : s.regs.get? .x10 = some (ofInt 64 message) := hargs 0 (.int message) rfl
  have hpad : s.regs.get? .x11 = some (ι.addr pad) := hargs 1 (.loc pad) rfl
  have hout : ¬codeRange ι otpCode (ι.importAddr "randombytes") := by
    intro hc
    exact (himports.1 "randombytes" ⟨[.array 8 (.arg 1), .uint 64], .unit⟩
      (by simp [otpCode, otpSig])).1 (imageByte_of_codeRange ι _ hc)
  exact (entryInputs ι s message pad).runsTo_call hconfig layout
    (ImageAt.of_codeImage ι s message pad hcode) hpc hsp hra hs0 hs1 hmessage hpad
    (codeRange ι otpCode)
    (fun _ hi => codeRange_codePC ι layout.codeRam hi) hout

end

/-- Every permitted callback resumption executes the continuation with its new pad byte. -/
theorem resume_runsTo_return (ι : Placement) (s t : Mach) (message : Int) (pad : Loc)
    (heap newHeap : LocHeap BoundaryValue) (response : BoundaryValue)
    (h : RVCompat ι otpCode (otpArgs message pad) heap s)
    (hr : RVResume ι otpCode (otpArgs message pad) {pad}
      ((entryInputs ι s message pad).paused s) response newHeap t) :
    let a := entryInputs ι s message pad
    ∃ byte, newHeap[pad]? = some (.int byte) ∧ inRange false 8 byte = true ∧
      RunsTo (codeRange ι otpCode)
        (fun u => u = returnState t a.base a.sp a.message a.ret a.savedS0 a.savedS1
          (ofInt 8 byte)) t := by
  let a := entryInputs ι s message pad
  have layout : RawLayout a.base a.sp a.pad a.callback a.ret :=
    entryInputs_layout ι s message pad heap h
  obtain ⟨_, _, _, hcode, _, ⟨-, -, hretImage, -, -⟩, _, _⟩ := h
  obtain ⟨_, _, ra, _, _, _, hra, _, hpc, _, _, _, hcontents, huser, hcallee, _, hmem⟩ := hr
  have hregisters := a.paused_registers s
  have hraEq : ra = codePC a.base 10 := Option.some.inj (hra.symm.trans hregisters.2.1)
  subst ra
  have htsp : t.regs.get? .x2 = some (reservedSP a.sp) :=
    (hcallee .x2 (by simp [calleeSaved])).trans hregisters.1
  have htpad : t.regs.get? .x8 = some a.pad :=
    (hcallee .x8 (by simp [calleeSaved])).trans hregisters.2.2.1
  have htmessage : t.regs.get? .x9 = some a.message :=
    (hcallee .x9 (by simp [calleeSaved])).trans hregisters.2.2.2.1
  obtain ⟨byte, hbyteHeap, hrange, hword⟩ :=
    hcontents.2 (padRegion pad) (by simp) 0 (by simp [padRegion])
  have hheapByte : newHeap[pad]? = some (.int byte) := by simpa [padRegion] using hbyteHeap
  have hbyte : t.mem.get? a.pad.toNat = some (ofInt 8 byte) := by
    apply (wordAt8_iff _ _ _).mp
    simpa [a, entryInputs, padRegion] using hword
  have hretOut : ¬codeRange ι otpCode a.ret :=
    fun hc => hretImage (imageByte_of_codeRange ι _ hc)
  have hout : ∀ base n address, disjointSpans base n (ι.addr pad).toNat 1 → base ≤ address →
      address < base + n → ¬footprintByte ι otpCode (otpArgs message pad) address := by
    intro base n address hsep hl hu hf
    rw [footprintByte_otp] at hf
    unfold disjointSpans at hsep
    omega
  have hpausedImage := a.paused_image (ImageAt.of_codeImage ι s message pad hcode) layout
  have hresumedImage : ImageAt t a.base a.callback := by
    apply hpausedImage.of_mem_eq_on_image layout.codeRam
    intro address ha
    obtain ⟨hl, hu⟩ := ha
    exact hmem address (hout _ _ address layout.codePad hl hu)
  have savedFrame (offset : Nat) (hoff : offset + 8 ≤ 32) (value : BitVec 64)
      (hsaved : Word64At (a.paused s) (stackAddress a.sp offset) value) :
      Word64At t (stackAddress a.sp offset) value := by
    intro i hi
    rw [hmem]
    · exact hsaved i hi
    · exact hout _ _ _ (layout.stack_pad_disjoint hoff) (by omega) (by omega)
  have hsaved := a.paused_saved s layout.stackLower
  refine ⟨byte, hheapByte, hrange, ?_⟩
  exact runsTo_return huser a.base a.sp a.pad a.callback a.message a.ret a.savedS0 a.savedS1
    (ofInt 8 byte) layout hresumedImage.continuation hpc htsp htpad htmessage hbyte
    (savedFrame 24 (by decide) _ hsaved.1)
    (savedFrame 16 (by decide) _ hsaved.2.1)
    (savedFrame 8 (by decide) _ hsaved.2.2) (codeRange ι otpCode)
    (fun _ hi => codeRange_codePC ι layout.codeRam hi) hretOut

end MetrologyAsm.OTP
