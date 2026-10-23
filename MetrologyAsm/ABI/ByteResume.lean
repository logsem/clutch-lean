import MetrologyAsm.ABI.Resume
import MetrologyAsm.Sail.ByteRules

/-! # Heap-changing resumption of an import owning one byte -/

namespace MetrologyAsm

open ProbLang ProbLang.Asm RiscvZkvm.Sail.Functions

/-- A single byte region occupies exactly the physical address of its logical base. -/
theorem footprintByte_single_byte (ι : Placement) (code : Code) (args : List BoundaryValue)
    (l : Loc) (hregions : callRegions code args = [⟨l, 1, 8, false⟩]) (a : Nat) :
    footprintByte ι code args a ↔ a = (ι.addr l).toNat := by
  simp only [footprintByte, hregions, List.mem_singleton, exists_eq_left]
  simp only [inSpan, Nat.reduceDiv, Nat.mul_one]
  omega

/-- Installing a representable byte realizes a valid single-cell logical fragment. -/
theorem footprintContents_write8State (ι : Placement) (code : Code) (args : List BoundaryValue)
    (l : Loc) (hregions : callRegions code args = [⟨l, 1, 8, false⟩])
    (heap : LocHeap BoundaryValue) (hvalid : validFragment code args heap)
    (byte : Int) (hbyte : heap[l]? = some (.int byte)) (hrange : inRange false 8 byte = true)
    (s : Mach) : footprintContents ι code args heap
      (write8State s (ι.addr l) (BitVec.ofInt 8 byte)) := by
  refine ⟨hvalid, ?_⟩
  intro r hr i hi
  simp only [hregions, List.mem_singleton] at hr
  subst r
  have hi0 : i = 0 := by
    change i < 1 at hi
    omega
  subst i
  refine ⟨byte, by simpa using hbyte, hrange, ?_⟩
  intro j hj
  have hj0 : j = 0 := by
    norm_num at hj
    omega
  subst j
  simpa using write8State_get s (ι.addr l) (BitVec.ofInt 8 byte)

/-- Resume a unit callback after installing its new owned byte and preserving the physical frame. -/
theorem rv_resume_unit_byte (ι : Placement) (code : Code) (args : List BoundaryValue)
    (F : Finset Loc) (paused : Mach) (name : String) (sig : CallSig) (ra : BitVec 64)
    (l : Loc) (heap : LocHeap BoundaryValue) (byte : Int)
    (hregions : callRegions code args = [⟨l, 1, 8, false⟩])
    (hvalid : validFragment code args heap) (hbyte : heap[l]? = some (.int byte))
    (hrange : inRange false 8 byte = true) (hprofile : UserConfig paused)
    (himport : (name, sig) ∈ code.sig.imports) (hpc : pc paused = some (ι.importAddr name))
    (hra : paused.regs.get? .x1 = some ra) (hcode : codeRange ι code ra)
    (hF : F = callFootprint code args) :
    rv.Resume ι code args F paused .unit heap
      (write8State (resumeIntState paused ra 0) (ι.addr l) (BitVec.ofInt 8 byte)) := by
  refine ⟨name, sig, ra, 0#64, himport, hpc, hra, hcode, ?_, rfl, ?_, hF, ?_,
    (hprofile.resumeIntState ra 0).write8State _ _, ?_, ?_, ?_⟩
  · simp [pc, write8State, resumeIntState, Std.ExtDHashMap.get?_insert]
  · simp [write8State, resumeIntState]
  · exact footprintContents_write8State ι code args l hregions heap hvalid byte hbyte hrange _
  · exact resumeIntState_calleeSavedRestored paused ra 0
  · exact resumeIntState_configurationFrame paused ra 0
  · intro a ha
    apply write8State_get_other
    intro heq
    exact ha ((footprintByte_single_byte ι code args l hregions a).mpr heq.symm)

end MetrologyAsm
