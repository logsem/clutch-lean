import MetrologyAsm.Examples.Swap.Bridge
import MetrologyAsm.Examples.Swap.Boundary

/-! # A universal Sail specification for the exchange source -/

namespace MetrologyAsm

open ProbLang ProbLang.Asm RiscvZkvm.Sail.Functions

/-- Exchange the two selected logical integer cells and preserve every other integer. -/
def swapValues (old : Loc → Int) (l k a : Loc) : Int :=
  if a = l then old k else if a = k then old l else old a

/-- The actual assembled fragment swaps its two cells for every compatible Sail layout and state. -/
theorem swap_rvspec (l k : Loc) (old : Loc → Int) (hne : l ≠ k)
    (hl : inRange true 64 (old l) = true) (hk : inRange true 64 (old k) = true) :
    RVSpec swapCode [.loc l, .loc k] (integerHeap {l, k} old)
      (.ret .unit (integerHeap {l, k} (swapValues old l k))) := by
  intro ι s h
  have hlayout := SwapPlacement.of_RVCompat ι s l k _ hne h
  obtain ⟨hplacement, hcontents, harguments, himage, himports, hreturn, hstack, hconfig⟩ := h
  have ha0 : s.regs.get? Register.x10 = some (ι.addr l) := harguments 0 (.loc l) rfl
  have ha1 : s.regs.get? Register.x11 = some (ι.addr k) := harguments 1 (.loc k) rfl
  have hwords := swap_words_of_contents ι s l k old hcontents
  have hram := codeImage_exchange_ram ι [.loc l, .loc k] s himage
  have hcode : ∀ p ∈ swapPCs ι.codeBase, codeRange ι swapCode p := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := (mem_swapPCs_iff ι.codeBase p).mp hp
    apply (codeRange_exchange ι _).mpr
    rw [inSpan, pcAt_toNat hram hi]
    constructor <;> omega
  have hout : ¬ codeRange ι swapCode ι.retAddr := by
    intro hp
    exact hreturn.2.2.1 (imageByte_of_codeRange_exchange ι ι.retAddr hp)
  have hrun := swap_runsTo hconfig.1 ι.codeBase (ι.addr l) (ι.addr k)
    (BitVec.ofInt 64 (old l)) (BitVec.ofInt 64 (old k)) ι.retAddr hlayout
    (SwapImage.of_codeImage ι [.loc l, .loc k] s himage)
    (codeImage_exchange_pc ι [.loc l, .loc k] s himage) ha0 ha1 hreturn.1
    hwords.1 hwords.2 (codeRange ι swapCode) hcode hout
  apply hrun.mono
  intro t ht
  subst t
  change RVExitCompat ι swapCode [.loc l, .loc k] (callFootprint swapCode [.loc l, .loc k])
    s (swapFinalState s ι.codeBase (ι.addr l) (ι.addr k)
      (BitVec.ofInt 64 (old l)) (BitVec.ofInt 64 (old k)) ι.retAddr)
    (.ret .unit (integerHeap {l, k} (swapValues old l k)))
  refine ⟨?_, swapFinalState_memoryFrame ι s l k _ _ hstack,
    swapFinalState_configurationFrame s _ _ _ _ _ _,
    swapFinalState_machineConfiguration s _ _ _ _ _ _ ι swapCode hconfig,
    hplacement, rfl, swapFinalState_calleeSavedRestored s _ _ _ _ _ _⟩
  have hw := swapFinalState_words s ι.codeBase (ι.addr l) (ι.addr k)
    (BitVec.ofInt 64 (old l)) (BitVec.ofInt 64 (old k)) ι.retAddr hlayout.dataDisjoint
  have hdecode := decodeF_exchange ι _ l k (swapValues old l k) hne
    (by simpa [swapValues] using hk) (by simpa [swapValues, Ne.symm hne] using hl)
    (by simpa [swapValues] using hw.1) (by simpa [swapValues, Ne.symm hne] using hw.2)
  apply observe_ret_unit ι swapCode [.loc l, .loc k] _ _ _ (ι.addr l) rfl
  · exact swapFinalState_pc s _ _ _ _ _ _
  · simpa only [swap_callFootprint] using hdecode
  · simp only [argumentRegister]
    rw [swapFinalState_reg_other s _ _ _ _ _ _ .x10 (by decide +kernel)]
    exact ha0

end MetrologyAsm
