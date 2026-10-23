import MetrologyAsm.ImportFrames

/-! # Observations at the callback and final return -/

namespace MetrologyAsm

open ProbLang ProbLang.Asm RiscvZkvm.Sail.Functions

/-- The external callback address decodes to the declared empty-argument import. -/
theorem observe_importToy_call (ι : Placement) (s : Mach)
    (hpc : pc s = some (ι.importAddr "cb")) (hne : ι.retAddr ≠ ι.importAddr "cb") :
    observe ι importToyCode [] ∅ s = some (.call "cb" [] ∅) := by
  simp [observe, hpc, Ne.symm hne, importToyCode]

/-- A representable signed result decodes exactly at the original return address. -/
theorem observe_importToy_ret (ι : Placement) (s : Mach) (z : Int)
    (hpc : pc s = some ι.retAddr)
    (ha0 : s.regs.get? Register.x10 = some (BitVec.ofInt 64 z))
    (hrange : inRange true 64 z = true) :
    observe ι importToyCode [] ∅ s = some (.ret (.int z) ∅) := by
  have hbounds : -(2 ^ 63 : Int) ≤ z ∧ z < 2 ^ 63 := by simpa [inRange] using hrange
  have hvalue := BitVec.toInt_ofInt_eq_self (w := 64) (by decide) hbounds.1 hbounds.2
  simp [observe, hpc, argumentRegister, ha0, importToyCode, decodeValue, hvalue, hrange]

/-- The original stack binding determines the scratch-frame lower bound. -/
theorem importToy_stack_lower (ι : Placement) (s : Mach) (sp : BitVec 64)
    (hstack : stackPlacement ι importToyCode [] s) (hsp : s.regs.get? .x2 = some sp) :
    16 ≤ sp.toNat := by
  obtain ⟨other, hother, _, hlower, _⟩ := hstack
  have heq : other = sp := Option.some.inj (hother.symm.trans hsp)
  subst other
  exact hlower

/-- Every source instruction and trampoline word is within the actual execution interval. -/
theorem importToy_code_contains (ι : Placement) (s : Mach) (h : codeImage ι importToyCode [] s) :
    ∀ p ∈ importToyPCs ι.codeBase, codeRange ι importToyCode p := by
  intro p hp
  have hram := codeImage_importToy_ram ι s h
  obtain ⟨i, hi, rfl⟩ := (mem_importToyPCs_iff ι.codeBase p).mp hp
  apply (codeRange_importToy ι _).mpr
  have hcast : 4 * (i : Int) = ((4 * i : Nat) : Int) := by omega
  rw [hcast, inSpan, importPC_toNat hram (by omega)]
  constructor <;> omega

end MetrologyAsm
