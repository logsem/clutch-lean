import MetrologyAsm.Profile.Initial

/-! # Sail instruction spike -/

namespace MetrologyAsm

/-- Put one little-endian word into Sail memory. -/
def writeWord (s : Mach) (a : Nat) (w : BitVec 32) : Mach :=
  (List.range 4).foldl (fun s i =>
    { s with mem := s.mem.insert (a + i) (BitVec.ofNat 8 (w.toNat / 2 ^ (8 * i))) }) s

/-- A concrete ADDI image placed in ordinary user-accessible memory. -/
noncomputable def addiInitial : Option Mach :=
  userInitial.map fun s => writeWord s 0x80000000 0x00700513#32

/-- The result register observed after one full Sail fetch-decode-execute step. -/
noncomputable def addiObservation : Option (Option Nat) :=
  (addiInitial.bind rvStep).map fun s => (s.regs.get? Register.x10).map BitVec.toNat

/-- Write one little-endian 64-bit integer into Sail memory. -/
def writeDword (s : Mach) (a : Nat) (w : BitVec 64) : Mach :=
  (List.range 8).foldl (fun s i =>
    { s with mem := s.mem.insert (a + i) (BitVec.ofNat 8 (w.toNat / 2 ^ (8 * i))) }) s

/-- Read one little-endian 64-bit integer from Sail memory. -/
def readDword (s : Mach) (a : Nat) : Option Nat :=
  (List.range 8).foldl (fun acc i => do
    let n ← acc
    let b ← s.mem.get? (a + i)
    pure (n + b.toNat * 2 ^ (8 * i))) (some 0)

/-- The assembler's uncompressed load-load-store-store-return image. -/
def swapWords : List (BitVec 32) :=
  [0x00053603#32, 0x0005b683#32, 0x00d53023#32, 0x00c5b023#32, 0x00008067#32]

/-- A concrete two-cell swap instance in ordinary user-accessible memory. -/
noncomputable def swapInitial : Option Mach := userInitial.map fun s =>
  let s := writeDword (writeDword s 0x80001000 42#64) 0x80001008 99#64
  swapWords.zipIdx.foldl (fun s (w, i) => writeWord s (0x80000000 + 4 * i) w) s

/-- Execute a fixed number of full Sail instruction steps. -/
noncomputable def runSteps (n : Nat) (s : Mach) : Option Mach :=
  (List.range n).foldl (fun acc _ => acc.bind rvStep) (some s)

/-- The two cells and return address observed after five full Sail steps. -/
noncomputable def swapObservation : Option (Nat × Nat × Option Nat) := do
  let s ← swapInitial
  let s ← runSteps 5 s
  let x ← readDword s 0x80001000
  let y ← readDword s 0x80001008
  pure (x, y, (pc s).map BitVec.toNat)

end MetrologyAsm
