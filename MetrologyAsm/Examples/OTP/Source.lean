import Metrology.ProbLang.Asm.Notation
import Metrology.ProbLang.Asm.Assembler

/-! # The compiled one-byte one-time pad -/

namespace MetrologyAsm.OTP

open ProbLang.Asm

/-- The compiler's complete encryption function, retaining its GNU source verbatim. -/
def otpAsm : AsmProg := riscv_asm!
  "\t.text
\t.globl\tencrypt_byte                    # -- Begin function encrypt_byte
\t.p2align\t2
\t.type\tencrypt_byte,@function
encrypt_byte:                           # @encrypt_byte
# %bb.0:
\taddi\tsp, sp, -32
\tsd\tra, 24(sp)                      # 8-byte Folded Spill
\tsd\ts0, 16(sp)                      # 8-byte Folded Spill
\tsd\ts1, 8(sp)                       # 8-byte Folded Spill
\tmv\ts0, a1
\tmv\ts1, a0
\tli\ta1, 1
\tmv\ta0, s0
\tcall\trandombytes
\tlbu\ta0, 0(s0)
\txor\ta0, a0, s1
\tld\tra, 24(sp)                      # 8-byte Folded Reload
\tld\ts0, 16(sp)                      # 8-byte Folded Reload
\tld\ts1, 8(sp)                       # 8-byte Folded Reload
\taddi\tsp, sp, 32
\tret
.Lfunc_end0:
\t.size\tencrypt_byte, .Lfunc_end0-encrypt_byte
"

/-- Encrypt a byte message using a fresh byte written by the imported randombytes callback. -/
def otpSig : Sig := {
    args := [.uint 64, .array 8 (.const 1)]
    result := .uint 64
    stackBound := 32
    imports := [("randombytes", ⟨[.array 8 (.arg 1), .uint 64], .unit⟩)] }

/-- The first-class assembly code used by the OTP game. -/
def otpCode : Code := ⟨otpAsm, otpSig⟩

/-- The assembled text and relocated import-slot layout. -/
def otpImage : Image :=
  (assemble otpAsm).toOption.getD ⟨[], 0, 0, 0, [], [], []⟩

/-- The retained OTP source assembles successfully. -/
theorem assemble_otpImage : assemble otpAsm = .ok otpImage := by
  rfl

end MetrologyAsm.OTP
