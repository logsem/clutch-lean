import MetrologyAsm.Examples.OTP.Source
import MetrologyAsm.Examples.OTP.Decode
import MetrologyAsm.Examples.OTP.Byte
import MetrologyAsm.Examples.OTP.Callback
import MetrologyAsm.Examples.OTP.Security
import MetrologyAsm.ABI.ByteResume
import MetrologyAsm.Sail.IntegerSteps

/-! # The compiled Sail-backed OTP: guarded game coupling, totality and perfect secrecy

The private-pad game has the uniform-byte output law; see docs/asm-ffi/OTP-PLAN.md. -/
