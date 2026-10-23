import MetrologyAsm.Examples.OTP.Source
import MetrologyAsm.Examples.OTP.Decode
import MetrologyAsm.Examples.OTP.Byte
import MetrologyAsm.Examples.OTP.Callback
import MetrologyAsm.Examples.OTP.Security
import MetrologyAsm.ABI.ByteResume
import MetrologyAsm.Sail.IntegerSteps

/-! # The compiled Sail-backed OTP: guarded game coupling, totality and perfect secrecy

The actual private-pad game has the exact uniform-byte output law. See docs/asm-ffi/OTP-PLAN.md
for its source, execution, evaluator, logic and probability proof chain. -/
