# One-byte assembly OTP implementation plan and completion evidence

Goal: compile a loop-free byte encryption function, prove its actual Sail interaction with the
ProbLang randombytes callback, and prove perfect secrecy for the resulting closed ProbLang game.
The message is an integer in [0,256); a fresh private one-byte array holds the pad. Only the returned
ciphertext is observable. The pad is freshly sampled for each execution.

The C interface is `uint64_t encrypt_byte(uint64_t message, uint8_t *pad)`, under message < 256.
It calls `randombytes(pad,1)` and returns `message ^ pad[0]`. The assembly quotation must preserve
the retained compiler output. The supported machine is the existing pinned RV64IM user profile;
these claims are about the extracted Lean model, within the documented compiler/backend scope.

## Required deliverables

1. **Source and arithmetic.** Retain C, GNU assembly, compiler command/version and hashes under
   `fixtures/otp/`. Quote the function under `MetrologyAsm/Examples/OTP/Source.lean`, certify emitted
   words/layout against the Sail decoder, and prove XOR is an involutive byte permutation.
2. **Actual Sail execution.** Add reusable byte-load/XOR and needed register/instruction rules.
   Prove the call prefix and resumed suffix over arbitrary compatible raw states and placements,
   including saved message/pointer/return address, stack, caller scratch freedom and physical frames.
3. **Boundary and evaluation.** Prove the universal RVSpec for the real randombytes call with one
   owned byte, every valid callback response/heap and arbitrary permitted resumption. Prove local
   heap-changing resumption existence, a genuine compatible-entry witness, canonical interaction
   and unconditional unique evaluation. No machine/spec/evaluator premises may remain at the top.
4. **Micrometer.** Prove ordinary sampler/heap transitions under the explicit FFI kernel, then use
   the existing guarded wpFor to prove actual assembly/callback correctness and a zero-cost coupling
   to the uniform-byte reference program. The randombytes implementation is the real ProbLang lambda.
   A base-kernel-only sampler theorem or abstract foreign machine does not satisfy this requirement.
5. **Distribution and finite adequacy.** Define/use the actual explicit-kernel bounded/limit execution
   semantics and justify the finite execution/coupling argument. Prove total termination and the exact
   returned-ciphertext law: for every valid byte m,c, Pr[game(m)=c]=1/256. Derive equality of ciphertext
   distributions for arbitrary valid m0,m1. The game really allocates its private pad and invokes the
   assembled Sail-backed code. Conditional evaluator assumptions and a standalone XOR lemma are not
   substitutes for this final theorem.
6. **Integration and audit.** Export the example, update the module guide/report, run meaningful input
   checks and the full root build, print axioms for all final claims and regenerate statement-dependency
   receipts. No new sorry, axiom or native_decide proof; preserve strict implicit settings and upstream
   model/runtime pins. Commit explicit owned paths; never stage notes or pre-existing user files.

## Implementation sequence

- Establish the compiled source and byte-XOR measure/coupling lemmas.
- Extend machine rules and the one-byte ABI installation/decoding/resumption bridge.
- Compose the full source-to-RVSpec-to-evaluator chain with entry nonvacuity.
- Extend explicit-kernel sampling/resource WP rules and compose the real callback/game.
- Close the finite-kernel execution and security theorem, then run completion audits.

The main risks are heap-changing resumption and the explicit-kernel probability/adequacy bridge.
The existing callback toy has an empty footprint, and current randombytes WP uses the base kernel.
These are implementation obligations of this example, not reasons to weaken its final claim.

## Completed proof chain

Proved foundations: the retained RV64IM C/compiler input assembles to20 instruction words/88 image
bytes; every emitted word has an official Sail decoder equation. Byte XOR is an involution and exact
uniform-measure permutation, with its zero-cost coupling and a bridge to the machine's64-bit XOR.
Explicit-kernel bounded/limit semantics have measurability, mass, monotonicity and finite termination
lemmas, and specialize exactly to the original base semantics.

Every enabled base transition is preserved by the FFI kernel. The guarded WP transport theorem
therefore reuses existing sampler/heap proofs, and the actual randombytes lambda's one-byte WP now
holds under the real Sail environment. A concrete physical resumption installs any valid owned byte
and preserves the remaining machine frame. Actual configured LBU memory operations are proved;
integer XOR has its actual generated-body rule.

The twenty full instruction-step lemmas and both raw runs are now proved: thirteen steps reach the
actual randombytes address, and seven continuation steps read the updated pad, XOR the saved message,
restore the original frame and return. Scratch writes preserve code, the import slot and the pad;
the continuation preserves all memory. `Placement` derives the physical layout from RVCompat, and
`ImageBridge` derives every instruction/slot assertion from the actual relocated source image.
`entry_runsTo_call` derives the call run from an arbitrary compatible entry;
`resume_runsTo_return` covers every allowed resumption, including caller-scratch freedom
and a changed owned byte. Both live in `MetrologyAsm.OTP`, in `Execution.lean`.
`Frames.lean` proves prefix memory/configuration preservation, continuation configuration
preservation and restoration of the original callee-saved frame across the complete execution.

The actual ABI/source specification is now proved in `Specification.lean`. `Responses` fixes the
canonical valid/invalid branches; `Observation` decodes the physical pointer, byte heap, import call
and ciphertext return. `Witness` installs the actual relocated image and initialized pad in a genuine
compatible profiled machine for every valid input, and `Evaluation.otp_eval` (declaration
`MetrologyAsm.OTP.otp_eval`) selects the unique tree without evaluator or machine-run premises.
Every valid unit/byte response has a local concrete heap-changing resumption.

`Dispatch` proves the actual language-level start and replay transitions with arbitrary framed
heaps. `wp_otp` in `Micrometer.lean` composes those steps with the real randombytes lambda under
the shared guarded FFI WP. `Coupling` couples the callback draw to an ideal uniform ciphertext with the XOR
bijection and transports this ordinary callback proof to the actual FFI kernel. The closed
`otpGame` in `Game.lean` allocates a fresh private pad initialized to zero, calls the actual assembled
OTP and returns only its ciphertext; `MetrologyAsm.OTP.wp_otpGame_coupled` proves its guarded
zero-cost coupling to the ideal uniform-byte program.

`CallbackExec` proves the actual callback's pure prefix, one uniform byte draw, concrete store and
terminating tail inside the real assembly resumption frame. It composes these with
`otp_start_step` and `otp_resume_step` into `otp_call_finite`, with a common finite fuel bound for
all valid message/initial-byte values at a given pad. `Finite.otp_game_finite` then composes actual
allocation and beta reduction with that call law. The resulting configuration measure records the
sampled byte in the private heap and the XOR ciphertext in the returned expression.

That finite measure has mass one. `otp_game_limExec` uses `limExecWith_term` to identify the full
actual-kernel limit with the finite law. `Security.lean` projects away the private state and proves
`otp_game_uniform`, `otp_ciphertext_probability` and `otp_game_perfect_secrecy`, together with
`otp_game_terminates`. These are unconditional execution claims apart from valid-byte message and
ciphertext bounds. They quantify arbitrary initial language states. The exact finite operational
calculation supplies the execution justification alongside the guarded coupling; no generic FFI
WP adequacy theorem is assumed or claimed. Only the returned ciphertext is observed, with a fresh
pad on every game execution; joint ciphertext/private-pad distributions are outside this claim.

## Validation history

Validation of this foundation checkpoint: complete root build7145 jobs passed; thirteen listed
foundation theorem closures contain only propext/Classical.choice/Quot.sound. Receipts are
`audit/OTP-foundations-{build,axioms}.txt`. These are foundation receipts, not a completed OTP claim.
The later machine-execution checkpoint passes the full root build7156 jobs; all thirty-two listed
instruction, raw-run, ABI-entry/resumption and frame theorem closures use only the same three axioms.
Those receipts are `audit/OTP-machine-{build,axioms}.txt`; the two `OTP-machine-*-tcb.json` receipts
audit the entry and arbitrary-resumption theorem statements, not a game-security statement.
The later evaluator/guarded-game checkpoint passes the full root build7166 jobs; twenty additional
specification/evaluator/dispatch/WP/coupling closures use only the standard three axioms. Receipts
are `audit/OTP-game-{build,axioms}.txt`, `audit/OTP-evaluation-tcb.json` and
`audit/OTP-game-coupling-tcb.json`. The machine statement receipts are refreshed for the added
entry-register/layout helper declarations. These historical receipts cover the evaluator and guarded coupling; the final execution-law
receipts are listed below.
The source has thirteen steps to the import (including its trampoline), with the saved link at
text offset40; the seven-step suffix occupies offsets40..64. `Sail/IntegerSteps.lean` supplies
reusable full-step composition for register and doubleword-store bodies.

## Completion evidence

| Required deliverable | Authoritative artifacts and checks |
|---|---|
| Retained compiled source and byte arithmetic | `fixtures/otp/{otp.c,otp.compiler.s,otp.s,provenance.json}`, `Source`, `Decode`, `Byte`; fixture check passes |
| Actual Sail execution over arbitrary compatible states | `Steps`, `Prefix`, `Continuation`, `Layout`, `ImageBridge`, `Execution`, `Frames` |
| Boundary, compatible-entry existence and unconditional evaluator | `Responses`, `Observation`, `Specification`, `Witness`, `EvaluationRules`, `Evaluation.otp_eval` |
| Actual guarded FFI WP and zero-cost uniform reference coupling | `Dispatch`, `Micrometer`, `Coupling`, `Game.wp_otpGame_coupled`; real `RandomBytes.randombytesValue` in `otpEnv` |
| Finite execution, totality, exact law and message independence | `CallbackExec`, `Finite`, `Security`; actual `execNWith`/`limExecVWith` under `primStepWith otpEnv` |
| Integration, provenance and proof audit | Root export via `MetrologyAsm.Examples.OTP`, module guide/report, full root build and receipts below |

Final validation: full root build **7169 jobs passed**, strict implicit options remain false, and
all twenty-six printed final/security/finite/evaluator/coupling/helper axiom closures use exactly
`propext`, `Classical.choice`, and `Quot.sound`. No OTP proof uses `sorry`, a new axiom or
`native_decide`. The retained compiler input/quotation hashes and the unchanged Sail/runtime pins
pass their checks. The pre-existing user notes and local assistant files are untouched.

- `audit/OTP-final-build.txt`: the full root build.
- `audit/OTP-final-axioms.txt`: all twenty-six checked closures.
- `audit/OTP-final-finite-tcb.json`: the exact finite actual-game configuration law.
- `audit/OTP-final-termination-tcb.json`: total termination.
- `audit/OTP-final-uniform-tcb.json`: exact returned uniform-byte distribution.
- `audit/OTP-final-exact-law-tcb.json`: the `1/256` ciphertext theorem.
- `audit/OTP-final-secrecy-tcb.json`: equality of output distributions for two valid messages.

The statement receipts follow declaration types and non-proof bodies, exclude proof bodies, and
check that all owned definitions have source ranges. They complement the kernel-checked proofs and
axiom closures. They do not prove C compiler correctness or remove the documented extraction scope.
