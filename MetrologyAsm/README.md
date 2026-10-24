# How the assembly proofs fit together

Start with [OTP security](Examples/OTP/Security.lean) for total termination and the exact ciphertext
law, or [its guarded game coupling](Examples/OTP/Game.lean). The smaller
[swap](Examples/Swap/Correctness.lean) and [callback](Examples/Callback/Correctness.lean) examples
state their final Micrometer results.
Then read the matching `Source.lean` and `Specification.lean` to see the assembly and its plain
machine contract. The keypair directory contains input and a game skeleton; it has no correctness proof.

## Directory map

| Directory | Responsibility | Entry points |
|---|---|---|
| `Sail/` | Actual Sail stepping, register/memory effects, fetch/decode and instruction rules | [Execution](Sail/Execution.lean), [InstructionRules](Sail/InstructionRules.lean) |
| `Profile/` | User-mode policy, register initialization, reductions and a consistency witness | [Config](Profile/Config.lean), [Witness](Profile/Witness.lean) |
| `ABI/` | Instantiate the generic FFI machine interface using Sail and the ABI facets | [Interface](ABI/Interface.lean), [Lemmas](ABI/Lemmas.lean), [Resume](ABI/Resume.lean) |
| `Examples/Swap/` | Complete two-cell swap proof | [Source](Examples/Swap/Source.lean), [Correctness](Examples/Swap/Correctness.lean) |
| `Examples/Callback/` | Complete assembly → ProbLang callback → assembly round trip | [Source](Examples/Callback/Source.lean), [Correctness](Examples/Callback/Correctness.lean) |
| `Examples/OTP/` | Complete compiled byte OTP: actual evaluator, guarded coupling, total termination and perfect secrecy | [Security](Examples/OTP/Security.lean), [Game](Examples/OTP/Game.lean), [plan](../docs/asm-ffi/OTP-PLAN.md) |
| `Examples/Keypair/` | Linked TweetNaCl source, declared signature and planned game | [Source](Examples/Keypair/Source.lean) |
| `Examples/Support.lean` | Concrete byte installation, placement and register fixtures shared by example witnesses | [Support](Examples/Support.lean) |
| `Diagnostics/` | Concrete observations and a small instruction-body experiment | [Spike](Diagnostics/Spike.lean), [InstructionBody](Diagnostics/InstructionBody.lean) |

`Sail/` and `Profile/` together form the machine foundation: basic step-state operations support the
profile, whose policy then supports configured memory/fetch/instruction rules. `ABI/` builds on that
foundation. Shared machine/ABI modules do not import example or diagnostic modules. The three
verified examples share infrastructure and witness support without importing each other's proofs.

## From source to the final theorem

```mermaid
flowchart TD
  Model["Pinned Sail architecture + runtime"] --> Machine["Sail/ + Profile/"]
  Machine --> ABI["ABI/Interface: rv, Compat, Exit, Resume"]
  Machine --> Execution["Execution: actual Sail steps"]
  Source["Source + assembler/decoder certificates"] --> Bridge["Boundary and bridge proofs"]
  ABI --> Bridge
  Execution --> Bridge
  Bridge --> Spec["Specification: universal RVSpec"]
  Spec --> Eval["Evaluation: unique interaction tree"]
  Witness["Witness: a compatible entry exists"] --> Eval
  Eval --> Correctness["Correctness: final Micrometer WP"]
  WP["Metrology/Micrometer/Asm: shared guarded WP bridge"] --> Correctness
```

The swap and callback examples use these filenames:

1. **`Source.lean`** contains literal GNU assembly, its signature and the first-class code value.
2. **`Decode.lean`, `Steps.lean`, `Execution.lean`** connect concrete instruction words to the official
   decoder and compose actual `try_step` executions. Swap also has `Assembler.lean` and `Layout.lean`.
3. **`Boundary.lean` and bridge files** translate between logical heaps and the physical machine.
   Swap uses `Bridge.lean`; callback uses `Placement`, `Image`, `Frames` and `Observation`.
4. **`Specification.lean`** proves `swap_rvspec` or `importToy_rvspec` for every compatible entry;
   callback additionally covers every valid response and allowed resumed state.
5. **`Witness.lean`** proves compatible entries exist, and **`Evaluation.lean`** selects the unique
   canonical return/callback tree. Callback's local uniqueness helpers are in `EvaluationRules.lean`.
6. **`Correctness.lean`** proves `wp_swap_spec` or `wp_importToy_spec` under the actual guarded WP.
   Callback's intermediate conditional WP is in `Micrometer.lean`.

The swap owns two distinct signed-64 cells. The callback toy has an empty logical footprint and a
16-byte stack frame. Keypair is explicitly unproved; its source/fixture checks establish an input,
not an RVSpec or cryptographic postcondition.

The OTP work is in `MetrologyAsm.OTP`. Read `Source` and `Decode` for the retained compiler output
and certified words, `Steps` for each actual Sail instruction, `Prefix` and `Continuation` for the
thirteen-step call and seven-step return, and `Placement`/`ImageBridge` for the ABI and relocation
bridges. `Execution` derives the raw runs from compatible entries and arbitrary allowed callback
resumptions. `Responses`/`Observation` connect the logical one-byte fragment to the actual stops;
`Specification`, `Witness` and `Evaluation` prove the universal contract and unconditional evaluator.
`Dispatch` proves the real foreign steps, `Micrometer` composes the guarded WP with randombytes,
and `Coupling`/`Game` prove the zero-cost uniform-reference coupling for a closed game allocating its
private pad and returning only the ciphertext. `CallbackExec` calculates the real callback's pure
prefix, sole random draw, store and terminating tail; `Finite` composes these with allocation and
the actual foreign steps. `Security` proves termination with probability one, the exact `1/256`
ciphertext law and equal returned-value distributions for any two valid messages. The private final
heap is hidden by the output marginal; the joint ciphertext/pad distribution is outside the claim.

## Imports and commands

Declaration names remain in `MetrologyAsm` (and `ProbLang.Asm` for the swap source). File organization
changes Lean module paths; the final theorem names `wp_swap_spec` and `wp_importToy_spec` stay the same.
Use a focused import:

```lean
import MetrologyAsm.Examples.Swap
-- or
import MetrologyAsm.Examples.Callback
-- or
import MetrologyAsm.Examples.OTP
```

`import MetrologyAsm` exports all three verified examples, including the completed OTP.
Diagnostics have explicit imports and are checked by `Tests/SailSpike.lean`. From the repository root:

```sh
lake build
lake build MetrologyAsm.Examples.Swap MetrologyAsm.Examples.Callback
python3 -I scripts/check-sail-pin.py
python3 -I fixtures/keypair/generate.py --check
python3 -I fixtures/otp/generate.py --check
```

The generic language/FFI definitions live in `Metrology/ProbLang/Asm/`; the guarded logic bridge lives
in `Metrology/Micrometer/Asm.lean`. Vendored architecture/runtime sources remain in `RiscvZkvm/` and
`runtime/lean-sail/`. See [the evaluation report](../docs/asm-ffi/REPORT.md) and
[statement dependency audit](../docs/asm-ffi/TCB.md) for scope, provenance and limits.
