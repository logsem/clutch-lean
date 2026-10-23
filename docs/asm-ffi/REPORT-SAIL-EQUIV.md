# WS6: pinned Rv64.Logic and SailEquiv evaluation

The pinned upstream library does **not** provide a ready-made simulation of the actual generated
`try_step` under this project's User-mode compatibility predicate. Its instruction equivalences
and bounded program logic are substantial reusable material, but using them requires a new bridge.
No alternative ISA was substituted for actual Sail, and no upstream axiom closure is claimed audited
by this source inspection.

## Source and inspection boundary

Inspected repository: `https://github.com/Verified-zkEVM/riscv-zkvm`, exact revision
`6810fc14d9c40373101321cefaec59df8d82e3e7`. The existing vendor checkout's `git rev-parse HEAD`
was checked, and its `RiscvZkvm/Rv64` subtree was copied as read-only input to
`/home/agent/asm-ffi-ws9-ws11/downloads/riscv-zkvm-pinned/Rv64`.
No upstream build script, Lake configuration, or compiler plugin was executed. This report is an
inspection of definitions and theorem statements, not a fresh compilation of the upstream project.
All source pointers below are relative to `RiscvZkvm/Rv64` at that revision.

## The 51 primary instruction equivalences

An anchored source scan of `theorem <name>_sail_equiv` gives 51 primary instruction lemmas after
separating the eight names ending `_step_sail_equiv`. The seven `_sail_equiv_of_present` wrappers
are also separate. The primary leaves are:

| Source under `SailEquiv/` | Count | Instruction names |
|---|---:|---|
| `ALUProofs.lean` | 14 | add, sub, and, or, xor, slt, sltu, sll, srl, sra, lui, addiw, auipc, mul |
| `ImmProofs.lean` | 8 | addi, andi, ori, xori, slti, sltiu, mv, nop |
| `ShiftProofs.lean` | 3 | slli, srli, srai |
| `MExtProofs.lean` | 7 | mulh, mulhsu, mulhu, div, divu, rem, remu |
| `BranchProofs.lean` | 8 | beq, bne, blt, bge, bltu, bgeu, jal, jalr |
| `VmemReduction.lean` | 1 | ld |
| `VmemReductionLoads.lean` | 6 | lw, lwu, lh, lhu, lb, lbu |
| `VmemReductionStores.lean` | 4 | sd, sw, sh, sb |

The collective `Instr.simulable` predicate (`StepSim.lean:81`) excludes ECALL, EBREAK, FENCE,
MV, LI, NOP, and CSRS; MV/NOP have useful leaf lemmas but are excluded from this mapped run theorem.
The 49 mapped constructors comprise 29 unconditional, nine control-flow, and eleven memory forms.
The header and predicate were checked against their actual constructors, not inferred from the
number 51. `InstrMap.lean:66` dispatches `executeSupported` directly to generated `execute_*`
bodies; generated CSRReg/CSRImm return illegal there. `toSailInstr?` is the explicit AST mapping.

The memory lemmas have real operational premises. For example, `ld_sail_equiv`
(`VmemReduction.lean:1053`) requires StateRel, BareModeInv, a matching readable PMA region,
virtual and physical alignment, three false MMIO checks, and eight successful byte lookups.
It concludes actual `execute_LOAD` success, StateRel of the resulting toy state, unchanged nextPC,
and PlatformFrame. This is useful instruction-body reasoning, not a complete fetch step.

## What the relation tracks

`StateRel` (`StateRel.lean:264`) has exactly two fields:

1. All 32 integer register values agree with `MachineState.getReg`.
2. At every eight-aligned address, reconstruction of eight Sail bytes agrees with the toy
   doubleword memory. The toy memory is doubleword-granular; the relation deliberately does not
   assert equality of every overlapping eight-byte window.

`reconstructDword` uses default-zero lookup for missing bytes. Consequently, StateRel alone does
not establish allocation/presence. `MemPresent lo hi` (`StateRel.lean:306`) separately states that
every byte of the chosen half-open window is present. `StateRelPC` (`StateRel.lean:295`) adds
committed PC agreement. Neither StateRel nor StateRelPC equates the toy code AST with instruction
bytes or decoding, and neither asserts ABI preservation of arbitrary raw-state fields.

`RunInv lo hi` (`RunInv.lean:50`) extends StateRelPC with readable misa, MemPresent, HTIF disabled,
and BareModeInv with the initializer's PMA table and MLPE zero.
`BareModeInv` (`VmemReduction.lean:956`) explicitly requires:

- `cur_privilege = Machine`;
- readable mstatus with MPRV zero;
- readable mseccfg with PMM zero;
- readable PMP configurations and addresses, with **all PMP entries OFF**;
- readable PMA region table.

These assumptions conflict with the present UserConfig's User privilege and active permissive
TOR PMP entry. The current compatibility predicate does not entail this RunInv.

## What sailStep_run_sim proves

The actual definition `sailStep` (`StepRun.lean:76`) is:

```lean
do
  let pc ← readReg Register.PC
  set_next_pc (pc + 4)
  let _ ← executeSupported si
  tick_pc ()
```

It takes an already decoded `si`. The preceding source comment explicitly leaves the instruction
decode tie out of scope. It does not call generated fetch, decode, interrupt dispatch, or `try_step`.

The theorem `sailStep_run_sim` (`StepRun.lean:327`) assumes:

```lean
hinv   : RunInv lo hi sRv sSail
hlo    : RAM_MEM_START ≤ lo
hhi    : hi ≤ RAM_MEM_END
hfetch : sRv.code sRv.pc = some i
hsim   : i.simulable = true
hsi    : toSailInstr? i = some si
hside  : stepSideCond lo hi sRv
hstep  : step sRv = some sRv'
```

It concludes some `sSail'` with `runSail (sailStep si) sSail = some ((), sSail')` and
`RunInv lo hi sRv' sSail'`. The RAM window is restricted to `[0xa0000000, 0xc0000000)`.
`stepSideCond` (`RunInv.lean:339`) supplies four-byte target alignment for branches/jumps and
width-specific address-window bounds for memory operations. The successful toy `step` premise
also supplies that model's memory alignment/validity checks.

`sailStepN` (`StepRun.lean:360`) obtains each next decoded instruction from **toy code memory**
`sRv.code sRv.pc >>= toSailInstr?`, and advances that toy state with `step`. Its run theorem
(`StepRun.lean:381`) additionally requires every intermediate toy state to contain a simulable
instruction and satisfy stepSideCond. This iteration does not add a byte-fetch/decoder theorem.

The distinction follows directly from the definitions: `CodeMem` is `Word → Option Instr`
(`Execution.lean:250`), and `step` matches on `s.code s.pc` (`Execution.lean:341`). Instruction
fetch is a lookup of an AST in this model, independent of Sail byte memory.

## What the program logic supplies

`Logic/WP/Core.lean:39` packages a precondition and step budget with a sound
`cpsTripleWithin`. The latter (`Logic/CPSSpec.lean:49`) quantifies over PC-free separating frames
and proves that some bounded **toy** `stepN` reaches the requested exit and framed postcondition.
`Logic/WP/Loop.lean:29` provides a bounded natural-number invariant/variant certificate: callers
supply the header branch, body triple, exit entailment, and final forced-exit triple; its theorem
composes those certificates. It does not infer field-arithmetic invariants or bypass them.

This suggests a productive design for the keypair loops and internal calls. It does not already
prove their arithmetic, ABI contracts, or correspondence with the current bytecode boundary.

## Reuse decision and remaining bridge

The direct-Sail route is justified for the required universal User-mode RVSpec. To reuse the
upstream logic instead, the missing work would include:

1. Tie assembled instruction bytes and actual fetch/decode to the AST CodeReq at every PC,
   including nonwrapping addresses, instruction permissions, and code preservation.
2. Replace or generalize the Machine/PMP-off invariant to the actual UserConfig and its PMA/PMP
   checks, proving preservation for arbitrary compatible raw states.
3. Simulate the complete generated `try_step` wrapper, including interrupt/config reads and
   retirement/frame behavior; `executeSupported ; tick_pc` is insufficient for that conclusion.
4. Connect toy separating assertions and memory updates to logical byte arrays, physical frames,
   imported stops/resumes, and the FFI interaction-tree specification.
5. Audit every reused theorem's actual axiom closure under the pinned extraction/runtime.

The last condition matters: upstream `scripts/AxiomSweep.lean:45` explicitly accepts four platform
axioms (`load_reservation`, `match_reservation`, `plat_term_write`, and
`sys_enable_experimental_extensions`) in addition to Lean's standard three. This is source evidence
of that project's policy, not a claim that all four occur in each of the 51 leaves. Its source
comments also document narrowing the dispatcher to exclude the Zkr seed source. Individual
`#print axioms` checks would be necessary before any reuse under this project's stricter policy.

No full `try_step` simulation, new library dependency, crypto correctness theorem, or axiom waiver
is supplied by this report. The actual source statements were examined before rejecting this as
a shortcut to the required specification.
