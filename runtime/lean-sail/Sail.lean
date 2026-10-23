import Sail.BitVec
import Sail.IntRange
import Sail.Sail

-- Lean 4.35's intrinsic `assert` do-element conflicts with Sail's runtime assertion.
-- This syntax preserves the generated model's original monadic assertion call.
syntax (priority := high) &"assert " term:arg term:arg : doElem
macro_rules
  | `(doElem| assert $cond $message) => do
    let fn := Lean.mkIdent `Sail.assert
    `(doElem| ($fn $cond $message))

-- Make only the pinned declarations' omitted binders explicit, with their original types/order.
-- The closed whitelist was captured from the original compiled extraction, not inferred here.
private def sailExplicitParameters : List (Lean.Name × Lean.Name × String × List (Lean.Name × String)) := [
  (`RiscvZkvm.Sail.Vmem, `satp_to_asid, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Vmem, `satp_to_ppn, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Vector, `sail_mask, "def", [(`k_v, "Nat")]),
  (`RiscvZkvm.Sail.Arithmetic, `brev8, "def", [(`k_m, "Nat")]),
  (`RiscvZkvm.Sail.Arithmetic, `carryless_mul, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Arithmetic, `carryless_mulr, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Arithmetic, `carryless_mul_reversed, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Arithmetic, `rev8, "def", [(`k_m, "Nat")]),
  (`RiscvZkvm.Sail.Arithmetic, `count_ones, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.MemUtils, `access_within, "def", [(`k_width, "Nat")]),
  (`RiscvZkvm.Sail.HexBitsSigned, `hex_bits_signed_forwards, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.HexBitsSigned, `hex_bits_signed_forwards_matches, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Common0, `sail_instr_announce, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Common0, `sail_mark_register, "def", [(`k_a, "Type")]),
  (`RiscvZkvm.Sail.Common0, `sail_mark_register_pair, "def", [(`k_a, "Type"), (`k_b, "Type")]),
  (`RiscvZkvm.Sail.Common0, `sail_ignore_write_to, "def", [(`k_a, "Type")]),
  (`RiscvZkvm.Sail.Common0, `sail_pick_dependency, "def", [(`k_a, "Type")]),
  (`RiscvZkvm.Sail.Common0, `__monomorphize, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.SysControl, `MemoryOpResult_add_meta, "def", [(`k_t, "Type")]),
  (`RiscvZkvm.Sail.SysControl, `MemoryOpResult_drop_meta, "def", [(`k_t, "Type")]),
  (`RiscvZkvm.Sail.Common, `float_decompose, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Common, `float_compose, "def", [(`k_n, "Int")]),
  (`RiscvZkvm.Sail.Common, `float_has_max_exp, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Common, `is_lowest_one, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Common, `is_highest_one, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Common, `is_all_ones, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Common, `is_lowest_zero, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Common, `is_highest_zero, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Common, `is_all_zeros, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.HexBits, `hex_bits_forwards, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.HexBits, `hex_bits_forwards_matches, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.FdextRegs, `nan_box, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.FdextRegs, `nan_unbox, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.ReadWriteV1, `mem_read_request_is_exclusive, "def", [(`k_n, "Nat"), (`k_vasize, "Nat"), (`k_pa, "Type"), (`k_translation_summary, "Type"), (`k_arch_ak, "Type")]),
  (`RiscvZkvm.Sail.ReadWriteV1, `mem_read_request_is_ifetch, "def", [(`k_n, "Nat"), (`k_vasize, "Nat"), (`k_pa, "Type"), (`k_translation_summary, "Type"), (`k_arch_ak, "Type")]),
  (`RiscvZkvm.Sail.ReadWriteV1, `mem_write_request_is_exclusive, "def", [(`k_n, "Nat"), (`k_vasize, "Nat"), (`k_pa, "Type"), (`k_translation_summary, "Type"), (`k_arch_ak, "Type")]),
  (`RiscvZkvm.Sail.Errors, `not_implemented, "def", [(`k_a, "Type")]),
  (`RiscvZkvm.Sail.Errors, `internal_error, "def", [(`k_a, "Type")]),
  (`RiscvZkvm.Sail.Errors, `reserved_behavior, "def", [(`k_a, "Type")]),
  (`RiscvZkvm.Sail.SplitAccessUtils, `split_access, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.SplitAccessUtils, `split_on_page_boundary, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.VmemTlb, `tlb_set_pte, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Prelude, `sign_extend, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Prelude, `trunc, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Prelude, `zopz0zI_s, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Prelude, `zopz0zK_s, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Prelude, `zopz0zIzJ_s, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Prelude, `zopz0zKzJ_s, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Prelude, `zopz0zI_u, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Prelude, `zopz0zK_u, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Prelude, `zopz0zIzJ_u, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Prelude, `zopz0zKzJ_u, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Prelude, `shift_bits_right_arith, "def", [(`k_n, "Nat"), (`k_m, "Nat")]),
  (`RiscvZkvm.Sail.Prelude, `rotater, "def", [(`k_m, "Nat")]),
  (`RiscvZkvm.Sail.Prelude, `rotatel, "def", [(`k_m, "Nat")]),
  (`RiscvZkvm.Sail.Prelude, `rotate_bits_right, "def", [(`k_m, "Nat"), (`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Prelude, `rotate_bits_left, "def", [(`k_m, "Nat"), (`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Prelude, `reverse_bits, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Prelude, `hex_bits_str, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.RangeUtil, `range_subset, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.VmemPte, `ext_bits_of_PTE, "def", [(`k_pte_size, "Nat")]),
  (`RiscvZkvm.Sail.VmemPte, `PPN_of_PTE, "def", [(`k_pte_size, "Nat")]),
  (`RiscvZkvm.Sail.VmemPte, `update_PTE_Bits, "def", [(`k_pte_size, "Nat")]),
  (`RiscvZkvm.Sail.Types, `is_load_store, "def", [(`k_a, "Type")]),
  (`RiscvZkvm.Sail.Types, `is_prefetch_access, "def", [(`k_a, "Type")]),
  (`RiscvZkvm.Sail.Types, `is_store_conditional, "def", [(`k_a, "Type")]),
  (`RiscvZkvm.Sail.Callbacks, `fetch_callback, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.BaseInsts, `extend_value, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Defs, `zero_extend, "def", [(`k_n, "Nat")]),
  (`RiscvZkvm.Sail.Specialization, `sailTryCatch, "def", [(`α, "Type")]),
  (`RiscvZkvm.Sail.Specialization, `sailThrow, "def", [(`α, "Type")]),
  (`RiscvZkvm.Sail.Specialization, `undefined_vector, "abbrev", [(`α, "Type")]),
  (`RiscvZkvm.Sail.Specialization, `readRegRef, "abbrev", [(`α, "Type")]),
  (`RiscvZkvm.Sail.Specialization, `writeRegRef, "abbrev", [(`α, "Type")]),
  (`RiscvZkvm.Sail.Specialization, `reg_deref, "abbrev", [(`α, "Type")]),
  (`RiscvZkvm.Sail.Specialization, `sail_mem_write, "abbrev", [(`n, "Nat"), (`vasize, "Nat"), (`pa_size, "Nat"), (`ts, "Type"), (`arch, "Type")]),
  (`RiscvZkvm.Sail.Specialization, `sail_mem_read, "abbrev", [(`n, "Nat"), (`vasize, "Nat"), (`pa_size, "Nat"), (`ts, "Type"), (`arch, "Type")]),
  (`RiscvZkvm.Sail.Specialization, `sail_barrier, "abbrev", [(`α, "Sort _")]),
  (`RiscvZkvm.Sail.Specialization, `SailME.run, "def", [(`α, "Type")]),
  (`RiscvZkvm.Sail.Specialization, `SailME.throw, "def", [(`α, "Type"), (`β, "Type")]),
  (`RiscvZkvm.Sail.Specialization, `sailTryCatchE, "abbrev", [(`β, "Type"), (`α, "Type")]),
  (`RiscvZkvm.Sail.Specialization, `unwrapValue, "def", [(`α, "Type")])]

syntax (name := sailPinnedDeclaration) "sail_pinned_decl " command : command

/-- Preserve qualified declaration heads before Lean's namespace-expansion macro. -/
@[macro Lean.Parser.Command.declaration]
private def wrapSailPinnedDeclaration : Lean.Macro := fun command => do
  let declaration := command[1]
  let name := declaration[1][0].getId
  if !sailExplicitParameters.any (fun entry => entry.2.1 == name) then
    Lean.Macro.throwUnsupported
  return Lean.mkNode `sailPinnedDeclaration #[Lean.mkAtom "sail_pinned_decl", command]

/-- Insert binders only for exact module/declaration/kind entries; otherwise remain strict. -/
@[command_elab sailPinnedDeclaration]
private def elabSailPinnedDeclaration : Lean.Elab.Command.CommandElab := fun wrapped => do
  let command := wrapped[1]
  let declaration := command[1]
  let kind := if declaration.isOfKind ``Lean.Parser.Command.definition then "def"
    else if declaration.isOfKind ``Lean.Parser.Command.abbrev then "abbrev" else ""
  let module := (← Lean.getEnv).mainModule
  let name := declaration[1][0].getId
  let some (_, _, _, parameters) := sailExplicitParameters.find?
    (fun entry => entry.1 == module && entry.2.1 == name && entry.2.2.1 == kind)
    | Lean.Elab.Command.elabDeclaration command
  let binders ← parameters.toArray.mapM fun (name, type) => do
    let name := Lean.mkIdent name
    let type ← match type with
      | "Nat" => `(term| Nat)
      | "Int" => `(term| Int)
      | "Type" => `(term| Type)
      | "Sort _" => `(term| Sort _)
      | _ => throwError "unsupported pinned Sail binder type"
    `(Lean.Parser.Term.bracketedBinderF| {$name : $type})
  let signature := declaration[2].modifyArg 0
    (fun original => Lean.mkNullNode (binders.map (·.raw) ++ original.getArgs))
  let command := command.modifyArg 1 (fun declaration =>
    declaration.modifyArg 2 (fun _ => signature))
  Lean.Elab.Command.elabDeclaration command
