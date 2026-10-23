import RiscvZkvm.Sail.Arithmetic
import RiscvZkvm.Sail.BaseInsts
import RiscvZkvm.Sail.Callbacks
import RiscvZkvm.Sail.Common
import RiscvZkvm.Sail.Common0
import RiscvZkvm.Sail.Defs
import RiscvZkvm.Sail.Errors
import RiscvZkvm.Sail.FdextRegs
import RiscvZkvm.Sail.HexBits
import RiscvZkvm.Sail.HexBitsSigned
import RiscvZkvm.Sail.MemUtils
import RiscvZkvm.Sail.Prelude
import RiscvZkvm.Sail.RangeUtil
import RiscvZkvm.Sail.ReadWriteV1
import RiscvZkvm.Sail.Specialization
import RiscvZkvm.Sail.SplitAccessUtils
import RiscvZkvm.Sail.SysControl
import RiscvZkvm.Sail.Types
import RiscvZkvm.Sail.Vector
import RiscvZkvm.Sail.Vmem
import RiscvZkvm.Sail.VmemPte
import RiscvZkvm.Sail.VmemTlb

/-! # Original Sail declarations captured before making omitted binders explicit

Generated from the pinned extraction's compiled types and values with `pp.all = true`.
Every equality is kernel checked against the strictly elaborated, unchanged model source.
-/

set_option maxHeartbeats 1000000000
set_option maxRecDepth 1000000
set_option linter.unusedVariables false

namespace MetrologyAsm.StrictSourceEquivalence

universe u_1

/-- The original type and body of `RiscvZkvm.Sail.Functions.satp_to_asid`. -/
theorem captured_Vmem_satp_to_asid :
    (@RiscvZkvm.Sail.Functions.satp_to_asid :
      {k_n : Nat} →
        (satp_val : BitVec k_n) →
          BitVec
            (@ite.{1} Nat
              (@Eq.{1} Bool
                (@Decidable.decide
                  (@Eq.{1} Nat k_n (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                  (instDecidableEqNat k_n
                    (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                Bool.true)
              (instDecidableEqBool
                (@Decidable.decide
                  (@Eq.{1} Nat k_n (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                  (instDecidableEqNat k_n
                    (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                Bool.true)
              (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
              (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))))) =
      (
        fun {k_n : Nat} (satp_val : BitVec k_n) =>
          @ite.{1}
            (BitVec
              (@ite.{1} Nat
                (@Eq.{1} Bool
                  (@Decidable.decide
                    (@Eq.{1} Nat k_n (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                    (instDecidableEqNat k_n
                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                  Bool.true)
                (instDecidableEqBool
                  (@Decidable.decide
                    (@Eq.{1} Nat k_n (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                    (instDecidableEqNat k_n
                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                  Bool.true)
                (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))))
            (@Eq.{1} Bool
              (@BEq.beq.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat)
                (@Sail.BitVec.length k_n satp_val)
                (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
              Bool.true)
            (instDecidableEqBool
              (@BEq.beq.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat)
                (@Sail.BitVec.length k_n satp_val)
                (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
              Bool.true)
            (@BitVec.setWidth (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
              (@ite.{1} Nat
                (@Eq.{1} Bool
                  (@Decidable.decide
                    (@Eq.{1} Nat k_n (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                    (instDecidableEqNat k_n
                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                  Bool.true)
                (instDecidableEqBool
                  (@Decidable.decide
                    (@Eq.{1} Nat k_n (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                    (instDecidableEqNat k_n
                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                  Bool.true)
                (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))))
              (RiscvZkvm.Sail.Functions._get_Satp32_Asid
                (RiscvZkvm.Sail.Functions.Mk_Satp32
                  (@BitVec.setWidth k_n (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))
                    satp_val))))
            (@BitVec.setWidth (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
              (@ite.{1} Nat
                (@Eq.{1} Bool
                  (@Decidable.decide
                    (@Eq.{1} Nat k_n (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                    (instDecidableEqNat k_n
                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                  Bool.true)
                (instDecidableEqBool
                  (@Decidable.decide
                    (@Eq.{1} Nat k_n (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                    (instDecidableEqNat k_n
                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                  Bool.true)
                (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))))
              (RiscvZkvm.Sail.Functions._get_Satp64_Asid
                (RiscvZkvm.Sail.Functions.Mk_Satp64
                  (@BitVec.setWidth k_n (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))
                    satp_val))))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.satp_to_ppn`. -/
theorem captured_Vmem_satp_to_ppn :
    (@RiscvZkvm.Sail.Functions.satp_to_ppn :
      {k_n : Nat} →
        (satp_val : BitVec k_n) →
          BitVec
            (@ite.{1} Nat
              (@Eq.{1} Bool
                (@Decidable.decide
                  (@Eq.{1} Nat k_n (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                  (instDecidableEqNat k_n
                    (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                Bool.true)
              (instDecidableEqBool
                (@Decidable.decide
                  (@Eq.{1} Nat k_n (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                  (instDecidableEqNat k_n
                    (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                Bool.true)
              (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
              (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))))) =
      (
        fun {k_n : Nat} (satp_val : BitVec k_n) =>
          @ite.{1}
            (BitVec
              (@ite.{1} Nat
                (@Eq.{1} Bool
                  (@Decidable.decide
                    (@Eq.{1} Nat k_n (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                    (instDecidableEqNat k_n
                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                  Bool.true)
                (instDecidableEqBool
                  (@Decidable.decide
                    (@Eq.{1} Nat k_n (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                    (instDecidableEqNat k_n
                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                  Bool.true)
                (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
                (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44)))))
            (@Eq.{1} Bool
              (@BEq.beq.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat)
                (@Sail.BitVec.length k_n satp_val)
                (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
              Bool.true)
            (instDecidableEqBool
              (@BEq.beq.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat)
                (@Sail.BitVec.length k_n satp_val)
                (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
              Bool.true)
            (@BitVec.setWidth (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
              (@ite.{1} Nat
                (@Eq.{1} Bool
                  (@Decidable.decide
                    (@Eq.{1} Nat k_n (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                    (instDecidableEqNat k_n
                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                  Bool.true)
                (instDecidableEqBool
                  (@Decidable.decide
                    (@Eq.{1} Nat k_n (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                    (instDecidableEqNat k_n
                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                  Bool.true)
                (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
                (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))))
              (RiscvZkvm.Sail.Functions._get_Satp32_PPN
                (RiscvZkvm.Sail.Functions.Mk_Satp32
                  (@BitVec.setWidth k_n (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))
                    satp_val))))
            (@BitVec.setWidth (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44)))
              (@ite.{1} Nat
                (@Eq.{1} Bool
                  (@Decidable.decide
                    (@Eq.{1} Nat k_n (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                    (instDecidableEqNat k_n
                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                  Bool.true)
                (instDecidableEqBool
                  (@Decidable.decide
                    (@Eq.{1} Nat k_n (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                    (instDecidableEqNat k_n
                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                  Bool.true)
                (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
                (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))))
              (RiscvZkvm.Sail.Functions._get_Satp64_PPN
                (RiscvZkvm.Sail.Functions.Mk_Satp64
                  (@BitVec.setWidth k_n (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))
                    satp_val))))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.sail_mask`. -/
theorem captured_Vector_sail_mask :
    (@RiscvZkvm.Sail.Functions.sail_mask :
      {k_v : Nat} → (len : Nat) → (v : BitVec k_v) → BitVec len) =
      (
        fun {k_v : Nat} (len : Nat) (v : BitVec k_v) =>
          @ite.{1} (BitVec len)
            (@Eq.{1} Bool
              (@Decidable.decide (@LE.le.{0} Nat instLENat len (@Sail.BitVec.length k_v v))
                (Nat.decLe len (@Sail.BitVec.length k_v v)))
              Bool.true)
            (instDecidableEqBool
              (@Decidable.decide (@LE.le.{0} Nat instLENat len (@Sail.BitVec.length k_v v))
                (Nat.decLe len (@Sail.BitVec.length k_v v)))
              Bool.true)
            (@Sail.BitVec.truncate k_v v len) (@Sail.BitVec.zeroExtend k_v v len)
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.brev8`. -/
theorem captured_Arithmetic_brev8 :
    (@RiscvZkvm.Sail.Functions.brev8 :
      {k_m : Nat} → (input : BitVec k_m) → BitVec k_m) =
      (
        fun {k_m : Nat} (input : BitVec k_m) =>
          @Id.run.{0} (BitVec k_m)
            (have output : BitVec k_m := @RiscvZkvm.Sail.Functions.zeros (@Sail.BitVec.length k_m input);
            have loop_i_lower : Int := @OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0));
            have loop_i_upper : Int :=
              (fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_m output))
                (@OfNat.ofNat.{0} Int (nat_lit 8) (@instOfNat (nat_lit 8)));
            have loop_vars : BitVec k_m := output;
            @Bind.bind.{0, 0} Id.{0} (@Monad.toBind.{0, 0} Id.{0} Id.instMonad.{0}) (BitVec k_m)
              (BitVec k_m)
              (@ForIn.forIn.{0, 0, 0, 0} Id.{0} IntRange Int
                (@instForInOfForIn'.{0, 0, 0, 0} Id.{0} IntRange Int
                  (@inferInstance.{1} (Membership.{0, 0} Int IntRange) IntRange.instMemIntRange)
                  (@IntRange.instForIn'IntInferInstanceMembershipOfMonad.{0, 0} Id.{0} Id.instMonad.{0}))
                (BitVec k_m)
                (IntRange.mk loop_i_lower loop_i_upper
                  (@OfNat.ofNat.{0} Int (nat_lit 8) (@instOfNat (nat_lit 8)))
                  fun
                    (a :
                      @Eq.{1} Int (@OfNat.ofNat.{0} Int (nat_lit 8) (@instOfNat (nat_lit 8)))
                        (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) =>
                  RiscvZkvm.Sail.Functions.brev8._proof_1 a)
                loop_vars fun (i : Int) (__s : BitVec k_m) =>
                have loop_vars : BitVec k_m := __s;
                have output : BitVec k_m := loop_vars;
                have loop_vars : BitVec k_m :=
                  @Sail.BitVec.updateSubrange k_m output
                    (Int.toNat
                      ((fun (x y : Int) =>
                          @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x y)
                        i (@OfNat.ofNat.{0} Int (nat_lit 7) (@instOfNat (nat_lit 7)))))
                    (Int.toNat i)
                    (@RiscvZkvm.Sail.Functions.reverse_bits
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                          (Int.toNat
                            ((fun (x y : Int) =>
                                @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x y)
                              i (@OfNat.ofNat.{0} Int (nat_lit 7) (@instOfNat (nat_lit 7)))))
                          (Int.toNat i))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@Sail.BitVec.extractLsb k_m input
                        (Int.toNat
                          ((fun (x y : Int) =>
                              @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x y)
                            i (@OfNat.ofNat.{0} Int (nat_lit 7) (@instOfNat (nat_lit 7)))))
                        (Int.toNat i)));
                @Pure.pure.{0, 0} Id.{0}
                  (@Applicative.toPure.{0, 0} Id.{0} (@Monad.toApplicative.{0, 0} Id.{0} Id.instMonad.{0}))
                  (ForInStep.{0} (BitVec k_m)) (@ForInStep.yield.{0} (BitVec k_m) loop_vars))
              fun (__s : BitVec k_m) =>
              have loop_vars : BitVec k_m := __s;
              @Pure.pure.{0, 0} Id.{0}
                (@Applicative.toPure.{0, 0} Id.{0} (@Monad.toApplicative.{0, 0} Id.{0} Id.instMonad.{0}))
                (BitVec k_m) loop_vars)
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.carryless_mul`. -/
theorem captured_Arithmetic_carryless_mul :
    (@RiscvZkvm.Sail.Functions.carryless_mul :
      {k_n : Nat} →
        (a b : BitVec k_n) →
          BitVec
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n)) =
      (
        fun {k_n : Nat} (a b : BitVec k_n) =>
          @Id.run.{0}
            (BitVec
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n))
            (have result :
              BitVec
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n) :=
              @RiscvZkvm.Sail.Functions.zeros
                (Int.toNat
                  ((fun (x y : Int) => @HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) x y)
                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))
                    (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n b))));
            have loop_i_lower : Int := @OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0));
            have loop_i_upper : Int :=
              (fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n b))
                (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)));
            have loop_vars :
              BitVec
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n) :=
              result;
            @Bind.bind.{0, 0} Id.{0} (@Monad.toBind.{0, 0} Id.{0} Id.instMonad.{0})
              (BitVec
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n))
              (BitVec
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n))
              (@ForIn.forIn.{0, 0, 0, 0} Id.{0} IntRange Int
                (@instForInOfForIn'.{0, 0, 0, 0} Id.{0} IntRange Int
                  (@inferInstance.{1} (Membership.{0, 0} Int IntRange) IntRange.instMemIntRange)
                  (@IntRange.instForIn'IntInferInstanceMembershipOfMonad.{0, 0} Id.{0} Id.instMonad.{0}))
                (BitVec
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n))
                (IntRange.mk loop_i_lower loop_i_upper
                  (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                  fun
                    (a :
                      @Eq.{1} Int (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) =>
                  RiscvZkvm.Sail.Functions.carryless_mul._proof_1 a)
                loop_vars
                fun (i : Int)
                  (__s :
                    BitVec
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n)) =>
                have loop_vars :
                  BitVec
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n) :=
                  __s;
                have result :
                  BitVec
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n) :=
                  loop_vars;
                have loop_vars :
                  BitVec
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n) :=
                  @ite.{1}
                    (BitVec
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n))
                    (@Eq.{1} Bool
                      (@BEq.beq.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@instBEqOfDecidableEq.{0}
                          (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@instDecidableEqBitVec
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@Sail.BitVec.access k_n a (Int.toNat i))
                        (BitVec.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@BEq.beq.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@instBEqOfDecidableEq.{0}
                          (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@instDecidableEqBitVec
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@Sail.BitVec.access k_n a (Int.toNat i))
                        (BitVec.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      Bool.true)
                    (@HXor.hXor.{0, 0, 0}
                      (BitVec
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n))
                      (BitVec
                        (Int.toNat
                          ((fun (x y : Int) =>
                              @HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) x y)
                            (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))
                            (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n b)))))
                      (BitVec
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n))
                      (@instHXorBitVec_sail
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n)
                        (Int.toNat
                          ((fun (x y : Int) =>
                              @HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) x y)
                            (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))
                            (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n b)))))
                      result
                      (@HShiftLeft.hShiftLeft.{0, 0, 0}
                        (BitVec
                          (Int.toNat
                            ((fun (x y : Int) =>
                                @HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) x y)
                              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))
                              (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n b)))))
                        Int
                        (BitVec
                          (Int.toNat
                            ((fun (x y : Int) =>
                                @HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) x y)
                              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))
                              (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n b)))))
                        (@Sail.instHShiftLeftBitVecInt_sail
                          (Int.toNat
                            ((fun (x y : Int) =>
                                @HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) x y)
                              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))
                              (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n b)))))
                        (@zero_extend k_n
                          (Int.toNat
                            ((fun (x y : Int) =>
                                @HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) x y)
                              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))
                              (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n b))))
                          b)
                        i))
                    result;
                @Pure.pure.{0, 0} Id.{0}
                  (@Applicative.toPure.{0, 0} Id.{0} (@Monad.toApplicative.{0, 0} Id.{0} Id.instMonad.{0}))
                  (ForInStep.{0}
                    (BitVec
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n)))
                  (@ForInStep.yield.{0}
                    (BitVec
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n))
                    loop_vars))
              fun
                (__s :
                  BitVec
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n)) =>
              have loop_vars :
                BitVec
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n) :=
                __s;
              @Pure.pure.{0, 0} Id.{0}
                (@Applicative.toPure.{0, 0} Id.{0} (@Monad.toApplicative.{0, 0} Id.{0} Id.instMonad.{0}))
                (BitVec
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n))
                loop_vars)
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.carryless_mulr`. -/
theorem captured_Arithmetic_carryless_mulr :
    (@RiscvZkvm.Sail.Functions.carryless_mulr :
      {k_n : Nat} → (a b : BitVec k_n) → BitVec k_n) =
      (
        fun {k_n : Nat} (a b : BitVec k_n) =>
          @Id.run.{0} (BitVec k_n)
            (have result : BitVec k_n := @RiscvZkvm.Sail.Functions.zeros (@Sail.BitVec.length k_n b);
            have loop_i_lower : Int := @OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0));
            have loop_i_upper : Int :=
              (fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n result))
                (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)));
            have loop_vars : BitVec k_n := result;
            @Bind.bind.{0, 0} Id.{0} (@Monad.toBind.{0, 0} Id.{0} Id.instMonad.{0}) (BitVec k_n)
              (BitVec k_n)
              (@ForIn.forIn.{0, 0, 0, 0} Id.{0} IntRange Int
                (@instForInOfForIn'.{0, 0, 0, 0} Id.{0} IntRange Int
                  (@inferInstance.{1} (Membership.{0, 0} Int IntRange) IntRange.instMemIntRange)
                  (@IntRange.instForIn'IntInferInstanceMembershipOfMonad.{0, 0} Id.{0} Id.instMonad.{0}))
                (BitVec k_n)
                (IntRange.mk loop_i_lower loop_i_upper
                  (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                  fun
                    (a :
                      @Eq.{1} Int (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) =>
                  RiscvZkvm.Sail.Functions.carryless_mul._proof_1 a)
                loop_vars fun (i : Int) (__s : BitVec k_n) =>
                have loop_vars : BitVec k_n := __s;
                have result : BitVec k_n := loop_vars;
                have loop_vars : BitVec k_n :=
                  @ite.{1} (BitVec k_n)
                    (@Eq.{1} Bool
                      (@BEq.beq.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@instBEqOfDecidableEq.{0}
                          (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@instDecidableEqBitVec
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@Sail.BitVec.access k_n a (Int.toNat i))
                        (BitVec.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@BEq.beq.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@instBEqOfDecidableEq.{0}
                          (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@instDecidableEqBitVec
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@Sail.BitVec.access k_n a (Int.toNat i))
                        (BitVec.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      Bool.true)
                    (@HXor.hXor.{0, 0, 0} (BitVec k_n) (BitVec k_n) (BitVec k_n)
                      (@instHXorOfXorOp.{0} (BitVec k_n) (@BitVec.instXorOp k_n)) result
                      (@HShiftRight.hShiftRight.{0, 0, 0} (BitVec k_n) Int (BitVec k_n)
                        (@Sail.instHShiftRightBitVecInt_sail k_n) b
                        ((fun (x y : Int) =>
                            @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                          ((fun (x y : Int) =>
                              @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                            (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n result)) i)
                          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                    result;
                @Pure.pure.{0, 0} Id.{0}
                  (@Applicative.toPure.{0, 0} Id.{0} (@Monad.toApplicative.{0, 0} Id.{0} Id.instMonad.{0}))
                  (ForInStep.{0} (BitVec k_n)) (@ForInStep.yield.{0} (BitVec k_n) loop_vars))
              fun (__s : BitVec k_n) =>
              have loop_vars : BitVec k_n := __s;
              @Pure.pure.{0, 0} Id.{0}
                (@Applicative.toPure.{0, 0} Id.{0} (@Monad.toApplicative.{0, 0} Id.{0} Id.instMonad.{0}))
                (BitVec k_n) loop_vars)
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.carryless_mul_reversed`. -/
theorem captured_Arithmetic_carryless_mul_reversed :
    (@RiscvZkvm.Sail.Functions.carryless_mul_reversed :
      {k_n : Nat} → (a b : BitVec k_n) → BitVec k_n) =
      (
        fun {k_n : Nat} (a b : BitVec k_n) =>
          have prod :
            BitVec
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n) :=
            @RiscvZkvm.Sail.Functions.carryless_mul k_n (@RiscvZkvm.Sail.Functions.reverse_bits k_n a)
              (@RiscvZkvm.Sail.Functions.reverse_bits k_n b);
          @RiscvZkvm.Sail.Functions.reverse_bits k_n
            (@BitVec.setWidth
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                  (Int.toNat
                    ((fun (x y : Int) =>
                        @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                      (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n b))
                      (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k_n
              (@Sail.BitVec.extractLsb
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k_n)
                prod
                (Int.toNat
                  ((fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                    (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n b))
                    (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.rev8`. -/
theorem captured_Arithmetic_rev8 :
    (@RiscvZkvm.Sail.Functions.rev8 :
      {k_m : Nat} → (input : BitVec k_m) → BitVec k_m) =
      (
        fun {k_m : Nat} (input : BitVec k_m) =>
          @Id.run.{0} (BitVec k_m)
            (have output : BitVec k_m := @RiscvZkvm.Sail.Functions.zeros (@Sail.BitVec.length k_m input);
            have loop_i_lower : Int := @OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0));
            have loop_i_upper : Int :=
              (fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_m output))
                (@OfNat.ofNat.{0} Int (nat_lit 8) (@instOfNat (nat_lit 8)));
            have loop_vars : BitVec k_m := output;
            @Bind.bind.{0, 0} Id.{0} (@Monad.toBind.{0, 0} Id.{0} Id.instMonad.{0}) (BitVec k_m)
              (BitVec k_m)
              (@ForIn.forIn.{0, 0, 0, 0} Id.{0} IntRange Int
                (@instForInOfForIn'.{0, 0, 0, 0} Id.{0} IntRange Int
                  (@inferInstance.{1} (Membership.{0, 0} Int IntRange) IntRange.instMemIntRange)
                  (@IntRange.instForIn'IntInferInstanceMembershipOfMonad.{0, 0} Id.{0} Id.instMonad.{0}))
                (BitVec k_m)
                (IntRange.mk loop_i_lower loop_i_upper
                  (@OfNat.ofNat.{0} Int (nat_lit 8) (@instOfNat (nat_lit 8)))
                  fun
                    (a :
                      @Eq.{1} Int (@OfNat.ofNat.{0} Int (nat_lit 8) (@instOfNat (nat_lit 8)))
                        (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) =>
                  RiscvZkvm.Sail.Functions.brev8._proof_1 a)
                loop_vars fun (i : Int) (__s : BitVec k_m) =>
                have loop_vars : BitVec k_m := __s;
                have output : BitVec k_m := loop_vars;
                have loop_vars : BitVec k_m :=
                  @Sail.BitVec.updateSubrange k_m output
                    (Int.toNat
                      ((fun (x y : Int) =>
                          @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x y)
                        i (@OfNat.ofNat.{0} Int (nat_lit 7) (@instOfNat (nat_lit 7)))))
                    (Int.toNat i)
                    (@BitVec.setWidth
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                          (Int.toNat
                            ((fun (x y : Int) =>
                                @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                              ((fun (x y : Int) =>
                                  @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                                (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_m output)) i)
                              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                          (Int.toNat
                            ((fun (x y : Int) =>
                                @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                              ((fun (x y : Int) =>
                                  @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                                (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_m output)) i)
                              (@OfNat.ofNat.{0} Int (nat_lit 8) (@instOfNat (nat_lit 8))))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                          (Int.toNat
                            ((fun (x y : Int) =>
                                @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x y)
                              i (@OfNat.ofNat.{0} Int (nat_lit 7) (@instOfNat (nat_lit 7)))))
                          (Int.toNat i))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@Sail.BitVec.extractLsb k_m input
                        (Int.toNat
                          ((fun (x y : Int) =>
                              @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                            ((fun (x y : Int) =>
                                @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                              (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_m output)) i)
                            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                        (Int.toNat
                          ((fun (x y : Int) =>
                              @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                            ((fun (x y : Int) =>
                                @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                              (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_m output)) i)
                            (@OfNat.ofNat.{0} Int (nat_lit 8) (@instOfNat (nat_lit 8)))))));
                @Pure.pure.{0, 0} Id.{0}
                  (@Applicative.toPure.{0, 0} Id.{0} (@Monad.toApplicative.{0, 0} Id.{0} Id.instMonad.{0}))
                  (ForInStep.{0} (BitVec k_m)) (@ForInStep.yield.{0} (BitVec k_m) loop_vars))
              fun (__s : BitVec k_m) =>
              have loop_vars : BitVec k_m := __s;
              @Pure.pure.{0, 0} Id.{0}
                (@Applicative.toPure.{0, 0} Id.{0} (@Monad.toApplicative.{0, 0} Id.{0} Id.instMonad.{0}))
                (BitVec k_m) loop_vars)
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.count_ones`. -/
theorem captured_Arithmetic_count_ones :
    (@RiscvZkvm.Sail.Functions.count_ones :
      {k_n : Nat} → (x : BitVec k_n) → SailM Nat) =
      (
        fun {k_n : Nat} (x : BitVec k_n) =>
          have count : Nat := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0));
          have loop_i_lower : Int := @OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0));
          have loop_i_upper : Int :=
            (fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
              (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))
              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)));
          have loop_vars : Nat := count;
          @Bind.bind.{0, 0} SailM
            (@Monad.toBind.{0, 0} SailM
              (@EStateM.instMonad.{0} (Sail.Error exception)
                (@Sail.ConcurrencyInterfaceV1.SequentialState Register instDecidableEqRegister
                  instHashableRegister RegisterType Sail.ConcurrencyInterfaceV1.trivialChoiceSource)))
            Nat Nat
            (@ForIn.forIn.{0, 0, 0, 0} SailM IntRange Int
              (@instForInOfForIn'.{0, 0, 0, 0} SailM IntRange Int
                (@inferInstance.{1} (Membership.{0, 0} Int IntRange) IntRange.instMemIntRange)
                (@IntRange.instForIn'IntInferInstanceMembershipOfMonad.{0, 0} SailM
                  (@EStateM.instMonad.{0} (Sail.Error exception)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState Register instDecidableEqRegister
                      instHashableRegister RegisterType Sail.ConcurrencyInterfaceV1.trivialChoiceSource))))
              Nat
              (IntRange.mk loop_i_lower loop_i_upper
                (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                fun
                  (a :
                    @Eq.{1} Int (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) =>
                RiscvZkvm.Sail.Functions.carryless_mul._proof_1 a)
              loop_vars fun (i : Int) (__s : Nat) =>
              have loop_vars : Nat := __s;
              have count : Nat := loop_vars;
              @ite.{1} (SailM (ForInStep.{0} Nat))
                (@Eq.{1} Bool
                  (@BEq.beq.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@instBEqOfDecidableEq.{0}
                      (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@instDecidableEqBitVec
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@Sail.BitVec.access k_n x (Int.toNat i))
                    (BitVec.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Bool.true)
                (instDecidableEqBool
                  (@BEq.beq.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@instBEqOfDecidableEq.{0}
                      (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@instDecidableEqBitVec
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@Sail.BitVec.access k_n x (Int.toNat i))
                    (BitVec.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  Bool.true)
                (@Bind.bind.{0, 0} SailM
                  (@Monad.toBind.{0, 0} SailM
                    (@EStateM.instMonad.{0} (Sail.Error exception)
                      (@Sail.ConcurrencyInterfaceV1.SequentialState Register instDecidableEqRegister
                        instHashableRegister RegisterType Sail.ConcurrencyInterfaceV1.trivialChoiceSource)))
                  Nat (ForInStep.{0} Nat)
                  (have new_count : Int :=
                    (fun (x y : Int) =>
                        @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x y)
                      (@Nat.cast.{0} Int instNatCastInt count)
                      (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)));
                  @Bind.bind.{0, 0} SailM
                    (@Monad.toBind.{0, 0} SailM
                      (@EStateM.instMonad.{0} (Sail.Error exception)
                        (@Sail.ConcurrencyInterfaceV1.SequentialState Register instDecidableEqRegister
                          instHashableRegister RegisterType
                          Sail.ConcurrencyInterfaceV1.trivialChoiceSource)))
                    Unit Nat
                    (Sail.assert
                      (@Decidable.decide
                        (@LE.le.{0} Int Int.instLEInt new_count
                          (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x)))
                        (Int.decLe new_count
                          (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))))
                      "core/arithmetic.sail:85.28-85.29")
                    fun (__r : Unit) =>
                    @Pure.pure.{0, 0} SailM
                      (@Applicative.toPure.{0, 0} SailM
                        (@Monad.toApplicative.{0, 0} SailM
                          (@EStateM.instMonad.{0} (Sail.Error exception)
                            (@Sail.ConcurrencyInterfaceV1.SequentialState Register instDecidableEqRegister
                              instHashableRegister RegisterType
                              Sail.ConcurrencyInterfaceV1.trivialChoiceSource))))
                      Nat (Int.toNat new_count))
                  fun (__x : Nat) =>
                  have loop_vars : Nat := __x;
                  @Pure.pure.{0, 0} SailM
                    (@Applicative.toPure.{0, 0} SailM
                      (@Monad.toApplicative.{0, 0} SailM
                        (@EStateM.instMonad.{0} (Sail.Error exception)
                          (@Sail.ConcurrencyInterfaceV1.SequentialState Register instDecidableEqRegister
                            instHashableRegister RegisterType
                            Sail.ConcurrencyInterfaceV1.trivialChoiceSource))))
                    (ForInStep.{0} Nat) (@ForInStep.yield.{0} Nat loop_vars))
                (@Bind.bind.{0, 0} SailM
                  (@Monad.toBind.{0, 0} SailM
                    (@EStateM.instMonad.{0} (Sail.Error exception)
                      (@Sail.ConcurrencyInterfaceV1.SequentialState Register instDecidableEqRegister
                        instHashableRegister RegisterType Sail.ConcurrencyInterfaceV1.trivialChoiceSource)))
                  Nat (ForInStep.{0} Nat)
                  (@Pure.pure.{0, 0} SailM
                    (@Applicative.toPure.{0, 0} SailM
                      (@Monad.toApplicative.{0, 0} SailM
                        (@EStateM.instMonad.{0} (Sail.Error exception)
                          (@Sail.ConcurrencyInterfaceV1.SequentialState Register instDecidableEqRegister
                            instHashableRegister RegisterType
                            Sail.ConcurrencyInterfaceV1.trivialChoiceSource))))
                    Nat count)
                  fun (__x : Nat) =>
                  have loop_vars : Nat := __x;
                  @Pure.pure.{0, 0} SailM
                    (@Applicative.toPure.{0, 0} SailM
                      (@Monad.toApplicative.{0, 0} SailM
                        (@EStateM.instMonad.{0} (Sail.Error exception)
                          (@Sail.ConcurrencyInterfaceV1.SequentialState Register instDecidableEqRegister
                            instHashableRegister RegisterType
                            Sail.ConcurrencyInterfaceV1.trivialChoiceSource))))
                    (ForInStep.{0} Nat) (@ForInStep.yield.{0} Nat loop_vars)))
            fun (__s : Nat) =>
            have loop_vars : Nat := __s;
            @Pure.pure.{0, 0} SailM
              (@Applicative.toPure.{0, 0} SailM
                (@Monad.toApplicative.{0, 0} SailM
                  (@EStateM.instMonad.{0} (Sail.Error exception)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState Register instDecidableEqRegister
                      instHashableRegister RegisterType Sail.ConcurrencyInterfaceV1.trivialChoiceSource))))
              Nat loop_vars
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.access_within`. -/
theorem captured_MemUtils_access_within :
    (@RiscvZkvm.Sail.Functions.access_within :
      {k_width : Nat} → (addr : BitVec k_width) → (bytes region_width_exp : Nat) → Bool) =
      (
        fun {k_width : Nat} (addr : BitVec k_width) (bytes region_width_exp : Nat) =>
          have mask : BitVec k_width :=
            @Complement.complement.{0} (BitVec k_width) (@BitVec.instComplement k_width)
              (@zero_extend region_width_exp (@Sail.BitVec.length k_width addr)
                (@RiscvZkvm.Sail.Functions.ones region_width_exp));
          @BEq.beq.{0} (BitVec k_width)
            (@instBEqOfDecidableEq.{0} (BitVec k_width) (@instDecidableEqBitVec k_width))
            (@HAnd.hAnd.{0, 0, 0} (BitVec k_width) (BitVec k_width) (BitVec k_width)
              (@instHAndOfAndOp.{0} (BitVec k_width) (@BitVec.instAndOp k_width)) addr mask)
            (@HAnd.hAnd.{0, 0, 0} (BitVec k_width) (BitVec k_width) (BitVec k_width)
              (@instHAndOfAndOp.{0} (BitVec k_width) (@BitVec.instAndOp k_width))
              (@Sail.BitVec.addInt k_width addr
                ((fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                  (@Nat.cast.{0} Int instNatCastInt bytes)
                  (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
              mask)
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.hex_bits_signed_forwards`. -/
theorem captured_HexBitsSigned_hex_bits_signed_forwards :
    (@RiscvZkvm.Sail.Functions.hex_bits_signed_forwards :
      {k_n : Nat} → (bv : BitVec k_n) → Prod.{0, 0} Nat String) =
      (
        fun {k_n : Nat} (bv : BitVec k_n) =>
          have len : Nat := @Sail.BitVec.length k_n bv;
          have s : String :=
            @ite.{1} String
              (@Eq.{1} Bool
                (@BEq.beq.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@instBEqOfDecidableEq.{0}
                    (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@instDecidableEqBitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@Sail.BitVec.access k_n bv
                    (Int.toNat
                      ((fun (x y : Int) =>
                          @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                        (@Nat.cast.{0} Int instNatCastInt len)
                        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                  (BitVec.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bool.true)
              (instDecidableEqBool
                (@BEq.beq.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@instBEqOfDecidableEq.{0}
                    (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@instDecidableEqBitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@Sail.BitVec.access k_n bv
                    (Int.toNat
                      ((fun (x y : Int) =>
                          @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                        (@Nat.cast.{0} Int instNatCastInt len)
                        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                  (BitVec.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                Bool.true)
              (@HAppend.hAppend.{0, 0, 0} String String String
                (@instHAppendOfAppend.{0} String instAppendString) "-"
                (Sail.Int.toHex
                  ((fun (x y : Int) => @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x y)
                    (@Sail.BitVec.toNatInt k_n
                      (@Complement.complement.{0} (BitVec k_n) (@BitVec.instComplement k_n) bv))
                    (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
              (Sail.Int.toHex (@Sail.BitVec.toNatInt k_n bv));
          @Prod.mk.{0, 0} Nat String (@Sail.BitVec.length k_n bv) s
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.hex_bits_signed_forwards_matches`. -/
theorem captured_HexBitsSigned_hex_bits_signed_forwards_matches :
    (@RiscvZkvm.Sail.Functions.hex_bits_signed_forwards_matches :
      {k_n : Nat} → (x_0 : BitVec k_n) → Bool) =
      (
        fun {k_n : Nat} (x_0 : BitVec k_n) => Bool.true
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.sail_instr_announce`. -/
theorem captured_Common0_sail_instr_announce :
    (@RiscvZkvm.Sail.Functions.sail_instr_announce :
      {k_n : Nat} → (x_0 : BitVec k_n) → Unit) =
      (
        fun {k_n : Nat} (x_0 : BitVec k_n) => Unit.unit
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.sail_mark_register`. -/
theorem captured_Common0_sail_mark_register :
    (@RiscvZkvm.Sail.Functions.sail_mark_register :
      {k_a : Type} → (x_0 : Sail.RegisterRef k_a) → (x_1 : String) → Unit) =
      (
        fun {k_a : Type} (x_0 : Sail.RegisterRef k_a) (x_1 : String) => Unit.unit
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.sail_mark_register_pair`. -/
theorem captured_Common0_sail_mark_register_pair :
    (@RiscvZkvm.Sail.Functions.sail_mark_register_pair :
      {k_a k_b : Type} →
        (x_0 : Sail.RegisterRef k_a) → (x_1 : Sail.RegisterRef k_b) → (x_2 : String) → Unit) =
      (
        fun {k_a k_b : Type} (x_0 : Sail.RegisterRef k_a) (x_1 : Sail.RegisterRef k_b) (x_2 : String) =>
          Unit.unit
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.sail_ignore_write_to`. -/
theorem captured_Common0_sail_ignore_write_to :
    (@RiscvZkvm.Sail.Functions.sail_ignore_write_to :
      {k_a : Type} → (reg : Sail.RegisterRef k_a) → Unit) =
      (
        fun {k_a : Type} (reg : Sail.RegisterRef k_a) =>
          @RiscvZkvm.Sail.Functions.sail_mark_register k_a reg "ignore_write"
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.sail_pick_dependency`. -/
theorem captured_Common0_sail_pick_dependency :
    (@RiscvZkvm.Sail.Functions.sail_pick_dependency :
      {k_a : Type} → (reg : Sail.RegisterRef k_a) → Unit) =
      (
        fun {k_a : Type} (reg : Sail.RegisterRef k_a) =>
          @RiscvZkvm.Sail.Functions.sail_mark_register k_a reg "pick"
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.__monomorphize`. -/
theorem captured_Common0___monomorphize :
    (@RiscvZkvm.Sail.Functions.__monomorphize :
      {k_n : Nat} → (bv : BitVec k_n) → BitVec k_n) =
      (
        fun {k_n : Nat} (bv : BitVec k_n) => bv
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.MemoryOpResult_add_meta`. -/
theorem captured_SysControl_MemoryOpResult_add_meta :
    (@RiscvZkvm.Sail.Functions.MemoryOpResult_add_meta :
      {k_t : Type} →
        (r : Sail.Result k_t (Prod.{0, 0} physaddr ExceptionType)) →
          (m : Unit) → Sail.Result (Prod.{0, 0} k_t Unit) (Prod.{0, 0} physaddr ExceptionType)) =
      (
        fun {k_t : Type} (r : Sail.Result k_t (Prod.{0, 0} physaddr ExceptionType)) (m : Unit) =>
          @RiscvZkvm.Sail.Functions.MemoryOpResult_add_meta.match_1.{1} k_t
            (fun (r : Sail.Result k_t (Prod.{0, 0} physaddr ExceptionType)) =>
              Sail.Result (Prod.{0, 0} k_t Unit) (Prod.{0, 0} physaddr ExceptionType))
            r
            (fun (v : k_t) =>
              @Sail.Result.Ok (Prod.{0, 0} k_t Unit) (Prod.{0, 0} physaddr ExceptionType)
                (@Prod.mk.{0, 0} k_t Unit v m))
            fun (e : Prod.{0, 0} physaddr ExceptionType) =>
            @Sail.Result.Err (Prod.{0, 0} k_t Unit) (Prod.{0, 0} physaddr ExceptionType) e
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.MemoryOpResult_drop_meta`. -/
theorem captured_SysControl_MemoryOpResult_drop_meta :
    (@RiscvZkvm.Sail.Functions.MemoryOpResult_drop_meta :
      {k_t : Type} →
        (r : Sail.Result (Prod.{0, 0} k_t Unit) (Prod.{0, 0} physaddr ExceptionType)) →
          Sail.Result k_t (Prod.{0, 0} physaddr ExceptionType)) =
      (
        fun {k_t : Type} (r : Sail.Result (Prod.{0, 0} k_t Unit) (Prod.{0, 0} physaddr ExceptionType)) =>
          @RiscvZkvm.Sail.Functions.MemoryOpResult_drop_meta.match_1.{1} k_t
            (fun (r : Sail.Result (Prod.{0, 0} k_t Unit) (Prod.{0, 0} physaddr ExceptionType)) =>
              Sail.Result k_t (Prod.{0, 0} physaddr ExceptionType))
            r (fun (v : k_t) (_m : Unit) => @Sail.Result.Ok k_t (Prod.{0, 0} physaddr ExceptionType) v)
            fun (e : Prod.{0, 0} physaddr ExceptionType) =>
            @Sail.Result.Err k_t (Prod.{0, 0} physaddr ExceptionType) e
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.float_decompose`. -/
theorem captured_Common_float_decompose :
    (@RiscvZkvm.Sail.Functions.float_decompose :
      {k_n : Nat} → (op : BitVec k_n) → float_bits (@Nat.cast.{0} Int instNatCastInt k_n)) =
      (
        fun {k_n : Nat} (op : BitVec k_n) =>
          RiscvZkvm.Sail.Functions.float_decompose.match_1.{1}
            (fun (x : Nat) => float_bits (@Nat.cast.{0} Int instNatCastInt k_n))
            (@Sail.BitVec.length k_n op)
            (fun (_ : Unit) =>
              @float_bits.mk (@Nat.cast.{0} Int instNatCastInt k_n)
                (@Sail.BitVec.extractLsb k_n op
                  (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))))
                (@BitVec.setWidth
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@ite.{1} Nat
                    (@Eq.{1} Bool
                      (@Decidable.decide
                        (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@Decidable.decide
                        (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@ite.{1} Nat
                        (@Eq.{1} Bool
                          (@Decidable.decide
                            (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (instDecidableEqBool
                          (@Decidable.decide
                            (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))))))
                  (@Sail.BitVec.extractLsb k_n op
                    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))
                (@BitVec.setWidth
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@ite.{1} Nat
                    (@Eq.{1} Bool
                      (@Decidable.decide
                        (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@Decidable.decide
                        (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                      (@ite.{1} Nat
                        (@Eq.{1} Bool
                          (@Decidable.decide
                            (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (instDecidableEqBool
                          (@Decidable.decide
                            (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))))
                  (@Sail.BitVec.extractLsb k_n op
                    (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            (fun (_ : Unit) =>
              @float_bits.mk (@Nat.cast.{0} Int instNatCastInt k_n)
                (@Sail.BitVec.extractLsb k_n op
                  (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31))))
                (@BitVec.setWidth
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@ite.{1} Nat
                    (@Eq.{1} Bool
                      (@Decidable.decide
                        (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@Decidable.decide
                        (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@ite.{1} Nat
                        (@Eq.{1} Bool
                          (@Decidable.decide
                            (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (instDecidableEqBool
                          (@Decidable.decide
                            (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))))))
                  (@Sail.BitVec.extractLsb k_n op
                    (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))))
                (@BitVec.setWidth
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@ite.{1} Nat
                    (@Eq.{1} Bool
                      (@Decidable.decide
                        (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@Decidable.decide
                        (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                      (@ite.{1} Nat
                        (@Eq.{1} Bool
                          (@Decidable.decide
                            (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (instDecidableEqBool
                          (@Decidable.decide
                            (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))))
                  (@Sail.BitVec.extractLsb k_n op
                    (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            (fun (_ : Unit) =>
              @float_bits.mk (@Nat.cast.{0} Int instNatCastInt k_n)
                (@Sail.BitVec.extractLsb k_n op
                  (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63))))
                (@BitVec.setWidth
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@ite.{1} Nat
                    (@Eq.{1} Bool
                      (@Decidable.decide
                        (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@Decidable.decide
                        (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@ite.{1} Nat
                        (@Eq.{1} Bool
                          (@Decidable.decide
                            (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (instDecidableEqBool
                          (@Decidable.decide
                            (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))))))
                  (@Sail.BitVec.extractLsb k_n op
                    (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52)))))
                (@BitVec.setWidth
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 51) (instOfNatNat (nat_lit 51)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@ite.{1} Nat
                    (@Eq.{1} Bool
                      (@Decidable.decide
                        (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@Decidable.decide
                        (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                      (@ite.{1} Nat
                        (@Eq.{1} Bool
                          (@Decidable.decide
                            (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (instDecidableEqBool
                          (@Decidable.decide
                            (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))))
                  (@Sail.BitVec.extractLsb k_n op
                    (@OfNat.ofNat.{0} Nat (nat_lit 51) (instOfNatNat (nat_lit 51)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            fun (x : Nat) =>
            @float_bits.mk (@Nat.cast.{0} Int instNatCastInt k_n)
              (@Sail.BitVec.extractLsb k_n op
                (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
                (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127))))
              (@BitVec.setWidth
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@ite.{1} Nat
                  (@Eq.{1} Bool
                    (@Decidable.decide
                      (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                        (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                      (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                        (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                    Bool.true)
                  (instDecidableEqBool
                    (@Decidable.decide
                      (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                        (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                      (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                        (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                    Bool.true)
                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                  (@ite.{1} Nat
                    (@Eq.{1} Bool
                      (@Decidable.decide
                        (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                        (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@Decidable.decide
                        (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                        (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                      Bool.true)
                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                          (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                          (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))))))
                (@Sail.BitVec.extractLsb k_n op
                  (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))))
              (@BitVec.setWidth
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 111) (instOfNatNat (nat_lit 111)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@ite.{1} Nat
                  (@Eq.{1} Bool
                    (@Decidable.decide
                      (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                        (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                      (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                        (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                    Bool.true)
                  (instDecidableEqBool
                    (@Decidable.decide
                      (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                        (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                      (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                        (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                    Bool.true)
                  (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                  (@ite.{1} Nat
                    (@Eq.{1} Bool
                      (@Decidable.decide
                        (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                        (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@Decidable.decide
                        (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                        (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                      Bool.true)
                    (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                          (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                          (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))))
                (@Sail.BitVec.extractLsb k_n op
                  (@OfNat.ofNat.{0} Nat (nat_lit 111) (instOfNatNat (nat_lit 111)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.float_compose`. -/
theorem captured_Common_float_compose :
    (@RiscvZkvm.Sail.Functions.float_compose :
      {k_n : Int} → (op : float_bits k_n) → BitVec (Int.toNat k_n)) =
      (
        fun {k_n : Int} (op : float_bits k_n) =>
          @BitVec.setWidth
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@ite.{1} Nat
                  (@Eq.{1} Bool
                    (@Decidable.decide
                      (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                      (Int.instDecidableEq k_n
                        (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                    Bool.true)
                  (instDecidableEqBool
                    (@Decidable.decide
                      (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                      (Int.instDecidableEq k_n
                        (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                    Bool.true)
                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                  (@ite.{1} Nat
                    (@Eq.{1} Bool
                      (@Decidable.decide
                        (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                        (Int.instDecidableEq k_n
                          (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@Decidable.decide
                        (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                        (Int.instDecidableEq k_n
                          (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                      Bool.true)
                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))))))
                (@ite.{1} Nat
                  (@Eq.{1} Bool
                    (@Decidable.decide
                      (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                      (Int.instDecidableEq k_n
                        (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                    Bool.true)
                  (instDecidableEqBool
                    (@Decidable.decide
                      (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                      (Int.instDecidableEq k_n
                        (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                    Bool.true)
                  (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                  (@ite.{1} Nat
                    (@Eq.{1} Bool
                      (@Decidable.decide
                        (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                        (Int.instDecidableEq k_n
                          (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@Decidable.decide
                        (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                        (Int.instDecidableEq k_n
                          (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                      Bool.true)
                    (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))))))
            (Int.toNat k_n)
            (@HAppend.hAppend.{0, 0, 0}
              (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (BitVec
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@ite.{1} Nat
                    (@Eq.{1} Bool
                      (@Decidable.decide
                        (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq k_n
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@Decidable.decide
                        (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq k_n
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@ite.{1} Nat
                        (@Eq.{1} Bool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (instDecidableEqBool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))))))
                  (@ite.{1} Nat
                    (@Eq.{1} Bool
                      (@Decidable.decide
                        (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq k_n
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@Decidable.decide
                        (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq k_n
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                      (@ite.{1} Nat
                        (@Eq.{1} Bool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (instDecidableEqBool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))))))
              (BitVec
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                      (@ite.{1} Nat
                        (@Eq.{1} Bool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                          Bool.true)
                        (instDecidableEqBool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                          Bool.true)
                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (@ite.{1} Nat
                          (@Eq.{1} Bool
                            (@Decidable.decide
                              (@Eq.{1} Int k_n
                                (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                              (Int.instDecidableEq k_n
                                (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                            Bool.true)
                          (instDecidableEqBool
                            (@Decidable.decide
                              (@Eq.{1} Int k_n
                                (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                              (Int.instDecidableEq k_n
                                (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                            Bool.true)
                          (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))))))
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                      (@ite.{1} Nat
                        (@Eq.{1} Bool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                          Bool.true)
                        (instDecidableEqBool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                          Bool.true)
                        (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                        (@ite.{1} Nat
                          (@Eq.{1} Bool
                            (@Decidable.decide
                              (@Eq.{1} Int k_n
                                (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                              (Int.instDecidableEq k_n
                                (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                            Bool.true)
                          (instDecidableEqBool
                            (@Decidable.decide
                              (@Eq.{1} Int k_n
                                (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                              (Int.instDecidableEq k_n
                                (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                            Bool.true)
                          (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))))))))
              (@BitVec.instHAppendHAddNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@ite.{1} Nat
                    (@Eq.{1} Bool
                      (@Decidable.decide
                        (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq k_n
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@Decidable.decide
                        (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq k_n
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@ite.{1} Nat
                        (@Eq.{1} Bool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (instDecidableEqBool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))))))
                  (@ite.{1} Nat
                    (@Eq.{1} Bool
                      (@Decidable.decide
                        (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq k_n
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@Decidable.decide
                        (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq k_n
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                      (@ite.{1} Nat
                        (@Eq.{1} Bool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (instDecidableEqBool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))))))
              (@float_bits.sign k_n op)
              (@HAppend.hAppend.{0, 0, 0}
                (BitVec
                  (@ite.{1} Nat
                    (@Eq.{1} Bool
                      (@Decidable.decide
                        (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq k_n
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@Decidable.decide
                        (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq k_n
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@ite.{1} Nat
                        (@Eq.{1} Bool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (instDecidableEqBool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))))))
                (BitVec
                  (@ite.{1} Nat
                    (@Eq.{1} Bool
                      (@Decidable.decide
                        (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq k_n
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@Decidable.decide
                        (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq k_n
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                      (@ite.{1} Nat
                        (@Eq.{1} Bool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (instDecidableEqBool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))))))
                (BitVec
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                      (@ite.{1} Nat
                        (@Eq.{1} Bool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                          Bool.true)
                        (instDecidableEqBool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                          Bool.true)
                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (@ite.{1} Nat
                          (@Eq.{1} Bool
                            (@Decidable.decide
                              (@Eq.{1} Int k_n
                                (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                              (Int.instDecidableEq k_n
                                (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                            Bool.true)
                          (instDecidableEqBool
                            (@Decidable.decide
                              (@Eq.{1} Int k_n
                                (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                              (Int.instDecidableEq k_n
                                (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                            Bool.true)
                          (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))))))
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                      (@ite.{1} Nat
                        (@Eq.{1} Bool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                          Bool.true)
                        (instDecidableEqBool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                          Bool.true)
                        (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                        (@ite.{1} Nat
                          (@Eq.{1} Bool
                            (@Decidable.decide
                              (@Eq.{1} Int k_n
                                (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                              (Int.instDecidableEq k_n
                                (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                            Bool.true)
                          (instDecidableEqBool
                            (@Decidable.decide
                              (@Eq.{1} Int k_n
                                (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                              (Int.instDecidableEq k_n
                                (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                            Bool.true)
                          (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))))))
                (@BitVec.instHAppendHAddNat
                  (@ite.{1} Nat
                    (@Eq.{1} Bool
                      (@Decidable.decide
                        (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq k_n
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@Decidable.decide
                        (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq k_n
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@ite.{1} Nat
                        (@Eq.{1} Bool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (instDecidableEqBool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))))))
                  (@ite.{1} Nat
                    (@Eq.{1} Bool
                      (@Decidable.decide
                        (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq k_n
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@Decidable.decide
                        (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq k_n
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq k_n
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                      (@ite.{1} Nat
                        (@Eq.{1} Bool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (instDecidableEqBool
                          (@Decidable.decide
                            (@Eq.{1} Int k_n (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq k_n
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))))))
                (@float_bits.exp k_n op) (@float_bits.mantissa k_n op)))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.float_has_max_exp`. -/
theorem captured_Common_float_has_max_exp :
    (@RiscvZkvm.Sail.Functions.float_has_max_exp :
      {k_n : Nat} → (op : BitVec k_n) → Bool) =
      (
        fun {k_n : Nat} (op : BitVec k_n) =>
          have fp : float_bits (@Nat.cast.{0} Int instNatCastInt k_n) :=
            @RiscvZkvm.Sail.Functions.float_decompose k_n op;
          have bitsize : Nat := @Sail.BitVec.length k_n op;
          have one : BitVec bitsize :=
            @Sail.BitVec.zeroExtend (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (BitVec.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              bitsize;
          have two : BitVec bitsize :=
            @HShiftLeft.hShiftLeft.{0, 0, 0} (BitVec bitsize) Nat (BitVec bitsize)
              (@BitVec.instHShiftLeftNat bitsize) one
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)));
          have max_exp : BitVec bitsize :=
            @HSub.hSub.{0, 0, 0} (BitVec bitsize) (BitVec bitsize) (BitVec bitsize)
              (@instHSub.{0} (BitVec bitsize) (@BitVec.instSub bitsize))
              (@HShiftLeft.hShiftLeft.{0, 0, 0} (BitVec bitsize) Nat (BitVec bitsize)
                (@BitVec.instHShiftLeftNat bitsize) one
                (@Sail.BitVec.length
                  (@ite.{1} Nat
                    (@Eq.{1} Bool
                      (@Decidable.decide
                        (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@Decidable.decide
                        (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                        (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                      Bool.true)
                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                    (@ite.{1} Nat
                      (@Eq.{1} Bool
                        (@Decidable.decide
                          (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (instDecidableEqBool
                        (@Decidable.decide
                          (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                          (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                            (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                        Bool.true)
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                      (@ite.{1} Nat
                        (@Eq.{1} Bool
                          (@Decidable.decide
                            (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (instDecidableEqBool
                          (@Decidable.decide
                            (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                            (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                              (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                          Bool.true)
                        (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))))))
                  (@float_bits.exp (@Nat.cast.{0} Int instNatCastInt k_n) fp)))
              two;
          @BEq.beq.{0} (BitVec bitsize)
            (@instBEqOfDecidableEq.{0} (BitVec bitsize) (@instDecidableEqBitVec bitsize)) max_exp
            (@Sail.BitVec.zeroExtend
              (@ite.{1} Nat
                (@Eq.{1} Bool
                  (@Decidable.decide
                    (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                      (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                    (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                      (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                  Bool.true)
                (instDecidableEqBool
                  (@Decidable.decide
                    (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                      (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
                    (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                      (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16)))))
                  Bool.true)
                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                (@ite.{1} Nat
                  (@Eq.{1} Bool
                    (@Decidable.decide
                      (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                        (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                      (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                        (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                    Bool.true)
                  (instDecidableEqBool
                    (@Decidable.decide
                      (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                        (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32))))
                      (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                        (@OfNat.ofNat.{0} Int (nat_lit 32) (@instOfNat (nat_lit 32)))))
                    Bool.true)
                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@ite.{1} Nat
                    (@Eq.{1} Bool
                      (@Decidable.decide
                        (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                        (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                      Bool.true)
                    (instDecidableEqBool
                      (@Decidable.decide
                        (@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64))))
                        (Int.instDecidableEq (@Nat.cast.{0} Int instNatCastInt k_n)
                          (@OfNat.ofNat.{0} Int (nat_lit 64) (@instOfNat (nat_lit 64)))))
                      Bool.true)
                    (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))))))
              (@float_bits.exp (@Nat.cast.{0} Int instNatCastInt k_n) fp) bitsize)
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.is_lowest_one`. -/
theorem captured_Common_is_lowest_one :
    (@RiscvZkvm.Sail.Functions.is_lowest_one :
      {k_n : Nat} → (op : BitVec k_n) → Bool) =
      (
        fun {k_n : Nat} (op : BitVec k_n) =>
          @BEq.beq.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@instBEqOfDecidableEq.{0}
              (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@instDecidableEqBitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Sail.BitVec.access k_n op (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (BitVec.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.is_highest_one`. -/
theorem captured_Common_is_highest_one :
    (@RiscvZkvm.Sail.Functions.is_highest_one :
      {k_n : Nat} → (op : BitVec k_n) → Bool) =
      (
        fun {k_n : Nat} (op : BitVec k_n) =>
          @BEq.beq.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@instBEqOfDecidableEq.{0}
              (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@instDecidableEqBitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Sail.BitVec.access k_n op
              (Int.toNat
                ((fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                  (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n op))
                  (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
            (BitVec.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.is_all_ones`. -/
theorem captured_Common_is_all_ones :
    (@RiscvZkvm.Sail.Functions.is_all_ones :
      {k_n : Nat} → (op : BitVec k_n) → Bool) =
      (
        fun {k_n : Nat} (op : BitVec k_n) =>
          @BEq.beq.{0} (BitVec k_n) (@instBEqOfDecidableEq.{0} (BitVec k_n) (@instDecidableEqBitVec k_n)) op
            (RiscvZkvm.Sail.Functions.sail_ones (@Sail.BitVec.length k_n op))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.is_lowest_zero`. -/
theorem captured_Common_is_lowest_zero :
    (@RiscvZkvm.Sail.Functions.is_lowest_zero :
      {k_n : Nat} → (op : BitVec k_n) → Bool) =
      (
        fun {k_n : Nat} (op : BitVec k_n) =>
          @BEq.beq.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@instBEqOfDecidableEq.{0}
              (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@instDecidableEqBitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Sail.BitVec.access k_n op (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (BitVec.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.is_highest_zero`. -/
theorem captured_Common_is_highest_zero :
    (@RiscvZkvm.Sail.Functions.is_highest_zero :
      {k_n : Nat} → (op : BitVec k_n) → Bool) =
      (
        fun {k_n : Nat} (op : BitVec k_n) =>
          @BEq.beq.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@instBEqOfDecidableEq.{0}
              (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@instDecidableEqBitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Sail.BitVec.access k_n op
              (Int.toNat
                ((fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                  (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n op))
                  (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
            (BitVec.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.is_all_zeros`. -/
theorem captured_Common_is_all_zeros :
    (@RiscvZkvm.Sail.Functions.is_all_zeros :
      {k_n : Nat} → (op : BitVec k_n) → Bool) =
      (
        fun {k_n : Nat} (op : BitVec k_n) =>
          @BEq.beq.{0} (BitVec k_n) (@instBEqOfDecidableEq.{0} (BitVec k_n) (@instDecidableEqBitVec k_n)) op
            (BitVec.zero (@Sail.BitVec.length k_n op))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.hex_bits_forwards`. -/
theorem captured_HexBits_hex_bits_forwards :
    (@RiscvZkvm.Sail.Functions.hex_bits_forwards :
      {k_n : Nat} → (bv : BitVec k_n) → Prod.{0, 0} Nat String) =
      (
        fun {k_n : Nat} (bv : BitVec k_n) =>
          @Prod.mk.{0, 0} Nat String (@Sail.BitVec.length k_n bv)
            (Sail.Int.toHex (@Sail.BitVec.toNatInt k_n bv))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.hex_bits_forwards_matches`. -/
theorem captured_HexBits_hex_bits_forwards_matches :
    (@RiscvZkvm.Sail.Functions.hex_bits_forwards_matches :
      {k_n : Nat} → (x_0 : BitVec k_n) → Bool) =
      (
        fun {k_n : Nat} (x_0 : BitVec k_n) => Bool.true
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.nan_box`. -/
theorem captured_FdextRegs_nan_box :
    (@RiscvZkvm.Sail.Functions.nan_box :
      {k_n n : Nat} → (x : BitVec k_n) → BitVec n) =
      (
        fun {k_n n : Nat} (x : BitVec k_n) =>
          @BitVec.setWidth
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (Int.toNat
                ((fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                  (@Nat.cast.{0} Int instNatCastInt n)
                  (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))))
              k_n)
            n
            (@HAppend.hAppend.{0, 0, 0}
              (BitVec
                (Int.toNat
                  ((fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                    (@Nat.cast.{0} Int instNatCastInt n)
                    (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x)))))
              (BitVec k_n)
              (BitVec
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (Int.toNat
                    ((fun (x y : Int) =>
                        @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                      (@Nat.cast.{0} Int instNatCastInt n)
                      (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))))
                  k_n))
              (@BitVec.instHAppendHAddNat
                (Int.toNat
                  ((fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                    (@Nat.cast.{0} Int instNatCastInt n)
                    (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))))
                k_n)
              (@RiscvZkvm.Sail.Functions.ones
                (Int.toNat
                  ((fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                    (@Nat.cast.{0} Int instNatCastInt n)
                    (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x)))))
              x)
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.nan_unbox`. -/
theorem captured_FdextRegs_nan_unbox :
    (@RiscvZkvm.Sail.Functions.nan_unbox :
      {k_n m : Nat} → (x : BitVec k_n) → BitVec m) =
      (
        fun {k_n m : Nat} (x : BitVec k_n) =>
          @ite.{1} (BitVec m)
            (@Eq.{1} Bool
              (@BEq.beq.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat)
                (@Sail.BitVec.length k_n x) m)
              Bool.true)
            (instDecidableEqBool
              (@BEq.beq.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat)
                (@Sail.BitVec.length k_n x) m)
              Bool.true)
            (@BitVec.setWidth k_n m x)
            (@ite.{1} (BitVec m)
              (@Eq.{1} Bool
                (@BEq.beq.{0}
                  (BitVec
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                        (Int.toNat
                          ((fun (x y : Int) =>
                              @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                            (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))
                            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                        m)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@instBEqOfDecidableEq.{0}
                    (BitVec
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                          (Int.toNat
                            ((fun (x y : Int) =>
                                @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                              (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))
                              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                          m)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@instDecidableEqBitVec
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                          (Int.toNat
                            ((fun (x y : Int) =>
                                @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                              (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))
                              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                          m)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@Sail.BitVec.extractLsb k_n x
                    (Int.toNat
                      ((fun (x y : Int) =>
                          @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                        (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))
                        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                    m)
                  (@BitVec.setWidth
                    (Int.toNat
                      ((fun (x y : Int) =>
                          @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x y)
                        ((fun (x y : Int) =>
                            @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                          ((fun (x y : Int) =>
                              @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                            (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))
                            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@Nat.cast.{0} Int instNatCastInt m))
                        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                        (Int.toNat
                          ((fun (x y : Int) =>
                              @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                            (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))
                            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                        m)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@RiscvZkvm.Sail.Functions.ones
                      (Int.toNat
                        ((fun (x y : Int) =>
                            @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x y)
                          ((fun (x y : Int) =>
                              @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                            ((fun (x y : Int) =>
                                @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                              (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))
                              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@Nat.cast.{0} Int instNatCastInt m))
                          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))))
                Bool.true)
              (instDecidableEqBool
                (@BEq.beq.{0}
                  (BitVec
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                        (Int.toNat
                          ((fun (x y : Int) =>
                              @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                            (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))
                            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                        m)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@instBEqOfDecidableEq.{0}
                    (BitVec
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                          (Int.toNat
                            ((fun (x y : Int) =>
                                @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                              (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))
                              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                          m)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@instDecidableEqBitVec
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                          (Int.toNat
                            ((fun (x y : Int) =>
                                @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                              (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))
                              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                          m)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@Sail.BitVec.extractLsb k_n x
                    (Int.toNat
                      ((fun (x y : Int) =>
                          @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                        (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))
                        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                    m)
                  (@BitVec.setWidth
                    (Int.toNat
                      ((fun (x y : Int) =>
                          @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x y)
                        ((fun (x y : Int) =>
                            @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                          ((fun (x y : Int) =>
                              @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                            (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))
                            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@Nat.cast.{0} Int instNatCastInt m))
                        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                        (Int.toNat
                          ((fun (x y : Int) =>
                              @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                            (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))
                            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                        m)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@RiscvZkvm.Sail.Functions.ones
                      (Int.toNat
                        ((fun (x y : Int) =>
                            @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x y)
                          ((fun (x y : Int) =>
                              @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                            ((fun (x y : Int) =>
                                @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                              (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))
                              (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@Nat.cast.{0} Int instNatCastInt m))
                          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))))
                Bool.true)
              (@BitVec.setWidth
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                    (Int.toNat
                      ((fun (x y : Int) =>
                          @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                        (@Nat.cast.{0} Int instNatCastInt m)
                        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                m
                (@Sail.BitVec.extractLsb k_n x
                  (Int.toNat
                    ((fun (x y : Int) =>
                        @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                      (@Nat.cast.{0} Int instNatCastInt m)
                      (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@RiscvZkvm.Sail.Functions.canonical_NaN m))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.mem_read_request_is_exclusive`. -/
theorem captured_ReadWriteV1_mem_read_request_is_exclusive :
    (@RiscvZkvm.Sail.Functions.mem_read_request_is_exclusive :
      {k_n k_vasize : Nat} →
        {k_pa k_translation_summary k_arch_ak : Type} →
          (request :
              Sail.ConcurrencyInterfaceV1.Mem_read_request k_n k_vasize k_pa k_translation_summary
                k_arch_ak) →
            Bool) =
      (
        fun {k_n k_vasize : Nat} {k_pa k_translation_summary k_arch_ak : Type}
            (request :
              Sail.ConcurrencyInterfaceV1.Mem_read_request k_n k_vasize k_pa k_translation_summary
                k_arch_ak) =>
          @RiscvZkvm.Sail.Functions.mem_read_request_is_exclusive.match_4.{1} k_arch_ak
            (fun (x : Sail.ConcurrencyInterfaceV1.Access_kind k_arch_ak) => Bool)
            (@Sail.ConcurrencyInterfaceV1.Mem_read_request.access_kind k_n k_vasize k_pa
              k_translation_summary k_arch_ak request)
            (fun (eak : Sail.ConcurrencyInterfaceV1.Explicit_access_kind) =>
              RiscvZkvm.Sail.Functions.mem_read_request_is_exclusive.match_1.{1}
                (fun (x : Sail.ConcurrencyInterfaceV1.Access_variety) => Bool)
                (Sail.ConcurrencyInterfaceV1.Explicit_access_kind.variety eak) (fun (_ : Unit) => Bool.true)
                fun (x : Sail.ConcurrencyInterfaceV1.Access_variety) => Bool.false)
            fun (x : Sail.ConcurrencyInterfaceV1.Access_kind k_arch_ak) => Bool.false
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.mem_read_request_is_ifetch`. -/
theorem captured_ReadWriteV1_mem_read_request_is_ifetch :
    (@RiscvZkvm.Sail.Functions.mem_read_request_is_ifetch :
      {k_n k_vasize : Nat} →
        {k_pa k_translation_summary k_arch_ak : Type} →
          (request :
              Sail.ConcurrencyInterfaceV1.Mem_read_request k_n k_vasize k_pa k_translation_summary
                k_arch_ak) →
            Bool) =
      (
        fun {k_n k_vasize : Nat} {k_pa k_translation_summary k_arch_ak : Type}
            (request :
              Sail.ConcurrencyInterfaceV1.Mem_read_request k_n k_vasize k_pa k_translation_summary
                k_arch_ak) =>
          @RiscvZkvm.Sail.Functions.mem_read_request_is_ifetch.match_1.{1} k_arch_ak
            (fun (x : Sail.ConcurrencyInterfaceV1.Access_kind k_arch_ak) => Bool)
            (@Sail.ConcurrencyInterfaceV1.Mem_read_request.access_kind k_n k_vasize k_pa
              k_translation_summary k_arch_ak request)
            (fun (_ : Unit) => Bool.true) fun (x : Sail.ConcurrencyInterfaceV1.Access_kind k_arch_ak) =>
            Bool.false
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.mem_write_request_is_exclusive`. -/
theorem captured_ReadWriteV1_mem_write_request_is_exclusive :
    (@RiscvZkvm.Sail.Functions.mem_write_request_is_exclusive :
      {k_n k_vasize : Nat} →
        {k_pa k_translation_summary k_arch_ak : Type} →
          (request :
              Sail.ConcurrencyInterfaceV1.Mem_write_request k_n k_vasize k_pa k_translation_summary
                k_arch_ak) →
            Bool) =
      (
        fun {k_n k_vasize : Nat} {k_pa k_translation_summary k_arch_ak : Type}
            (request :
              Sail.ConcurrencyInterfaceV1.Mem_write_request k_n k_vasize k_pa k_translation_summary
                k_arch_ak) =>
          @RiscvZkvm.Sail.Functions.mem_read_request_is_exclusive.match_4.{1} k_arch_ak
            (fun (x : Sail.ConcurrencyInterfaceV1.Access_kind k_arch_ak) => Bool)
            (@Sail.ConcurrencyInterfaceV1.Mem_write_request.access_kind k_n k_vasize k_pa
              k_translation_summary k_arch_ak request)
            (fun (eak : Sail.ConcurrencyInterfaceV1.Explicit_access_kind) =>
              RiscvZkvm.Sail.Functions.mem_read_request_is_exclusive.match_1.{1}
                (fun (x : Sail.ConcurrencyInterfaceV1.Access_variety) => Bool)
                (Sail.ConcurrencyInterfaceV1.Explicit_access_kind.variety eak) (fun (_ : Unit) => Bool.true)
                fun (x : Sail.ConcurrencyInterfaceV1.Access_variety) => Bool.false)
            fun (x : Sail.ConcurrencyInterfaceV1.Access_kind k_arch_ak) => Bool.false
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.not_implemented`. -/
theorem captured_Errors_not_implemented :
    (@RiscvZkvm.Sail.Functions.not_implemented :
      {k_a : Type} → (message : String) → SailM k_a) =
      (
        fun {k_a : Type} (message : String) => @Sail.sailThrow k_a (exception.Error_not_implemented message)
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.internal_error`. -/
theorem captured_Errors_internal_error :
    (@RiscvZkvm.Sail.Functions.internal_error :
      {k_a : Type} → (file : String) → (line : Int) → (s : String) → SailM k_a) =
      (
        fun {k_a : Type} (file : String) (line : Int) (s : String) =>
          @Sail.sailThrow k_a
            (exception.Error_internal_error
              (@HAppend.hAppend.{0, 0, 0} String String String
                (@instHAppendOfAppend.{0} String instAppendString) file
                (@HAppend.hAppend.{0, 0, 0} String String String
                  (@instHAppendOfAppend.{0} String instAppendString) ":"
                  (@HAppend.hAppend.{0, 0, 0} String String String
                    (@instHAppendOfAppend.{0} String instAppendString) (Int.repr line)
                    (@HAppend.hAppend.{0, 0, 0} String String String
                      (@instHAppendOfAppend.{0} String instAppendString) ": " s)))))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.reserved_behavior`. -/
theorem captured_Errors_reserved_behavior :
    (@RiscvZkvm.Sail.Functions.reserved_behavior :
      {k_a : Type} → (message : String) → SailM k_a) =
      (
        fun {k_a : Type} (message : String) =>
          @Sail.sailThrow k_a (exception.Error_reserved_behavior message)
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.split_access`. -/
theorem captured_SplitAccessUtils_split_access :
    (@RiscvZkvm.Sail.Functions.split_access :
      {k_n : Nat} → (addr : BitVec k_n) → (width : Nat) → SailM (Prod.{0, 0} Int Int)) =
      (
        fun {k_n : Nat} (addr : BitVec k_n) (width : Nat) =>
          have addr_align : Nat := @Sail.BitVec.countTrailingZeros k_n addr;
          have width_align : Nat :=
            @Sail.BitVec.countTrailingZeros
              (Int.toNat
                ((fun (x y : Int) => @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x y)
                  (@OfNat.ofNat.{0} Int (nat_lit 12) (@instOfNat (nat_lit 12)))
                  (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
              (@RiscvZkvm.Sail.Functions.to_bits
                (Int.toNat
                  ((fun (x y : Int) => @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x y)
                    (@OfNat.ofNat.{0} Int (nat_lit 12) (@instOfNat (nat_lit 12)))
                    (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                width);
          have bytes_per_access : Int :=
            (fun (x y : Int) => @HPow.hPow.{0, 0, 0} Int Int Int instHPowInt_sail x y)
              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))
              (@Min.min.{0} Int Int.instMin (@Nat.cast.{0} Int instNatCastInt addr_align)
                (@Nat.cast.{0} Int instNatCastInt width_align));
          have num_accesses : Int := Int.tdiv (@Nat.cast.{0} Int instNatCastInt width) bytes_per_access;
          @Bind.bind.{0, 0} SailM
            (@Monad.toBind.{0, 0} SailM
              (@EStateM.instMonad.{0} (Sail.Error exception)
                (@Sail.ConcurrencyInterfaceV1.SequentialState Register instDecidableEqRegister
                  instHashableRegister RegisterType Sail.ConcurrencyInterfaceV1.trivialChoiceSource)))
            Unit (Prod.{0, 0} Int Int)
            (Sail.assert
              (@BEq.beq.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat) width
                (Int.toNat
                  ((fun (x y : Int) => @HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) x y)
                    num_accesses bytes_per_access)))
              "sys/split_access_utils.sail:53.49-53.50")
            fun (__r : Unit) =>
            @Pure.pure.{0, 0} SailM
              (@Applicative.toPure.{0, 0} SailM
                (@Monad.toApplicative.{0, 0} SailM
                  (@EStateM.instMonad.{0} (Sail.Error exception)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState Register instDecidableEqRegister
                      instHashableRegister RegisterType Sail.ConcurrencyInterfaceV1.trivialChoiceSource))))
              (Prod.{0, 0} Int Int) (@Prod.mk.{0, 0} Int Int num_accesses bytes_per_access)
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.split_on_page_boundary`. -/
theorem captured_SplitAccessUtils_split_on_page_boundary :
    (@RiscvZkvm.Sail.Functions.split_on_page_boundary :
      {k_n : Nat} → (addr : BitVec k_n) → (width : Nat) → SailM (Prod.{0, 0} Int Int)) =
      (
        fun {k_n : Nat} (addr : BitVec k_n) (width : Nat) =>
          have page_mask : BitVec (@Sail.BitVec.length k_n addr) :=
            @Sail.BitVec.updateSubrange (@Sail.BitVec.length k_n addr)
              (@RiscvZkvm.Sail.Functions.ones (@Sail.BitVec.length k_n addr))
              (Int.toNat
                ((fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                  (@Nat.cast.{0} Int instNatCastInt RiscvZkvm.Sail.Functions.pagesize_bits)
                  (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@RiscvZkvm.Sail.Functions.zeros
                (Int.toNat
                  ((fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                    ((fun (x y : Int) =>
                        @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                      (@OfNat.ofNat.{0} Int (nat_lit 12) (@instOfNat (nat_lit 12)))
                      (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    ((fun (x y : Int) =>
                        @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                      (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))));
          have intra_page_access : Bool :=
            @BEq.beq.{0} (BitVec k_n) (@instBEqOfDecidableEq.{0} (BitVec k_n) (@instDecidableEqBitVec k_n))
              (@HAnd.hAnd.{0, 0, 0} (BitVec k_n) (BitVec (@Sail.BitVec.length k_n addr)) (BitVec k_n)
                (@instHAndOfAndOp.{0} (BitVec k_n) (@BitVec.instAndOp k_n)) addr page_mask)
              (@HAnd.hAnd.{0, 0, 0} (BitVec k_n) (BitVec (@Sail.BitVec.length k_n addr)) (BitVec k_n)
                (@instHAndOfAndOp.{0} (BitVec k_n) (@BitVec.instAndOp k_n))
                (@Sail.BitVec.subInt k_n
                  (@Sail.BitVec.addInt k_n addr (@Nat.cast.{0} Int instNatCastInt width))
                  (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                page_mask);
          @ite.{1} (SailM (Prod.{0, 0} Int Int)) (@Eq.{1} Bool intra_page_access Bool.true)
            (instDecidableEqBool intra_page_access Bool.true)
            (@Pure.pure.{0, 0} SailM
              (@Applicative.toPure.{0, 0} SailM
                (@Monad.toApplicative.{0, 0} SailM
                  (@EStateM.instMonad.{0} (Sail.Error exception)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState Register instDecidableEqRegister
                      instHashableRegister RegisterType Sail.ConcurrencyInterfaceV1.trivialChoiceSource))))
              (Prod.{0, 0} Int Int)
              (@Prod.mk.{0, 0} Int Int (@Nat.cast.{0} Int instNatCastInt width)
                (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
            (have nbytes_to_boundary : Int :=
              (fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                ((fun (x y : Int) => @HPow.hPow.{0, 0, 0} Int Int Int instHPowInt_sail x y)
                  (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))
                  (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))))
                (@Sail.BitVec.toNatInt
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                      (Int.toNat
                        ((fun (x y : Int) =>
                            @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                          (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3)))
                          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Sail.BitVec.extractLsb k_n addr
                    (Int.toNat
                      ((fun (x y : Int) =>
                          @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                        (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3)))
                        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))));
            @Bind.bind.{0, 0} SailM
              (@Monad.toBind.{0, 0} SailM
                (@EStateM.instMonad.{0} (Sail.Error exception)
                  (@Sail.ConcurrencyInterfaceV1.SequentialState Register instDecidableEqRegister
                    instHashableRegister RegisterType Sail.ConcurrencyInterfaceV1.trivialChoiceSource)))
              Unit (Prod.{0, 0} Int Int)
              (Sail.assert
                (@Decidable.decide
                  (@LT.lt.{0} Int Int.instLTInt nbytes_to_boundary (@Nat.cast.{0} Int instNatCastInt width))
                  (Int.decLt nbytes_to_boundary (@Nat.cast.{0} Int instNatCastInt width)))
                "sys/split_access_utils.sail:111.37-111.38")
              fun (__r : Unit) =>
              @Pure.pure.{0, 0} SailM
                (@Applicative.toPure.{0, 0} SailM
                  (@Monad.toApplicative.{0, 0} SailM
                    (@EStateM.instMonad.{0} (Sail.Error exception)
                      (@Sail.ConcurrencyInterfaceV1.SequentialState Register instDecidableEqRegister
                        instHashableRegister RegisterType
                        Sail.ConcurrencyInterfaceV1.trivialChoiceSource))))
                (Prod.{0, 0} Int Int)
                (@Prod.mk.{0, 0} Int Int nbytes_to_boundary
                  ((fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                    (@Nat.cast.{0} Int instNatCastInt width) nbytes_to_boundary)))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.tlb_set_pte`. -/
theorem captured_VmemTlb_tlb_set_pte :
    (@RiscvZkvm.Sail.Functions.tlb_set_pte :
      {k_n : Nat} →
        (ent : TLB_Entry) →
          (pte :
              BitVec
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) k_n
                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))) →
            TLB_Entry) =
      (
        fun {k_n : Nat} (ent : TLB_Entry)
            (pte :
              BitVec
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) k_n
                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))) =>
          TLB_Entry.mk (TLB_Entry.asid ent) (TLB_Entry.global ent) (TLB_Entry.vpn ent)
            (TLB_Entry.levelMask ent) (TLB_Entry.ppn ent)
            (@zero_extend
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) k_n
                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
              (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) pte)
            (TLB_Entry.pteAddr ent)
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.sign_extend`. -/
theorem captured_Prelude_sign_extend :
    (@RiscvZkvm.Sail.Functions.sign_extend :
      {k_n m : Nat} → (v : BitVec k_n) → BitVec m) =
      (
        fun {k_n m : Nat} (v : BitVec k_n) => @Sail.BitVec.signExtend k_n v m
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.trunc`. -/
theorem captured_Prelude_trunc :
    (@RiscvZkvm.Sail.Functions.trunc :
      {k_n m : Nat} → (v : BitVec k_n) → BitVec m) =
      (
        fun {k_n m : Nat} (v : BitVec k_n) => @Sail.BitVec.truncate k_n v m
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.zopz0zI_s`. -/
theorem captured_Prelude_zopz0zI_s :
    (@RiscvZkvm.Sail.Functions.zopz0zI_s :
      {k_n : Nat} → (x y : BitVec k_n) → Bool) =
      (
        fun {k_n : Nat} (x y : BitVec k_n) =>
          @Decidable.decide (@LT.lt.{0} Int Int.instLTInt (@BitVec.toInt k_n x) (@BitVec.toInt k_n y))
            (Int.decLt (@BitVec.toInt k_n x) (@BitVec.toInt k_n y))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.zopz0zK_s`. -/
theorem captured_Prelude_zopz0zK_s :
    (@RiscvZkvm.Sail.Functions.zopz0zK_s :
      {k_n : Nat} → (x y : BitVec k_n) → Bool) =
      (
        fun {k_n : Nat} (x y : BitVec k_n) =>
          @Decidable.decide (@GT.gt.{0} Int Int.instLTInt (@BitVec.toInt k_n x) (@BitVec.toInt k_n y))
            (Int.decLt (@BitVec.toInt k_n y) (@BitVec.toInt k_n x))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.zopz0zIzJ_s`. -/
theorem captured_Prelude_zopz0zIzJ_s :
    (@RiscvZkvm.Sail.Functions.zopz0zIzJ_s :
      {k_n : Nat} → (x y : BitVec k_n) → Bool) =
      (
        fun {k_n : Nat} (x y : BitVec k_n) =>
          @Decidable.decide (@LE.le.{0} Int Int.instLEInt (@BitVec.toInt k_n x) (@BitVec.toInt k_n y))
            (Int.decLe (@BitVec.toInt k_n x) (@BitVec.toInt k_n y))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.zopz0zKzJ_s`. -/
theorem captured_Prelude_zopz0zKzJ_s :
    (@RiscvZkvm.Sail.Functions.zopz0zKzJ_s :
      {k_n : Nat} → (x y : BitVec k_n) → Bool) =
      (
        fun {k_n : Nat} (x y : BitVec k_n) =>
          @Decidable.decide (@GE.ge.{0} Int Int.instLEInt (@BitVec.toInt k_n x) (@BitVec.toInt k_n y))
            (Int.decLe (@BitVec.toInt k_n y) (@BitVec.toInt k_n x))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.zopz0zI_u`. -/
theorem captured_Prelude_zopz0zI_u :
    (@RiscvZkvm.Sail.Functions.zopz0zI_u :
      {k_n : Nat} → (x y : BitVec k_n) → Bool) =
      (
        fun {k_n : Nat} (x y : BitVec k_n) =>
          @Decidable.decide
            (@LT.lt.{0} Int Int.instLTInt (@Sail.BitVec.toNatInt k_n x) (@Sail.BitVec.toNatInt k_n y))
            (Int.decLt (@Sail.BitVec.toNatInt k_n x) (@Sail.BitVec.toNatInt k_n y))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.zopz0zK_u`. -/
theorem captured_Prelude_zopz0zK_u :
    (@RiscvZkvm.Sail.Functions.zopz0zK_u :
      {k_n : Nat} → (x y : BitVec k_n) → Bool) =
      (
        fun {k_n : Nat} (x y : BitVec k_n) =>
          @Decidable.decide
            (@GT.gt.{0} Int Int.instLTInt (@Sail.BitVec.toNatInt k_n x) (@Sail.BitVec.toNatInt k_n y))
            (Int.decLt (@Sail.BitVec.toNatInt k_n y) (@Sail.BitVec.toNatInt k_n x))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.zopz0zIzJ_u`. -/
theorem captured_Prelude_zopz0zIzJ_u :
    (@RiscvZkvm.Sail.Functions.zopz0zIzJ_u :
      {k_n : Nat} → (x y : BitVec k_n) → Bool) =
      (
        fun {k_n : Nat} (x y : BitVec k_n) =>
          @Decidable.decide
            (@LE.le.{0} Int Int.instLEInt (@Sail.BitVec.toNatInt k_n x) (@Sail.BitVec.toNatInt k_n y))
            (Int.decLe (@Sail.BitVec.toNatInt k_n x) (@Sail.BitVec.toNatInt k_n y))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.zopz0zKzJ_u`. -/
theorem captured_Prelude_zopz0zKzJ_u :
    (@RiscvZkvm.Sail.Functions.zopz0zKzJ_u :
      {k_n : Nat} → (x y : BitVec k_n) → Bool) =
      (
        fun {k_n : Nat} (x y : BitVec k_n) =>
          @Decidable.decide
            (@GE.ge.{0} Int Int.instLEInt (@Sail.BitVec.toNatInt k_n x) (@Sail.BitVec.toNatInt k_n y))
            (Int.decLe (@Sail.BitVec.toNatInt k_n y) (@Sail.BitVec.toNatInt k_n x))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.shift_bits_right_arith`. -/
theorem captured_Prelude_shift_bits_right_arith :
    (@RiscvZkvm.Sail.Functions.shift_bits_right_arith :
      {k_n k_m : Nat} → (value : BitVec k_n) → (shift : BitVec k_m) → BitVec k_n) =
      (
        fun {k_n k_m : Nat} (value : BitVec k_n) (shift : BitVec k_m) =>
          @BitVec.sshiftRight k_n value (Int.toNat (@Sail.BitVec.toNatInt k_m shift))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.rotater`. -/
theorem captured_Prelude_rotater :
    (@RiscvZkvm.Sail.Functions.rotater :
      {k_m : Nat} → (value : BitVec k_m) → (shift : Nat) → BitVec k_m) =
      (
        fun {k_m : Nat} (value : BitVec k_m) (shift : Nat) =>
          @HOr.hOr.{0, 0, 0} (BitVec k_m) (BitVec k_m) (BitVec k_m)
            (@instHOrOfOrOp.{0} (BitVec k_m) (@BitVec.instOrOp k_m))
            (@HShiftRight.hShiftRight.{0, 0, 0} (BitVec k_m) Nat (BitVec k_m)
              (@BitVec.instHShiftRightNat k_m) value shift)
            (@HShiftLeft.hShiftLeft.{0, 0, 0} (BitVec k_m) Int (BitVec k_m)
              (@Sail.instHShiftLeftBitVecInt_sail k_m) value
              ((fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_m value))
                (@Nat.cast.{0} Int instNatCastInt shift)))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.rotatel`. -/
theorem captured_Prelude_rotatel :
    (@RiscvZkvm.Sail.Functions.rotatel :
      {k_m : Nat} → (value : BitVec k_m) → (shift : Nat) → BitVec k_m) =
      (
        fun {k_m : Nat} (value : BitVec k_m) (shift : Nat) =>
          @HOr.hOr.{0, 0, 0} (BitVec k_m) (BitVec k_m) (BitVec k_m)
            (@instHOrOfOrOp.{0} (BitVec k_m) (@BitVec.instOrOp k_m))
            (@HShiftLeft.hShiftLeft.{0, 0, 0} (BitVec k_m) Nat (BitVec k_m) (@BitVec.instHShiftLeftNat k_m)
              value shift)
            (@HShiftRight.hShiftRight.{0, 0, 0} (BitVec k_m) Int (BitVec k_m)
              (@Sail.instHShiftRightBitVecInt_sail k_m) value
              ((fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_m value))
                (@Nat.cast.{0} Int instNatCastInt shift)))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.rotate_bits_right`. -/
theorem captured_Prelude_rotate_bits_right :
    (@RiscvZkvm.Sail.Functions.rotate_bits_right :
      {k_m k_n : Nat} → (value : BitVec k_m) → (shift : BitVec k_n) → BitVec k_m) =
      (
        fun {k_m k_n : Nat} (value : BitVec k_m) (shift : BitVec k_n) =>
          @RiscvZkvm.Sail.Functions.rotater k_m value (Int.toNat (@Sail.BitVec.toNatInt k_n shift))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.rotate_bits_left`. -/
theorem captured_Prelude_rotate_bits_left :
    (@RiscvZkvm.Sail.Functions.rotate_bits_left :
      {k_m k_n : Nat} → (value : BitVec k_m) → (shift : BitVec k_n) → BitVec k_m) =
      (
        fun {k_m k_n : Nat} (value : BitVec k_m) (shift : BitVec k_n) =>
          @RiscvZkvm.Sail.Functions.rotatel k_m value (Int.toNat (@Sail.BitVec.toNatInt k_n shift))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.reverse_bits`. -/
theorem captured_Prelude_reverse_bits :
    (@RiscvZkvm.Sail.Functions.reverse_bits :
      {k_n : Nat} → (xs : BitVec k_n) → BitVec k_n) =
      (
        fun {k_n : Nat} (xs : BitVec k_n) =>
          @Id.run.{0} (BitVec k_n)
            (have ys : BitVec k_n := @RiscvZkvm.Sail.Functions.zeros (@Sail.BitVec.length k_n xs);
            have loop_i_lower : Int := @OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0));
            have loop_i_upper : Int :=
              (fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n ys))
                (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)));
            have loop_vars : BitVec k_n := ys;
            @Bind.bind.{0, 0} Id.{0} (@Monad.toBind.{0, 0} Id.{0} Id.instMonad.{0}) (BitVec k_n)
              (BitVec k_n)
              (@ForIn.forIn.{0, 0, 0, 0} Id.{0} IntRange Int
                (@instForInOfForIn'.{0, 0, 0, 0} Id.{0} IntRange Int
                  (@inferInstance.{1} (Membership.{0, 0} Int IntRange) IntRange.instMemIntRange)
                  (@IntRange.instForIn'IntInferInstanceMembershipOfMonad.{0, 0} Id.{0} Id.instMonad.{0}))
                (BitVec k_n)
                (IntRange.mk loop_i_lower loop_i_upper
                  (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                  fun
                    (a :
                      @Eq.{1} Int (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) =>
                  RiscvZkvm.Sail.Functions.reverse_bits._proof_1 a)
                loop_vars fun (i : Int) (__s : BitVec k_n) =>
                have loop_vars : BitVec k_n := __s;
                have ys : BitVec k_n := loop_vars;
                have loop_vars : BitVec k_n :=
                  @Sail.BitVec.update k_n ys (Int.toNat i)
                    (@Sail.BitVec.access k_n xs
                      (Int.toNat
                        ((fun (x y : Int) =>
                            @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                          ((fun (x y : Int) =>
                              @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                            (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n ys))
                            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          i)));
                @Pure.pure.{0, 0} Id.{0}
                  (@Applicative.toPure.{0, 0} Id.{0} (@Monad.toApplicative.{0, 0} Id.{0} Id.instMonad.{0}))
                  (ForInStep.{0} (BitVec k_n)) (@ForInStep.yield.{0} (BitVec k_n) loop_vars))
              fun (__s : BitVec k_n) =>
              have loop_vars : BitVec k_n := __s;
              @Pure.pure.{0, 0} Id.{0}
                (@Applicative.toPure.{0, 0} Id.{0} (@Monad.toApplicative.{0, 0} Id.{0} Id.instMonad.{0}))
                (BitVec k_n) loop_vars)
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.hex_bits_str`. -/
theorem captured_Prelude_hex_bits_str :
    (@RiscvZkvm.Sail.Functions.hex_bits_str :
      {k_n : Nat} → (x : BitVec k_n) → String) =
      (
        fun {k_n : Nat} (x : BitVec k_n) =>
          @Sail.BitVec.toFormatted
            (Int.toNat
              ((fun (x y : Int) => @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x y)
                ((fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                  (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3)))
                  (Int.tmod
                    ((fun (x y : Int) =>
                        @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x y)
                      (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))
                      (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))))
                    (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))))
                (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))))
            (@zero_extend k_n
              (Int.toNat
                ((fun (x y : Int) => @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x y)
                  ((fun (x y : Int) => @HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub) x y)
                    (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3)))
                    (Int.tmod
                      ((fun (x y : Int) =>
                          @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x y)
                        (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))
                        (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))))
                      (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))))
                  (@Nat.cast.{0} Int instNatCastInt (@Sail.BitVec.length k_n x))))
              x)
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.range_subset`. -/
theorem captured_RangeUtil_range_subset :
    (@RiscvZkvm.Sail.Functions.range_subset :
      {k_n : Nat} → (a_begin a_size b_begin b_size : BitVec k_n) → Bool) =
      (
        fun {k_n : Nat} (a_begin a_size b_begin b_size : BitVec k_n) =>
          have a_end : BitVec k_n :=
            @HSub.hSub.{0, 0, 0} (BitVec k_n) (BitVec k_n) (BitVec k_n)
              (@instHSub.{0} (BitVec k_n) (@BitVec.instSub k_n))
              (@HAdd.hAdd.{0, 0, 0} (BitVec k_n) (BitVec k_n) (BitVec k_n)
                (@instHAdd.{0} (BitVec k_n) (@BitVec.instAdd k_n)) a_begin a_size)
              b_begin;
          have b_end : BitVec k_n :=
            @HSub.hSub.{0, 0, 0} (BitVec k_n) (BitVec k_n) (BitVec k_n)
              (@instHSub.{0} (BitVec k_n) (@BitVec.instSub k_n))
              (@HAdd.hAdd.{0, 0, 0} (BitVec k_n) (BitVec k_n) (BitVec k_n)
                (@instHAdd.{0} (BitVec k_n) (@BitVec.instAdd k_n)) b_begin b_size)
              b_begin;
          have a_begin : BitVec k_n :=
            @HSub.hSub.{0, 0, 0} (BitVec k_n) (BitVec k_n) (BitVec k_n)
              (@instHSub.{0} (BitVec k_n) (@BitVec.instSub k_n)) a_begin b_begin;
          Bool.and (@RiscvZkvm.Sail.Functions.zopz0zIzJ_u k_n a_begin b_end)
            (Bool.and (@RiscvZkvm.Sail.Functions.zopz0zIzJ_u k_n a_end b_end)
              (@RiscvZkvm.Sail.Functions.zopz0zIzJ_u k_n a_begin a_end))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.ext_bits_of_PTE`. -/
theorem captured_VmemPte_ext_bits_of_PTE :
    (@RiscvZkvm.Sail.Functions.ext_bits_of_PTE :
      {k_pte_size : Nat} →
        (pte : BitVec k_pte_size) → BitVec (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))) =
      (
        fun {k_pte_size : Nat} (pte : BitVec k_pte_size) =>
          RiscvZkvm.Sail.Functions.Mk_PTE_Ext
            (@ite.{1} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
              (@Eq.{1} Bool
                (@BEq.beq.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat)
                  (@Sail.BitVec.length k_pte_size pte)
                  (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
                Bool.true)
              (instDecidableEqBool
                (@BEq.beq.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat)
                  (@Sail.BitVec.length k_pte_size pte)
                  (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
                Bool.true)
              (@Sail.BitVec.extractLsb k_pte_size pte
                (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
                (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))))
              RiscvZkvm.Sail.Functions.default_sv32_ext_pte)
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.PPN_of_PTE`. -/
theorem captured_VmemPte_PPN_of_PTE :
    (@RiscvZkvm.Sail.Functions.PPN_of_PTE :
      {k_pte_size : Nat} →
        (pte : BitVec k_pte_size) →
          BitVec
            (@ite.{1} Nat
              (@Eq.{1} Bool
                (@Decidable.decide
                  (@Eq.{1} Nat k_pte_size (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                  (instDecidableEqNat k_pte_size
                    (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                Bool.true)
              (instDecidableEqBool
                (@Decidable.decide
                  (@Eq.{1} Nat k_pte_size (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                  (instDecidableEqNat k_pte_size
                    (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                Bool.true)
              (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
              (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))))) =
      (
        fun {k_pte_size : Nat} (pte : BitVec k_pte_size) =>
          @ite.{1}
            (BitVec
              (@ite.{1} Nat
                (@Eq.{1} Bool
                  (@Decidable.decide
                    (@Eq.{1} Nat k_pte_size (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                    (instDecidableEqNat k_pte_size
                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                  Bool.true)
                (instDecidableEqBool
                  (@Decidable.decide
                    (@Eq.{1} Nat k_pte_size (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                    (instDecidableEqNat k_pte_size
                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                  Bool.true)
                (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
                (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44)))))
            (@Eq.{1} Bool
              (@BEq.beq.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat)
                (@Sail.BitVec.length k_pte_size pte)
                (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
              Bool.true)
            (instDecidableEqBool
              (@BEq.beq.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat)
                (@Sail.BitVec.length k_pte_size pte)
                (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
              Bool.true)
            (@BitVec.setWidth
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@ite.{1} Nat
                (@Eq.{1} Bool
                  (@Decidable.decide
                    (@Eq.{1} Nat k_pte_size (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                    (instDecidableEqNat k_pte_size
                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                  Bool.true)
                (instDecidableEqBool
                  (@Decidable.decide
                    (@Eq.{1} Nat k_pte_size (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                    (instDecidableEqNat k_pte_size
                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                  Bool.true)
                (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
                (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))))
              (@Sail.BitVec.extractLsb k_pte_size pte
                (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))
            (@BitVec.setWidth
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 53) (instOfNatNat (nat_lit 53)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@ite.{1} Nat
                (@Eq.{1} Bool
                  (@Decidable.decide
                    (@Eq.{1} Nat k_pte_size (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                    (instDecidableEqNat k_pte_size
                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                  Bool.true)
                (instDecidableEqBool
                  (@Decidable.decide
                    (@Eq.{1} Nat k_pte_size (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                    (instDecidableEqNat k_pte_size
                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                  Bool.true)
                (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))
                (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))))
              (@Sail.BitVec.extractLsb k_pte_size pte
                (@OfNat.ofNat.{0} Nat (nat_lit 53) (instOfNatNat (nat_lit 53)))
                (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.update_PTE_Bits`. -/
theorem captured_VmemPte_update_PTE_Bits :
    (@RiscvZkvm.Sail.Functions.update_PTE_Bits :
      {k_pte_size : Nat} →
        (pte : BitVec k_pte_size) →
          (access : MemoryAccessType mem_payload) → Option.{0} (BitVec k_pte_size)) =
      (
        fun {k_pte_size : Nat} (pte : BitVec k_pte_size) (access : MemoryAccessType mem_payload) =>
          have pte_flags : BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) :=
            RiscvZkvm.Sail.Functions.Mk_PTE_Flags
              (@Sail.BitVec.extractLsb k_pte_size pte
                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))));
          have update_d : Bool :=
            Bool.and
              (@BEq.beq.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@instBEqOfDecidableEq.{0}
                  (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@instDecidableEqBitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (RiscvZkvm.Sail.Functions._get_PTE_Flags_D pte_flags)
                (BitVec.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (RiscvZkvm.Sail.Functions.update_PTE_Bits.match_1.{1}
                (fun (access : MemoryAccessType mem_payload) => Bool) access (fun (_ : Unit) => Bool.false)
                (fun (x : mem_payload) => Bool.false)
                (fun (x : Prod.{0, 0} Bool (Prod.{0, 0} Bool mem_payload)) => Bool.false)
                (fun (x : mem_payload) => Bool.true)
                (fun (x : Prod.{0, 0} Bool (Prod.{0, 0} Bool mem_payload)) => Bool.true)
                (fun
                    (x :
                      Prod.{0, 0} amoop
                        (Prod.{0, 0} Bool (Prod.{0, 0} Bool (Prod.{0, 0} mem_payload mem_payload)))) =>
                  Bool.true)
                (fun (x : cbop_zicbom) => Bool.false) (fun (_ : Unit) => Bool.true) fun (x : cbop_zicbop) =>
                Bool.false);
          have update_a : Bool :=
            Bool.and
              (@BEq.beq.{0} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@instBEqOfDecidableEq.{0}
                  (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@instDecidableEqBitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (RiscvZkvm.Sail.Functions._get_PTE_Flags_A pte_flags)
                (BitVec.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (RiscvZkvm.Sail.Functions.not
                (@RiscvZkvm.Sail.Functions.is_prefetch_access mem_payload access));
          @ite.{1} (Option.{0} (BitVec k_pte_size)) (@Eq.{1} Bool (Bool.or update_d update_a) Bool.true)
            (instDecidableEqBool (Bool.or update_d update_a) Bool.true)
            (have pte_flags : BitVec (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) :=
              RiscvZkvm.Sail.Functions._update_PTE_Flags_D
                (RiscvZkvm.Sail.Functions._update_PTE_Flags_A pte_flags
                  (BitVec.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@ite.{1} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Eq.{1} Bool update_d Bool.true) (instDecidableEqBool update_d Bool.true)
                  (BitVec.ofNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (RiscvZkvm.Sail.Functions._get_PTE_Flags_D pte_flags));
            @Option.some.{0} (BitVec k_pte_size)
              (@Sail.BitVec.updateSubrange k_pte_size pte
                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) pte_flags))
            (@Option.none.{0} (BitVec k_pte_size))
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.is_load_store`. -/
theorem captured_Types_is_load_store :
    (@RiscvZkvm.Sail.Functions.is_load_store :
      {k_a : Type} → (access : MemoryAccessType k_a) → Bool) =
      (
        fun {k_a : Type} (access : MemoryAccessType k_a) =>
          @RiscvZkvm.Sail.Functions.is_load_store.match_1.{1} k_a
            (fun (access : MemoryAccessType k_a) => Bool) access (fun (x : k_a) => Bool.true)
            (fun (x : k_a) => Bool.true) (fun (x : Prod.{0, 0} Bool (Prod.{0, 0} Bool k_a)) => Bool.true)
            (fun (x : Prod.{0, 0} Bool (Prod.{0, 0} Bool k_a)) => Bool.true)
            (fun (x : Prod.{0, 0} amoop (Prod.{0, 0} Bool (Prod.{0, 0} Bool (Prod.{0, 0} k_a k_a)))) =>
              Bool.true)
            (fun (x : Unit) => Bool.false) fun (x : cacheop) => Bool.true
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.is_prefetch_access`. -/
theorem captured_Types_is_prefetch_access :
    (@RiscvZkvm.Sail.Functions.is_prefetch_access :
      {k_a : Type} → (access : MemoryAccessType k_a) → Bool) =
      (
        fun {k_a : Type} (access : MemoryAccessType k_a) =>
          @RiscvZkvm.Sail.Functions.is_prefetch_access.match_1.{1} k_a
            (fun (access : MemoryAccessType k_a) => Bool) access (fun (x : cbop_zicbop) => Bool.true)
            fun (x : MemoryAccessType k_a) => Bool.false
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.is_store_conditional`. -/
theorem captured_Types_is_store_conditional :
    (@RiscvZkvm.Sail.Functions.is_store_conditional :
      {k_a : Type} → (access : MemoryAccessType k_a) → Bool) =
      (
        fun {k_a : Type} (access : MemoryAccessType k_a) =>
          @RiscvZkvm.Sail.Functions.is_store_conditional.match_1.{1} k_a
            (fun (access : MemoryAccessType k_a) => Bool) access
            (fun (x : Prod.{0, 0} Bool (Prod.{0, 0} Bool k_a)) => Bool.true)
            fun (x : MemoryAccessType k_a) => Bool.false
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.fetch_callback`. -/
theorem captured_Callbacks_fetch_callback :
    (@RiscvZkvm.Sail.Functions.fetch_callback :
      {k_n : Nat} → (x_0 : BitVec k_n) → Unit) =
      (
        fun {k_n : Nat} (x_0 : BitVec k_n) => Unit.unit
      ) := rfl

/-- The original type and body of `RiscvZkvm.Sail.Functions.extend_value`. -/
theorem captured_BaseInsts_extend_value :
    (@RiscvZkvm.Sail.Functions.extend_value :
      {k_n : Nat} →
        (is_unsigned : Bool) →
          (value : BitVec k_n) → BitVec (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) =
      (
        fun {k_n : Nat} (is_unsigned : Bool) (value : BitVec k_n) =>
          @ite.{1} (BitVec (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
            (@Eq.{1} Bool is_unsigned Bool.true) (instDecidableEqBool is_unsigned Bool.true)
            (@zero_extend k_n (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) value)
            (@RiscvZkvm.Sail.Functions.sign_extend k_n
              (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) value)
      ) := rfl

/-- The original type and body of `zero_extend`. -/
theorem captured_Defs_zero_extend :
    (@zero_extend :
      {k_n m : Nat} → (v : BitVec k_n) → BitVec m) =
      (
        fun {k_n m : Nat} (v : BitVec k_n) => @Sail.BitVec.zeroExtend k_n v m
      ) := rfl

/-- The original type and body of `Sail.sailTryCatch`. -/
theorem captured_Specialization_sailTryCatch :
    (@Sail.sailTryCatch :
      {α : Type} → (e : SailM α) → (h : exception → SailM α) → SailM α) =
      (
        fun {α : Type} (e : SailM α) (h : exception → SailM α) =>
          @Sail.ConcurrencyInterfaceV1.PreSail.sailTryCatch Register RegisterType instDecidableEqRegister
            instHashableRegister Sail.ConcurrencyInterfaceV1.trivialChoiceSource exception α e h
      ) := rfl

/-- The original type and body of `Sail.sailThrow`. -/
theorem captured_Specialization_sailThrow :
    (@Sail.sailThrow :
      {α : Type} → (e : exception) → SailM α) =
      (
        fun {α : Type} (e : exception) =>
          @Sail.ConcurrencyInterfaceV1.PreSail.sailThrow Register RegisterType instDecidableEqRegister
            instHashableRegister exception Sail.ConcurrencyInterfaceV1.trivialChoiceSource α e
      ) := rfl

/-- The original type and body of `Sail.undefined_vector`. -/
theorem captured_Specialization_undefined_vector :
    (@Sail.undefined_vector :
      {α : Type} → (n : Nat) → (a : α) → SailM (Vector.{0} α n)) =
      (
        fun {α : Type} (n : Nat) (a : α) =>
          @Sail.ConcurrencyInterfaceV1.PreSail.undefined_vector Register RegisterType
            instDecidableEqRegister instHashableRegister α Sail.ConcurrencyInterfaceV1.trivialChoiceSource
            exception n a
      ) := rfl

/-- The original type and body of `Sail.readRegRef`. -/
theorem captured_Specialization_readRegRef :
    (@Sail.readRegRef :
      {α : Type} → (reg_ref : Sail.RegisterRef α) → SailM α) =
      (
        fun {α : Type} (reg_ref : Sail.RegisterRef α) =>
          @Sail.ConcurrencyInterfaceV1.PreSail.readRegRef Register RegisterType instDecidableEqRegister
            instHashableRegister α Sail.ConcurrencyInterfaceV1.trivialChoiceSource exception reg_ref
      ) := rfl

/-- The original type and body of `Sail.writeRegRef`. -/
theorem captured_Specialization_writeRegRef :
    (@Sail.writeRegRef :
      {α : Type} → (reg_ref : Sail.RegisterRef α) → (a : α) → SailM Unit) =
      (
        fun {α : Type} (reg_ref : Sail.RegisterRef α) (a : α) =>
          @Sail.ConcurrencyInterfaceV1.PreSail.writeRegRef Register RegisterType instDecidableEqRegister
            instHashableRegister α Sail.ConcurrencyInterfaceV1.trivialChoiceSource exception reg_ref a
      ) := rfl

/-- The original type and body of `Sail.reg_deref`. -/
theorem captured_Specialization_reg_deref :
    (@Sail.reg_deref :
      {α : Type} → (reg_ref : Sail.RegisterRef α) → SailM α) =
      (
        fun {α : Type} (reg_ref : Sail.RegisterRef α) =>
          @Sail.ConcurrencyInterfaceV1.PreSail.reg_deref Register RegisterType instDecidableEqRegister
            instHashableRegister α Sail.ConcurrencyInterfaceV1.trivialChoiceSource exception reg_ref
      ) := rfl

/-- The original type and body of `Sail.ConcurrencyInterfaceV1.sail_mem_write`. -/
theorem captured_Specialization_sail_mem_write :
    (@Sail.ConcurrencyInterfaceV1.sail_mem_write :
      {n vasize pa_size : Nat} →
        {ts arch : Type} →
          [inst : Sail.ConcurrencyInterfaceV1.Arch] →
            (req : Sail.ConcurrencyInterfaceV1.Mem_write_request n vasize (BitVec pa_size) ts arch) →
              SailM (Sail.Result (Option.{0} Bool) (@Sail.ConcurrencyInterfaceV1.Arch.abort inst))) =
      (
        fun {n vasize pa_size : Nat} {ts arch : Type} [inst : Sail.ConcurrencyInterfaceV1.Arch]
            (req : Sail.ConcurrencyInterfaceV1.Mem_write_request n vasize (BitVec pa_size) ts arch) =>
          @Sail.ConcurrencyInterfaceV1.PreSail.sail_mem_write Register RegisterType instDecidableEqRegister
            instHashableRegister n vasize pa_size ts arch Sail.ConcurrencyInterfaceV1.trivialChoiceSource
            exception inst req
      ) := rfl

/-- The original type and body of `Sail.ConcurrencyInterfaceV1.sail_mem_read`. -/
theorem captured_Specialization_sail_mem_read :
    (@Sail.ConcurrencyInterfaceV1.sail_mem_read :
      {n vasize pa_size : Nat} →
        {ts arch : Type} →
          [inst : Sail.ConcurrencyInterfaceV1.Arch] →
            (req : Sail.ConcurrencyInterfaceV1.Mem_read_request n vasize (BitVec pa_size) ts arch) →
              SailM
                (Sail.Result
                  (Prod.{0, 0}
                    (BitVec
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) n))
                    (Option.{0} Bool))
                  (@Sail.ConcurrencyInterfaceV1.Arch.abort inst))) =
      (
        fun {n vasize pa_size : Nat} {ts arch : Type} [inst : Sail.ConcurrencyInterfaceV1.Arch]
            (req : Sail.ConcurrencyInterfaceV1.Mem_read_request n vasize (BitVec pa_size) ts arch) =>
          @Sail.ConcurrencyInterfaceV1.PreSail.sail_mem_read Register RegisterType instDecidableEqRegister
            instHashableRegister n vasize pa_size ts arch Sail.ConcurrencyInterfaceV1.trivialChoiceSource
            exception inst req
      ) := rfl

/-- The original type and body of `Sail.ConcurrencyInterfaceV1.sail_barrier`. -/
theorem captured_Specialization_sail_barrier :
    (@Sail.ConcurrencyInterfaceV1.sail_barrier.{u_1} :
      {α : Sort u_1} → (a : α) → SailM Unit) =
      (
        fun {α : Sort u_1} (a : α) =>
          @Sail.ConcurrencyInterfaceV1.PreSail.sail_barrier.{u_1} Register RegisterType
            instDecidableEqRegister instHashableRegister α Sail.ConcurrencyInterfaceV1.trivialChoiceSource
            exception a
      ) := rfl

/-- The original type and body of `Sail.SailME.run`. -/
theorem captured_Specialization_SailME_run :
    (@Sail.SailME.run :
      {α : Type} → (m : SailME α α) → SailM α) =
      (
        fun {α : Type} (m : SailME α α) =>
          @Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run Register RegisterType instDecidableEqRegister
            instHashableRegister Sail.ConcurrencyInterfaceV1.trivialChoiceSource exception α m
      ) := rfl

/-- The original type and body of `Sail.SailME.throw`. -/
theorem captured_Specialization_SailME_throw :
    (@Sail.SailME.throw :
      {α β : Type} → (e : α) → SailME α β) =
      (
        fun {α β : Type} (e : α) =>
          @Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw Register RegisterType instDecidableEqRegister
            instHashableRegister α Sail.ConcurrencyInterfaceV1.trivialChoiceSource exception β e
      ) := rfl

/-- The original type and body of `Sail.sailTryCatchE`. -/
theorem captured_Specialization_sailTryCatchE :
    (@Sail.sailTryCatchE :
      {β α : Type} → (e : SailME β α) → (h : exception → SailME β α) → SailME β α) =
      (
        fun {β α : Type} (e : SailME β α) (h : exception → SailME β α) =>
          @Sail.ConcurrencyInterfaceV1.PreSail.sailTryCatchE Register RegisterType instDecidableEqRegister
            instHashableRegister (Sum.{0, 0} (Sail.Error exception) β)
            Sail.ConcurrencyInterfaceV1.trivialChoiceSource exception α e h
      ) := rfl

/-- The original type and body of `Sail.unwrapValue`. -/
theorem captured_Specialization_unwrapValue :
    (@Sail.unwrapValue :
      {α : Type} → [Inhabited.{1} α] → (x : SailM α) → α) =
      (
        fun {α : Type} [inst : Inhabited.{1} α] (x : SailM α) =>
          @Sail.unwrapValue.match_1.{1} α
            (fun
                (x :
                  EStateM.Result.{0} (Sail.Error exception)
                    (@Sail.ConcurrencyInterfaceV1.SequentialState Register instDecidableEqRegister
                      instHashableRegister RegisterType Sail.ConcurrencyInterfaceV1.trivialChoiceSource)
                    α) =>
              α)
            (@EStateM.run.{0} (Sail.Error exception)
              (@Sail.ConcurrencyInterfaceV1.SequentialState Register instDecidableEqRegister
                instHashableRegister RegisterType Sail.ConcurrencyInterfaceV1.trivialChoiceSource)
              α x
              (@Inhabited.default.{1}
                (@Sail.ConcurrencyInterfaceV1.SequentialState Register instDecidableEqRegister
                  instHashableRegister RegisterType Sail.ConcurrencyInterfaceV1.trivialChoiceSource)
                (@Sail.ConcurrencyInterfaceV1.PreSail.instInhabitedSequentialStateTrivialChoiceSource
                  Register RegisterType instDecidableEqRegister instHashableRegister)))
            (fun (x : α)
                (a :
                  @Sail.ConcurrencyInterfaceV1.SequentialState Register instDecidableEqRegister
                    instHashableRegister RegisterType Sail.ConcurrencyInterfaceV1.trivialChoiceSource) =>
              x)
            fun
              (x :
                EStateM.Result.{0} (Sail.Error exception)
                  (@Sail.ConcurrencyInterfaceV1.SequentialState Register instDecidableEqRegister
                    instHashableRegister RegisterType Sail.ConcurrencyInterfaceV1.trivialChoiceSource)
                  α) =>
            @Inhabited.default.{1} α inst
      ) := rfl

end MetrologyAsm.StrictSourceEquivalence
