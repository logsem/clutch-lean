module

public import Metrology.Approxis.PrimitiveLaws
public import Metrology.Approxis.AppWeakestpre
public import Metrology.Approxis.Model
public import Metrology.Approxis.Adequacy
public import Iris.Algebra.Auth
public import Iris.Instances.Lib.WSat
public import Iris.Instances.Lib.LaterCredits
public import Iris.Instances.Lib.FUpd

@[expose] public section

/-! # Relational adequacy: bridging parametric `refines` to an `AddCoupl` on `limExec`. -/

namespace ProbLang

open Iris Iris.BI Iris.ProofMode OFE COFE Iris.Std DisjointLeibnizSet Auth HeapView
open ProbLang.ApproxisWpGS

variable {rT : Type _} [LawfulProbLangℝ rT]

class RefinesPreGS (rT : outParam (Type _)) [LawfulProbLangℝ rT]
    [MeasurableSingletonClass rT] (GF : BundledGFunctors) where
  [app : AppPreGS rT GF]
  [spec : SpecPreGS rT GF]
  [ec : ECPreGS GF]
  [inv : InvGpreS GF]
  [nainv : NaInvG GF]

attribute [reducible, instance] RefinesPreGS.app RefinesPreGS.spec RefinesPreGS.ec
  RefinesPreGS.inv RefinesPreGS.nainv

theorem spec_eq_fill_nil {GF : BundledGFunctors} [SpecGS rT GF] (e : Exp rT) :
    (iprop(⤇ e) : IProp GF) = iprop(⤇ Ectx.fill ([] : Ectx rT) e) :=
  rfl

theorem spec_fill_nil_eq_ofVal {GF : BundledGFunctors} [SpecGS rT GF] (v : Val rT) :
    (iprop(⤇ Ectx.fill ([] : Ectx rT) v.1) : IProp GF) = iprop(⤇ Exp.ofVal v) :=
  rfl

theorem approximates_coupling {GF : BundledGFunctors} [RefinesPreGS rT GF]
    (A : ∀ (_ : ApproxisRGS rT .hasNoLC GF), lrel rT GF)
    (φ : Val rT → Val rT → Prop) (e e' : Exp rT) (σ σ' : State rT) (ε : ENNReal)
    (HA : ∀ (IR : ApproxisRGS rT .hasNoLC GF) (v v' : Val rT),
      ⊢@{IProp GF} (A IR).car v v' -∗ ⌜φ v v'⌝)
    (Hlog : ∀ (IR : ApproxisRGS rT .hasNoLC GF), ⊢@{IProp GF} ↯ ε -∗ refines ⊤ e e' (A IR)) :
    AddCoupl ε (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) := by
  refine wp_adequacy_error_lim (GF := GF) e e' σ σ' ε φ fun IGS ε' hε' => ?_
  iintro He' Herr
  imod Iris.NonAtomicInvariant.alloc with ⟨%γ, Htok⟩
  set IR : ApproxisRGS rT .hasNoLC GF := { approxisGS := IGS, naInvG := _, nais := γ }
  icases ErrorCredit.difference hε'.le $$ Herr with ⟨Hεc, Hrest⟩
  ihave HlogR := Hlog IR $$ Hεc
  iunfold refines at HlogR
  rw [spec_eq_fill_nil e']
  ispecialize HlogR $$ %([] : Ectx rT) %(ε' - ε) He' Htok Hrest %(tsub_pos_of_lt hε')
  iapply ApproxisWpGS.wp_mono $$ HlogR
  intro v
  iintro ⟨%v', %_, Hspec, -, -, -, HAv⟩
  iexists v'
  rw [← spec_fill_nil_eq_ofVal v']
  iframe Hspec
  iapply HA IR v v' $$ HAv

theorem refines_coupling {GF : BundledGFunctors} [RefinesPreGS rT GF]
    (A : ∀ (_ : ApproxisRGS rT .hasNoLC GF), lrel rT GF)
    (φ : Val rT → Val rT → Prop) (e e' : Exp rT) (σ σ' : State rT)
    (HA : ∀ (IR : ApproxisRGS rT .hasNoLC GF) (v v' : Val rT),
      ⊢@{IProp GF} (A IR).car v v' -∗ ⌜φ v v'⌝)
    (Hlog : ∀ (IR : ApproxisRGS rT .hasNoLC GF), ⊢@{IProp GF} refines ⊤ e e' (A IR)) :
    AddCoupl 0 (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  approximates_coupling A φ e e' σ σ' 0 HA fun IR => by
    iintro -
    iapply Hlog IR

section ApproxisFunctor
variable (rT : Type) [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

noncomputable def ApproxisFunctor : BundledGFunctors := fun
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF (DisjointLeibnizSet CoPset), by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (SpecHeap rT), by infer_instance⟩
  | 5 => ⟨constOF SpecTapes, by infer_instance⟩
  | 6 => ⟨constOF (SpecProg rT), by infer_instance⟩
  | 7 => ⟨constOF (Auth ErrorCredit), by infer_instance⟩
  | 8 => ⟨NaInvF, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

/-! ### `RefinesPreGS` instances for `ApproxisFunctor` -/

instance ApproxisFunctor_WsatGpreS : WsatGpreS (ApproxisFunctor rT) where
  inv := ⟨0, rfl⟩
  enabled := ⟨1, rfl⟩
  disabled := ⟨2, rfl⟩

instance ApproxisFunctor_LcGpreS : LcGpreS (ApproxisFunctor rT) where lc_elem := ⟨3, rfl⟩

instance ApproxisFunctor_InvGpreS : InvGpreS (ApproxisFunctor rT) where
  toWsatGpreS := ApproxisFunctor_WsatGpreS rT
  toLcGpreS := ApproxisFunctor_LcGpreS rT

instance ApproxisFunctor_AppPreGS : AppPreGS rT (ApproxisFunctor rT) where
  heap := ⟨4, rfl⟩
  tapes := ⟨5, rfl⟩

instance ApproxisFunctor_SpecPreGS : SpecPreGS rT (ApproxisFunctor rT) where
  prog := ⟨6, rfl⟩
  heap := ⟨4, rfl⟩
  tapes := ⟨5, rfl⟩

instance ApproxisFunctor_ECPreGS : ECPreGS (ApproxisFunctor rT) where ec := ⟨7, rfl⟩

instance ApproxisFunctor_NaInvG : NaInvG (ApproxisFunctor rT) where inv := ⟨8, rfl⟩

instance ApproxisFunctor_RefinesPreGS : RefinesPreGS rT (ApproxisFunctor rT) where

end ApproxisFunctor

end ProbLang
