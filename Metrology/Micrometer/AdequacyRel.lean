module

public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.Micrometer.AppWeakestpre
public import Metrology.Micrometer.Model
public import Metrology.Micrometer.Adequacy
public import Iris.Algebra.Auth
public import Iris.Instances.Lib.WSat
public import Iris.Instances.Lib.LaterCredits
public import Iris.Instances.Lib.FUpd

@[expose] public section

/-! # Relational adequacy: bridging parametric `refines` to a codensity lifting on `limExecV`. -/

namespace ProbLang

open Iris Iris.BI Iris.ProofMode OFE COFE Iris.Std DisjointLeibnizSet Auth HeapView
open ProbLang.MicrometerWpGS

variable {rT : Type} [LawfulProbLangℝ rT]
variable {ι : Type} [Monoid ι]

class RefinesPreGS (rT : outParam Type) [LawfulProbLangℝ rT]
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

section Coupling
variable {Δ : GradedDivergence.{0} ι} [Δ.IsMassBounded] [Δ.IsZeroLeft] [Δ.IsLeftContinuous]

theorem approximates_coupling {GF : BundledGFunctors} [RefinesPreGS rT GF]
    (A : ∀ (_ : MicrometerRGS rT .hasNoLC GF), lrel rT GF)
    (φ : Val rT → Val rT → Prop) (e e' : Exp rT) (σ σ' : State rT) (ε : ENNReal)
    (HA : ∀ (IR : MicrometerRGS rT .hasNoLC GF) (v v' : Val rT),
      ⊢@{IProp GF} (A IR).car v v' -∗ ⌜φ v v'⌝)
    (Hlog : ∀ (IR : MicrometerRGS rT .hasNoLC GF), ⊢@{IProp GF} ↯ ε -∗ refines Δ ⊤ e e' (A IR)) :
    Δ.Codensity 1 ε (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) := by
  refine wp_adequacy_error_lim (GF := GF) e e' σ σ' ε φ fun IGS ε' hε' => ?_
  iintro He' Herr
  imod Iris.NonAtomicInvariant.alloc with ⟨%γ, Htok⟩
  set IR : MicrometerRGS rT .hasNoLC GF := { micrometerGS := IGS, naInvG := _, nais := γ }
  icases ErrorCredit.difference hε'.le $$ Herr with ⟨Hεc, Hrest⟩
  ihave HlogR := Hlog IR $$ Hεc
  iunfold refines at HlogR
  rw [spec_eq_fill_nil e']
  ispecialize HlogR $$ %([] : Ectx rT) %(ε' - ε) He' Htok Hrest %(tsub_pos_of_lt hε')
  iapply MicrometerWpGS.wp_mono $$ HlogR
  intro v
  iintro ⟨%v', %_, Hspec, -, -, -, HAv⟩
  iexists v'
  rw [← spec_fill_nil_eq_ofVal v']
  iframe Hspec
  iapply HA IR v v' $$ HAv

theorem refines_coupling {GF : BundledGFunctors} [RefinesPreGS rT GF]
    (A : ∀ (_ : MicrometerRGS rT .hasNoLC GF), lrel rT GF)
    (φ : Val rT → Val rT → Prop) (e e' : Exp rT) (σ σ' : State rT)
    (HA : ∀ (IR : MicrometerRGS rT .hasNoLC GF) (v v' : Val rT),
      ⊢@{IProp GF} (A IR).car v v' -∗ ⌜φ v v'⌝)
    (Hlog : ∀ (IR : MicrometerRGS rT .hasNoLC GF), ⊢@{IProp GF} refines Δ ⊤ e e' (A IR)) :
    Δ.Codensity 1 0 (adequacyRel φ) (limExecV ⟨e, σ⟩) (limExecV ⟨e', σ'⟩) :=
  approximates_coupling A φ e e' σ σ' 0 HA fun IR => by
    iintro -
    iapply Hlog IR

end Coupling

section MicrometerFunctor
variable (rT : Type) [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]

noncomputable def MicrometerFunctor : BundledGFunctors := fun
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

/-! ### `RefinesPreGS` instances for `MicrometerFunctor` -/

instance MicrometerFunctor_WsatGpreS : WsatGpreS (MicrometerFunctor rT) where
  inv := ⟨0, rfl⟩
  enabled := ⟨1, rfl⟩
  disabled := ⟨2, rfl⟩

instance MicrometerFunctor_LcGpreS : LcGpreS (MicrometerFunctor rT) where lc_elem := ⟨3, rfl⟩

instance MicrometerFunctor_InvGpreS : InvGpreS (MicrometerFunctor rT) where
  toWsatGpreS := MicrometerFunctor_WsatGpreS rT
  toLcGpreS := MicrometerFunctor_LcGpreS rT

instance MicrometerFunctor_AppPreGS : AppPreGS rT (MicrometerFunctor rT) where
  heap := ⟨4, rfl⟩
  tapes := ⟨5, rfl⟩

instance MicrometerFunctor_SpecPreGS : SpecPreGS rT (MicrometerFunctor rT) where
  prog := ⟨6, rfl⟩
  heap := ⟨4, rfl⟩
  tapes := ⟨5, rfl⟩

instance MicrometerFunctor_ECPreGS : ECPreGS (MicrometerFunctor rT) where ec := ⟨7, rfl⟩

instance MicrometerFunctor_NaInvG : NaInvG (MicrometerFunctor rT) where inv := ⟨8, rfl⟩

instance MicrometerFunctor_RefinesPreGS : RefinesPreGS rT (MicrometerFunctor rT) where

end MicrometerFunctor

end ProbLang
