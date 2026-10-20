module

public import Metrology.Micrometer.AppWeakestpre
public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.ProbLang.Syntax.LocallyClosed
public import Iris.Instances.Lib.NaInvariants
public import Iris.Instances.Lib.Invariants
public import Metrology.Iris.Countable
import Metrology.ProbLang.Syntax.Notation

/-! # Value relations and the refinement judgement

Value relations `lrel` (a COFE, so `lrel_rec` is a fixpoint), one constructor per type former,
and the refinement judgement `refines` (`REL[L] e << e' @ E : A`). -/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting

namespace ProbLang

variable {rT : Type}

/-! ## Value relations -/

/-- A value relation: a persistent Iris relation on values that only relates closed values. -/
structure lrel (rT : Type) (GF : BundledGFunctors) where
  car : Val rT → Val rT → IProp GF
  [persistent : ∀ v1 v2, Persistent (car v1 v2)]
  closed v1 v2 : car v1 v2 ⊢ ⌜v1.1.isClosedEmpty ∧ v2.1.isClosedEmpty⌝

attribute [instance] lrel.persistent

/-- Apply a value relation to two values directly. -/
instance coeFun_lrel {GF} : CoeFun (lrel rT GF) (fun _ => Val rT → Val rT → IProp GF) := ⟨lrel.car⟩

/-- Value relations are equal when their underlying relations are. -/
theorem lrel.ext {GF : BundledGFunctors} {A B : lrel rT GF}
    (h : ∀ v1 v2, A.car v1 v2 = B.car v1 v2) : A = B := by
  obtain ⟨carA, _⟩ := A
  obtain ⟨carB, _⟩ := B
  obtain rfl : carA = carB := funext fun v1 => funext (h v1)
  rfl

/-! ### OFE and COFE structure, used for recursive relations -/

/-- Value relations are an OFE under pointwise distance. -/
instance ofe_lrel {GF : BundledGFunctors} : OFE (lrel rT GF) where
  Dist n A B := ∀ v1 v2, A.car v1 v2 ≡{n}≡ B.car v1 v2
  dist_eqv := {
    refl _ _ _ := dist_eqv.refl _
    symm h v1 v2 := dist_eqv.symm (h v1 v2)
    trans h1 h2 v1 v2 := dist_eqv.trans (h1 v1 v2) (h2 v1 v2)
  }
  eq_dist' :=
    ⟨fun h _ _ _ => h ▸ .rfl, fun h => lrel.ext fun _ _ => OFE.eq_dist.mpr fun _ => h _ _ _⟩
  dist_lt hd hmn v1 v2 := OFE.dist_lt (hd v1 v2) hmn

/-- The chain of underlying relations of a chain of `lrel`s, used to take limits pointwise. -/
noncomputable def lrel.toFunChain {GF : BundledGFunctors}
    (c : Chain (lrel rT GF)) : Chain (Val rT → Val rT → IProp GF) where
  chain k := (c.chain k).car
  cauchy h := (c.cauchy h : _)

/-- Evaluation of a binary relation at a pair of values. -/
abbrev lrel.appAt {GF : BundledGFunctors} (v1 v2 : Val rT) :
    (Val rT → Val rT → IProp GF) → IProp GF := (· v1 v2)

/-- Evaluation at a pair of values is nonexpansive. -/
instance lrel.appAt_ne {GF : BundledGFunctors} (v1 v2 : Val rT) :
    OFE.NonExpansive (lrel.appAt (GF := GF) v1 v2) := ⟨fun _ _ _ h => h v1 v2⟩

/-- Value relations are complete: limits are taken pointwise. -/
noncomputable instance isCOFE_lrel {GF : BundledGFunctors} : IsCOFE (lrel rT GF) where
  compl c :=
    { car := IsCOFE.compl (lrel.toFunChain c)
      persistent v1 v2 :=
        (limitPreserving_persistent (lrel.appAt v1 v2)).compl
          (lrel.toFunChain c) fun k => (c.chain k).persistent v1 v2
      closed v1 v2 :=
        (Iris.BI.LimitPreserving.entails (lrel.appAt v1 v2)
            (Function.const _ iprop(⌜v1.1.isClosedEmpty ∧ v2.1.isClosedEmpty⌝))).compl
          (lrel.toFunChain c) fun k => (c.chain k).closed v1 v2 }
  conv_compl {_ c} v1 v2 := IsCOFE.conv_compl (c := lrel.toFunChain c) v1 v2

/-- The empty relation. -/
instance inhabited_lrel {GF : BundledGFunctors} : Inhabited (lrel rT GF) where
  default :=
    { car := fun _ _ => iprop(False)
      closed := fun _ _ => Iris.BI.false_elim }

/-- A relation's proposition at a fixed pair of values is nonexpansive in the relation. -/
instance lrel.car_ne {GF : BundledGFunctors} (v1 v2 : Val rT) :
    OFE.NonExpansive (fun A : lrel rT GF => A.car v1 v2) where
  ne {_ _ _} hAB := hAB v1 v2

/-! ## Relation constructors that do not mention `refines` -/

section SimpleLRels
variable {GF : BundledGFunctors}

/-- Two units are closed. -/
theorem lrel_unit_closed (v1 v2 : Val rT) :
    ⌜v1 = .unit ∧ v2 = .unit⌝ ⊢@{IProp GF} ⌜v1.1.isClosedEmpty ∧ v2.1.isClosedEmpty⌝ := by
  iintro %h !%
  exact ⟨h.1 ▸ Exp.lit_isClosedEmpty _, h.2 ▸ Exp.lit_isClosedEmpty _⟩

/-- Values related when both are `()`. -/
noncomputable def lrel_unit : lrel rT GF where
  car v1 v2 := iprop% ⌜ v1 = .unit ∧ v2 = .unit ⌝
  closed v1 v2 := lrel_unit_closed v1 v2

/-- Values related when both are the same boolean. -/
noncomputable def lrel_bool : lrel rT GF where
  car v1 v2 := iprop% ∃ b : Bool, ⌜ v1 = .bool b ∧ v2 = .bool b ⌝
  closed v1 v2 := by
    iintro ⟨%b, %h⟩ !%
    exact ⟨h.1 ▸ Exp.lit_isClosedEmpty _, h.2 ▸ Exp.lit_isClosedEmpty _⟩

/-- Values related when both are the same natural-number literal. -/
noncomputable def lrel_nat : lrel rT GF where
  car v1 v2 := iprop% ∃ n : Nat, ⌜ v1 = .int n ∧ v2 = .int n ⌝
  closed v1 v2 := by
    iintro ⟨%n, %h⟩ !%
    exact ⟨h.1 ▸ Exp.lit_isClosedEmpty _, h.2 ▸ Exp.lit_isClosedEmpty _⟩

/-- Values related when both are the same positive natural-number literal. -/
noncomputable def lrel_pos_nat : lrel rT GF where
  car v1 v2 := iprop% ∃ n : Nat, ⌜ 0 < n ∧ v1 = .int n ∧ v2 = .int n ⌝
  closed v1 v2 := by
    iintro ⟨%n, %h⟩ !%
    exact ⟨h.2.1 ▸ Exp.lit_isClosedEmpty _, h.2.2 ▸ Exp.lit_isClosedEmpty _⟩

/-- Values related when both are the same integer literal. -/
noncomputable def lrel_int : lrel rT GF where
  car v1 v2 := iprop% ∃ n : Int, ⌜ v1 = .int n ∧ v2 = .int n ⌝
  closed v1 v2 := by
    iintro ⟨%n, %h⟩ !%
    exact ⟨h.1 ▸ Exp.lit_isClosedEmpty _, h.2 ▸ Exp.lit_isClosedEmpty _⟩

/-- Values related when both are the same real literal. -/
noncomputable def lrel_real : lrel rT GF where
  car v1 v2 := iprop% ∃ r : rT, ⌜ v1 = .real r ∧ v2 = .real r ⌝
  closed v1 v2 := by
    iintro ⟨%r, %h⟩ !%
    exact ⟨h.1 ▸ Exp.lit_isClosedEmpty _, h.2 ▸ Exp.lit_isClosedEmpty _⟩

/-! ### A literal is related to itself -/

theorem lrel_unit_lit : ⊢@{IProp GF} lrel_unit.car (.unit : Val rT) .unit := by
  unfold lrel_unit; ipureintro; exact ⟨rfl, rfl⟩

theorem lrel_int_lit (n : Int) : ⊢@{IProp GF} lrel_int.car (.int n : Val rT) (.int n) := by
  unfold lrel_int; iexists n; ipureintro; exact ⟨rfl, rfl⟩

theorem lrel_nat_lit {n : Int} (hn : 0 ≤ n) :
    ⊢@{IProp GF} lrel_nat.car (.int n : Val rT) (.int n) := by
  unfold lrel_nat
  iexists n.toNat
  ipureintro
  refine ⟨?_, ?_⟩ <;> rw [Int.toNat_of_nonneg hn]

theorem lrel_bool_lit (b : Bool) : ⊢@{IProp GF} lrel_bool.car (.bool b : Val rT) (.bool b) := by
  unfold lrel_bool; iexists b; ipureintro; exact ⟨rfl, rfl⟩

theorem lrel_real_lit (r : rT) : ⊢@{IProp GF} lrel_real.car (.real r : Val rT) (.real r) := by
  unfold lrel_real; iexists r; ipureintro; exact ⟨rfl, rfl⟩

/-- Pairs related componentwise. -/
noncomputable def lrel_prod (A B : lrel rT GF) : lrel rT GF where
  car v1 v2 := iprop%
    ∃ (a1 a2 b1 b2 : Val rT),
      ⌜ v1.1 = .pair a1.1 b1.1 ⌝ ∗ ⌜ v2.1 = .pair a2.1 b2.1 ⌝ ∗
      A a1 a2 ∗ B b1 b2
  closed v1 v2 := by
    iintro ⟨%a1, %a2, %b1, %b2, %h1, %h2, HA, HB⟩
    ihave %hAcl := A.closed a1 a2 $$ HA
    ihave %hBcl := B.closed b1 b2 $$ HB
    ipureintro
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [h1]; exact Exp.IsLocallyClosed.pair hAcl.1.1 hBcl.1.1
    · rw [h1]; simp [Exp.fv]; exact ⟨hAcl.1.2, hBcl.1.2⟩
    · rw [h2]; exact Exp.IsLocallyClosed.pair hAcl.2.1 hBcl.2.1
    · rw [h2]; simp [Exp.fv]; exact ⟨hAcl.2.2, hBcl.2.2⟩

/-- Related components give related pairs. -/
theorem lrel_prod_pair {A B : lrel rT GF} {a a' b b' : Val rT} :
    iprop% A a a' ∗ B b b' ⊢ (lrel_prod A B).car (.pair a b) (.pair a' b') := by
  iintro ⟨HA, HB⟩
  iunfold lrel_prod
  iexists a, a', b, b'
  iframe HA HB
  isplitr <;> ipureintro <;> rfl

/-- Sums related when both are injections of the same side, with related payloads. -/
noncomputable def lrel_sum (A B : lrel rT GF) : lrel rT GF where
  car v1 v2 := iprop%
    ∃ (w1 w2 : Val rT),
      (⌜ v1.1 = .inl w1.1 ⌝ ∗ ⌜ v2.1 = .inl w2.1 ⌝ ∗ A w1 w2) ∨
      (⌜ v1.1 = .inr w1.1 ⌝ ∗ ⌜ v2.1 = .inr w2.1 ⌝ ∗ B w1 w2)
  closed v1 v2 := by
    iintro ⟨%w1, %w2, Hd⟩
    icases Hd with (⟨%h1, %h2, HA⟩ | ⟨%h1, %h2, HB⟩)
    · ihave %hAcl := A.closed w1 w2 $$ HA
      ipureintro
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · rw [h1]; exact Exp.IsLocallyClosed.inl hAcl.1.1
      · rw [h1]; simp [Exp.fv]; exact hAcl.1.2
      · rw [h2]; exact Exp.IsLocallyClosed.inl hAcl.2.1
      · rw [h2]; simp [Exp.fv]; exact hAcl.2.2
    · ihave %hBcl := B.closed w1 w2 $$ HB
      ipureintro
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · rw [h1]; exact Exp.IsLocallyClosed.inr hBcl.1.1
      · rw [h1]; simp [Exp.fv]; exact hBcl.1.2
      · rw [h2]; exact Exp.IsLocallyClosed.inr hBcl.2.1
      · rw [h2]; simp [Exp.fv]; exact hBcl.2.2

/-- Closed values related by `C A` for some relation `A`. -/
noncomputable def lrel_exists (C : lrel rT GF → lrel rT GF) : lrel rT GF where
  car v1 v2 := iprop% ⌜v1.1.isClosedEmpty ∧ v2.1.isClosedEmpty⌝ ∗ ∃ A : lrel rT GF, C A v1 v2
  closed _ _ := by iintro ⟨%h, _⟩; ipureintro; exact h

/-- Relates every pair of closed values. -/
noncomputable def lrel_true : lrel rT GF where
  car v1 v2 := iprop% ⌜v1.1.isClosedEmpty ∧ v2.1.isClosedEmpty⌝
  closed _ _ := .rfl

/-! ### Recursive relations, as a fixpoint on the COFE -/

-- TODO: Tweak the declarations below when fixpoints land
/-- One unfolding of a recursive relation, with the recursive occurrence guarded by `▷`. -/
noncomputable def lrelRec1 (C : lrel rT GF -n> lrel rT GF) (r : lrel rT GF) : lrel rT GF where
  car w1 w2 := iprop% ⌜w1.1.isClosedEmpty ∧ w2.1.isClosedEmpty⌝ ∗ ▷ (C r).car w1 w2
  closed _ _ := by iintro ⟨%h, _⟩; ipureintro; exact h

/-- `lrelRec1 C` is contractive, since the recursive occurrence sits under `▷`. -/
instance lrelRec1_contractive (C : lrel rT GF -n> lrel rT GF) : OFE.Contractive (lrelRec1 C) where
  distLater_dist {n P Q} hPQ w1 w2 := by
    show iprop(_ ∗ ▷ _) ≡{n}≡ iprop(_ ∗ ▷ _)
    exact sep_ne.ne .rfl <| Contractive.distLater_dist
      fun k hk => C.ne.ne (show P ≡{k}≡ Q from hPQ k hk) w1 w2

/-- `lrelRec1` bundled as a contractive function. -/
noncomputable def lrelRec1Hom (C : lrel rT GF -n> lrel rT GF) : lrel rT GF -c> lrel rT GF where
  f := lrelRec1 C

/-- Recursive relations, as the fixpoint of `lrelRec1`. -/
noncomputable def lrel_rec (C : lrel rT GF -n> lrel rT GF) : lrel rT GF :=
  fixpoint (lrelRec1 C)

/-- A recursive relation equals its one-step unfolding. -/
theorem lrel_rec_unfold (C : lrel rT GF -n> lrel rT GF) :
    lrel_rec C = lrelRec1 C (lrel_rec C) :=
  fixpoint_unfold (lrelRec1Hom C)

-- TODO: Attempt to simplify once nonexp lands
/-- Recursive relations are `n`-close when their bodies are `n`-close pointwise. -/
theorem lrel_rec_ne {n : Nat} {C1 C2 : lrel rT GF -n> lrel rT GF}
    (hC : ∀ A : lrel rT GF, C1 A ≡{n}≡ C2 A) :
    lrel_rec C1 ≡{n}≡ lrel_rec C2 :=
  fixpoint_dist fun r w1 w2 =>
    sep_ne.ne .rfl
      (OFE.NonExpansive.ne (hC r w1 w2))

/-! ### Nonexpansiveness of the simple constructors -/

-- TODO: Remove these hand-written proofs when nonexp lands

instance lrel_prod_ne_2 : OFE.NonExpansive₂ (lrel_prod (rT := rT) (GF := GF)) where
  ne {n A1 A2} hA {B1 B2} hB v1 v2 := by
    refine exists_ne fun a1 => exists_ne fun a2 => exists_ne fun b1 => exists_ne fun b2 => ?_
    exact sep_ne.ne .rfl <| sep_ne.ne .rfl <| sep_ne.ne (hA a1 a2) (hB b1 b2)

instance lrel_sum_ne_2 : OFE.NonExpansive₂ (lrel_sum (rT := rT) (GF := GF)) where
  ne {n A1 A2} hA {B1 B2} hB v1 v2 := by
    refine exists_ne fun w1 => exists_ne fun w2 => or_ne.ne ?_ ?_
    · exact sep_ne.ne .rfl <| sep_ne.ne .rfl (hA w1 w2)
    · exact sep_ne.ne .rfl <| sep_ne.ne .rfl (hB w1 w2)

theorem lrel_exists_ne {n : Nat} {C1 C2 : lrel rT GF → lrel rT GF}
    (h : ∀ A, C1 A ≡{n}≡ C2 A) :
    (lrel_exists C1 : lrel rT GF) ≡{n}≡ lrel_exists C2 := by
  intro v1 v2
  show iprop(_ ∗ ∃ _, _) ≡{n}≡ iprop(_ ∗ ∃ _, _)
  exact sep_ne.ne .rfl <| exists_ne fun A => h A v1 v2

end SimpleLRels

/-! ## Ghost state of the logical relation -/

/-- The namespace of the invariants of the logical relation. -/
def logN : Namespace := nroot.@ (1 : Pos)

/-- Ghost state of the logical relation: Micrometer, non-atomic invariants and their pool name. -/
class MicrometerRGS (rT : Type) [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
    (hlc : outParam HasLC) (GF : BundledGFunctors) where
  micrometerGS : MicrometerGS rT hlc GF
  naInvG     : NaInvG GF
  nais       : NaInvPoolName

attribute [reducible, instance] MicrometerRGS.micrometerGS MicrometerRGS.naInvG

section NaShorthand
variable [LawfulProbLangℝ rT] {hlc : HasLC} {GF : BundledGFunctors} [MicrometerRGS rT hlc GF]

/-- Ownership of the non-atomic invariant mask `E`, in the pool of `MicrometerRGS`. -/
@[reducible] noncomputable def naOwnP (E : CoPset) : IProp GF :=
  Iris.NonAtomicInvariant.own (MicrometerRGS.nais (rT := rT) GF) E

/-- The non-atomic invariant `P` at namespace `N`, in the pool of `MicrometerRGS`. -/
@[reducible] noncomputable def naInvP (N : Namespace) (P : IProp GF) : IProp GF :=
  Iris.NonAtomicInvariant.inv (MicrometerRGS.nais (rT := rT) GF) N P

/-- The update that closes the non-atomic invariant `P` at `N`, opened from mask `E`. -/
@[reducible] noncomputable def naCloseP (P : IProp GF) (N : Namespace) (E : CoPset) : IProp GF :=
  iprop% (▷ P) ∗ naOwnP (rT := rT) (E \ ↑N) ={⊤}=∗ naOwnP (rT := rT) E

end NaShorthand

/-! ## Refinement judgement -/

section Refines
variable [LawfulProbLangℝ rT] {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B]
  [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors} [MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF]

variable (L) in
/-- `REL[L] e << e' @ E : A`: `e` refines `e'` at `A` under the graded lifting `L`.

The right context `K` is quantified so `refines_bind` can work inside a larger spec context;
`naOwnP E` says the non-atomic invariants outside `E` are open and must be closed by the end; the
threaded positive credit `b` must come back as some positive `b'` (see `approximates_coupling`). -/
noncomputable def refines (E : CoPset) (e e' : Exp rT) (A : lrel rT GF) : IProp GF := iprop%
  ∀ (K : Ectx rT) (b : B),
    ⤇ K.fill e' -∗
    naOwnP (rT := rT) E -∗
    ↯b b -∗
    ⌜ (0 : B) < b ⌝ -∗
    wp L ⊤ e (fun v => iprop%
      ∃ (v' : Val rT) (b' : B),
        ⤇ K.fill v'.1 ∗
        naOwnP (rT := rT) ⊤ ∗
        ↯b b' ∗
        ⌜ (0 : B) < b' ⌝ ∗
        A v v')

end Refines

/-! ### Notation `REL[L] e << e' @ E : A` -/

scoped syntax:100 (name := micrometerRel)
  "REL[" term "] " term " << " term (" @ " term)? " : " term : term

macro_rules
  | `(REL[$L] $e1 << $e2 $[@ $E]? : $A) => do
    let E ← match E with | some E => pure E | none => `((⊤ : CoPset))
    `(refines $L $E $e1 $e2 $A)

/-- Print `refines` through `REL[L]`, dropping the mask when it is `⊤`. -/
@[app_unexpander ProbLang.refines]
meta def unexpandRefines : Lean.PrettyPrinter.Unexpander
  | `($_ $L $E $e1 $e2 $A) =>
    if E.raw.getNumArgs == 1 && E.raw[0].isToken "⊤" then `(REL[$L] $e1 << $e2 : $A)
    else `(REL[$L] $e1 << $e2 @ $E : $A)
  | _ => throw ()

/-! ## Relations that refer to the logic -/

-- TODO: Remove the hand-written nonexpansiveness proofs below when nonexp lands

section LogicLRels
variable [LawfulProbLangℝ rT] {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B]
  [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors} [MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF]

variable (L) in
/-- Closed functions whose applications to `A1`-related arguments refine at `A2`. -/
noncomputable def lrel_arr (A1 A2 : lrel rT GF) : lrel rT GF where
  car v1 v2 := iprop%
    ⌜v1.1.isClosedEmpty ∧ v2.1.isClosedEmpty⌝ ∗
      □ (∀ (w1 w2 : Val rT), A1 w1 w2 -∗
        refines L (⊤ : CoPset) (.app v1.1 w1.1) (.app v2.1 w2.1) A2)
  closed _ _ := by iintro ⟨%h, _⟩; ipureintro; exact h

variable (L) in
/-- Type abstractions: thunks whose applications to `()` refine at `C A` for every `A`. -/
noncomputable def lrel_forall (C : lrel rT GF → lrel rT GF) : lrel rT GF where
  car v1 v2 := iprop% ∀ (A : lrel rT GF), (lrel_arr L lrel_unit (C A)).car v1 v2
  closed v1 v2 := by
    iintro Hall
    ihave Hinst := Hall $$ %(default : lrel rT GF)
    iapply (lrel_arr L lrel_unit (C default)).closed v1 v2 $$ Hinst

/-- Locations whose contents stay `A`-related, kept in an invariant. -/
noncomputable def lrel_ref (A : lrel rT GF) : lrel rT GF where
  car v1 v2 := iprop%
    ∃ (l1 l2 : Loc),
      ⌜ v1 = .loc l1 ⌝ ∗ ⌜ v2 = .loc l2 ⌝ ∗
      Iris.inv (logN.@ (l1, l2)) iprop(∃ w1 w2, appHeapFrag l1 w1 ∗ specHeapFrag l2 w2 ∗ A w1 w2)
  closed v1 v2 := by
    iintro ⟨%l1, %l2, %h1, %h2, _⟩ !%
    exact ⟨h1 ▸ Exp.lit_isClosedEmpty _, h2 ▸ Exp.lit_isClosedEmpty _⟩

/-- Tape labels of two empty tapes with the same bound, kept in an invariant. -/
noncomputable def lrel_tape : lrel rT GF where
  car v1 v2 := iprop%
    ∃ (α1 α2 : Loc) (z : Int),
      ⌜ v1 = .lbl α1 ⌝ ∗ ⌜ v2 = .lbl α2 ⌝ ∗
      Iris.inv (logN.@ (α1, α2)) iprop(appTapesFrag α1 ⟨z, []⟩ ∗ specTapesFrag α2 ⟨z, []⟩)
  closed v1 v2 := by
    iintro ⟨%α1, %α2, %z, %h1, %h2, _⟩ !%
    exact ⟨h1 ▸ Exp.lit_isClosedEmpty _, h2 ▸ Exp.lit_isClosedEmpty _⟩

/-- `refines` is nonexpansive in the relation. -/
theorem refines_ne {E : CoPset} {e e' : Exp rT} {n : Nat} {A B : lrel rT GF}
    (h : A ≡{n}≡ B) : refines L E e e' A ≡{n}≡ refines L E e e' B := by
  unfold refines
  refine forall_ne fun K => forall_ne fun b => ?_
  refine wand_ne.ne .rfl <| wand_ne.ne .rfl <| wand_ne.ne .rfl <| wand_ne.ne .rfl ?_
  refine NonExpansive.ne fun v => exists_ne fun v' => exists_ne fun b' => ?_
  exact sep_ne.ne .rfl <| sep_ne.ne .rfl <| sep_ne.ne .rfl <| sep_ne.ne .rfl (h v v')

instance lrel_arr_ne_2 : OFE.NonExpansive₂ (lrel_arr L (rT := rT) (GF := GF)) where
  ne {n A1 A2} hA {B1 B2} hB v1 v2 := by
    exact sep_ne.ne .rfl <| intuitionistically_ne.ne <| forall_ne fun w1 => forall_ne fun w2 =>
      wand_ne.ne (hA w1 w2) (refines_ne hB)

instance lrel_ref_ne : OFE.NonExpansive (lrel_ref (rT := rT) (GF := GF)) where
  ne {n A B} hAB v1 v2 := by
    show iprop(∃ _ _, _) ≡{n}≡ iprop(∃ _ _, _)
    refine exists_ne fun l1 => exists_ne fun l2 => ?_
    refine sep_ne.ne .rfl <| sep_ne.ne .rfl <| (Iris.inv_ne _).ne ?_
    show iprop(∃ _ _, _) ≡{n}≡ iprop(∃ _ _, _)
    exact exists_ne fun w1 => exists_ne fun w2 => sep_ne.ne .rfl <| sep_ne.ne .rfl (hAB w1 w2)

variable (L) in
theorem lrel_forall_ne {n : Nat} {C1 C2 : lrel rT GF → lrel rT GF}
    (h : ∀ A, C1 A ≡{n}≡ C2 A) :
    (lrel_forall L C1 : lrel rT GF) ≡{n}≡ lrel_forall L C2 := by
  intro v1 v2
  show iprop(∀ _, _) ≡{n}≡ iprop(∀ _, _)
  exact forall_ne fun A => lrel_arr_ne_2.ne .rfl (h A) v1 v2

end LogicLRels

end ProbLang
