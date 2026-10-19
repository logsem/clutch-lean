module

public import Metrology.Micrometer.AppWeakestpre
public import Metrology.Micrometer.PrimitiveLaws
public import Metrology.ProbLang.Syntax.LocallyClosed
public import Iris.Instances.Lib.NaInvariants
public import Iris.Instances.Lib.Invariants
public import Metrology.Iris.Countable
import Metrology.ProbLang.Syntax.Notation

/-! # Semantic Model -/

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting

namespace ProbLang

variable {rT : Type} [LawfulProbLangℝ rT]

/-! ## Log-relation namespace -/

/-- The namespace of the invariants of the logical relation. -/
def logN : Namespace := nroot.@ (1 : Pos)

/-! ## `MicrometerRGS` ghost-state bundle -/

/-- Ghost state of the logical relation: Micrometer, non-atomic invariants and their pool name. -/
class MicrometerRGS (rT : Type) [LawfulProbLangℝ rT] [MeasurableSingletonClass rT]
    (hlc : outParam HasLC) (GF : BundledGFunctors) where
  micrometerGS : MicrometerGS rT hlc GF
  naInvG     : NaInvG GF
  nais       : NaInvPoolName

attribute [reducible, instance] MicrometerRGS.micrometerGS MicrometerRGS.naInvG

/-! ## Logical relation type -/

/-- A value relation: persistent, and only relating closed values. -/
structure lrel (rT : Type) (GF : BundledGFunctors) where
  car : Val rT → Val rT → IProp GF
  [persistent : ∀ v1 v2, Persistent (car v1 v2)]
  closed v1 v2 : car v1 v2 ⊢ ⌜v1.1.isClosedEmpty ∧ v2.1.isClosedEmpty⌝

attribute [instance] lrel.persistent

instance {GF} : CoeFun (lrel rT GF) (fun _ => Val rT → Val rT → IProp GF) := ⟨lrel.car⟩

/-! ## OFE/COFE structure on `lrel` -/

omit [LawfulProbLangℝ rT] in
theorem lrel.ext {GF : BundledGFunctors} {A B : lrel rT GF}
    (h : ∀ v1 v2, A.car v1 v2 = B.car v1 v2) : A = B := by
  obtain ⟨carA, _⟩ := A
  obtain ⟨carB, _⟩ := B
  obtain rfl : carA = carB := funext fun v1 => funext (h v1)
  rfl

instance {GF : BundledGFunctors} : OFE (lrel rT GF) where
  Dist n A B := ∀ v1 v2, A.car v1 v2 ≡{n}≡ B.car v1 v2
  dist_eqv := {
    refl _ _ _ := dist_eqv.refl _
    symm h v1 v2 := dist_eqv.symm (h v1 v2)
    trans h1 h2 v1 v2 := dist_eqv.trans (h1 v1 v2) (h2 v1 v2)
  }
  eq_dist' :=
    ⟨fun h _ _ _ => h ▸ .rfl, fun h => lrel.ext fun _ _ => OFE.eq_dist.mpr fun _ => h _ _ _⟩
  dist_lt hd hmn v1 v2 := OFE.dist_lt (hd v1 v2) hmn

/-- Project an `lrel`-valued chain into the underlying function-space chain. -/
noncomputable def lrel.toFunChain {GF : BundledGFunctors}
    (c : Chain (lrel rT GF)) : Chain (Val rT → Val rT → IProp GF) where
  chain k := (c.chain k).car
  cauchy h := (c.cauchy h : _)

/-- Evaluation of a binary relation at a pair of values. -/
abbrev lrel.appAt {GF : BundledGFunctors} (v1 v2 : Val rT) :
    (Val rT → Val rT → IProp GF) → IProp GF := (· v1 v2)

instance lrel.appAt_ne {GF : BundledGFunctors} (v1 v2 : Val rT) :
    OFE.NonExpansive (lrel.appAt (GF := GF) v1 v2) := ⟨fun _ _ _ h => h v1 v2⟩

noncomputable instance {GF : BundledGFunctors} : IsCOFE (lrel rT GF) where
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

instance {GF : BundledGFunctors} : Inhabited (lrel rT GF) where
  default :=
    { car := fun _ _ => iprop(False)
      closed := fun _ _ => Iris.BI.false_elim }

instance lrel.car_ne {GF : BundledGFunctors} (v1 v2 : Val rT) :
    OFE.NonExpansive (fun A : lrel rT GF => A.car v1 v2) where
  ne {_ _ _} hAB := hAB v1 v2

/-! ## `na_own` / `na_inv` abbreviations keyed on the pool name -/

section NaShorthand
variable {hlc : HasLC} {GF : BundledGFunctors} [MicrometerRGS rT hlc GF]

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
variable {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B] [OrderTop B]
  {L : GradedLifting.{0} B} {GF : BundledGFunctors} [MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF]

variable (L) in
/-- `REL[L] e << e' @ E : A`: `e` refines `e'` at `A` under the graded lifting `L`. -/
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

/-! ## Notation for the refinement judgement -/

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

/-! ## Simple lrel constructors -/

section SimpleLRels
variable {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B] [OrderTop B]
  {L : GradedLifting.{0} B} {GF : BundledGFunctors} [MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF]

omit [LawfulProbLangℝ rT] in
theorem lrel_closed_lit_pair (v1 v2 : Val rT) :
    ⌜v1 = .unit ∧ v2 = .unit⌝ ⊢@{IProp GF} ⌜v1.1.isClosedEmpty ∧ v2.1.isClosedEmpty⌝ := by
  iintro %h !%
  exact ⟨h.1 ▸ Exp.lit_isClosedEmpty _, h.2 ▸ Exp.lit_isClosedEmpty _⟩

/-- Values related when both are `()`. -/
noncomputable def lrel_unit : lrel rT GF where
  car v1 v2 := iprop% ⌜ v1 = .unit ∧ v2 = .unit ⌝
  closed v1 v2 := lrel_closed_lit_pair v1 v2

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

omit [LawfulProbLangℝ rT] in
theorem lrel_unit_lit : ⊢@{IProp GF} lrel_unit.car (.unit : Val rT) .unit := by
  unfold lrel_unit; ipureintro; exact ⟨rfl, rfl⟩

omit [LawfulProbLangℝ rT] in
theorem lrel_int_lit (n : Int) : ⊢@{IProp GF} lrel_int.car (.int n : Val rT) (.int n) := by
  unfold lrel_int; iexists n; ipureintro; exact ⟨rfl, rfl⟩

omit [LawfulProbLangℝ rT] in
theorem lrel_nat_lit {n : Int} (hn : 0 ≤ n) :
    ⊢@{IProp GF} lrel_nat.car (.int n : Val rT) (.int n) := by
  unfold lrel_nat
  iexists n.toNat
  ipureintro
  refine ⟨?_, ?_⟩ <;> rw [Int.toNat_of_nonneg hn]

omit [LawfulProbLangℝ rT] in
theorem lrel_bool_lit (b : Bool) : ⊢@{IProp GF} lrel_bool.car (.bool b : Val rT) (.bool b) := by
  unfold lrel_bool; iexists b; ipureintro; exact ⟨rfl, rfl⟩

omit [LawfulProbLangℝ rT] in
theorem lrel_real_lit (r : rT) : ⊢@{IProp GF} lrel_real.car (.real r : Val rT) (.real r) := by
  unfold lrel_real; iexists r; ipureintro; exact ⟨rfl, rfl⟩

variable (L) in
/-- Closed values whose applications to `A1`-related arguments refine at `A2`. -/
noncomputable def lrel_arr (A1 A2 : lrel rT GF) : lrel rT GF where
  car v1 v2 := iprop%
    ⌜v1.1.isClosedEmpty ∧ v2.1.isClosedEmpty⌝ ∗
      □ (∀ (w1 w2 : Val rT), A1 w1 w2 -∗
        refines L (⊤ : CoPset) (.app v1.1 w1.1) (.app v2.1 w2.1) A2)
  closed _ _ := by iintro ⟨%h, _⟩; ipureintro; exact h

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

omit [LawfulProbLangℝ rT] in
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

variable (L) in
/-- Thunks related by `C A` for every relation `A`. -/
noncomputable def lrel_forall (C : lrel rT GF → lrel rT GF) : lrel rT GF where
  car v1 v2 := iprop% ∀ (A : lrel rT GF), (lrel_arr L lrel_unit (C A)).car v1 v2
  closed v1 v2 := by
    iintro Hall
    ihave Hinst := Hall $$ %(default : lrel rT GF)
    iapply (lrel_arr L lrel_unit (C default)).closed v1 v2 $$ Hinst

/-- Relates every pair of closed values. -/
noncomputable def lrel_true : lrel rT GF where
  car v1 v2 := iprop% ⌜v1.1.isClosedEmpty ∧ v2.1.isClosedEmpty⌝
  closed _ _ := .rfl

/-! ### Recursive lrel via `fixpoint` -/

-- TODO: Tweak when fixpoints land
/-- One unfolding of a recursive relation, with the recursive occurrence guarded by `▷`. -/
noncomputable def lrelRec1 (C : lrel rT GF -n> lrel rT GF) (r : lrel rT GF) : lrel rT GF where
  car w1 w2 := iprop% ⌜w1.1.isClosedEmpty ∧ w2.1.isClosedEmpty⌝ ∗ ▷ (C r).car w1 w2
  closed _ _ := by iintro ⟨%h, _⟩; ipureintro; exact h

-- TODO: Tweak when fixpoints land
instance lrelRec1_contractive (C : lrel rT GF -n> lrel rT GF) : OFE.Contractive (lrelRec1 C) where
  distLater_dist {n P Q} hPQ w1 w2 := by
    show iprop(_ ∗ ▷ _) ≡{n}≡ iprop(_ ∗ ▷ _)
    exact sep_ne.ne .rfl <| Contractive.distLater_dist
      fun k hk => C.ne.ne (show P ≡{k}≡ Q from hPQ k hk) w1 w2

-- TODO: Tweak when fixpoints land
/-- `lrelRec1` bundled as a contractive function. -/
noncomputable def lrelRec1Hom (C : lrel rT GF -n> lrel rT GF) : lrel rT GF -c> lrel rT GF where
  f := lrelRec1 C

-- TODO: Tweak when fixpoints land
/-- Recursive relations, as the fixpoint of `lrelRec1`. -/
noncomputable def lrel_rec (C : lrel rT GF -n> lrel rT GF) : lrel rT GF :=
  fixpoint (lrelRec1 C)

-- TODO: Tweak when fixpoints land
omit [LawfulProbLangℝ rT] in
theorem lrel_rec_unfold (C : lrel rT GF -n> lrel rT GF) :
    lrel_rec C = lrelRec1 C (lrel_rec C) :=
  fixpoint_unfold (lrelRec1Hom C)

-- TODO: Attempt to simplify once nonexp lands
omit [LawfulProbLangℝ rT] in
/-- Recursive relations are `n`-close when their bodies are `n`-close pointwise. -/
theorem lrel_rec_ne {n : Nat} {C1 C2 : lrel rT GF -n> lrel rT GF}
    (hC : ∀ A : lrel rT GF, C1 A ≡{n}≡ C2 A) :
    lrel_rec C1 ≡{n}≡ lrel_rec C2 :=
  fixpoint_dist fun r w1 w2 =>
    sep_ne.ne .rfl
      (OFE.NonExpansive.ne (hC r w1 w2))

/-! ### Nonexpansive instances on simple lrel constructors -/

instance lrel_prod_ne_2 : OFE.NonExpansive₂ (lrel_prod (rT := rT) (GF := GF)) where
  ne {n A1 A2} hA {B1 B2} hB v1 v2 := by
    -- TODO: Remove when nonexp lands
    refine exists_ne fun a1 => exists_ne fun a2 => exists_ne fun b1 => exists_ne fun b2 => ?_
    exact sep_ne.ne .rfl <| sep_ne.ne .rfl <| sep_ne.ne (hA a1 a2) (hB b1 b2)

instance lrel_sum_ne_2 : OFE.NonExpansive₂ (lrel_sum (rT := rT) (GF := GF)) where
  ne {n A1 A2} hA {B1 B2} hB v1 v2 := by
    -- TODO: Remove when nonexp lands
    refine exists_ne fun w1 => exists_ne fun w2 => or_ne.ne ?_ ?_
    · exact sep_ne.ne .rfl <| sep_ne.ne .rfl (hA w1 w2)
    · exact sep_ne.ne .rfl <| sep_ne.ne .rfl (hB w1 w2)

theorem refines_ne {E : CoPset} {e e' : Exp rT} {n : Nat} {A B : lrel rT GF}
    (h : A ≡{n}≡ B) : refines L E e e' A ≡{n}≡ refines L E e e' B := by
  -- TODO: Remove when nonexp lands
  unfold refines
  refine forall_ne fun K => forall_ne fun b => ?_
  refine wand_ne.ne .rfl <| wand_ne.ne .rfl <| wand_ne.ne .rfl <| wand_ne.ne .rfl ?_
  refine NonExpansive.ne fun v => exists_ne fun v' => exists_ne fun b' => ?_
  exact sep_ne.ne .rfl <| sep_ne.ne .rfl <| sep_ne.ne .rfl <| sep_ne.ne .rfl (h v v')

instance lrel_arr_ne_2 : OFE.NonExpansive₂ (lrel_arr L (rT := rT) (GF := GF)) where
  ne {n A1 A2} hA {B1 B2} hB v1 v2 := by
    -- TODO: Remove when nonexp lands
    exact sep_ne.ne .rfl <| intuitionistically_ne.ne <| forall_ne fun w1 => forall_ne fun w2 =>
      wand_ne.ne (hA w1 w2) (refines_ne hB)

-- TODO: Can this be removed?
theorem refines_proper {E : CoPset} {e e' : Exp rT} {A B : lrel rT GF}
    (h : A = B) : refines L E e e' A = refines L E e e' B :=
  OFE.eq_dist.mpr fun n => refines_ne (OFE.eq_dist_1 h n)

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

instance lrel_ref_ne : OFE.NonExpansive (lrel_ref (rT := rT) (GF := GF)) where
  ne {n A B} hAB v1 v2 := by
    -- TODO: Tweak when nonexp lands
    show iprop(∃ _ _, _) ≡{n}≡ iprop(∃ _ _, _)
    refine exists_ne fun l1 => exists_ne fun l2 => ?_
    refine sep_ne.ne .rfl <| sep_ne.ne .rfl <| (Iris.inv_ne _).ne ?_
    show iprop(∃ _ _, _) ≡{n}≡ iprop(∃ _ _, _)
    exact exists_ne fun w1 => exists_ne fun w2 => sep_ne.ne .rfl <| sep_ne.ne .rfl (hAB w1 w2)

variable (L) in
theorem lrel_forall_ne {n : Nat} {C1 C2 : lrel rT GF → lrel rT GF}
    (h : ∀ A, C1 A ≡{n}≡ C2 A) :
    (lrel_forall L C1 : lrel rT GF) ≡{n}≡ lrel_forall L C2 := by
  -- TODO: Tweak when nonexp lands
  intro v1 v2
  show iprop(∀ _, _) ≡{n}≡ iprop(∀ _, _)
  exact forall_ne fun A => lrel_arr_ne_2.ne .rfl (h A) v1 v2

omit [LawfulProbLangℝ rT] in
theorem lrel_exists_ne {n : Nat} {C1 C2 : lrel rT GF → lrel rT GF}
    (h : ∀ A, C1 A ≡{n}≡ C2 A) :
    (lrel_exists C1 : lrel rT GF) ≡{n}≡ lrel_exists C2 := by
  -- TODO: Tweak when nonexp lands
  intro v1 v2
  show iprop(_ ∗ ∃ _, _) ≡{n}≡ iprop(_ ∗ ∃ _, _)
  exact sep_ne.ne .rfl <| exists_ne fun A => h A v1 v2

end SimpleLRels

/-! ### Semantic property lemmas -/

section SemtypesProperties
variable {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B] [OrderTop B]
  {L : GradedLifting.{0} B} {GF : BundledGFunctors} [MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF]

instance : Inhabited (Val rT) := ⟨.unit⟩

/-- Two `logN` invariants with incompatible bodies have equal names, so `l1 = l2` holds whenever
equal names imply it. -/
theorem fupd_eq_of_inv_excl {E : CoPset} {P1 P2 : IProp GF} {p1 p2 : Loc × Loc}
    {l1 l2 : Loc} (HE : (↑logN : CoPset) ⊆ E) (hp : p1 = p2 → l1 = l2)
    (hfalse : ⊢ P1 -∗ P2 -∗ False) :
    ⊢ Iris.inv (logN.@ p1) P1 -∗ Iris.inv (logN.@ p2) P2 -∗ |={E}=> ⌜l1 = l2⌝ := by
  by_cases h : l1 = l2
  · iintro - - !> !%; exact h
  have hN_disj : logN.@ p1 ## logN.@ p2 := ndot_ne_disjoint _ (mt hp h)
  have h1 : (↑(logN.@ p1) : CoPset) ⊆ E := LawfulSet.subset_trans (nclose_subseteq _ _) HE
  have h2 : (↑(logN.@ p2) : CoPset) ⊆ E := LawfulSet.subset_trans (nclose_subseteq _ _) HE
  have h2' : (↑(logN.@ p2) : CoPset) ⊆ E \ (↑(logN.@ p1) : CoPset) :=
    fun p hp => CoPset.in_diff.mpr ⟨h2 p hp, fun hp1 => hN_disj p ⟨hp1, hp⟩⟩
  iintro Hinv1 Hinv2
  iinv Hinv1 with HP1
  iinv Hinv2 with HP2
  ihave Hfalse : iprop% ▷ False $$ [HP1 HP2]
  · inext
    iapply hfalse $$ HP1 HP2
  imod Hfalse with %hf
  exact hf.elim

/-- Reference type is functional in the program-side location. -/
theorem interp_ref_funct {E : CoPset} (A : lrel rT GF) (l l1 l2 : Loc)
    (HE : (↑logN : CoPset) ⊆ E) :
    ⊢ (lrel_ref A).car (.loc l) (.loc l1) -∗
        (lrel_ref A).car (.loc l) (.loc l2) -∗
        |={E}=> ⌜l1 = l2⌝ := by
  unfold lrel_ref
  iintro ⟨%l', %l1', %Heq1, %Heq1', Hinv1⟩ ⟨%l'', %l2', %Heq2, %Heq2', Hinv2⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ : l = l' ∧ l = l'' ∧ l1 = l1' ∧ l2 = l2' := by
    simp_all [Val.ext_iff]
  iapply fupd_eq_of_inv_excl HE (by simp) (by
    iintro ⟨%wa1, %ws1, Hl1L, -⟩ ⟨%wa2, %ws2, Hl2L, -⟩
    iapply appHeapFrag_valid_2 $$ Hl1L Hl2L) $$ Hinv1 Hinv2

/-- Reference type is injective on the program-side location. -/
theorem interp_ref_inj {E : CoPset} (A : lrel rT GF) (l l1 l2 : Loc)
    (HE : (↑logN : CoPset) ⊆ E) :
    ⊢ (lrel_ref A).car (.loc l1) (.loc l) -∗
        (lrel_ref A).car (.loc l2) (.loc l) -∗
        |={E}=> ⌜l1 = l2⌝ := by
  unfold lrel_ref
  iintro ⟨%l1', %l', %Heq1, %Heq1', Hinv1⟩ ⟨%l2', %l'', %Heq2, %Heq2', Hinv2⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ : l = l' ∧ l = l'' ∧ l1 = l1' ∧ l2 = l2' := by
    simp_all [Val.ext_iff]
  iapply fupd_eq_of_inv_excl HE (by simp) (by
    iintro ⟨%wa1, %ws1, -, Hs1L, -⟩ ⟨%wa2, %ws2, -, Hs2L, -⟩
    iapply specHeapFrag_valid_2 $$ Hs1L Hs2L) $$ Hinv1 Hinv2

/-- Tape type is functional in the program-side location. -/
theorem interp_tape_funct {E : CoPset} (l l1 l2 : Loc)
    (HE : (↑logN : CoPset) ⊆ E) :
    ⊢ (lrel_tape (rT := rT) (GF := GF)).car (.lbl l) (.lbl l1) -∗
        (lrel_tape (rT := rT) (GF := GF)).car (.lbl l) (.lbl l2) -∗
        |={E}=> ⌜l1 = l2⌝ := by
  unfold lrel_tape
  iintro ⟨%l', %l1', %z1, %Heq1, %Heq1', Hinv1⟩ ⟨%l'', %l2', %z2, %Heq2, %Heq2', Hinv2⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ : l = l' ∧ l = l'' ∧ l1 = l1' ∧ l2 = l2' := by
    simp_all [Val.ext_iff]
  iapply fupd_eq_of_inv_excl HE (by simp) (by
    iintro ⟨Hl1L, -⟩ ⟨Hl2L, -⟩
    iapply appTapesFrag_valid_2 $$ Hl1L Hl2L) $$ Hinv1 Hinv2

/-- Tape type is injective on the program-side location. -/
theorem interp_tape_inj {E : CoPset} (l l1 l2 : Loc)
    (HE : (↑logN : CoPset) ⊆ E) :
    ⊢ (lrel_tape (rT := rT) (GF := GF)).car (.lbl l1) (.lbl l) -∗
        (lrel_tape (rT := rT) (GF := GF)).car (.lbl l2) (.lbl l) -∗
        |={E}=> ⌜l1 = l2⌝ := by
  unfold lrel_tape
  iintro ⟨%l1', %l', %z1, %Heq1, %Heq1', Hinv1⟩ ⟨%l2', %l'', %z2, %Heq2, %Heq2', Hinv2⟩
  obtain ⟨rfl, rfl, rfl, rfl⟩ : l = l' ∧ l = l'' ∧ l1 = l1' ∧ l2 = l2' := by
    simp_all [Val.ext_iff]
  iapply fupd_eq_of_inv_excl HE (by simp) (by
    iintro ⟨-, Hs1L⟩ ⟨-, Hs2L⟩
    iapply specTapesFrag_valid_2 $$ Hs1L Hs2L) $$ Hinv1 Hinv2

end SemtypesProperties

/-! ## Monadic layer -/

section Monadic
variable {hlc : HasLC} {B : Type} [AddCommMonoid B] [PartialOrder B] [OrderTop B]
  {L : GradedLifting.{0} B} {GF : BundledGFunctors} [MicrometerRGS rT hlc GF]
  [BudgetCreditGS B GF]

theorem fupd_refines {E : CoPset} {e t : Exp rT} {A : lrel rT GF} :
    iprop(|={⊤}=> refines L E e t A) ⊢ refines L E e t A := by
  unfold refines
  iintro >H
  iexact H

/-- Sequence two refinements via evaluation-context framing. -/
theorem refines_bind [L.IsLawful] [L.IsTopAbsorbing] [L.HasBind] (K K' : Ectx rT) {E : CoPset}
    {A A' : lrel rT GF} {e e' : Exp rT} :
    ⊢ refines L E e e' A -∗
      (∀ v v', A v v' -∗ refines L ⊤ (K.fill v.1) (K'.fill v'.1) A') -∗
      refines L E (K.fill e) (K'.fill e') A' := by
  unfold refines
  iintro Hm Hf %K'' %b Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K'' K' e'] at Hj
  ispecialize Hm $$ %(K''.comp K') %b Hj Hna Herr Hpos
  iapply MicrometerWpGS.wp_bind
  iapply MicrometerWpGS.wp_mono
  -- Take the `wp` premise first: it pins the intermediate postcondition to the one of `Hm`,
  -- with the continuation `Hf` framed alongside it.
  swap
  · iapply MicrometerWpGS.wp_frame_l
    iframe Hf
    iexact Hm
  intro v
  change _ ⊢ wp L ⊤ (K.fill v.1) _
  iintro ⟨Hf, %v', %b', Hj, Hna, Herr, Hpos, HA⟩
  ispecialize Hf $$ %v %v' HA
  isimp only [← Ectx.fill_comp K'' K' v'.1] at Hj
  iapply Hf $$ %K'' %b' Hj Hna Herr Hpos

/-- Values refine at `A` when `naOwnP E` updates to `naOwnP ⊤` together with `A v1 v2`. -/
theorem refines_ret_na {E : CoPset} {e1 e2 : Exp rT} {v1 v2 : Val rT} {A : lrel rT GF}
    (hv1 : e1 = v1.1) (hv2 : e2 = v2.1) :
    iprop(naOwnP (rT := rT) E ={⊤}=∗ naOwnP (rT := rT) ⊤ ∗ A v1 v2)
      ⊢ refines L E e1 e2 A := by
  subst hv1 hv2
  unfold refines
  iintro HFA %K %b HK Hnais Herr Hpos
  iapply wp_value_fupd_of_toVal (e := v1.1) (Exp.toVal?_ofVal v1)
  imod HFA $$ Hnais with ⟨HF, HA⟩
  imodintro
  iexists v2, b
  iframe HK HF Herr Hpos HA

/-- Values refine at `A` when a `⊤` update gives the missing `naOwnP (⊤ \ E)` and `A v1 v2`. -/
theorem refines_ret_na_compl {E : CoPset} {e1 e2 : Exp rT} {v1 v2 : Val rT} {A : lrel rT GF}
    (hv1 : e1 = v1.1) (hv2 : e2 = v2.1) :
    iprop(|={⊤}=> naOwnP (rT := rT) ((⊤ : CoPset) \ E) ∗ A v1 v2)
      ⊢ refines L E e1 e2 A := by
  iintro HFA
  iapply refines_ret_na hv1 hv2
  iintro Hnais
  imod HFA with ⟨HF, HA⟩
  imodintro
  have hun := (Iris.NonAtomicInvariant.own_union (GF := GF)
    (p := MicrometerRGS.nais (rT := rT) GF) (E2 := (⊤ : CoPset) \ E)
    LawfulSet.disjoint_diff_right).mpr
  rw [LawfulSet.subset_union_diff (s₂ := (⊤ : CoPset)) (fun _ _ => CoPset.mem_full)] at hun
  iframe HA
  iapply hun
  iframe Hnais HF

theorem refines_ret {e1 e2 : Exp rT} {v1 v2 : Val rT} {A : lrel rT GF}
    (hv1 : e1 = v1.1) (hv2 : e2 = v2.1) :
    iprop(|={⊤}=> A v1 v2) ⊢ refines L (⊤ : CoPset) e1 e2 A := by
  iintro HA
  iapply refines_ret_na hv1 hv2
  iintro Hna
  imod HA
  imodintro
  iframe Hna HA

instance elim_fupd_refines {io : InOut} (E : CoPset) (e t : Exp rT)
    (P : IProp GF) (A : lrel rT GF) :
    ElimModal True false io false (iprop(|={⊤}=> P)) P
      (refines L E e t A) (refines L E e t A) where
  elim_modal _ := calc
    _ ⊢ (|={⊤}=> P) ∗ (P -∗ refines L E e t A) := sep_mono_left intuitionisticallyIf_elim
    _ ⊢ |={⊤}=> P ∗ (P -∗ refines L E e t A)   := fupd_frame_right
    _ ⊢ |={⊤}=> refines L E e t A              := BIFUpdate.mono wand_elim_right
    _ ⊢ refines L E e t A                      := fupd_refines

instance elim_bupd_refines {io : InOut} (E : CoPset) (e t : Exp rT)
    (P : IProp GF) (A : lrel rT GF) :
    ElimModal True false io false (iprop(|==> P)) P
      (refines L E e t A) (refines L E e t A) where
  elim_modal h :=
    (sep_mono_left (intuitionisticallyIf_mono BIUpdateFUpdate.fupd_of_bupd)).trans
      ((elim_fupd_refines (io := io) E e t P A).elim_modal h)

instance is_except_0_refines (E : CoPset) (e t : Exp rT) (A : lrel rT GF) :
    IsExcept0 (refines L E e t A) where
  is_except0 := calc
    ◇ refines L E e t A ⊢ ◇ |={⊤}=> refines L E e t A := except0_mono fupd_intro
    _ ⊢ |={⊤}=> refines L E e t A := BIFUpdate.except0
    _ ⊢ refines L E e t A := fupd_refines

theorem refines_na_update {E F : CoPset} {e1 e2 : Exp rT} {A : lrel rT GF} :
    iprop(naOwnP (rT := rT) E ={⊤}=∗ naOwnP (rT := rT) F ∗ refines L F e1 e2 A)
      ⊢ refines L E e1 e2 A := by
  unfold refines
  iintro Hupd %K %b Hj Hna Herr Hpos
  iapply MicrometerWpGS.fupd_wp
  imod Hupd $$ Hna with ⟨Hna, HR⟩
  imodintro
  iapply HR $$ %K %b Hj Hna Herr Hpos

theorem refines_na_alloc {P : IProp GF} (N : Namespace) {E : CoPset} {e1 e2 : Exp rT}
    {A : lrel rT GF} :
    iprop% (▷ P) ∗ (naInvP (rT := rT) N P -∗ refines L E e1 e2 A)
      ⊢ refines L E e1 e2 A := by
  iintro ⟨HP, Hcont⟩
  iapply fupd_refines
  imod Iris.NonAtomicInvariant.inv_alloc $$ [$HP] with Hinv
  imodintro
  iapply Hcont $$ Hinv

theorem refines_na_inv {P : IProp GF} {E : CoPset} {N : Namespace} {e1 e2 : Exp rT} {A : lrel rT GF}
    (HNE : (↑N : CoPset) ⊆ E) :
    iprop% naInvP (rT := rT) N P ∗
        ((▷ P) ∗ naCloseP (rT := rT) P N E -∗ refines L (E \ ↑N) e1 e2 A)
      ⊢ refines L E e1 e2 A := by
  iintro ⟨Hinv, IH⟩
  iapply refines_na_update
  iintro Hnais
  imod Iris.NonAtomicInvariant.inv_acc CoPset.subseteq_top HNE $$ Hinv Hnais
    with ⟨HP, Hnais, Hclose⟩
  imodintro
  iframe Hnais
  iapply IH $$ [$HP $Hclose]

theorem refines_na_close {P : IProp GF} {E : CoPset} {N : Namespace} {e1 e2 : Exp rT}
    {A : lrel rT GF} :
    iprop% (▷ P) ∗ naCloseP (rT := rT) P N E ∗ refines L E e1 e2 A
      ⊢ refines L (E \ ↑N) e1 e2 A := by
  iintro ⟨HP, Hclose, IH⟩
  iapply refines_na_update
  iintro HownFN
  imod Hclose $$ [$HP $HownFN] with HownF
  imodintro
  iframe

end Monadic

end ProbLang
