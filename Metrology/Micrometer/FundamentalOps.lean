module

public import Metrology.Micrometer.FundamentalCompat
import Metrology.ProbLang.Syntax.Notation

@[expose] public section

/-! Compatibility of `bin_log_related` with operators, matching and the stateful fragment. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.MicrometerWpGS
  GradedLifting

namespace ProbLang

open Cslib Exp

section Fundamental
variable {rT : Type} [LawfulProbLangℝ rT] {hlc : HasLC} {B : Type} [AddCommMonoid B]
  [PartialOrder B] [OrderTop B] {L : GradedLifting.{0} B} {GF : BundledGFunctors}
  [IR : MicrometerRGS rT hlc GF] [BudgetCreditGS B GF]

theorem pat_match_lit {Δ : TyEnv rT GF} {l l' : BaseLit rT} {v v' : Val rT}
    (hv : v = .ofBaseLit l') (hv' : v' = .ofBaseLit l') (hll : l = l' ∨ ¬ (l == l') = true) :
    ⊢@{IProp GF} (∃ (b b' : Val rT), ⌜Pat.tryMatch (.lit l) v.1 = some b.1 ∧
      Pat.tryMatch (.lit l) v'.1 = some b'.1⌝ ∗ (interp L Ty.unit Δ).car b b') ∨
      ⌜Pat.tryMatch (.lit l) v.1 = none ∧ Pat.tryMatch (.lit l) v'.1 = none⌝ := by
  subst hv hv'
  rcases hll with rfl | hne
  · ileft
    iexists (.unit : Val _), (.unit : Val _)
    isplitr
    · ipureintro; exact ⟨Pat.tryMatch_lit_eq l, Pat.tryMatch_lit_eq l⟩
    rw [interp_unit]
    iapply lrel_unit_lit
  · iright
    ipureintro
    exact ⟨Pat.tryMatch_lit_ne hne, Pat.tryMatch_lit_ne hne⟩

theorem pat_match_related {Δ : TyEnv rT GF} {τs τb : Ty} {p : Pat rT}
    (Hpat : PatTyped τs p τb) (v v' : Val rT) :
    (interp L τs Δ).car v v' ⊢@{IProp GF}
      (∃ (b b' : Val rT), ⌜Pat.tryMatch p v.1 = some b.1 ∧ Pat.tryMatch p v'.1 = some b'.1⌝ ∗
        (interp L τb Δ).car b b') ∨
      ⌜Pat.tryMatch p v.1 = none ∧ Pat.tryMatch p v'.1 = none⌝ := by
  induction Hpat generalizing v v' with
  | @wildcard τ =>
    iintro Hvv
    ileft
    iexists v, v'
    isplitr
    · ipureintro; simp [Pat.tryMatch]
    iexact Hvv
  | @lit_int z =>
    rw [interp_int]
    iintro Hv
    iunfold lrel_int at Hv
    icases Hv with ⟨%n, %h⟩
    have hll : (BaseLit.int z : BaseLit rT) = .int n ∨
        ¬ ((BaseLit.int z : BaseLit rT) == .int n) = true := by
      by_cases hzn : z = n <;> simp [hzn]
    iapply pat_match_lit h.1 h.2 hll
  | @lit_bool b =>
    rw [interp_bool]
    iintro Hv
    iunfold lrel_bool at Hv
    icases Hv with ⟨%b', %h⟩
    have hll : (BaseLit.bool b : BaseLit rT) = .bool b' ∨
        ¬ ((BaseLit.bool b : BaseLit rT) == .bool b') = true := by
      by_cases hbb : b = b' <;> simp [hbb]
    iapply pat_match_lit h.1 h.2 hll
  | lit_unit =>
    show iprop(⌜v = .unit ∧ v' = .unit⌝) ⊢ _
    iintro %h
    iapply pat_match_lit h.1 h.2 (.inl rfl)
  | @pair τ1 τ2 p1 p2 b1 b2 Hpat1 Hpat2 ih1 ih2 =>
    rw [interp_prod]
    iintro Hv
    iunfold lrel_prod at Hv
    icases Hv with ⟨%a1, %a2, %c1, %c2, %hv1, %hv2, HA, HC⟩
    icases ih1 a1 a2 $$ HA with (⟨%ba, %ba', %hra, HBa⟩ | %hna)
    · icases ih2 c1 c2 $$ HC with (⟨%bb, %bb', %hrb, HBb⟩ | %hnb)
      · ileft
        iexists .pair ba bb, .pair ba' bb'
        isplitr
        · ipureintro; simp [Pat.tryMatch, hv1, hv2, hra.1, hra.2, hrb.1, hrb.2]
        rw [interp_prod]
        unfold lrel_prod
        iexists ba, ba', bb, bb'
        isplitr; · ipureintro; rfl
        isplitr; · ipureintro; rfl
        iframe HBa HBb
      · iright
        ipureintro
        simp [Pat.tryMatch, hv1, hv2, hra.1, hra.2, hnb.1, hnb.2]
    · iright
      ipureintro
      simp [Pat.tryMatch, hv1, hv2, hna.1, hna.2]
  | @inl τ1 τ2 p b Hpat' ih =>
    rw [interp_sum]
    iintro Hv
    iunfold lrel_sum at Hv
    icases Hv with ⟨%w1, %w2, Hcase⟩
    icases Hcase with (⟨%hv1, %hv2, HA⟩ | ⟨%hv1, %hv2, HB⟩)
    · icases ih w1 w2 $$ HA with (⟨%bb, %bb', %hr, Hbnd⟩ | %hn)
      · ileft
        iexists bb, bb'
        isplitr
        · ipureintro; simp [Pat.tryMatch, hv1, hv2, hr.1, hr.2]
        iexact Hbnd
      · iright
        ipureintro
        simp [Pat.tryMatch, hv1, hv2, hn.1, hn.2]
    · iright
      ipureintro
      simp [Pat.tryMatch, hv1, hv2]
  | @inr τ1 τ2 p b Hpat' ih =>
    rw [interp_sum]
    iintro Hv
    iunfold lrel_sum at Hv
    icases Hv with ⟨%w1, %w2, Hcase⟩
    icases Hcase with (⟨%hv1, %hv2, HA⟩ | ⟨%hv1, %hv2, HB⟩)
    · iright
      ipureintro
      simp [Pat.tryMatch, hv1, hv2]
    · icases ih w1 w2 $$ HB with (⟨%bb, %bb', %hr, Hbnd⟩ | %hn)
      · ileft
        iexists bb, bb'
        isplitr
        · ipureintro; simp [Pat.tryMatch, hv1, hv2, hr.1, hr.2]
        iexact Hbnd
      · iright
        ipureintro
        simp [Pat.tryMatch, hv1, hv2, hn.1, hn.2]

section Steps
variable [L.IsLawful] [L.IsTopAbsorbing]

/-! ## Operators

`lrel_int`, `lrel_bool` and `lrel_real` relate exactly equal literals, so each operator
lemma binds the operands (`refines_{un,bin}op_bind`) and takes one pure step. -/

theorem refines_binop_val (op : BinOp) (w1 w2 : Val rT) {l : BaseLit rT}
    {A : lrel rT GF} (heval : op.eval w1.1 w2.1 = some (.lit l))
    (HA : ⊢@{IProp GF} A.car (.ofBaseLit l) (.ofBaseLit l)) :
    ⊢@{IProp GF} refines L ⊤ (.binop op w1.1 w2.1) (.binop op w1.1 w2.1) A :=
  refines_binop_pure op _ _ _ w1.2 w2.2 IsVal.lit heval HA

theorem refines_unop_val (op : UnOp) (w : Val rT) {l : BaseLit rT} {A : lrel rT GF}
    (heval : op.eval w.1 = some (.lit l)) (HA : ⊢@{IProp GF} A.car (.ofBaseLit l) (.ofBaseLit l)) :
    ⊢@{IProp GF} refines L ⊤ (.unop op w.1) (.unop op w.1) A :=
  refines_unop_pure op _ _ w.2 IsVal.lit heval HA

theorem refines_binop_bind (op : BinOp) {ι : Type _} (V : ι → Val rT) {A C : lrel rT GF}
    {e1 e2 e1' e2' : Exp rT} (hA : ∀ v v', A.car v v' ⊢ ∃ i, ⌜v = V i ∧ v' = V i⌝) : iprop%
    refines L ⊤ e1 e1' A ⊢
    refines L ⊤ e2 e2' A -∗
    (∀ i1 i2, refines L ⊤ (.binop op (V i1).1 (V i2).1) (.binop op (V i1).1 (V i2).1) C) -∗
    refines L ⊤ (.binop op e1 e2) (.binop op e1' e2') C := by
  iintro IH1 IH2 Hcont
  rw [show binop op e1 e2 = Ectx.fill [EctxItem.binopR op e1] e2 from rfl,
    show binop op e1' e2' = Ectx.fill [EctxItem.binopR op e1'] e2' from rfl]
  iapply refines_bind [EctxItem.binopR op e1] [EctxItem.binopR op e1'] $$ IH2
  iintro %v2 %v2' Hv2
  icases hA v2 v2' $$ Hv2 with ⟨%i2, %hv2, %hv2'⟩
  rw [show Ectx.fill [EctxItem.binopR op e1] v2.1 = binop op e1 v2.1 from rfl,
    show Ectx.fill [EctxItem.binopR op e1'] v2'.1 = binop op e1' v2'.1 from rfl, hv2, hv2',
    show binop op e1 (V i2).1 = Ectx.fill [EctxItem.binopL op (V i2)] e1 from rfl,
    show binop op e1' (V i2).1 = Ectx.fill [EctxItem.binopL op (V i2)] e1' from rfl]
  iapply refines_bind [EctxItem.binopL op (V i2)] [EctxItem.binopL op (V i2)] $$ IH1
  iintro %v1 %v1' Hv1
  icases hA v1 v1' $$ Hv1 with ⟨%i1, %hv1, %hv1'⟩
  rw [show Ectx.fill [EctxItem.binopL op (V i2)] v1.1 = binop op v1.1 (V i2).1 from rfl,
    show Ectx.fill [EctxItem.binopL op (V i2)] v1'.1 = binop op v1'.1 (V i2).1 from rfl, hv1, hv1']
  iapply Hcont $$ %i1 %i2

theorem refines_unop_bind (op : UnOp) {ι : Type _} (V : ι → Val rT) {A C : lrel rT GF}
    {e e' : Exp rT} (hA : ∀ v v', A.car v v' ⊢ ∃ i, ⌜v = V i ∧ v' = V i⌝) : iprop%
    refines L ⊤ e e' A ⊢
    (∀ i, refines L ⊤ (.unop op (V i).1) (.unop op (V i).1) C) -∗
    refines L ⊤ (.unop op e) (.unop op e') C := by
  iintro IH Hcont
  rw [show unop op e = Ectx.fill [EctxItem.unop op] e from rfl,
    show unop op e' = Ectx.fill [EctxItem.unop op] e' from rfl]
  iapply refines_bind [EctxItem.unop op] [EctxItem.unop op] $$ IH
  iintro %v %v' Hv
  icases hA v v' $$ Hv with ⟨%i, %hv, %hv'⟩
  rw [show Ectx.fill [EctxItem.unop op] v.1 = unop op v.1 from rfl,
    show Ectx.fill [EctxItem.unop op] v'.1 = unop op v'.1 from rfl, hv, hv']
  iapply Hcont $$ %i

theorem bin_log_related_int_binop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (op : BinOp)
    {e1 e2 e1' e2' : Exp rT} {τ : Ty} (Hres : op.intResTy = some τ) : iprop%
    bin_log_related_ty L ⊤ Δ Γ e1 e1' .int ⊢
    bin_log_related_ty L ⊤ Δ Γ e2 e2' .int -∗
    bin_log_related_ty L ⊤ Δ Γ (.binop op e1 e2) (.binop op e1' e2') τ :=
  bin_log_related_lift2 (fun σ => substMap_binop σ op) fun _ _ _ _ => by
    rw [interp_int]
    iintro IH1 IH2
    iapply refines_binop_bind op Val.int (fun _ _ => .rfl) $$ IH1 IH2
    iintro %n1 %n2
    cases op <;> simp [BinOp.intResTy] at Hres <;> subst Hres
    all_goals first
      | (rw [interp_int]; iapply refines_binop_val _ _ _ rfl (lrel_int_lit _))
      | (rw [interp_bool]; iapply refines_binop_val _ _ _ rfl (lrel_bool_lit _))

theorem bin_log_related_bool_binop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (op : BinOp)
    {e1 e2 e1' e2' : Exp rT} {τ : Ty} (Hres : op.boolResTy = some τ) : iprop%
    bin_log_related_ty L ⊤ Δ Γ e1 e1' .bool ⊢
    bin_log_related_ty L ⊤ Δ Γ e2 e2' .bool -∗
    bin_log_related_ty L ⊤ Δ Γ (.binop op e1 e2) (.binop op e1' e2') τ :=
  bin_log_related_lift2 (fun σ => substMap_binop σ op) fun _ _ _ _ => by
    rw [interp_bool]
    iintro IH1 IH2
    iapply refines_binop_bind op Val.bool (fun _ _ => .rfl) $$ IH1 IH2
    iintro %b1 %b2
    cases op <;> simp [BinOp.boolResTy] at Hres <;> subst Hres
    all_goals (rw [interp_bool]; iapply refines_binop_val _ _ _ rfl (lrel_bool_lit _))

theorem bin_log_related_int_unop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (op : UnOp)
    {e e' : Exp rT} {τ : Ty} (Hres : op.intResTy = some τ) :
    bin_log_related_ty L ⊤ Δ Γ e e' .int ⊢
    bin_log_related_ty L ⊤ Δ Γ (.unop op e) (.unop op e') τ :=
  bin_log_related_lift1 (fun σ => substMap_unop σ op) fun _ _ => by
    rw [interp_int]
    iintro IH
    iapply refines_unop_bind op Val.int (fun _ _ => .rfl) $$ IH
    iintro %n
    cases op <;> simp [UnOp.intResTy] at Hres <;> subst Hres
    all_goals first
      | (rw [interp_int]; iapply refines_unop_val _ _ rfl (lrel_int_lit _))
      | (rw [interp_real]; iapply refines_unop_val _ _ rfl (lrel_real_lit _))

theorem bin_log_related_bool_unop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (op : UnOp)
    {e e' : Exp rT} {τ : Ty} (Hres : op.boolResTy = some τ) :
    bin_log_related_ty L ⊤ Δ Γ e e' .bool ⊢
    bin_log_related_ty L ⊤ Δ Γ (.unop op e) (.unop op e') τ :=
  bin_log_related_lift1 (fun σ => substMap_unop σ op) fun _ _ => by
    rw [interp_bool]
    iintro IH
    iapply refines_unop_bind op Val.bool (fun _ _ => .rfl) $$ IH
    iintro %b
    cases op <;> simp [UnOp.boolResTy] at Hres
    subst Hres
    rw [interp_bool]
    iapply refines_unop_val _ _ rfl (lrel_bool_lit _)

/-! ## The real fragment -/

theorem bin_log_related_real_unop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (op : UnOp)
    {e e' : Exp rT} {τ : Ty} (Hres : op.realResTy = some τ) :
    bin_log_related_ty L ⊤ Δ Γ e e' .real ⊢
    bin_log_related_ty L ⊤ Δ Γ (.unop op e) (.unop op e') τ :=
  bin_log_related_lift1 (fun σ => substMap_unop σ op) fun _ _ => by
    rw [interp_real]
    iintro IH
    iapply refines_unop_bind op Val.real (fun _ _ => .rfl) $$ IH
    iintro %r
    cases op <;> simp [UnOp.realResTy] at Hres <;> subst Hres
    all_goals (rw [interp_real]; iapply refines_unop_val _ _ rfl (lrel_real_lit _))

theorem bin_log_related_real_binop (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) (op : BinOp)
    {e1 e2 e1' e2' : Exp rT} {τ : Ty} (Hres : op.realResTy = some τ) : iprop%
    bin_log_related_ty L ⊤ Δ Γ e1 e1' .real ⊢
    bin_log_related_ty L ⊤ Δ Γ e2 e2' .real -∗
    bin_log_related_ty L ⊤ Δ Γ (.binop op e1 e2) (.binop op e1' e2') τ :=
  bin_log_related_lift2 (fun σ => substMap_binop σ op) fun _ _ _ _ => by
    rw [interp_real]
    iintro IH1 IH2
    iapply refines_binop_bind op Val.real (fun _ _ => .rfl) $$ IH1 IH2
    iintro %r1 %r2
    cases op <;> simp [BinOp.realResTy] at Hres <;> subst Hres
    all_goals first
      | (rw [interp_real]; iapply refines_binop_val _ _ _ rfl (lrel_real_lit _))
      | (rw [interp_bool]; iapply refines_binop_val _ _ _ rfl (lrel_bool_lit _))

/-! ## Equality and pattern matching -/

theorem bin_log_related_unboxed_eq (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e1 e2 e1' e2' : Exp rT}
    {τ : Ty} (HUnboxed : UnboxedType τ) : iprop%
    bin_log_related_ty L ⊤ Δ Γ e1 e1' τ ⊢
    bin_log_related_ty L ⊤ Δ Γ e2 e2' τ -∗
    bin_log_related_ty L ⊤ Δ Γ (.binop .eq e1 e2) (.binop .eq e1' e2') .bool := by
  unfold bin_log_related_ty bin_log_related
  iintro IH1 IH2 %vs #Hvs
  rw [substMap_binop, substMap_binop, ← Ectx.fill_binopR .eq (substMap vs.fst e1),
    ← Ectx.fill_binopR .eq (substMap vs.snd e1')]
  iapply refines_bind [EctxItem.binopR .eq (substMap vs.fst e1)]
    [EctxItem.binopR .eq (substMap vs.snd e1')] $$ (IH2 $$ %vs Hvs)
  iintro %v2 %v2' #Hv2
  rw [show Ectx.fill [EctxItem.binopR .eq (substMap vs.fst e1)] v2.1 =
      Ectx.fill [EctxItem.binopL .eq v2] (substMap vs.fst e1) from rfl,
    show Ectx.fill [EctxItem.binopR .eq (substMap vs.snd e1')] v2'.1 =
      Ectx.fill [EctxItem.binopL .eq v2'] (substMap vs.snd e1') from rfl]
  iapply refines_bind [EctxItem.binopL .eq v2] [EctxItem.binopL .eq v2'] $$ (IH1 $$ %vs Hvs)
  iintro %v1 %v1' #Hv1
  ihave Heq : iprop(|={⊤}=> ⌜v1 = v2 ↔ v1' = v2'⌝) $$ [Hv1 Hv2]
  · iapply unboxed_type_eq HUnboxed $$ Hv1 Hv2
  icases unboxed_type_lit_shape HUnboxed $$ Hv1 with ⟨%l1, %l1', %hv1eq, %hv1'eq⟩
  icases unboxed_type_lit_shape HUnboxed $$ Hv2 with ⟨%l2, %l2', %hv2eq, %hv2'eq⟩
  rw [show Ectx.fill [EctxItem.binopL .eq v2] v1.1 = .binop .eq v1.1 v2.1 from rfl,
    show Ectx.fill [EctxItem.binopL .eq v2'] v1'.1 = .binop .eq v1'.1 v2'.1 from rfl,
    hv1eq, hv2eq, hv1'eq, hv2'eq]
  imod Heq with %heqIff
  have hval : ∀ {w w' : Val rT} {m m' : BaseLit rT}, w.1 = .lit m → w'.1 = .lit m' →
      (w = w' ↔ m = m') := fun hw hw' => by simp [Val.ext_iff, hw, hw']
  have hdec : decide (l1 = l2) = decide (l1' = l2') := decide_eq_decide.mpr <| calc
    l1 = l2 ↔ v1 = v2 := (hval hv1eq hv2eq).symm
    _ ↔ v1' = v2' := heqIff
    _ ↔ l1' = l2' := hval hv1'eq hv2'eq
  have hφ : ∀ l l' : BaseLit rT, (Exp.lit l).isValue ∧ (Exp.lit l').isValue ∧
      BinOp.eval .eq (.lit l) (.lit l') = some pl(#(.bool (decide (l = l')))) :=
    fun _ _ => ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, by rw [← Bool.beq_eq_decide_eq]; rfl⟩
  rw [Ectx.eq_fill_nil (.binop .eq (.lit l1) (.lit l2)),
    Ectx.eq_fill_nil (.binop .eq (.lit l1') (.lit l2'))]
  iapply refines_pure_l (hφ l1 l2)
  inext
  iapply refines_pure_r (hφ l1' l2')
  simp only [Ectx.fill_nil]
  iapply refines_ret (v1 := .bool (decide (l1 = l2))) (v2 := .bool (decide (l1' = l2'))) rfl rfl
  imodintro
  rw [interp_bool, hdec]
  iapply lrel_bool_lit _

theorem bin_log_related_scrut (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT}
    {p : Pat rT} {τs τb : Ty} (Hpat : PatTyped τs p τb) :
    bin_log_related_ty L ⊤ Δ Γ e e' τs ⊢
    bin_log_related_ty L ⊤ Δ Γ (.scrut e p) (.scrut e' p) (.sum τb .unit) := by
  unfold bin_log_related_ty bin_log_related
  iintro IH %vs #Hvs
  rw [substMap_scrut, substMap_scrut, ← Ectx.fill_scrut p, ← Ectx.fill_scrut p]
  iapply refines_bind [EctxItem.scrut p] [EctxItem.scrut p] $$ (IH $$ %vs Hvs)
  iintro %v %v' #Hv
  rw [show Ectx.fill [EctxItem.scrut p] v.1 = Ectx.fill [] (.scrut v.1 p) from rfl,
    show Ectx.fill [EctxItem.scrut p] v'.1 = Ectx.fill [] (.scrut v'.1 p) from rfl]
  icases pat_match_related Hpat v v' $$ Hv with (⟨%bb, %bb', %hr, Hbnd⟩ | %hn)
  · iapply refines_pure_l (Hex := pureExec_scrut_some) ⟨v.2.toIsValue, hr.1⟩
    inext
    iapply refines_pure_r (Hex := pureExec_scrut_some) ⟨v'.2.toIsValue, hr.2⟩
    simp only [Ectx.fill_nil]
    iapply refines_ret (v1 := .inl bb) (v2 := .inl bb') rfl rfl
    imodintro
    rw [interp_sum, interp_unit]
    unfold lrel_sum
    iexists bb, bb'
    ileft
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; rfl
    iexact Hbnd
  · iapply refines_pure_l (Hex := pureExec_scrut_none) ⟨v.2.toIsValue, hn.1⟩
    inext
    iapply refines_pure_r (Hex := pureExec_scrut_none) ⟨v'.2.toIsValue, hn.2⟩
    simp only [Ectx.fill_nil]
    iapply refines_ret (v1 := .inr .unit) (v2 := .inr .unit) rfl rfl
    imodintro
    rw [interp_sum, interp_unit]
    unfold lrel_sum
    iexists (.unit : Val _), (.unit : Val _)
    iright
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; rfl
    iapply lrel_unit_lit

section Prim
variable [CanonicallyOrderedAdd B] [L.IsReflexive] [L.IsSupportLocal] [L.HasBind]

theorem bin_log_related_urand (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) :
    ⊢@{IProp GF} bin_log_related_ty L ⊤ Δ Γ .urand .urand .real := by
  unfold bin_log_related_ty bin_log_related
  iintro %vs -
  rw [substMap_urand, substMap_urand, interp_real,
    show (Exp.urand : Exp rT) = Ectx.fill [] Exp.urand from rfl]
  iapply refines_couple_urands_lr id (MeasureTheory.MeasurePreserving.id _)
  iintro %r -
  simp only [id_eq, Ectx.fill_nil]
  iapply refines_ret (v1 := .real r) (v2 := .real r) rfl rfl
  imodintro
  iapply lrel_real_lit r

/-! ## Heap and tape cases -/

theorem bin_log_related_alloc (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ : Ty} :
    bin_log_related_ty L ⊤ Δ Γ e e' τ ⊢
    bin_log_related_ty L ⊤ Δ Γ (.alloc e) (.alloc e') (.ref τ) :=
  bin_log_related_lift1 substMap_alloc fun _ _ => refines_alloc

theorem bin_log_related_load (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} {τ : Ty} :
    bin_log_related_ty L ⊤ Δ Γ e e' (.ref τ) ⊢ bin_log_related_ty L ⊤ Δ Γ (.load e) (.load e') τ :=
  bin_log_related_lift1 substMap_load fun _ _ => refines_load

theorem bin_log_related_store (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e1 e2 e1' e2' : Exp rT}
    {τ : Ty} : iprop%
    bin_log_related_ty L ⊤ Δ Γ e1 e1' (.ref τ) ⊢
    bin_log_related_ty L ⊤ Δ Γ e2 e2' τ -∗
    bin_log_related_ty L ⊤ Δ Γ (.store e1 e2) (.store e1' e2') .unit :=
  bin_log_related_lift2 substMap_store fun _ _ _ _ => refines_store

theorem bin_log_related_alloctape (Δ : TyEnv rT GF) (Γ : RelCtx rT GF) {e e' : Exp rT} :
    bin_log_related_ty L ⊤ Δ Γ e e' .int ⊢ bin_log_related_ty L ⊤ Δ Γ (.tape e) (.tape e') .tape :=
  bin_log_related_lift1 substMap_tape fun _ _ => refines_alloctape

theorem bin_log_related_rand_tape (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e1 e1' e2 e2' : Exp rT} : iprop%
    bin_log_related_ty L ⊤ Δ Γ e1 e1' .int ⊢
    bin_log_related_ty L ⊤ Δ Γ e2 e2' .tape -∗
    bin_log_related_ty L ⊤ Δ Γ (.rand e1 e2) (.rand e1' e2') .int :=
  bin_log_related_lift2 substMap_rand fun _ _ _ _ => refines_rand_tape_int

theorem bin_log_related_rand_unit (Δ : TyEnv rT GF) (Γ : RelCtx rT GF)
    {e1 e1' e2 e2' : Exp rT} : iprop%
    bin_log_related_ty L ⊤ Δ Γ e1 e1' .int ⊢
    bin_log_related_ty L ⊤ Δ Γ e2 e2' .unit -∗
    bin_log_related_ty L ⊤ Δ Γ (.rand e1 e2) (.rand e1' e2') .int :=
  bin_log_related_lift2 substMap_rand fun t1 t2 t1' _ => by
    rw [interp_int, interp_unit]
    iintro IH1 IH2
    rw [← Ectx.fill_randR t1, ← Ectx.fill_randR t1']
    iapply refines_bind [EctxItem.randR t1] [EctxItem.randR t1'] $$ IH2
    iintro %v2 %v2' Hu
    iunfold lrel_unit at Hu
    icases Hu with ⟨%hv2, %hv2'⟩
    rw [hv2, hv2',
      show Ectx.fill [EctxItem.randR t1] pl(#(.unit)) = Ectx.fill [EctxItem.randL .unit] t1
        from rfl,
      show Ectx.fill [EctxItem.randR t1'] pl(#(.unit)) = Ectx.fill [EctxItem.randL .unit] t1'
        from rfl]
    iapply refines_rand_unit_int $$ IH1

end Prim

end Steps

end Fundamental

end ProbLang
