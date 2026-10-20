module

public import Metrology.ProbLang.CoreMeasures.Exp
public import Metrology.ProbLang.CoreMeasures.Val
public import Metrology.ProbLang.CoreMeasures.EctxItem

meta import Metrology.ProbLang.CoreMeasures.ArmTactics

@[expose] public section

/-!
# Measurability of recursive functions on `Exp`

Most proofs apply `Exp.measurable_struct_rec(_param)` with one combinator per constructor
and close the side goals by `rfl` or `fun_prop`.
-/

noncomputable section ProbLangMeasures

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

namespace ProbLang.Exp

/-! ### `Exp.height` -/

theorem height.measurable [MeasurableSpace rT] :
    Measurable (Exp.height : Exp rT → Nat) := by
  apply_arms measurable_struct_rec (f := Exp.height)

/-! ### `Exp.subst` -/

theorem subst.measurable_fixed [MeasurableSpace rT] (x : Var) (sub : Exp rT) :
    Measurable (fun e : Exp rT => Exp.subst e x sub) := by
  apply_arms measurable_struct_rec (f := fun e => Exp.subst e x sub)

theorem subst.measurable [MeasurableSpace rT] :
    Measurable (fun (q : (Var × Exp rT) × Exp rT) => Exp.subst q.2 q.1.1 q.1.2) := by
  apply_arms measurable_struct_rec_param
    (f := fun (b : Var × Exp rT) (e : Exp rT) => Exp.subst e b.1 b.2)
  case h_fvar =>
    have : Function.uncurry (fun (b : Var × Exp rT) (y : Var) =>
              if b.1 = y then b.2 else (Exp.fvar y : Exp rT))
        = (fun (q : (Var × Var) × Exp rT) =>
              if q.1.1 = q.1.2 then q.2 else Exp.fvar q.1.2)
            ∘ (fun (p : (Var × Exp rT) × Var) => ((p.1.1, p.2), p.1.2)) := by
      funext ⟨⟨x, sub⟩, y⟩; rfl
    rw [this]
    have h1 : Measurable (fun (q : (Var × Var) × Exp rT) =>
                if q.1.1 = q.1.2 then q.2 else (Exp.fvar q.1.2 : Exp rT)) := by
      apply measurable_from_prod_countable_right
      intro xy
      by_cases hxy : xy.1 = xy.2
      · simp only [hxy, ite_true]; exact measurable_id
      · simp only [hxy, ite_false]; exact measurable_const
    exact h1.comp (by fun_prop : Measurable
      (fun (p : (Var × Exp rT) × Var) => ((p.1.1, p.2), p.1.2)))

/-! ### `Exp.isValueR`, `Exp.lcb`, `Exp.fv` -/

theorem isValueR.measurable [MeasurableSpace rT] :
    Measurable (Exp.isValueR : Exp rT → Prop) := by
  apply_arms measurable_struct_rec (f := Exp.isValueR)

theorem lcb.measurable [MeasurableSpace rT] :
    Measurable (fun (q : Nat × Exp rT) => Exp.lcb q.1 q.2) := by
  apply_arms measurable_struct_rec_param
    (f := fun (b : Nat) (e : Exp rT) => Exp.lcb b e)
    (t_lam   := fun b => b + 1)
    (t_fix   := fun b => b + 1)

theorem lcb_zero.measurableSet [MeasurableSpace rT] :
    MeasurableSet {e : Exp rT | Exp.lcb 0 e = true} := by
  have hm : Measurable (fun e : Exp rT => Exp.lcb 0 e) :=
    lcb.measurable.comp (by fun_prop : Measurable (fun e : Exp rT => ((0 : Nat), e)))
  exact hm (measurableSet_singleton true)

/-- The discrete measurable space on finite sets of variables. -/
instance : MeasurableSpace (Finset Var) := ⊤

theorem fv.measurable [MeasurableSpace rT] : Measurable (Exp.fv : Exp rT → Finset Var) := by
  apply_arms measurable_struct_rec (f := Exp.fv)

/-! ### `UnOp.eval` -/

/-- Every singleton of `UnOp` is measurable. -/
instance instMeasurableSingletonClassUnOp : MeasurableSingletonClass UnOp where
  measurableSet_singleton _ := trivial

/-- Every singleton of `BinOp` is measurable. -/
instance instMeasurableSingletonClassBinOp : MeasurableSingletonClass BinOp where
  measurableSet_singleton _ := trivial

private theorem measurable_of_lit_only [MeasurableSpace rT] {α : Type _} [MeasurableSpace α]
    {g : Exp rT → α} (z : α) {f : BaseLit rT → α} (hf : Measurable f)
    (hg : ∀ v, g v = match v with | .lit l => f l | _ => z) : Measurable g := by
  have hrw : g = fun v => Exp.casesOn (motive := fun _ => α) v
      (fun _ => z) (fun _ => z) f (fun _ => z) (fun _ => z) (fun _ _ => z)
      (fun _ _ => z) (fun _ _ _ => z) (fun _ _ _ => z)
      (fun _ _ => z) (fun _ => z) (fun _ => z) (fun _ => z) (fun _ => z)
      (fun _ _ _ => z) (fun _ => z) (fun _ => z) (fun _ _ => z)
      (fun _ => z) (fun _ _ => z) z z (fun _ _ => z) := by
    funext v; rw [hg]; cases v <;> rfl
  rw [hrw]
  refine Exp.measurable_casesOn
    (c_bvar := fun _ => z) (c_fvar := fun _ => z) (c_lit := f)
    (c_lam := fun _ => z) (c_fix := fun _ => z) (c_app := fun _ => z)
    (c_unop := fun _ => z) (c_binop := fun _ => z) (c_cond := fun _ => z)
    (c_pair := fun _ => z) (c_fst := fun _ => z) (c_snd := fun _ => z)
    (c_inl := fun _ => z) (c_inr := fun _ => z) (c_case := fun _ => z)
    (c_alloc := fun _ => z) (c_load := fun _ => z) (c_store := fun _ => z)
    (c_tape := fun _ => z) (c_rand := fun _ => z) (c_fail := fun _ => z)
    (c_urand := fun _ => z) (c_scrut := fun _ => z)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact hf
  all_goals exact measurable_const

theorem UnOp.eval_op_measurable [LawfulProbLangℝ rT] (op : UnOp) :
    Measurable (fun v : Exp rT => UnOp.eval op v) := by
  cases op with
  | neg =>
    refine measurable_of_lit_only none
      (f := fun l => BaseLit.casesOn (motive := fun _ => Option (Exp rT)) l
        (fun _ => none) (fun b => some (Exp.lit (.bool ¬b))) none
        (fun _ => none) (fun _ => none) (fun _ => none)) ?_
      fun v => by
        cases v <;> simp [UnOp.eval]
        rename_i b; cases b <;> simp
    apply BaseLit.measurable_casesOn
      (c_int := fun _ => none) (c_bool := fun b => some (Exp.lit (.bool ¬b)))
      (c_unit := fun _ => none) (c_loc := fun _ => none) (c_lbl := fun _ => none)
      (c_real := fun _ => none)
    exact measurable_const
  | minus =>
    refine measurable_of_lit_only none
      (f := fun l => BaseLit.casesOn (motive := fun _ => Option (Exp rT)) l
        (fun z => some (Exp.lit (.int z.neg))) (fun _ => none) none
        (fun _ => none) (fun _ => none)
        (fun r => some (Exp.lit (.real (ProbLangℝ.realNeg r))))) ?_
      fun v => by
        cases v <;> simp [UnOp.eval]
        rename_i b; cases b <;> simp
    apply BaseLit.measurable_casesOn
      (c_int := fun z => some (Exp.lit (.int z.neg))) (c_bool := fun _ => none)
      (c_unit := fun _ => none) (c_loc := fun _ => none) (c_lbl := fun _ => none)
      (c_real := fun r => some (Exp.lit (.real (ProbLangℝ.realNeg r))))
    exact MeasurableEmbedding.some_mk.measurable.comp
      (Exp.lit.measurable.comp (BaseLit.real.measurable.comp LawfulProbLangℝ.measurable_realNeg))
  | toReal =>
    refine measurable_of_lit_only none
      (f := fun l => BaseLit.casesOn (motive := fun _ => Option (Exp rT)) l
        (fun z => some (Exp.lit (.real (ProbLangℝ.realOfInt z)))) (fun _ => none) none
        (fun _ => none) (fun _ => none)
        (fun r => some (Exp.lit (.real r)))) ?_
      fun v => by
        cases v <;> simp [UnOp.eval]
        rename_i l; cases l <;> simp
    apply BaseLit.measurable_casesOn
      (c_int := fun z => some (Exp.lit (.real (ProbLangℝ.realOfInt z))))
      (c_bool := fun _ => none)
      (c_unit := fun _ => none) (c_loc := fun _ => none) (c_lbl := fun _ => none)
      (c_real := fun r => some (Exp.lit (.real r)))
    exact MeasurableEmbedding.some_mk.measurable.comp
      (Exp.lit.measurable.comp BaseLit.real.measurable)
  | frac =>
    refine measurable_of_lit_only none
      (f := fun l => BaseLit.casesOn (motive := fun _ => Option (Exp rT)) l
        (fun _ => none) (fun _ => none) none
        (fun _ => none) (fun _ => none)
        (fun r => some (Exp.lit (.real (ProbLangℝ.realFrac r))))) ?_
      fun v => by
        cases v <;> simp [UnOp.eval]
        rename_i l; cases l <;> simp
    apply BaseLit.measurable_casesOn
      (c_int := fun _ => none) (c_bool := fun _ => none)
      (c_unit := fun _ => none) (c_loc := fun _ => none) (c_lbl := fun _ => none)
      (c_real := fun r => some (Exp.lit (.real (ProbLangℝ.realFrac r))))
    exact MeasurableEmbedding.some_mk.measurable.comp
      (Exp.lit.measurable.comp
        (BaseLit.real.measurable.comp LawfulProbLangℝ.measurable_realFrac))

theorem UnOp_eval.measurable [LawfulProbLangℝ rT] :
    Measurable (Function.uncurry (UnOp.eval (α := rT))) := by
  apply measurable_from_prod_countable_right
  exact UnOp.eval_op_measurable

/-! ### `EctxItem.fillItem`, `Ectx.fill` -/

theorem fillItem.measurable [MeasurableSpace rT] :
    Measurable (fun (q : EctxItem rT × Exp rT) => q.1.fillItem q.2) := by
  have heq : (fun q : EctxItem rT × Exp rT => q.1.fillItem q.2) = fun p : EctxItem rT × Exp rT =>
      EctxItem.casesOn (motive := fun _ => Exp rT) p.1
        (fun v => (fun pp : Exp rT × Val rT => Exp.app pp.1 (Exp.ofVal pp.2)) (p.2, v))
        (fun e => (fun pp : Exp rT × Exp rT => Exp.app pp.2 pp.1) (p.2, e))
        (fun u => (fun pp : Exp rT × UnOp => Exp.unop pp.2 pp.1) (p.2, u))
        (fun op v =>
          (fun pp : Exp rT × BinOp × Val rT => Exp.binop pp.2.1 pp.1 (Exp.ofVal pp.2.2))
            (p.2, op, v))
        (fun op e =>
          (fun pp : Exp rT × BinOp × Exp rT => Exp.binop pp.2.1 pp.2.2 pp.1) (p.2, op, e))
        (fun e₁ e₂ =>
          (fun pp : Exp rT × Exp rT × Exp rT => Exp.cond pp.1 pp.2.1 pp.2.2) (p.2, e₁, e₂))
        (fun v => (fun pp : Exp rT × Val rT => Exp.pair pp.1 (Exp.ofVal pp.2)) (p.2, v))
        (fun e => (fun pp : Exp rT × Exp rT => Exp.pair pp.2 pp.1) (p.2, e))
        ((fun pp : Exp rT × Unit => Exp.fst pp.1) (p.2, ()))
        ((fun pp : Exp rT × Unit => Exp.snd pp.1) (p.2, ()))
        ((fun pp : Exp rT × Unit => Exp.inl pp.1) (p.2, ()))
        ((fun pp : Exp rT × Unit => Exp.inr pp.1) (p.2, ()))
        (fun e₁ e₂ =>
          (fun pp : Exp rT × Exp rT × Exp rT => Exp.case pp.1 pp.2.1 pp.2.2) (p.2, e₁, e₂))
        ((fun pp : Exp rT × Unit => Exp.alloc pp.1) (p.2, ()))
        ((fun pp : Exp rT × Unit => Exp.load pp.1) (p.2, ()))
        (fun v => (fun pp : Exp rT × Val rT => Exp.store pp.1 (Exp.ofVal pp.2)) (p.2, v))
        (fun e => (fun pp : Exp rT × Exp rT => Exp.store pp.2 pp.1) (p.2, e))
        ((fun pp : Exp rT × Unit => Exp.tape pp.1) (p.2, ()))
        (fun v => (fun pp : Exp rT × Val rT => Exp.rand pp.1 (Exp.ofVal pp.2)) (p.2, v))
        (fun e => (fun pp : Exp rT × Exp rT => Exp.rand pp.2 pp.1) (p.2, e))
        (fun pat => (fun pp : Exp rT × Pat rT => Exp.scrut pp.1 pp.2) (p.2, pat)) := by
    funext q
    cases q.1 <;> simp [EctxItem.fillItem]
  rw [heq]
  refine EctxItem.measurable_casesOn_param (α := rT) (β := Exp rT) (α' := Exp rT)
    (c_appL := fun p => Exp.app p.1 (Exp.ofVal p.2))
    (c_appR := fun p => Exp.app p.2 p.1)
    (c_unop := fun p => Exp.unop p.2 p.1)
    (c_binopL := fun p => Exp.binop p.2.1 p.1 (Exp.ofVal p.2.2))
    (c_binopR := fun p => Exp.binop p.2.1 p.2.2 p.1)
    (c_condC := fun p => Exp.cond p.1 p.2.1 p.2.2)
    (c_pairL := fun p => Exp.pair p.1 (Exp.ofVal p.2))
    (c_pairR := fun p => Exp.pair p.2 p.1)
    (c_fst := fun p => Exp.fst p)
    (c_snd := fun p => Exp.snd p)
    (c_inl := fun p => Exp.inl p)
    (c_inr := fun p => Exp.inr p)
    (c_case := fun p => Exp.case p.1 p.2.1 p.2.2)
    (c_alloc := fun p => Exp.alloc p)
    (c_load := fun p => Exp.load p)
    (c_storeL := fun p => Exp.store p.1 (Exp.ofVal p.2))
    (c_storeR := fun p => Exp.store p.2 p.1)
    (c_tape := fun p => Exp.tape p)
    (c_randL := fun p => Exp.rand p.1 (Exp.ofVal p.2))
    (c_randR := fun p => Exp.rand p.2 p.1)
    (c_scrut := fun p => Exp.scrut p.1 p.2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show Measurable (fun p : Exp rT × Val rT => Function.uncurry Exp.app (p.1, Exp.ofVal p.2))
    exact Exp.app.measurable.comp (measurable_fst.prodMk <| Val.fst.measurable.comp measurable_snd)
  · fun_prop
  · fun_prop
  · show Measurable (fun p : Exp rT × BinOp × Val rT =>
        (fun (q : BinOp × Exp rT × Exp rT) => Exp.binop q.1 q.2.1 q.2.2)
          (p.2.1, p.1, Exp.ofVal p.2.2))
    refine Exp.binop.measurable.comp ?_
    refine (measurable_fst.comp measurable_snd).prodMk ?_
    exact measurable_fst.prodMk <| Val.fst.measurable.comp <| measurable_snd.comp measurable_snd
  · fun_prop
  · fun_prop
  · show Measurable (fun p : Exp rT × Val rT => Function.uncurry Exp.pair (p.1, Exp.ofVal p.2))
    exact Exp.pair.measurable.comp (measurable_fst.prodMk <| Val.fst.measurable.comp measurable_snd)
  iterate 8 fun_prop
  · show Measurable (fun p : Exp rT × Val rT => Function.uncurry Exp.store (p.1, Exp.ofVal p.2))
    exact Exp.store.measurable.comp
      (measurable_fst.prodMk <| Val.fst.measurable.comp measurable_snd)
  iterate 2 fun_prop
  · show Measurable (fun p : Exp rT × Val rT => Function.uncurry Exp.rand (p.1, Exp.ofVal p.2))
    exact Exp.rand.measurable.comp (measurable_fst.prodMk <| Val.fst.measurable.comp measurable_snd)
  iterate 2 fun_prop

@[fun_prop]
theorem Ectx_fill.measurable [MeasurableSpace rT] :
    Measurable (fun (q : Ectx rT × Exp rT) => Ectx.fill q.1 q.2) := by
  have hflip : Measurable (Function.uncurry (flip (EctxItem.fillItem (α := rT)))) :=
    Exp.fillItem.measurable.comp measurable_swap
  exact List.measurable_foldl hflip

/-! ### `Exp.openRec`, `Exp.closeRec` -/

@[fun_prop]
theorem openRec.measurable [MeasurableSpace rT] :
    Measurable (fun (q : (Nat × Exp rT) × Exp rT) => Exp.openRec q.1.1 q.1.2 q.2) := by
  apply_arms measurable_struct_rec_param
    (f := fun (b : Nat × Exp rT) (e : Exp rT) => Exp.openRec b.1 b.2 e)
    (t_lam   := fun b => (b.1 + 1, b.2))
    (t_fix   := fun b => (b.1 + 1, b.2))
  case h_bvar =>
    have hrw : Function.uncurry (fun (b : Nat × Exp rT) (j : Nat) =>
              if b.1 = j then b.2 else (Exp.bvar j : Exp rT))
        = (fun (q : (Nat × Nat) × Exp rT) =>
              if q.1.1 = q.1.2 then q.2 else Exp.bvar q.1.2)
            ∘ (fun (p : (Nat × Exp rT) × Nat) => ((p.1.1, p.2), p.1.2)) := by
      funext ⟨⟨i, sub⟩, j⟩; rfl
    rw [hrw]
    have h1 : Measurable (fun (q : (Nat × Nat) × Exp rT) =>
                if q.1.1 = q.1.2 then q.2 else (Exp.bvar q.1.2 : Exp rT)) := by
      apply measurable_from_prod_countable_right
      intro ij
      by_cases h : ij.1 = ij.2
      · simp only [h, ite_true]; exact measurable_id
      · simp only [h, ite_false]; exact measurable_const
    exact h1.comp (by fun_prop : Measurable
      (fun (p : (Nat × Exp rT) × Nat) => ((p.1.1, p.2), p.1.2)))

theorem open'.measurable [MeasurableSpace rT] :
    Measurable (fun (q : Exp rT × Exp rT) => Exp.open' q.1 q.2) := by
  have hpack : Measurable (fun q : Exp rT × Exp rT => ((0, q.2), q.1)) := by fun_prop
  exact Exp.openRec.measurable (rT := rT) |>.comp hpack

theorem closeRec.measurable [MeasurableSpace rT] :
    Measurable (fun (q : (Nat × Var) × Exp rT) => Exp.closeRec q.1.1 q.1.2 q.2) := by
  apply_arms measurable_struct_rec_param
    (f := fun (b : Nat × Var) (e : Exp rT) => Exp.closeRec b.1 b.2 e)
    (t_lam   := fun b => (b.1 + 1, b.2))
    (t_fix   := fun b => (b.1 + 1, b.2))

theorem close.measurable [MeasurableSpace rT] :
    Measurable (fun (q : Exp rT × Var) => Exp.close q.1 q.2) := by
  have hpack : Measurable (fun q : Exp rT × Var => ((0, q.2), q.1)) := by fun_prop
  exact Exp.closeRec.measurable (rT := rT) |>.comp hpack

attribute [local instance] Classical.propDecidable

/-- A measurable space on `Option α` through `Option α ≃ α ⊕ PUnit`. -/
instance instLocalOption [MeasurableSpace α] : MeasurableSpace (Option α) :=
  MeasurableSpace.comap (Equiv.optionEquivSumPUnit.{0, _} α) inferInstance

/-! ### `Exp.toVal?`

`IsVal.check?` has a dependent codomain, so `toVal?` is handled through its value set
`{e | e.isValue}` rather than the recursion keystone. -/

theorem toVal_question.measurable [MeasurableSpace rT] :
    let _ : MeasurableSpace (Option (Val rT)) := instLocalOption
    Measurable (Exp.toVal? : Exp rT → Option (Val rT)) := by
  intro mOpt
  have hrw : (Exp.toVal? : Exp rT → Option (Val rT)) =
      fun e => if h : e.isValue then
        some (Val.mk e (Classical.choice h) (Classical.choice h).lc) else none := by
    funext e
    by_cases h : e.isValue
    · simp only [Exp.toVal?, dite_eq_left h]
      cases hc : IsVal.check? e with
      | none => exact absurd (IsVal.not_isValue_of_check?_none hc) (not_not.mpr h)
      | some w => exact congrArg some (Val.ext rfl)
    · have hnone : Exp.toVal? e = none := Exp.toVal?_eq_none.mpr h
      simp only [hnone, dite_eq_right h]
  rw [hrw]
  intro S hS
  obtain ⟨Ssum, hSsum, hSeq⟩ := hS
  obtain ⟨Uval, hUval, hUval_eq⟩ : ∃ U : Set (Exp rT), MeasurableSet U ∧
      Val.fst ⁻¹' U = (Sum.inl ⁻¹' Ssum : Set (Val rT)) :=
    MeasurableSpace.measurableSet_comap.mp (measurable_inl hSsum)
  have hMset : MeasurableSet {e : Exp rT | e.isValue} := by
    have heq : {e : Exp rT | e.isValue} = {e | e.isValueR} ∩ {e | Exp.lcb 0 e = true} := by
      ext e; simp [Exp.isValue_iff_isValueR, Set.mem_inter_iff]
    rw [heq]; exact (isValueR.measurable.setOf).inter lcb_zero.measurableSet
  set noneIn : Prop := ((⟨⟩ : PUnit) ∈ (Sum.inr ⁻¹' Ssum : Set PUnit)) with hNoneIn
  classical
  have hpreimage_eq :
      (fun e : Exp rT => if h : e.isValue then
        some (Val.mk e (Classical.choice h) (Classical.choice h).lc) else none) ⁻¹' S =
        ({e | e.isValue} ∩ Uval) ∪ (if noneIn then {e | ¬e.isValue} else ∅) := by
    ext e
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    by_cases hv : e.isValue
    · simp only [dite_eq_left hv]
      rw [← hSeq]
      simp only [Set.mem_preimage]
      have heqv : Equiv.optionEquivSumPUnit (Val rT)
          (some (Val.mk e (Classical.choice hv) (Classical.choice hv).lc)) =
          .inl (Val.mk e (Classical.choice hv) (Classical.choice hv).lc) := by
        simp [Equiv.optionEquivSumPUnit]
      rw [heqv]
      have hmem_iff :
          (Sum.inl (Val.mk e (Classical.choice hv) (Classical.choice hv).lc) : Val rT ⊕ PUnit)
            ∈ Ssum ↔
          (Val.mk e (Classical.choice hv) (Classical.choice hv).lc : Val rT) ∈
          (Sum.inl ⁻¹' Ssum : Set (Val rT)) := Iff.rfl
      rw [hmem_iff, ← hUval_eq]
      simp only [Set.mem_preimage]
      constructor
      · intro hUe
        left; exact ⟨hv, hUe⟩
      · rintro (⟨_, hUe⟩ | hcontra)
        · exact hUe
        · split_ifs at hcontra with hni
          · exact absurd hv hcontra
          · exact absurd hcontra (Set.notMem_empty _)
    · simp only [dite_eq_right hv]
      rw [← hSeq]
      simp only [Set.mem_preimage]
      have heqv : Equiv.optionEquivSumPUnit (Val rT) none = .inr ⟨⟩ := by
        simp [Equiv.optionEquivSumPUnit]
      rw [heqv]
      have hmem_iff : (Sum.inr ⟨⟩ : Val rT ⊕ PUnit) ∈ Ssum ↔ noneIn := Iff.rfl
      rw [hmem_iff]
      constructor
      · intro hni
        right; rw [ite_eq_left hni]; exact hv
      · rintro (⟨hcontra, _⟩ | hcase)
        · exact absurd hcontra hv
        · split_ifs at hcase with hni
          · exact hni
          · exact absurd hcase (Set.notMem_empty _)
  rw [hpreimage_eq]
  refine MeasurableSet.union (hMset.inter hUval) ?_
  split_ifs
  · exact hMset.compl
  · exact MeasurableSet.empty

/-! ### Eliminating `Option` measurably -/

theorem _root_.Option.measurable_elim_param
    {α β γ : Type _} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {f : α → Option β} (hf : @Measurable _ _ _ instLocalOption f)
    {default : α → γ} (hdef : Measurable default)
    {some_branch : α × β → γ} (hsome : Measurable some_branch) :
    Measurable (fun a => Option.casesOn (motive := fun _ => γ) (f a) (default a)
      (fun b => some_branch (a, b))) := by
  intro S hS
  have hpre : (fun a => Option.casesOn (motive := fun _ => γ) (f a) (default a)
        (fun b => some_branch (a, b))) ⁻¹' S
      = ({a | f a = none} ∩ default ⁻¹' S)
      ∪ (fun a => (a, f a)) ⁻¹'
          ((fun q : α × β => (q.1, (some q.2 : Option β))) ''
            ((fun q : α × β => some_branch q) ⁻¹' S)) := by
    ext a
    rcases hfa : f a with _ | b
    · simp [hfa]
    · simp only [hfa, Set.mem_preimage, Set.mem_union, Set.mem_inter_iff,
        Set.mem_ofPred_eq, Set.mem_image, Prod.mk.injEq]
      constructor
      · intro h; right; exact ⟨(a, b), h, rfl, rfl⟩
      · rintro (⟨hcontra, _⟩ | ⟨⟨a', b'⟩, hab, rfl, hbeq⟩)
        · simp_all
        · exact Option.some_injective _ hbeq ▸ hab
  rw [hpre]
  refine MeasurableSet.union ?_ ?_
  · exact (hf MeasurableSet.singleton_none).inter (hdef hS)
  · refine MeasurableSet.preimage ?_ (measurable_id.prodMk hf)
    exact (MeasurableEmbedding.id.prodMap MeasurableEmbedding.some_mk).measurableSet_image'
      (hsome hS)

theorem _root_.Option.measurable_elim_param_zero
    {α β γ : Type _} [MeasurableSpace α] [MeasurableSpace β]
    [Zero γ] [MeasurableSpace γ]
    {f : α → Option β} (hf : @Measurable _ _ _ instLocalOption f)
    {some_branch : α × β → γ} (hsome : Measurable some_branch) :
    Measurable (fun a => Option.casesOn (motive := fun _ => γ) (f a) 0
      (fun b => some_branch (a, b))) :=
  Option.measurable_elim_param hf measurable_const hsome

theorem _root_.Option.measurable_bind_param
    {α β γ : Type _} [MeasurableSpace α] [MeasurableSpace β]
    [_mγ : MeasurableSpace (Option γ)]
    {f : α → Option β} (hf : @Measurable _ _ _ instLocalOption f)
    {some_branch : α × β → Option γ} (hsome : Measurable some_branch) :
    Measurable (fun a => (f a).bind (fun b => some_branch (a, b))) := by
  have hrw : (fun a => (f a).bind (fun b => some_branch (a, b)))
      = fun a => Option.casesOn (motive := fun _ => Option γ) (f a)
          none (fun b => some_branch (a, b)) := by
    funext a; cases f a <;> rfl
  rw [hrw]
  exact Option.measurable_elim_param hf measurable_const hsome

/-! ### `measurable_casesOn_param` with every arm defaulting to `0` -/

theorem _root_.ProbLang.Exp.measurable_casesOn_param_zero
    {rT : Type _} [MeasurableSpace rT]
    {α : Type _} [Zero α] [MeasurableSpace α]
    {β : Type _} [MeasurableSpace β]
    (c_bvar : β × Nat → α := fun _ => 0) (c_fvar : β × Var → α := fun _ => 0)
    (c_lit : β × BaseLit rT → α := fun _ => 0)
    (c_lam : β × Exp rT → α := fun _ => 0) (c_fix : β × Exp rT → α := fun _ => 0)
    (c_app : β × Exp rT × Exp rT → α := fun _ => 0)
    (c_unop : β × UnOp × Exp rT → α := fun _ => 0)
    (c_binop : β × BinOp × Exp rT × Exp rT → α := fun _ => 0)
    (c_cond : β × Exp rT × Exp rT × Exp rT → α := fun _ => 0)
    (c_pair : β × Exp rT × Exp rT → α := fun _ => 0)
    (c_fst : β × Exp rT → α := fun _ => 0) (c_snd : β × Exp rT → α := fun _ => 0)
    (c_inl : β × Exp rT → α := fun _ => 0) (c_inr : β × Exp rT → α := fun _ => 0)
    (c_case : β × Exp rT × Exp rT × Exp rT → α := fun _ => 0)
    (c_alloc : β × Exp rT → α := fun _ => 0)
    (c_load : β × Exp rT → α := fun _ => 0)
    (c_store : β × Exp rT × Exp rT → α := fun _ => 0)
    (c_tape : β × Exp rT → α := fun _ => 0)
    (c_rand : β × Exp rT × Exp rT → α := fun _ => 0)
    (c_fail : β → α := fun _ => 0)
    (c_urand : β → α := fun _ => 0)
    (c_scrut : β × Exp rT × Pat rT → α := fun _ => 0)
    (h_bvar : Measurable c_bvar := by exact measurable_const)
    (h_fvar : Measurable c_fvar := by exact measurable_const)
    (h_lit : Measurable c_lit := by exact measurable_const)
    (h_lam : Measurable c_lam := by exact measurable_const)
    (h_fix : Measurable c_fix := by exact measurable_const)
    (h_app : Measurable c_app := by exact measurable_const)
    (h_unop : Measurable c_unop := by exact measurable_const)
    (h_binop : Measurable c_binop := by exact measurable_const)
    (h_cond : Measurable c_cond := by exact measurable_const)
    (h_pair : Measurable c_pair := by exact measurable_const)
    (h_fst : Measurable c_fst := by exact measurable_const)
    (h_snd : Measurable c_snd := by exact measurable_const)
    (h_inl : Measurable c_inl := by exact measurable_const)
    (h_inr : Measurable c_inr := by exact measurable_const)
    (h_case : Measurable c_case := by exact measurable_const)
    (h_alloc : Measurable c_alloc := by exact measurable_const)
    (h_load : Measurable c_load := by exact measurable_const)
    (h_store : Measurable c_store := by exact measurable_const)
    (h_tape : Measurable c_tape := by exact measurable_const)
    (h_rand : Measurable c_rand := by exact measurable_const)
    (h_fail : Measurable c_fail := by exact measurable_const)
    (h_urand : Measurable c_urand := by exact measurable_const)
    (h_scrut : Measurable c_scrut := by exact measurable_const) :
    Measurable (fun p : Exp rT × β => Exp.casesOn (motive := fun _ => α) p.1
        (fun n => c_bvar (p.2, n)) (fun x => c_fvar (p.2, x))
        (fun l => c_lit (p.2, l))
        (fun e => c_lam (p.2, e)) (fun e => c_fix (p.2, e))
        (fun e1 e2 => c_app (p.2, e1, e2))
        (fun u e => c_unop (p.2, u, e))
        (fun b e1 e2 => c_binop (p.2, b, e1, e2))
        (fun ec et ef => c_cond (p.2, ec, et, ef))
        (fun e1 e2 => c_pair (p.2, e1, e2))
        (fun e => c_fst (p.2, e)) (fun e => c_snd (p.2, e))
        (fun e => c_inl (p.2, e)) (fun e => c_inr (p.2, e))
        (fun ec el er => c_case (p.2, ec, el, er))
        (fun e => c_alloc (p.2, e)) (fun e => c_load (p.2, e))
        (fun e1 e2 => c_store (p.2, e1, e2))
        (fun e => c_tape (p.2, e))
        (fun e1 e2 => c_rand (p.2, e1, e2))
        (c_fail p.2)
        (c_urand p.2)
        (fun e pat => c_scrut (p.2, e, pat))) :=
  Exp.measurable_casesOn_param
    c_bvar c_fvar c_lit c_lam c_fix c_app c_unop c_binop c_cond c_pair c_fst c_snd
    c_inl c_inr c_case c_alloc c_load c_store c_tape c_rand c_fail c_urand c_scrut
    h_bvar h_fvar h_lit h_lam h_fix h_app h_unop h_binop h_cond h_pair h_fst h_snd
    h_inl h_inr h_case h_alloc h_load h_store h_tape h_rand h_fail h_urand h_scrut

theorem _root_.ProbLang.BaseLit.measurable_casesOn_param_zero
    {rT : Type _} [MeasurableSpace rT] [Inhabited rT]
    {α : Type _} [Zero α] [MeasurableSpace α]
    {β : Type _} [MeasurableSpace β]
    (c_int : β × Int → α := fun _ => 0) (c_bool : β × Bool → α := fun _ => 0)
    (c_unit : β → α := fun _ => 0)
    (c_loc : β × Loc → α := fun _ => 0) (c_lbl : β × Lbl → α := fun _ => 0)
    (c_real : β × rT → α := fun _ => 0)
    (h_int : Measurable c_int := by exact measurable_const)
    (h_bool : Measurable c_bool := by exact measurable_const)
    (h_unit : Measurable c_unit := by exact measurable_const)
    (h_loc : Measurable c_loc := by exact measurable_const)
    (h_lbl : Measurable c_lbl := by exact measurable_const)
    (h_real : Measurable c_real := by exact measurable_const) :
    Measurable (fun p : BaseLit rT × β =>
      BaseLit.casesOn (motive := fun _ => α) p.1
        (fun z => c_int (p.2, z)) (fun b => c_bool (p.2, b))
        (c_unit p.2)
        (fun l => c_loc (p.2, l)) (fun l => c_lbl (p.2, l))
        (fun r => c_real (p.2, r))) :=
  BaseLit.measurable_casesOn_param c_int c_bool c_unit c_loc c_lbl c_real
    h_int h_bool h_unit h_loc h_lbl h_real

/-! ### Macros for `headStep` continuations

The `_zero` theorems above time out in `HeadStep.lean`: elaborating 21 `Measure 0`
defaults is too slow there. These macros emit the explicit arguments instead; each
takes the live continuations and their measurability proofs. -/

/-- Only the `.lit` arm is live. -/
macro "exp_zero_lit_apply " ct:term ", " ht:term : tactic =>
  `(tactic|
    exact Exp.measurable_casesOn_param
        (c_bvar := fun _ => 0) (c_fvar := fun _ => 0) (c_lit := $ct)
        (c_lam := fun _ => 0) (c_fix := fun _ => 0)
        (c_app := fun _ => 0) (c_unop := fun _ => 0) (c_binop := fun _ => 0)
        (c_cond := fun _ => 0) (c_pair := fun _ => 0)
        (c_fst := fun _ => 0) (c_snd := fun _ => 0)
        (c_inl := fun _ => 0) (c_inr := fun _ => 0) (c_case := fun _ => 0)
        (c_alloc := fun _ => 0) (c_load := fun _ => 0) (c_store := fun _ => 0)
        (c_tape := fun _ => 0) (c_rand := fun _ => 0)
        (c_fail := fun _ => 0) (c_urand := fun _ => 0) (c_scrut := fun _ => 0)
        (h_bvar := measurable_const) (h_fvar := measurable_const)
        (h_lit := $ht)
        (h_lam := measurable_const) (h_fix := measurable_const)
        (h_app := measurable_const) (h_unop := measurable_const) (h_binop := measurable_const)
        (h_cond := measurable_const) (h_pair := measurable_const)
        (h_fst := measurable_const) (h_snd := measurable_const)
        (h_inl := measurable_const) (h_inr := measurable_const) (h_case := measurable_const)
        (h_alloc := measurable_const) (h_load := measurable_const) (h_store := measurable_const)
        (h_tape := measurable_const) (h_rand := measurable_const)
        (h_fail := measurable_const) (h_urand := measurable_const) (h_scrut := measurable_const))

/-- Only the `.pair` arm is live. -/
macro "exp_zero_pair_apply " ct:term ", " ht:term : tactic =>
  `(tactic|
    exact Exp.measurable_casesOn_param
        (c_bvar := fun _ => 0) (c_fvar := fun _ => 0) (c_lit := fun _ => 0)
        (c_lam := fun _ => 0) (c_fix := fun _ => 0)
        (c_app := fun _ => 0) (c_unop := fun _ => 0) (c_binop := fun _ => 0)
        (c_cond := fun _ => 0) (c_pair := $ct)
        (c_fst := fun _ => 0) (c_snd := fun _ => 0)
        (c_inl := fun _ => 0) (c_inr := fun _ => 0) (c_case := fun _ => 0)
        (c_alloc := fun _ => 0) (c_load := fun _ => 0) (c_store := fun _ => 0)
        (c_tape := fun _ => 0) (c_rand := fun _ => 0)
        (c_fail := fun _ => 0) (c_urand := fun _ => 0) (c_scrut := fun _ => 0)
        (h_bvar := measurable_const) (h_fvar := measurable_const)
        (h_lit := measurable_const)
        (h_lam := measurable_const) (h_fix := measurable_const)
        (h_app := measurable_const) (h_unop := measurable_const) (h_binop := measurable_const)
        (h_cond := measurable_const)
        (h_pair := $ht)
        (h_fst := measurable_const) (h_snd := measurable_const)
        (h_inl := measurable_const) (h_inr := measurable_const) (h_case := measurable_const)
        (h_alloc := measurable_const) (h_load := measurable_const) (h_store := measurable_const)
        (h_tape := measurable_const) (h_rand := measurable_const)
        (h_fail := measurable_const) (h_urand := measurable_const) (h_scrut := measurable_const))

/-- Only the `.lam` and `.fix` arms are live. -/
macro "exp_zero_app_apply "
    clamt:term ", " hlamt:term ", " cfixt:term ", " hfixt:term : tactic =>
  `(tactic|
    exact Exp.measurable_casesOn_param
        (c_bvar := fun _ => 0) (c_fvar := fun _ => 0) (c_lit := fun _ => 0)
        (c_lam := $clamt) (c_fix := $cfixt)
        (c_app := fun _ => 0) (c_unop := fun _ => 0) (c_binop := fun _ => 0)
        (c_cond := fun _ => 0) (c_pair := fun _ => 0)
        (c_fst := fun _ => 0) (c_snd := fun _ => 0)
        (c_inl := fun _ => 0) (c_inr := fun _ => 0) (c_case := fun _ => 0)
        (c_alloc := fun _ => 0) (c_load := fun _ => 0) (c_store := fun _ => 0)
        (c_tape := fun _ => 0) (c_rand := fun _ => 0)
        (c_fail := fun _ => 0) (c_urand := fun _ => 0) (c_scrut := fun _ => 0)
        (h_bvar := measurable_const) (h_fvar := measurable_const)
        (h_lit := measurable_const)
        (h_lam := $hlamt) (h_fix := $hfixt)
        (h_app := measurable_const) (h_unop := measurable_const) (h_binop := measurable_const)
        (h_cond := measurable_const) (h_pair := measurable_const)
        (h_fst := measurable_const) (h_snd := measurable_const)
        (h_inl := measurable_const) (h_inr := measurable_const) (h_case := measurable_const)
        (h_alloc := measurable_const) (h_load := measurable_const) (h_store := measurable_const)
        (h_tape := measurable_const) (h_rand := measurable_const)
        (h_fail := measurable_const) (h_urand := measurable_const) (h_scrut := measurable_const))

/-- Only the `.inl` and `.inr` arms are live. -/
macro "exp_zero_case_apply "
    cinlt:term ", " hinlt:term ", " cinrt:term ", " hinrt:term : tactic =>
  `(tactic|
    exact Exp.measurable_casesOn_param
        (c_bvar := fun _ => 0) (c_fvar := fun _ => 0) (c_lit := fun _ => 0)
        (c_lam := fun _ => 0) (c_fix := fun _ => 0)
        (c_app := fun _ => 0) (c_unop := fun _ => 0) (c_binop := fun _ => 0)
        (c_cond := fun _ => 0) (c_pair := fun _ => 0)
        (c_fst := fun _ => 0) (c_snd := fun _ => 0)
        (c_inl := $cinlt) (c_inr := $cinrt) (c_case := fun _ => 0)
        (c_alloc := fun _ => 0) (c_load := fun _ => 0) (c_store := fun _ => 0)
        (c_tape := fun _ => 0) (c_rand := fun _ => 0)
        (c_fail := fun _ => 0) (c_urand := fun _ => 0) (c_scrut := fun _ => 0)
        (h_bvar := measurable_const) (h_fvar := measurable_const)
        (h_lit := measurable_const)
        (h_lam := measurable_const) (h_fix := measurable_const)
        (h_app := measurable_const) (h_unop := measurable_const) (h_binop := measurable_const)
        (h_cond := measurable_const) (h_pair := measurable_const)
        (h_fst := measurable_const) (h_snd := measurable_const)
        (h_inl := $hinlt) (h_inr := $hinrt) (h_case := measurable_const)
        (h_alloc := measurable_const) (h_load := measurable_const) (h_store := measurable_const)
        (h_tape := measurable_const) (h_rand := measurable_const)
        (h_fail := measurable_const) (h_urand := measurable_const) (h_scrut := measurable_const))

/-- Only the `.int` arm is live. -/
macro "baseLit_zero_int_apply " ct:term ", " ht:term : tactic =>
  `(tactic|
    apply BaseLit.measurable_casesOn_param
        (c_int := $ct) (c_bool := fun _ => 0) (c_unit := fun _ => 0)
        (c_loc := fun _ => 0) (c_lbl := fun _ => 0) (c_real := fun _ => 0)
        (h_int := $ht) (h_bool := measurable_const)
        (h_unit := measurable_const) (h_loc := measurable_const)
        (h_lbl := measurable_const) (h_real := measurable_const))

/-- Only the `.loc` arm is live. -/
macro "baseLit_zero_loc_apply " ct:term ", " ht:term : tactic =>
  `(tactic|
    apply BaseLit.measurable_casesOn_param
        (c_int := fun _ => 0) (c_bool := fun _ => 0) (c_unit := fun _ => 0)
        (c_loc := $ct) (c_lbl := fun _ => 0) (c_real := fun _ => 0)
        (h_int := measurable_const) (h_bool := measurable_const)
        (h_unit := measurable_const) (h_loc := $ht)
        (h_lbl := measurable_const) (h_real := measurable_const))

/-- Only the `.bool` arm is live. -/
macro "baseLit_zero_bool_apply " ct:term ", " ht:term : tactic =>
  `(tactic|
    apply BaseLit.measurable_casesOn_param
        (c_int := fun _ => 0) (c_bool := $ct) (c_unit := fun _ => 0)
        (c_loc := fun _ => 0) (c_lbl := fun _ => 0) (c_real := fun _ => 0)
        (h_int := measurable_const) (h_bool := $ht)
        (h_unit := measurable_const) (h_loc := measurable_const)
        (h_lbl := measurable_const) (h_real := measurable_const))

/-- Adapts `BaseLit.measurable_casesOn_param` to the `(β, BaseLit)` argument order of `c_lit`. -/
theorem _root_.ProbLang.BaseLit.measurable_param_swap
    {rT : Type _} [MeasurableSpace rT] [Inhabited rT]
    {α : Type _} [MeasurableSpace α]
    {β : Type _} [MeasurableSpace β]
    {f : BaseLit rT × β → α} (hf : Measurable f) :
    Measurable (fun q : β × BaseLit rT => f (q.2, q.1)) :=
  hf.comp (measurable_snd.prodMk measurable_fst)

/-! ### `Exp.decompItem`, `Exp.decomp` -/

theorem decompItem.measurable [MeasurableSpace rT] :
    let _ : MeasurableSpace (Option (EctxItem rT × Exp rT)) := instLocalOption
    Measurable (Exp.decompItem : Exp rT → Option (EctxItem rT × Exp rT)) := by
  intro mOpt
  have hrw : (Exp.decompItem : Exp rT → Option (EctxItem rT × Exp rT)) = fun e =>
      Exp.casesOn (motive := fun _ => Option (EctxItem rT × Exp rT)) e
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ => none) (fun _ => none)
        (fun e1 e2 =>
          e2.toVal?.casesOn (some (.appR e1, e2)) fun v2 =>
          e1.toVal?.casesOn (some (.appL v2, e1)) fun _ => none)
        (fun op e1 =>
          e1.toVal?.casesOn (some (.unop op, e1)) fun _ => none)
        (fun op e1 e2 =>
          e2.toVal?.casesOn (some (.binopR op e1, e2)) fun v2 =>
          e1.toVal?.casesOn (some (.binopL op v2, e1)) fun _ => none)
        (fun ec et ef =>
          ec.toVal?.casesOn (some (.condC et ef, ec)) fun _ => none)
        (fun e1 e2 =>
          e2.toVal?.casesOn (some (.pairR e1, e2)) fun v2 =>
          e1.toVal?.casesOn (some (.pairL v2, e1)) fun _ => none)
        (fun e1 => e1.toVal?.casesOn (some (.fst, e1)) fun _ => none)
        (fun e1 => e1.toVal?.casesOn (some (.snd, e1)) fun _ => none)
        (fun e1 => e1.toVal?.casesOn (some (.inl, e1)) fun _ => none)
        (fun e1 => e1.toVal?.casesOn (some (.inr, e1)) fun _ => none)
        (fun ec el er =>
          ec.toVal?.casesOn (some (.case el er, ec)) fun _ => none)
        (fun e1 => e1.toVal?.casesOn (some (.alloc, e1)) fun _ => none)
        (fun e1 => e1.toVal?.casesOn (some (.load, e1)) fun _ => none)
        (fun e1 e2 =>
          e2.toVal?.casesOn (some (.storeR e1, e2)) fun v2 =>
          e1.toVal?.casesOn (some (.storeL v2, e1)) fun _ => none)
        (fun e1 => e1.toVal?.casesOn (some (.tape, e1)) fun _ => none)
        (fun e1 e2 =>
          e2.toVal?.casesOn (some (.randR e1, e2)) fun v2 =>
          e1.toVal?.casesOn (some (.randL v2, e1)) fun _ => none)
        none
        none
        (fun e1 p => e1.toVal?.casesOn (some (.scrut p, e1)) fun _ => none) := by
    funext e; cases e <;> rfl
  rw [hrw]
  have htv : @Measurable (Exp rT) (Option (Val rT)) _ instLocalOption Exp.toVal? :=
    toVal_question.measurable
  have hunary : ∀ {β : Type _} [MeasurableSpace β] (K : β → EctxItem rT) (proj : β → Exp rT),
      Measurable K → Measurable proj →
      @Measurable β (Option (EctxItem rT × Exp rT)) _ instLocalOption
        (fun b : β => Option.casesOn (motive := fun _ => Option (EctxItem rT × Exp rT))
          (proj b).toVal? (some (K b, proj b)) fun _ => none) := by
    intro β _ K proj hK hproj
    exact Option.measurable_elim_param (f := fun b => (proj b).toVal?)
      (htv.comp hproj)
      (MeasurableEmbedding.some_mk.measurable.comp (hK.prodMk hproj))
      measurable_const
  have hbinary : ∀ {β : Type _} [MeasurableSpace β]
      (KR : β → EctxItem rT) (KL : β × Val rT → EctxItem rT)
      (projL : β → Exp rT) (projR : β → Exp rT),
      Measurable KR → Measurable KL → Measurable projL → Measurable projR →
      @Measurable β (Option (EctxItem rT × Exp rT)) _ instLocalOption
        (fun b : β => Option.casesOn (motive := fun _ => Option (EctxItem rT × Exp rT))
          (projR b).toVal? (some (KR b, projR b)) fun v2 =>
          Option.casesOn (motive := fun _ => Option (EctxItem rT × Exp rT))
            (projL b).toVal? (some (KL (b, v2), projL b)) fun _ => none) := by
    intro β _ KR KL projL projR hKR hKL hprojL hprojR
    have h_some_branch : Measurable
        (fun bv : β × Val rT =>
          Option.casesOn (motive := fun _ => Option (EctxItem rT × Exp rT))
            (projL bv.1).toVal? (some (KL bv, projL bv.1)) fun _ => none) :=
      Option.measurable_elim_param
        (f := fun bv : β × Val rT => (projL bv.1).toVal?)
        (htv.comp (hprojL.comp measurable_fst))
        (MeasurableEmbedding.some_mk.measurable.comp (hKL.prodMk (hprojL.comp measurable_fst)))
        measurable_const
    exact Option.measurable_elim_param (f := fun b => (projR b).toVal?)
      (htv.comp hprojR) (MeasurableEmbedding.some_mk.measurable.comp (hKR.prodMk hprojR))
      h_some_branch
  refine Exp.measurable_casesOn
    (c_bvar := fun _ => none) (c_fvar := fun _ => none) (c_lit := fun _ => none)
    (c_lam := fun _ => none) (c_fix := fun _ => none)
    (c_app := fun (q : Exp rT × Exp rT) =>
      q.2.toVal?.casesOn (some (EctxItem.appR q.1, q.2)) fun v2 =>
      q.1.toVal?.casesOn (some (EctxItem.appL v2, q.1)) fun _ => none)
    (c_unop := fun (q : UnOp × Exp rT) =>
      q.2.toVal?.casesOn (some (EctxItem.unop q.1, q.2)) fun _ => none)
    (c_binop := fun (q : BinOp × Exp rT × Exp rT) =>
      q.2.2.toVal?.casesOn (some (EctxItem.binopR q.1 q.2.1, q.2.2)) fun v2 =>
      q.2.1.toVal?.casesOn (some (EctxItem.binopL q.1 v2, q.2.1)) fun _ => none)
    (c_cond := fun (q : Exp rT × Exp rT × Exp rT) =>
      q.1.toVal?.casesOn (some (EctxItem.condC q.2.1 q.2.2, q.1)) fun _ => none)
    (c_pair := fun (q : Exp rT × Exp rT) =>
      q.2.toVal?.casesOn (some (EctxItem.pairR q.1, q.2)) fun v2 =>
      q.1.toVal?.casesOn (some (EctxItem.pairL v2, q.1)) fun _ => none)
    (c_fst := fun e1 => e1.toVal?.casesOn (some (EctxItem.fst, e1)) fun _ => none)
    (c_snd := fun e1 => e1.toVal?.casesOn (some (EctxItem.snd, e1)) fun _ => none)
    (c_inl := fun e1 => e1.toVal?.casesOn (some (EctxItem.inl, e1)) fun _ => none)
    (c_inr := fun e1 => e1.toVal?.casesOn (some (EctxItem.inr, e1)) fun _ => none)
    (c_case := fun (q : Exp rT × Exp rT × Exp rT) =>
      q.1.toVal?.casesOn (some (EctxItem.case q.2.1 q.2.2, q.1)) fun _ => none)
    (c_alloc := fun e1 => e1.toVal?.casesOn (some (EctxItem.alloc, e1)) fun _ => none)
    (c_load := fun e1 => e1.toVal?.casesOn (some (EctxItem.load, e1)) fun _ => none)
    (c_store := fun (q : Exp rT × Exp rT) =>
      q.2.toVal?.casesOn (some (EctxItem.storeR q.1, q.2)) fun v2 =>
      q.1.toVal?.casesOn (some (EctxItem.storeL v2, q.1)) fun _ => none)
    (c_tape := fun e1 => e1.toVal?.casesOn (some (EctxItem.tape, e1)) fun _ => none)
    (c_rand := fun (q : Exp rT × Exp rT) =>
      q.2.toVal?.casesOn (some (EctxItem.randR q.1, q.2)) fun v2 =>
      q.1.toVal?.casesOn (some (EctxItem.randL v2, q.1)) fun _ => none)
    (c_fail := fun _ => none)
    (c_urand := fun _ => none)
    (c_scrut := fun (q : Exp rT × Pat rT) =>
      q.1.toVal?.casesOn (some (EctxItem.scrut q.2, q.1)) fun _ => none)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  iterate 3 exact measurable_const
  · exact hbinary
      (KR := fun q : Exp rT × Exp rT => EctxItem.appR q.1)
      (KL := fun (q : (Exp rT × Exp rT) × Val rT) => EctxItem.appL q.2)
      (projL := fun q => q.1) (projR := fun q => q.2)
      (EctxItem.appR.ι.measurable.comp measurable_fst)
      (EctxItem.appL.ι.measurable.comp measurable_snd)
      measurable_fst measurable_snd
  · exact hunary (β := UnOp × Exp rT)
      (K := fun q => EctxItem.unop q.1) (proj := fun q => q.2)
      (EctxItem.unop.ι.measurable.comp measurable_fst) measurable_snd
  · exact hbinary
      (KR := fun q : BinOp × Exp rT × Exp rT => EctxItem.binopR q.1 q.2.1)
      (KL := fun (q : (BinOp × Exp rT × Exp rT) × Val rT) => EctxItem.binopL q.1.1 q.2)
      (projL := fun q => q.2.1) (projR := fun q => q.2.2)
      (EctxItem.binopR.ι.measurable.comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
      (EctxItem.binopL.ι.measurable.comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
  · exact hunary (β := Exp rT × Exp rT × Exp rT)
      (K := fun q => EctxItem.condC q.2.1 q.2.2)
      (proj := fun q => q.1)
      (EctxItem.condC.ι.measurable.comp
        ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)))
      measurable_fst
  · exact hbinary
      (KR := fun q : Exp rT × Exp rT => EctxItem.pairR q.1)
      (KL := fun (q : (Exp rT × Exp rT) × Val rT) => EctxItem.pairL q.2)
      (projL := fun q => q.1) (projR := fun q => q.2)
      (EctxItem.pairR.ι.measurable.comp measurable_fst)
      (EctxItem.pairL.ι.measurable.comp measurable_snd)
      measurable_fst measurable_snd
  · exact hunary (β := Exp rT) (K := fun _ => EctxItem.fst) (proj := id)
      measurable_const measurable_id
  · exact hunary (β := Exp rT) (K := fun _ => EctxItem.snd) (proj := id)
      measurable_const measurable_id
  · exact hunary (β := Exp rT) (K := fun _ => EctxItem.inl) (proj := id)
      measurable_const measurable_id
  · exact hunary (β := Exp rT) (K := fun _ => EctxItem.inr) (proj := id)
      measurable_const measurable_id
  · exact hunary (β := Exp rT × Exp rT × Exp rT)
      (K := fun q => EctxItem.case q.2.1 q.2.2) (proj := fun q => q.1)
      (EctxItem.case.ι.measurable.comp
        ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)))
      measurable_fst
  · exact hunary (β := Exp rT) (K := fun _ => EctxItem.alloc) (proj := id)
      measurable_const measurable_id
  · exact hunary (β := Exp rT) (K := fun _ => EctxItem.load) (proj := id)
      measurable_const measurable_id
  · exact hbinary
      (KR := fun q : Exp rT × Exp rT => EctxItem.storeR q.1)
      (KL := fun (q : (Exp rT × Exp rT) × Val rT) => EctxItem.storeL q.2)
      (projL := fun q => q.1) (projR := fun q => q.2)
      (EctxItem.storeR.ι.measurable.comp measurable_fst)
      (EctxItem.storeL.ι.measurable.comp measurable_snd)
      measurable_fst measurable_snd
  · exact hunary (β := Exp rT) (K := fun _ => EctxItem.tape) (proj := id)
      measurable_const measurable_id
  · exact hbinary
      (KR := fun q : Exp rT × Exp rT => EctxItem.randR q.1)
      (KL := fun (q : (Exp rT × Exp rT) × Val rT) => EctxItem.randL q.2)
      (projL := fun q => q.1) (projR := fun q => q.2)
      (EctxItem.randR.ι.measurable.comp measurable_fst)
      (EctxItem.randL.ι.measurable.comp measurable_snd)
      measurable_fst measurable_snd
  · exact hunary (β := Exp rT × Pat rT)
      (K := fun q => EctxItem.scrut q.2) (proj := fun q => q.1)
      (EctxItem.scrut.ι.measurable.comp measurable_snd)
      measurable_fst

/-- `Exp.decomp` with explicit fuel; agrees with it once `n ≥ e.height`. -/
private def decompN {α : Type _} : ℕ → Exp α → Ectx α × Exp α
  | 0, e => ([], e)
  | n+1, e =>
    match e.decompItem with
    | none => ([], e)
    | some (Ki, e') =>
      let (K, e'') := decompN n e'
      (K ++ [Ki], e'')

private theorem decompN_eq_decomp {α : Type _} :
    ∀ (n : ℕ) (e : Exp α), n ≥ e.height → decompN n e = e.decomp := by
  intro n
  induction n with
  | zero =>
    intro e he
    have hdec : e.decompItem = none := by
      rcases hne : e.decompItem with _ | ⟨Ki, e'⟩
      · rfl
      · have := Exp.decompItem_height hne
        omega
    show ([], e) = e.decomp
    conv_rhs => rw [Exp.decomp_unfold]
    rw [hdec]
  | succ n ih =>
    intro e he
    rw [decompN]
    conv_rhs => rw [Exp.decomp_unfold]
    rcases hdec : e.decompItem with _ | ⟨Ki, e'⟩
    · simp
    · have := Exp.decompItem_height hdec
      simp [ih e' (by omega)]

private theorem decompN_measurable [MeasurableSpace rT] : ∀ n,
    Measurable (decompN n : Exp rT → Ectx rT × Exp rT) := by
  intro n
  induction n with
  | zero =>
    show Measurable (fun e : Exp rT => (([], e) : Ectx rT × Exp rT))
    exact measurable_const.prodMk measurable_id
  | succ n ih =>
    have hrw : (decompN (n+1) : Exp rT → Ectx rT × Exp rT)
        = fun e => Option.casesOn (motive := fun _ => Ectx rT × Exp rT) e.decompItem
            (([], e) : Ectx rT × Exp rT)
            (fun (p : EctxItem rT × Exp rT) =>
              ((decompN n p.2).1 ++ [p.1], (decompN n p.2).2)) := by
      funext e
      show decompN (n+1) e = _
      rw [decompN]
      rcases e.decompItem with _ | ⟨Ki, e'⟩ <;> rfl
    rw [hrw]
    refine @Option.measurable_elim_param _ _ _ _ _ _ _ decompItem.measurable
      (default := fun e => ([], e)) ?_
      (some_branch := fun q : Exp rT × (EctxItem rT × Exp rT) =>
        ((decompN n q.2.2).1 ++ [q.2.1], (decompN n q.2.2).2)) ?_
    · exact measurable_const.prodMk measurable_id
    · have h_decompN : Measurable (fun q : Exp rT × (EctxItem rT × Exp rT) =>
          decompN n q.2.2) :=
        ih.comp (measurable_snd.comp measurable_snd)
      exact (List.measurable_append_singleton.comp
        (h_decompN.fst.prodMk (measurable_fst.comp measurable_snd))).prodMk h_decompN.snd

@[fun_prop]
theorem decomp.measurable [MeasurableSpace rT] :
    Measurable (Exp.decomp : Exp rT → Ectx rT × Exp rT) := by
  have hrw : (Exp.decomp : Exp rT → Ectx rT × Exp rT) = fun e => decompN e.height e := by
    funext e; exact (decompN_eq_decomp e.height e (Nat.le_refl _)).symm
  rw [hrw]
  have hjoint : Measurable (fun p : ℕ × Exp rT => decompN p.1 p.2) :=
    measurable_from_prod_countable_right decompN_measurable
  exact hjoint.comp (height.measurable.prodMk measurable_id)

/-! ### Constructor extractors -/

/-- The literal of `e`, if `e` is one. -/
def litExtract (e : Exp rT) : Option (BaseLit rT) :=
  match e with | .lit b => some b | _ => none

/-- The components of `e`, if `e` is a pair. -/
def pairExtract (e : Exp rT) : Option (Exp rT × Exp rT) :=
  match e with | .pair e1 e2 => some (e1, e2) | _ => none

/-- The payload of `e`, if `e` is a left injection. -/
def inlExtract (e : Exp rT) : Option (Exp rT) :=
  match e with | .inl e' => some e' | _ => none

/-- The payload of `e`, if `e` is a right injection. -/
def inrExtract (e : Exp rT) : Option (Exp rT) :=
  match e with | .inr e' => some e' | _ => none

theorem litExtract.measurable [MeasurableSpace rT] :
    let _ : MeasurableSpace (Option (BaseLit rT)) := instLocalOption
    Measurable (Exp.litExtract : Exp rT → Option (BaseLit rT)) := by
  intro _
  exact measurable_of_lit_only none (f := fun b => some b)
    MeasurableEmbedding.some_mk.measurable fun e => by cases e <;> rfl

theorem pairExtract.measurable [MeasurableSpace rT] :
    let _ : MeasurableSpace (Option (Exp rT × Exp rT)) := instLocalOption
    Measurable (Exp.pairExtract : Exp rT → Option (Exp rT × Exp rT)) := by
  intro _
  apply_arms measurable_cases

theorem inlExtract.measurable [MeasurableSpace rT] :
    let _ : MeasurableSpace (Option (Exp rT)) := instLocalOption
    Measurable (Exp.inlExtract : Exp rT → Option (Exp rT)) := by
  intro _
  apply_arms measurable_cases

theorem inrExtract.measurable [MeasurableSpace rT] :
    let _ : MeasurableSpace (Option (Exp rT)) := instLocalOption
    Measurable (Exp.inrExtract : Exp rT → Option (Exp rT)) := by
  intro _
  apply_arms measurable_cases

/-- The integer of `l`, if `l` is one. -/
def _root_.ProbLang.BaseLit.intExtract (l : BaseLit rT) : Option Int :=
  match l with | .int z => some z | _ => none

/-- The boolean of `l`, if `l` is one. -/
def _root_.ProbLang.BaseLit.boolExtract (l : BaseLit rT) : Option Bool :=
  match l with | .bool b => some b | _ => none

theorem _root_.ProbLang.BaseLit.intExtract.measurable
    [MeasurableSpace rT] [Inhabited rT] :
    let _ : MeasurableSpace (Option Int) := instLocalOption
    Measurable (BaseLit.intExtract : BaseLit rT → Option Int) := by
  intro _
  apply_arms BaseLit.measurable_cases

theorem _root_.ProbLang.BaseLit.boolExtract.measurable
    [MeasurableSpace rT] [Inhabited rT] :
    let _ : MeasurableSpace (Option Bool) := instLocalOption
    Measurable (BaseLit.boolExtract : BaseLit rT → Option Bool) := by
  intro _
  apply_arms BaseLit.measurable_cases

/-- The real of `l`, if `l` is one. -/
def _root_.ProbLang.BaseLit.realExtract (l : BaseLit rT) : Option rT :=
  match l with | .real r => some r | _ => none

theorem _root_.ProbLang.BaseLit.realExtract.measurable
    [MeasurableSpace rT] [Inhabited rT] :
    let _ : MeasurableSpace (Option rT) := instLocalOption
    Measurable (BaseLit.realExtract : BaseLit rT → Option rT) := by
  intro _
  apply_arms BaseLit.measurable_cases

/-- Applies `mkResult` to the `extr`-extracted literals of two operands, if both succeed. -/
def liftBin {β : Type _} (extr : BaseLit rT → Option β)
    (mkResult : β → β → BaseLit rT) (p : Exp rT × Exp rT) : Option (Exp rT) :=
  ((Exp.litExtract p.1).bind extr).bind fun x1 =>
    ((Exp.litExtract p.2).bind extr).bind fun x2 =>
      some (Exp.lit (mkResult x1 x2))

theorem liftBin.measurable [MeasurableSpace rT] [Inhabited rT]
    {β : Type _} [MeasurableSpace β]
    (extr : BaseLit rT → Option β) (mkResult : β → β → BaseLit rT)
    (hextr : @Measurable _ _ _ instLocalOption extr)
    (hmk : Measurable (Function.uncurry mkResult)) :
    Measurable (liftBin (rT := rT) extr mkResult) := by
  let _ : MeasurableSpace (Option β) := instLocalOption
  let _ : MeasurableSpace (Option (BaseLit rT)) := instLocalOption
  let _ : MeasurableSpace (Option (Exp rT)) := instLocalOption
  unfold liftBin
  refine Option.measurable_bind_param (β := β) (γ := Exp rT)
    (f := fun p : Exp rT × Exp rT => (Exp.litExtract p.1).bind extr)
    (some_branch := fun q : (Exp rT × Exp rT) × β =>
      (Exp.litExtract q.1.2).bind extr |>.bind fun x2 =>
        some (Exp.lit (mkResult q.2 x2))) ?_ ?_
  · refine Option.measurable_bind_param (β := BaseLit rT) (γ := β)
      (f := fun p : Exp rT × Exp rT => Exp.litExtract p.1)
      (some_branch := fun q : (Exp rT × Exp rT) × BaseLit rT => extr q.2) ?_ ?_
    · exact litExtract.measurable.comp measurable_fst
    · exact hextr.comp measurable_snd
  · refine Option.measurable_bind_param (β := β) (γ := Exp rT)
      (f := fun q : (Exp rT × Exp rT) × β => (Exp.litExtract q.1.2).bind extr)
      (some_branch := fun r : ((Exp rT × Exp rT) × β) × β =>
        some (Exp.lit (mkResult r.1.2 r.2))) ?_ ?_
    · refine Option.measurable_bind_param (β := BaseLit rT) (γ := β)
        (f := fun q : (Exp rT × Exp rT) × β => Exp.litExtract q.1.2)
        (some_branch := fun r : ((Exp rT × Exp rT) × β) × BaseLit rT => extr r.2)
        ?_ ?_
      · exact litExtract.measurable.comp (measurable_snd.comp measurable_fst)
      · exact hextr.comp measurable_snd
    · show Measurable fun r : ((Exp rT × Exp rT) × β) × β =>
        (some (Exp.lit (mkResult r.1.2 r.2)) : Option (Exp rT))
      refine MeasurableEmbedding.some_mk.measurable.comp ?_
      refine Exp.lit.measurable.comp ?_
      exact hmk.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

/-- Integer binary operation on literals. -/
@[reducible] def liftII (f : Int → Int → Int) : Exp rT × Exp rT → Option (Exp rT) :=
  liftBin BaseLit.intExtract (fun z1 z2 => .int (f z1 z2))

/-- Boolean binary operation on literals. -/
@[reducible] def liftBB (f : Bool → Bool → Bool) : Exp rT × Exp rT → Option (Exp rT) :=
  liftBin BaseLit.boolExtract (fun b1 b2 => .bool (f b1 b2))

/-- Integer comparison on literals. -/
@[reducible] def liftIB (f : Int → Int → Bool) : Exp rT × Exp rT → Option (Exp rT) :=
  liftBin BaseLit.intExtract (fun z1 z2 => .bool (f z1 z2))

theorem liftII.measurable [MeasurableSpace rT] [Inhabited rT] (f : Int → Int → Int) :
    Measurable (liftII (rT := rT) f) :=
  liftBin.measurable _ _ BaseLit.intExtract.measurable
    (Measurable.of_discrete.comp (Measurable.of_discrete (α := Int × Int) (β := Int)
      (f := Function.uncurry f)))

theorem liftBB.measurable [MeasurableSpace rT] [Inhabited rT] (f : Bool → Bool → Bool) :
    Measurable (liftBB (rT := rT) f) :=
  liftBin.measurable _ _ BaseLit.boolExtract.measurable
    (Measurable.of_discrete.comp (Measurable.of_discrete (α := Bool × Bool) (β := Bool)
      (f := Function.uncurry f)))

theorem liftIB.measurable [MeasurableSpace rT] [Inhabited rT] (f : Int → Int → Bool) :
    Measurable (liftIB (rT := rT) f) :=
  liftBin.measurable _ _ BaseLit.intExtract.measurable
    (Measurable.of_discrete.comp (Measurable.of_discrete (α := Int × Int) (β := Bool)
      (f := Function.uncurry f)))

/-- Real comparison on literals. -/
@[reducible] def liftRB (f : rT → rT → Bool) : Exp rT × Exp rT → Option (Exp rT) :=
  liftBin BaseLit.realExtract (fun r1 r2 => .bool (f r1 r2))

theorem liftRB.measurable [MeasurableSpace rT] [Inhabited rT] (f : rT → rT → Bool)
    (hf : Measurable (Function.uncurry f)) :
    Measurable (liftRB (rT := rT) f) := by
  refine liftBin.measurable _ _ BaseLit.realExtract.measurable ?_
  show Measurable (Function.uncurry (fun r1 r2 : rT => BaseLit.bool (f r1 r2)))
  exact BaseLit.bool.measurable.comp hf

/-- Real binary operation on literals. -/
@[reducible] def liftRR (f : rT → rT → rT) : Exp rT × Exp rT → Option (Exp rT) :=
  liftBin BaseLit.realExtract (fun r1 r2 => .real (f r1 r2))

theorem liftRR.measurable [MeasurableSpace rT] [Inhabited rT] (f : rT → rT → rT)
    (hf : Measurable (Function.uncurry f)) :
    Measurable (liftRR (rT := rT) f) := by
  refine liftBin.measurable _ _ BaseLit.realExtract.measurable ?_
  show Measurable (Function.uncurry (fun r1 r2 : rT => BaseLit.real (f r1 r2)))
  exact BaseLit.real.measurable.comp hf

/-- Integer operation on integer literals, real operation on real literals. -/
@[reducible] def liftIIorRR (fi : Int → Int → Int) (f : rT → rT → rT) :
    Exp rT × Exp rT → Option (Exp rT) :=
  fun p => (liftII fi p).orElse (fun _ => liftRR f p)

theorem liftIIorRR.measurable [MeasurableSpace rT] [Inhabited rT]
    (fi : Int → Int → Int) (f : rT → rT → rT) (hf : Measurable (Function.uncurry f)) :
    Measurable (liftIIorRR (rT := rT) fi f) := by
  have hrw : liftIIorRR (rT := rT) fi f
      = fun p => Option.casesOn (motive := fun _ => Option (Exp rT)) (liftII fi p)
          (liftRR f p) (fun x => some x) := by
    funext p
    show (liftII fi p).orElse (fun _ => liftRR f p) = _
    cases liftII fi p <;> rfl
  rw [hrw]
  exact Option.measurable_elim_param (liftII.measurable fi) (liftRR.measurable f hf)
    (MeasurableEmbedding.some_mk.measurable.comp measurable_snd)

/-- Integer comparison on integer literals, real comparison on real literals. -/
@[reducible] def liftLtLe (fi : Int → Int → Bool) (f : rT → rT → Bool) :
    Exp rT × Exp rT → Option (Exp rT) :=
  fun p => (liftIB fi p).orElse (fun _ => liftRB f p)

theorem liftLtLe.measurable [MeasurableSpace rT] [Inhabited rT]
    (fi : Int → Int → Bool) (f : rT → rT → Bool) (hf : Measurable (Function.uncurry f)) :
    Measurable (liftLtLe (rT := rT) fi f) := by
  have hrw : liftLtLe (rT := rT) fi f
      = fun p => Option.casesOn (motive := fun _ => Option (Exp rT)) (liftIB fi p)
          (liftRB f p) (fun x => some x) := by
    funext p
    show (liftIB fi p).orElse (fun _ => liftRB f p) = _
    cases liftIB fi p <;> rfl
  rw [hrw]
  exact Option.measurable_elim_param (liftIB.measurable fi) (liftRB.measurable f hf)
    (MeasurableEmbedding.some_mk.measurable.comp measurable_snd)

/-- Equality of literals, also under a common `inl` or `inr`. -/
def liftEq (p : Exp rT × Exp rT) : Option (Exp rT) :=
  match p.1, p.2 with
  | .lit l1, .lit l2 => some (Exp.lit (.bool (decide (l1 = l2))))
  | .inl (.lit l1), .inl (.lit l2) => some (Exp.lit (.bool (decide (l1 = l2))))
  | .inr (.lit l1), .inr (.lit l2) => some (Exp.lit (.bool (decide (l1 = l2))))
  | .inl (.lit _), .inr (.lit _) => some (Exp.lit (.bool false))
  | .inr (.lit _), .inl (.lit _) => some (Exp.lit (.bool false))
  | _, _ => none

/-! `liftEq` splits on the first operand into one continuation per live shape
(`.lit`, `.inl`, `.inr`); a direct `cases` on both operands is too large. -/

/-- `liftEq (.lit l1, v2)`, taking `(v2, l1)`. -/
def liftEq_litK [DecidableEq (BaseLit rT)] (p : Exp rT × BaseLit rT) : Option (Exp rT) :=
  match p.1 with
  | .lit l2 => some (Exp.lit (.bool (decide (p.2 = l2))))
  | _ => none

/-- `liftEq (.inl e1', v2)`, taking `(e1', v2)`. -/
def liftEq_inlK [DecidableEq (BaseLit rT)] (p : Exp rT × Exp rT) : Option (Exp rT) :=
  match p.1, p.2 with
  | .lit l1, .inl (.lit l2) => some (Exp.lit (.bool (decide (l1 = l2))))
  | .lit _, .inr (.lit _) => some (Exp.lit (.bool false))
  | _, _ => none

/-- `liftEq (.inr e1', v2)`, taking `(e1', v2)`. -/
def liftEq_inrK [DecidableEq (BaseLit rT)] (p : Exp rT × Exp rT) : Option (Exp rT) :=
  match p.1, p.2 with
  | .lit l1, .inr (.lit l2) => some (Exp.lit (.bool (decide (l1 = l2))))
  | .lit _, .inl (.lit _) => some (Exp.lit (.bool false))
  | _, _ => none

private theorem measurableSet_range_diag {X Y : Type _} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableEq X] {ι : X → Y} (hι : MeasurableEmbedding ι) :
    MeasurableSet (Set.range fun x => (ι x, ι x)) := by
  have hrw : Set.range (fun x => (ι x, ι x)) = Prod.map ι ι '' Set.diagonal X := by
    ext ⟨a, b⟩; constructor
    · rintro ⟨x, hx⟩; exact ⟨(x, x), rfl, hx⟩
    · rintro ⟨⟨x, y⟩, hxy, hx⟩
      obtain rfl : x = y := hxy
      exact ⟨x, hx⟩
  rw [hrw]
  exact (hι.prodMap hι).measurableSet_image' MeasurableEq.measurableSet_diagonal

/-- Lets `BinOp.eval .eq` compare literals without requiring a discrete `rT`. -/
instance _root_.ProbLang.BaseLit.instMeasurableEq
    {rT : Type _} [MeasurableSpace rT] [Inhabited rT] [MeasurableEq rT] :
    MeasurableEq (BaseLit rT) := by
  refine MeasurableEq.mk ?_
  let Pi (z : Int) : BaseLit rT × BaseLit rT := (.int z, .int z)
  let Pb (b : Bool) : BaseLit rT × BaseLit rT := (.bool b, .bool b)
  let Pl (l : Loc) : BaseLit rT × BaseLit rT := (.loc l, .loc l)
  let Pll (l : Lbl) : BaseLit rT × BaseLit rT := (.lbl l, .lbl l)
  let Pr (r : rT) : BaseLit rT × BaseLit rT := (.real r, .real r)
  have hdecomp : Set.diagonal (BaseLit rT)
      = Set.range Pi ∪ Set.range Pb ∪ {(BaseLit.unit, BaseLit.unit)}
      ∪ Set.range Pl ∪ Set.range Pll ∪ Set.range Pr := by
    ext ⟨a, b⟩
    simp only [Set.mem_diagonal_iff, Set.mem_union, Set.mem_range, Set.mem_singleton_iff,
      Pi, Pb, Pl, Pll, Pr]
    constructor
    · rintro rfl
      cases a with
      | int z => exact .inl (.inl (.inl (.inl (.inl ⟨z, rfl⟩))))
      | bool b => exact .inl (.inl (.inl (.inl (.inr ⟨b, rfl⟩))))
      | unit => exact .inl (.inl (.inl (.inr rfl)))
      | loc l => exact .inl (.inl (.inr ⟨l, rfl⟩))
      | lbl l => exact .inl (.inr ⟨l, rfl⟩)
      | real r => exact .inr ⟨r, rfl⟩
    · rintro ((((((⟨_, h⟩) | ⟨_, h⟩) | h) | ⟨_, h⟩) | ⟨_, h⟩) | ⟨_, h⟩) <;> cases h <;> rfl
  rw [hdecomp]
  refine ((((MeasurableSet.union ?_ ?_).union ?_).union ?_).union ?_).union ?_
  · exact measurableSet_range_diag BaseLit.int.measurableEmbedding
  · exact measurableSet_range_diag BaseLit.bool.measurableEmbedding
  · exact MeasurableSet.singleton _
  · exact measurableSet_range_diag BaseLit.loc.measurableEmbedding
  · exact measurableSet_range_diag BaseLit.lbl.measurableEmbedding
  · exact measurableSet_range_diag BaseLit.real.measurableEmbedding

private theorem decide_eq_BaseLit_measurable
    [MeasurableSpace rT] [Inhabited rT] [DecidableEq (BaseLit rT)]
    [MeasurableEq rT] :
    Measurable (fun p : BaseLit rT × BaseLit rT => decide (p.1 = p.2)) := by
  refine measurable_to_bool ?_
  have hpre : (fun p : BaseLit rT × BaseLit rT => decide (p.1 = p.2)) ⁻¹' {true}
      = Set.diagonal (BaseLit rT) := by ext p; simp [Set.diagonal]
  rw [hpre]
  exact MeasurableEq.measurableSet_diagonal

theorem liftEq_litK.measurable [MeasurableSpace rT] [Inhabited rT]
    [DecidableEq (BaseLit rT)] [MeasurableEq rT] :
    Measurable (liftEq_litK (rT := rT)) := by
  let _ : MeasurableSpace (Option Int) := instLocalOption
  let _ : MeasurableSpace (Option (BaseLit rT)) := instLocalOption
  let _ : MeasurableSpace (Option (Exp rT)) := instLocalOption
  have hrw : liftEq_litK (rT := rT) = fun p : Exp rT × BaseLit rT =>
      (Exp.litExtract p.1).bind fun l2 => some (Exp.lit (.bool (decide (p.2 = l2)))) := by
    funext p; obtain ⟨v2, l1⟩ := p
    cases v2 <;> simp [liftEq_litK, Exp.litExtract, Option.bind]
  rw [hrw]
  refine Option.measurable_bind_param (β := BaseLit rT) (γ := Exp rT)
    (f := fun p : Exp rT × BaseLit rT => Exp.litExtract p.1)
    (some_branch := fun r : (Exp rT × BaseLit rT) × BaseLit rT =>
      some (Exp.lit (BaseLit.bool (decide (r.1.2 = r.2))))) ?_ ?_
  · exact litExtract.measurable.comp measurable_fst
  · refine MeasurableEmbedding.some_mk.measurable.comp ?_
    refine Exp.lit.measurable.comp ?_
    refine BaseLit.bool.measurable.comp ?_
    exact decide_eq_BaseLit_measurable.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

theorem liftEq_inlK.measurable [MeasurableSpace rT] [Inhabited rT]
    [DecidableEq (BaseLit rT)] [MeasurableEq rT] :
    Measurable (liftEq_inlK (rT := rT)) := by
  let _ : MeasurableSpace (Option (BaseLit rT)) := instLocalOption
  let _ : MeasurableSpace (Option (Exp rT)) := instLocalOption
  have hrw : liftEq_inlK (rT := rT) = fun p : Exp rT × Exp rT =>
      (Exp.litExtract p.1).bind fun l1 =>
        (Exp.inlExtract p.2).casesOn
          ((Exp.inrExtract p.2).casesOn none (fun e2 => (Exp.litExtract e2).bind fun _ =>
            some (Exp.lit (.bool false))))
          (fun e1 => (Exp.litExtract e1).bind fun l2 =>
            some (Exp.lit (.bool (decide (l1 = l2))))) := by
    funext p; obtain ⟨v1, v2⟩ := p
    cases v1 <;> simp [liftEq_inlK, Exp.litExtract, Exp.inlExtract, Exp.inrExtract, Option.bind];
      cases v2 <;> simp <;>
      rename_i e2 <;> cases e2 <;>
      simp
  rw [hrw]
  refine Option.measurable_bind_param (β := BaseLit rT) (γ := Exp rT)
    (f := fun p : Exp rT × Exp rT => Exp.litExtract p.1)
    (some_branch := fun r : (Exp rT × Exp rT) × BaseLit rT =>
      (Exp.inlExtract r.1.2).casesOn
        ((Exp.inrExtract r.1.2).casesOn none (fun e2 => (Exp.litExtract e2).bind fun _ =>
          some (Exp.lit (BaseLit.bool false))))
        (fun e1 => (Exp.litExtract e1).bind fun l2 =>
          some (Exp.lit (BaseLit.bool (decide (r.2 = l2)))))) ?_ ?_
  · exact litExtract.measurable.comp measurable_fst
  · apply Option.measurable_elim_param (β := Exp rT) (γ := Option (Exp rT))
      (f := fun r : (Exp rT × Exp rT) × BaseLit rT => Exp.inlExtract r.1.2)
      (default := fun r : (Exp rT × Exp rT) × BaseLit rT =>
        (Exp.inrExtract r.1.2).casesOn none (fun e2 =>
          (Exp.litExtract e2).bind fun _ => some (Exp.lit (BaseLit.bool false))))
      (some_branch := fun s : ((Exp rT × Exp rT) × BaseLit rT) × Exp rT =>
        (Exp.litExtract s.2).bind fun l2 =>
          some (Exp.lit (BaseLit.bool (decide (s.1.2 = l2)))))
    · exact inlExtract.measurable.comp (measurable_snd.comp measurable_fst)
    · apply Option.measurable_elim_param (β := Exp rT) (γ := Option (Exp rT))
        (f := fun r : (Exp rT × Exp rT) × BaseLit rT => Exp.inrExtract r.1.2)
        (default := fun _ => none)
        (some_branch := fun s : ((Exp rT × Exp rT) × BaseLit rT) × Exp rT =>
          (Exp.litExtract s.2).bind fun _ => some (Exp.lit (BaseLit.bool false)))
      · exact inrExtract.measurable.comp (measurable_snd.comp measurable_fst)
      · exact measurable_const
      · refine Option.measurable_bind_param (β := BaseLit rT) (γ := Exp rT)
          (f := fun s : ((Exp rT × Exp rT) × BaseLit rT) × Exp rT => Exp.litExtract s.2)
          (some_branch := fun _ : (((Exp rT × Exp rT) × BaseLit rT) × Exp rT) × BaseLit rT =>
            some (Exp.lit (BaseLit.bool false))) ?_ ?_
        · exact litExtract.measurable.comp measurable_snd
        · exact measurable_const
    · refine Option.measurable_bind_param (β := BaseLit rT) (γ := Exp rT)
        (f := fun s : ((Exp rT × Exp rT) × BaseLit rT) × Exp rT => Exp.litExtract s.2)
        (some_branch := fun t : (((Exp rT × Exp rT) × BaseLit rT) × Exp rT) × BaseLit rT =>
          some (Exp.lit (BaseLit.bool (decide (t.1.1.2 = t.2))))) ?_ ?_
      · exact litExtract.measurable.comp measurable_snd
      · refine MeasurableEmbedding.some_mk.measurable.comp ?_
        refine Exp.lit.measurable.comp ?_
        refine BaseLit.bool.measurable.comp ?_
        exact decide_eq_BaseLit_measurable.comp
          ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)

theorem liftEq_inrK.measurable [MeasurableSpace rT] [Inhabited rT]
    [DecidableEq (BaseLit rT)] [MeasurableEq rT] :
    Measurable (liftEq_inrK (rT := rT)) := by
  let _ : MeasurableSpace (Option (BaseLit rT)) := instLocalOption
  let _ : MeasurableSpace (Option (Exp rT)) := instLocalOption
  have hrw : liftEq_inrK (rT := rT) = fun p : Exp rT × Exp rT =>
      (Exp.litExtract p.1).bind fun l1 =>
        (Exp.inrExtract p.2).casesOn
          ((Exp.inlExtract p.2).casesOn none (fun e2 => (Exp.litExtract e2).bind fun _ =>
            some (Exp.lit (.bool false))))
          (fun e1 => (Exp.litExtract e1).bind fun l2 =>
            some (Exp.lit (.bool (decide (l1 = l2))))) := by
    funext p; obtain ⟨v1, v2⟩ := p
    cases v1 <;> simp [liftEq_inrK, Exp.litExtract, Exp.inlExtract, Exp.inrExtract, Option.bind];
      cases v2 <;> simp <;>
      rename_i e2 <;> cases e2 <;>
      simp
  rw [hrw]
  refine Option.measurable_bind_param (β := BaseLit rT) (γ := Exp rT)
    (f := fun p : Exp rT × Exp rT => Exp.litExtract p.1)
    (some_branch := fun r : (Exp rT × Exp rT) × BaseLit rT =>
      (Exp.inrExtract r.1.2).casesOn
        ((Exp.inlExtract r.1.2).casesOn none (fun e2 => (Exp.litExtract e2).bind fun _ =>
          some (Exp.lit (BaseLit.bool false))))
        (fun e1 => (Exp.litExtract e1).bind fun l2 =>
          some (Exp.lit (BaseLit.bool (decide (r.2 = l2)))))) ?_ ?_
  · exact litExtract.measurable.comp measurable_fst
  · apply Option.measurable_elim_param (β := Exp rT) (γ := Option (Exp rT))
      (f := fun r : (Exp rT × Exp rT) × BaseLit rT => Exp.inrExtract r.1.2)
      (default := fun r : (Exp rT × Exp rT) × BaseLit rT =>
        (Exp.inlExtract r.1.2).casesOn none (fun e2 =>
          (Exp.litExtract e2).bind fun _ => some (Exp.lit (BaseLit.bool false))))
      (some_branch := fun s : ((Exp rT × Exp rT) × BaseLit rT) × Exp rT =>
        (Exp.litExtract s.2).bind fun l2 =>
          some (Exp.lit (BaseLit.bool (decide (s.1.2 = l2)))))
    · exact inrExtract.measurable.comp (measurable_snd.comp measurable_fst)
    · apply Option.measurable_elim_param (β := Exp rT) (γ := Option (Exp rT))
        (f := fun r : (Exp rT × Exp rT) × BaseLit rT => Exp.inlExtract r.1.2)
        (default := fun _ => none)
        (some_branch := fun s : ((Exp rT × Exp rT) × BaseLit rT) × Exp rT =>
          (Exp.litExtract s.2).bind fun _ => some (Exp.lit (BaseLit.bool false)))
      · exact inlExtract.measurable.comp (measurable_snd.comp measurable_fst)
      · exact measurable_const
      · refine Option.measurable_bind_param (β := BaseLit rT) (γ := Exp rT)
          (f := fun s : ((Exp rT × Exp rT) × BaseLit rT) × Exp rT => Exp.litExtract s.2)
          (some_branch := fun _ : (((Exp rT × Exp rT) × BaseLit rT) × Exp rT) × BaseLit rT =>
            some (Exp.lit (BaseLit.bool false))) ?_ ?_
        · exact litExtract.measurable.comp measurable_snd
        · exact measurable_const
    · refine Option.measurable_bind_param (β := BaseLit rT) (γ := Exp rT)
        (f := fun s : ((Exp rT × Exp rT) × BaseLit rT) × Exp rT => Exp.litExtract s.2)
        (some_branch := fun t : (((Exp rT × Exp rT) × BaseLit rT) × Exp rT) × BaseLit rT =>
          some (Exp.lit (BaseLit.bool (decide (t.1.1.2 = t.2))))) ?_ ?_
      · exact litExtract.measurable.comp measurable_snd
      · refine MeasurableEmbedding.some_mk.measurable.comp ?_
        refine Exp.lit.measurable.comp ?_
        refine BaseLit.bool.measurable.comp ?_
        exact decide_eq_BaseLit_measurable.comp
          ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)

/-- A separate lemma to keep `liftEq.measurable` within its heartbeat budget. -/
private theorem liftEq_dispatch [MeasurableSpace rT] [Inhabited rT]
    [DecidableEq (BaseLit rT)] (p : Exp rT × Exp rT) :
    liftEq p =
      Exp.casesOn (motive := fun _ => Option (Exp rT)) p.1
        (fun _ => none) (fun _ => none)
        (fun l1 => liftEq_litK (p.2, l1))
        (fun _ => none) (fun _ => none)
        (fun _ _ => none) (fun _ _ => none) (fun _ _ _ => none) (fun _ _ _ => none)
        (fun _ _ => none) (fun _ => none) (fun _ => none)
        (fun e1' => liftEq_inlK (e1', p.2))
        (fun e1' => liftEq_inrK (e1', p.2))
        (fun _ _ _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (fun _ => none) (fun _ _ => none) none none (fun _ _ => none) := by
  obtain ⟨v1, v2⟩ := p
  cases v1 with
  | lit l1 =>
    show liftEq (.lit l1, v2) = liftEq_litK (v2, l1)
    cases v2 <;> simp [liftEq, liftEq_litK]
  | inl e1' =>
    show liftEq (.inl e1', v2) = liftEq_inlK (e1', v2)
    cases e1' <;> cases v2 <;> simp [liftEq, liftEq_inlK] <;>
      (rename_i e2'; cases e2' <;> simp)
  | inr e1' =>
    show liftEq (.inr e1', v2) = liftEq_inrK (e1', v2)
    cases e1' <;> cases v2 <;> simp [liftEq, liftEq_inrK] <;>
      (rename_i e2'; cases e2' <;> simp)
  | _ => rfl

theorem liftEq.measurable [MeasurableSpace rT] [Inhabited rT]
    [DecidableEq (BaseLit rT)] [MeasurableEq rT] :
    Measurable (liftEq (rT := rT)) := by
  rw [show liftEq (rT := rT) = _ from funext liftEq_dispatch]
  refine Exp.measurable_casesOn_param (rT := rT) (α := Option (Exp rT)) (β := Exp rT)
    (c_bvar := fun _ => none) (c_fvar := fun _ => none)
    (c_lit := fun q : Exp rT × BaseLit rT => liftEq_litK q)
    (c_lam := fun _ => none) (c_fix := fun _ => none)
    (c_app := fun _ => none) (c_unop := fun _ => none) (c_binop := fun _ => none)
    (c_cond := fun _ => none) (c_pair := fun _ => none)
    (c_fst := fun _ => none) (c_snd := fun _ => none)
    (c_inl := fun q : Exp rT × Exp rT => liftEq_inlK (q.2, q.1))
    (c_inr := fun q : Exp rT × Exp rT => liftEq_inrK (q.2, q.1))
    (c_case := fun _ => none) (c_alloc := fun _ => none) (c_load := fun _ => none)
    (c_store := fun _ => none) (c_tape := fun _ => none) (c_rand := fun _ => none)
    (c_fail := fun _ => none) (c_urand := fun _ => none) (c_scrut := fun _ => none)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  iterate 2 exact measurable_const
  · exact liftEq_litK.measurable
  iterate 9 exact measurable_const
  · show Measurable fun q : Exp rT × Exp rT => liftEq_inlK (q.2, q.1)
    exact liftEq_inlK.measurable.comp (measurable_snd.prodMk measurable_fst)
  · show Measurable fun q : Exp rT × Exp rT => liftEq_inrK (q.2, q.1)
    exact liftEq_inrK.measurable.comp (measurable_snd.prodMk measurable_fst)
  all_goals exact measurable_const

/-- Splits two `Exp` operands down to their `BaseLit` constructors, closing each arm by `rfl`. -/
local macro "lit_pair_cases " v1:ident v2:ident : tactic =>
  `(tactic| cases $v1:ident <;> first
    | rfl
    | (rename_i l1; cases l1 <;> first
        | rfl
        | (cases $v2:ident <;> first
            | rfl
            | (rename_i l2; cases l2 <;> rfl))))

private theorem liftII_def_eq (f : Int → Int → Int) (v1 v2 : Exp rT) :
    liftII f (v1, v2) =
      (match v1, v2 with
       | .lit (.int z1), .lit (.int z2) => some (Exp.lit (.int (f z1 z2)))
       | _, _ => none) := by
  unfold liftII liftBin
  cases v1 <;> simp [Exp.litExtract, BaseLit.intExtract, Option.bind]
  rename_i l1
  cases l1 <;> simp; cases v2 <;> simp [BaseLit.intExtract]
  rename_i l2
  cases l2 <;> simp

private theorem liftBB_def_eq (f : Bool → Bool → Bool) (v1 v2 : Exp rT) :
    liftBB f (v1, v2) =
      (match v1, v2 with
       | .lit (.bool b1), .lit (.bool b2) => some (Exp.lit (.bool (f b1 b2)))
       | _, _ => none) := by
  unfold liftBB liftBin
  cases v1 <;> simp [Exp.litExtract, BaseLit.boolExtract, Option.bind]
  rename_i l1
  cases l1 <;> simp; cases v2 <;>
    simp [BaseLit.boolExtract]
  rename_i l2
  cases l2 <;> simp

private theorem liftIB_def_eq (f : Int → Int → Bool) (v1 v2 : Exp rT) :
    liftIB f (v1, v2) =
      (match v1, v2 with
       | .lit (.int z1), .lit (.int z2) => some (Exp.lit (.bool (f z1 z2)))
       | _, _ => none) := by
  unfold liftIB liftBin
  cases v1 <;> simp [Exp.litExtract, BaseLit.intExtract, Option.bind]
  rename_i l1
  cases l1 <;> simp; cases v2 <;>
    simp [BaseLit.intExtract]
  rename_i l2
  cases l2 <;> simp

private theorem liftRB_def_eq [LawfulProbLangℝ rT] (f : rT → rT → Bool) (v1 v2 : Exp rT) :
    liftRB f (v1, v2) =
      (match v1, v2 with
       | .lit (.real r1), .lit (.real r2) => some (Exp.lit (.bool (f r1 r2)))
       | _, _ => none) := by
  unfold liftRB liftBin
  cases v1 <;> simp [Exp.litExtract, BaseLit.realExtract, Option.bind]
  rename_i l1
  cases l1 <;> simp; cases v2 <;>
    simp [BaseLit.realExtract]
  rename_i l2
  cases l2 <;> simp

private theorem liftRR_def_eq [LawfulProbLangℝ rT] (f : rT → rT → rT) (v1 v2 : Exp rT) :
    liftRR f (v1, v2) =
      (match v1, v2 with
       | .lit (.real r1), .lit (.real r2) => some (Exp.lit (.real (f r1 r2)))
       | _, _ => none) := by
  unfold liftRR liftBin
  cases v1 <;> simp [Exp.litExtract, BaseLit.realExtract, Option.bind]
  rename_i l1
  cases l1 <;> simp; cases v2 <;>
    simp [BaseLit.realExtract]
  rename_i l2
  cases l2 <;> simp

private theorem liftIIorRR_def_eq [LawfulProbLangℝ rT] (fi : Int → Int → Int) (f : rT → rT → rT)
    (v1 v2 : Exp rT) :
    liftIIorRR fi f (v1, v2) =
      (match v1, v2 with
       | .lit (.int z1), .lit (.int z2) => some (Exp.lit (.int (fi z1 z2)))
       | .lit (.real r1), .lit (.real r2) => some (Exp.lit (.real (f r1 r2)))
       | _, _ => none) := by
  show (liftII fi (v1, v2)).orElse (fun _ => liftRR f (v1, v2)) = _
  rw [liftII_def_eq, liftRR_def_eq]
  lit_pair_cases v1 v2

private theorem liftLtLe_def_eq [LawfulProbLangℝ rT] (fi : Int → Int → Bool) (f : rT → rT → Bool)
    (v1 v2 : Exp rT) :
    liftLtLe fi f (v1, v2) =
      (match v1, v2 with
       | .lit (.int z1), .lit (.int z2) => some (Exp.lit (.bool (fi z1 z2)))
       | .lit (.real r1), .lit (.real r2) => some (Exp.lit (.bool (f r1 r2)))
       | _, _ => none) := by
  show (liftIB fi (v1, v2)).orElse (fun _ => liftRB f (v1, v2)) = _
  rw [liftIB_def_eq, liftRB_def_eq]
  lit_pair_cases v1 v2

private theorem BinOp.eval_plus_eq_liftIIorRR [LawfulProbLangℝ rT] (v1 v2 : Exp rT) :
    BinOp.eval .plus v1 v2 = liftIIorRR (· + ·) ProbLangℝ.realAdd (v1, v2) := by
  rw [liftIIorRR_def_eq]
  lit_pair_cases v1 v2

private theorem BinOp.eval_lt_eq_liftLtLe [LawfulProbLangℝ rT] (v1 v2 : Exp rT) :
    BinOp.eval .lt v1 v2 = liftLtLe (decide <| · < ·) ProbLangℝ.realLt (v1, v2) := by
  rw [liftLtLe_def_eq]
  lit_pair_cases v1 v2

private theorem BinOp.eval_le_eq_liftLtLe [LawfulProbLangℝ rT] (v1 v2 : Exp rT) :
    BinOp.eval .le v1 v2 = liftLtLe (decide <| · ≤ ·) ProbLangℝ.realLe (v1, v2) := by
  rw [liftLtLe_def_eq]
  lit_pair_cases v1 v2

/-- A separate lemma to keep `BinOp.eval_eq_lift` within its heartbeat budget. -/
private theorem BinOp.eval_eq_eq_liftEq [LawfulProbLangℝ rT] (v1 v2 : Exp rT) :
    BinOp.eval .eq v1 v2 = liftEq (v1, v2) := by
  have h (l1 l2 : BaseLit rT) : (l1 == l2) = decide (l1 = l2) := Bool.beq_eq_decide_eq l1 l2
  cases v1 <;> cases v2 <;> (try simp [BinOp.eval, liftEq, h]) <;>
    (rename_i ein1 ein2; cases ein1 <;> cases ein2 <;> simp)

theorem BinOp.eval_eq_lift [LawfulProbLangℝ rT] (op : BinOp) (v1 v2 : Exp rT) :
    BinOp.eval op v1 v2 =
      (match op with
       | .plus  => liftIIorRR (· + ·) ProbLangℝ.realAdd
       | .minus => liftII (· - ·)
       | .mult  => liftII (· * ·)
       | .div   => liftII (· / ·)
       | .mod   => liftII (· % ·)
       | .shl   => liftII (fun z1 z2 => z1 * 2 ^ z2.toNat)
       | .shr   => liftII (fun z1 z2 => z1 / 2 ^ z2.toNat)
       | .and   => liftBB (· && ·)
       | .or    => liftBB (· || ·)
       | .xor   => liftBB (· ^^ ·)
       | .lt    => liftLtLe (decide <| · < ·) ProbLangℝ.realLt
       | .le    => liftLtLe (decide <| · ≤ ·) ProbLangℝ.realLe
       | .eq    => liftEq) (v1, v2) := by
  cases op
  all_goals
    dsimp only []
    first
      | (rw [liftII_def_eq]; lit_pair_cases v1 v2)
      | (rw [liftBB_def_eq]; lit_pair_cases v1 v2)
      | exact BinOp.eval_plus_eq_liftIIorRR v1 v2
      | exact BinOp.eval_lt_eq_liftLtLe v1 v2
      | exact BinOp.eval_le_eq_liftLtLe v1 v2
      | exact BinOp.eval_eq_eq_liftEq v1 v2

theorem BinOp_eval.measurable [LawfulProbLangℝ rT] :
    Measurable (fun (q : BinOp × Exp rT × Exp rT) => BinOp.eval q.1 q.2.1 q.2.2) := by
  rw [show (fun (q : BinOp × Exp rT × Exp rT) => BinOp.eval q.1 q.2.1 q.2.2) = _ from
    funext fun q => BinOp.eval_eq_lift q.1 q.2.1 q.2.2]
  apply measurable_from_prod_countable_right
  intro op
  cases op
  all_goals dsimp only
  · exact liftIIorRR.measurable _ _ LawfulProbLangℝ.measurable_realAdd
  · exact liftII.measurable _
  · exact liftII.measurable _
  · exact liftII.measurable _
  · exact liftII.measurable _
  · exact liftBB.measurable _
  · exact liftBB.measurable _
  · exact liftBB.measurable _
  · exact liftEq.measurable
  · exact liftLtLe.measurable _ _ LawfulProbLangℝ.measurable_realLt
  · exact liftLtLe.measurable _ _ LawfulProbLangℝ.measurable_realLe
  · exact liftII.measurable _
  · exact liftII.measurable _

/-! ### `Pat.tryMatch` -/

theorem tryMatch_fixed.measurable [LawfulProbLangℝ rT] (p : Pat rT) :
    Measurable (fun e : Exp rT => Pat.tryMatch p e) := by
  induction p with
  | wildcard =>
    have hrw : (fun e : Exp rT => Pat.tryMatch .wildcard e)
             = (fun e => (some e : Option (Exp rT))) := by
      funext e; rfl
    rw [hrw]
    exact MeasurableEmbedding.some_mk.measurable
  | lit l =>
    refine measurable_of_lit_only none
      (f := fun l' => if (l == l') = true then some (Exp.lit .unit) else none) ?_
      fun e => by cases e <;> rfl
    intro S hS
    have hrw : (fun l' : BaseLit rT =>
        if (l == l') = true then (some (Exp.lit BaseLit.unit) : Option (Exp rT)) else none) ⁻¹' S
        = (if (some (Exp.lit BaseLit.unit) : Option (Exp rT)) ∈ S then {l} else ∅)
          ∪ (if (none : Option (Exp rT)) ∈ S then ({l}ᶜ : Set (BaseLit rT)) else ∅) := by
      ext l'
      by_cases hll : l = l'
      · subst hll; simp
      · simp [hll, Ne.symm hll]
    rw [hrw]
    refine MeasurableSet.union ?_ ?_
    · split_ifs
      · exact MeasurableSet.singleton l
      · exact MeasurableSet.empty
    · split_ifs
      · exact (MeasurableSet.singleton l).compl
      · exact MeasurableSet.empty
  | pair p1 p2 ih1 ih2 =>
    have hrw : (fun e : Exp rT => Pat.tryMatch (.pair p1 p2) e)
        = fun e => Exp.casesOn (motive := fun _ => Option (Exp rT)) e
            (fun _ => none) (fun _ => none) (fun _ => none)
            (fun _ => none) (fun _ => none)
            (fun _ _ => none) (fun _ _ => none) (fun _ _ _ => none) (fun _ _ _ => none)
            (fun e1 e2 =>
              (Pat.tryMatch p1 e1).bind fun b1 =>
              (Pat.tryMatch p2 e2).bind fun b2 =>
              some (.pair b1 b2))
            (fun _ => none) (fun _ => none) (fun _ => none) (fun _ => none)
            (fun _ _ _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
            (fun _ => none) (fun _ _ => none) none none (fun _ _ => none) := by
      funext e; cases e <;> rfl
    rw [hrw]
    apply Exp.measurable_casesOn
      (c_bvar := fun _ => none) (c_fvar := fun _ => none) (c_lit := fun _ => none)
      (c_lam := fun _ => none) (c_fix := fun _ => none)
      (c_app := fun _ => none) (c_unop := fun _ => none) (c_binop := fun _ => none)
      (c_cond := fun _ => none)
      (c_pair := fun q : Exp rT × Exp rT =>
        (Pat.tryMatch p1 q.1).bind fun b1 =>
        (Pat.tryMatch p2 q.2).bind fun b2 =>
        some (Exp.pair b1 b2))
      (c_fst := fun _ => none) (c_snd := fun _ => none)
      (c_inl := fun _ => none) (c_inr := fun _ => none) (c_case := fun _ => none)
      (c_alloc := fun _ => none) (c_load := fun _ => none) (c_store := fun _ => none)
      (c_tape := fun _ => none) (c_rand := fun _ => none) (c_fail := fun _ => none)
      (c_urand := fun _ => none)
      (c_scrut := fun _ => none)
    case h_pair =>
      let _ : MeasurableSpace (Option (Exp rT)) := instLocalOption
      refine Option.measurable_bind_param (β := Exp rT) (γ := Exp rT)
        (f := fun q : Exp rT × Exp rT => Pat.tryMatch p1 q.1)
        (some_branch := fun s : (Exp rT × Exp rT) × Exp rT =>
          (Pat.tryMatch p2 s.1.2).bind fun b2 =>
          some (Exp.pair s.2 b2)) ?_ ?_
      · exact ih1.comp measurable_fst
      · refine Option.measurable_bind_param (β := Exp rT) (γ := Exp rT)
          (f := fun s : (Exp rT × Exp rT) × Exp rT => Pat.tryMatch p2 s.1.2)
          (some_branch := fun r : ((Exp rT × Exp rT) × Exp rT) × Exp rT =>
            (some (Exp.pair r.1.2 r.2) : Option (Exp rT))) ?_ ?_
        · exact ih2.comp (measurable_snd.comp measurable_fst)
        · exact MeasurableEmbedding.some_mk.measurable.comp (Exp.pair.measurable.comp
            ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    all_goals exact measurable_const
  | inl p ih =>
    have hrw : (fun e : Exp rT => Pat.tryMatch (.inl p) e)
        = fun e => Exp.casesOn (motive := fun _ => Option (Exp rT)) e
            (fun _ => none) (fun _ => none) (fun _ => none)
            (fun _ => none) (fun _ => none)
            (fun _ _ => none) (fun _ _ => none) (fun _ _ _ => none) (fun _ _ _ => none)
            (fun _ _ => none) (fun _ => none) (fun _ => none)
            (fun e' => Pat.tryMatch p e')
            (fun _ => none)
            (fun _ _ _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
            (fun _ => none) (fun _ _ => none) none none (fun _ _ => none) := by
      funext e; cases e <;> rfl
    rw [hrw]
    apply Exp.measurable_casesOn
      (c_bvar := fun _ => none) (c_fvar := fun _ => none) (c_lit := fun _ => none)
      (c_lam := fun _ => none) (c_fix := fun _ => none)
      (c_app := fun _ => none) (c_unop := fun _ => none) (c_binop := fun _ => none)
      (c_cond := fun _ => none) (c_pair := fun _ => none)
      (c_fst := fun _ => none) (c_snd := fun _ => none)
      (c_inl := fun e' : Exp rT => Pat.tryMatch p e')
      (c_inr := fun _ => none) (c_case := fun _ => none)
      (c_alloc := fun _ => none) (c_load := fun _ => none) (c_store := fun _ => none)
      (c_tape := fun _ => none) (c_rand := fun _ => none) (c_fail := fun _ => none)
      (c_urand := fun _ => none)
      (c_scrut := fun _ => none)
    case h_inl => exact ih
    all_goals exact measurable_const
  | inr p ih =>
    have hrw : (fun e : Exp rT => Pat.tryMatch (.inr p) e)
        = fun e => Exp.casesOn (motive := fun _ => Option (Exp rT)) e
            (fun _ => none) (fun _ => none) (fun _ => none)
            (fun _ => none) (fun _ => none)
            (fun _ _ => none) (fun _ _ => none) (fun _ _ _ => none) (fun _ _ _ => none)
            (fun _ _ => none) (fun _ => none) (fun _ => none) (fun _ => none)
            (fun e' => Pat.tryMatch p e')
            (fun _ _ _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
            (fun _ => none) (fun _ _ => none) none none (fun _ _ => none) := by
      funext e; cases e <;> rfl
    rw [hrw]
    apply Exp.measurable_casesOn
      (c_bvar := fun _ => none) (c_fvar := fun _ => none) (c_lit := fun _ => none)
      (c_lam := fun _ => none) (c_fix := fun _ => none)
      (c_app := fun _ => none) (c_unop := fun _ => none) (c_binop := fun _ => none)
      (c_cond := fun _ => none) (c_pair := fun _ => none)
      (c_fst := fun _ => none) (c_snd := fun _ => none)
      (c_inl := fun _ => none)
      (c_inr := fun e' : Exp rT => Pat.tryMatch p e')
      (c_case := fun _ => none)
      (c_alloc := fun _ => none) (c_load := fun _ => none) (c_store := fun _ => none)
      (c_tape := fun _ => none) (c_rand := fun _ => none) (c_fail := fun _ => none)
      (c_urand := fun _ => none)
      (c_scrut := fun _ => none)
    case h_inr => exact ih
    all_goals exact measurable_const

theorem tryMatch.measurable [LawfulProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT] :
    Measurable (fun (q : Pat rT × Exp rT) => Pat.tryMatch q.1 q.2) := by
  apply measurable_from_prod_countable_right
  exact tryMatch_fixed.measurable

/-- The set where `Pat.shape` of a measurable `Exp × Pat`-valued map is `s` is measurable,
given the cell hypothesis at `s`. -/
theorem tryMatch.measurableSet_shape_preimage [LawfulProbLangℝ rT] {s : Pat.Shape}
    {α : Type*} [MeasurableSpace α]
    (ih : ∀ {U : Set (Option (Exp rT))}, MeasurableSet U →
      MeasurableSet {q : Exp rT × Pat rT | Pat.shape q.2 = s ∧
        Function.uncurry (fun (e : Exp rT) (p : Pat rT) => Pat.tryMatch p e) q ∈ U})
    {g : α → Exp rT × Pat rT} (hg : Measurable g) :
    MeasurableSet {q : α | Pat.shape (g q).2 = s} := by
  convert (ih MeasurableSet.univ).preimage hg using 1
  ext q; simp

/-- The cell of a pattern shape `sw` wrapping `s'` by a unary constructor (`inl` or `inr`) is
measurable: the wrapped match splits on whether the `Exp` is built by `ctorE` (cell IH) or not
(`none`). -/
theorem tryMatch.measurableSet_wrap [LawfulProbLangℝ rT] {s' sw : Pat.Shape}
    {ctorE : Exp rT → Exp rT} {ctorP : Pat rT → Pat rT}
    (hE : MeasurableEmbedding ctorE) (hP : MeasurableEmbedding ctorP)
    (hcases : ∀ p, Pat.shape p = sw → ∃ p', p = ctorP p' ∧ Pat.shape p' = s')
    (hshape : ∀ p', Pat.shape (ctorP p') = sw ↔ Pat.shape p' = s')
    (hA : ∀ e' p', Pat.tryMatch (ctorP p') (ctorE e') = Pat.tryMatch p' e')
    (hB : ∀ e p', (¬ ∃ e', ctorE e' = e) → Pat.tryMatch (ctorP p') e = none)
    (ih : ∀ {U : Set (Option (Exp rT))}, MeasurableSet U →
      MeasurableSet {q : Exp rT × Pat rT | Pat.shape q.2 = s' ∧
        Function.uncurry (fun (e : Exp rT) (p : Pat rT) => Pat.tryMatch p e) q ∈ U})
    {U : Set (Option (Exp rT))} (hU : MeasurableSet U) :
    MeasurableSet {q : Exp rT × Pat rT | Pat.shape q.2 = sw ∧
      Function.uncurry (fun (e : Exp rT) (p : Pat rT) => Pat.tryMatch p e) q ∈ U} := by
  have hcell : {q : Exp rT × Pat rT | Pat.shape q.2 = sw ∧
        Function.uncurry (fun (e : Exp rT) (p : Pat rT) => Pat.tryMatch p e) q ∈ U}
      = (Prod.map (id : Exp rT → Exp rT) ctorP) ''
        {q : Exp rT × Pat rT | Pat.shape q.2 = s' ∧ Pat.tryMatch (ctorP q.2) q.1 ∈ U} := by
    ext ⟨e, p⟩
    constructor
    · rintro ⟨hsh, hp⟩
      obtain ⟨p', rfl, hs'⟩ := hcases p hsh
      exact ⟨(e, p'), ⟨hs', hp⟩, by simp [Prod.map_apply]⟩
    · rintro ⟨⟨e0, p0⟩, ⟨hsh, hp⟩, hheq⟩
      simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at hheq
      obtain ⟨rfl, rfl⟩ := hheq
      exact ⟨(hshape _).2 hsh, hp⟩
  rw [hcell]
  refine (MeasurableEmbedding.id.prodMap hP).measurableSet_image' ?_
  have h_inner_eq : {q : Exp rT × Pat rT | Pat.shape q.2 = s' ∧
          Pat.tryMatch (ctorP q.2) q.1 ∈ U}
      = ((Prod.map ctorE (id : Pat rT → Pat rT)) ''
          {q : Exp rT × Pat rT | Pat.shape q.2 = s' ∧
            Function.uncurry (fun (e : Exp rT) (p : Pat rT) => Pat.tryMatch p e) q ∈ U})
        ∪ ({q : Exp rT × Pat rT | q.1 ∉ Set.range ctorE ∧
            Pat.shape q.2 = s' ∧ (none : Option (Exp rT)) ∈ U}) := by
    ext ⟨e, p'⟩
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨hsh, hp⟩
      by_cases hrange : ∃ e', ctorE e' = e
      · left
        obtain ⟨e', rfl⟩ := hrange
        refine ⟨(e', p'), ⟨hsh, ?_⟩, ?_⟩
        · show Pat.tryMatch p' e' ∈ U
          rw [← hA]; exact hp
        · simp [Prod.map_apply]
      · right
        refine ⟨hrange, hsh, ?_⟩
        rw [hB _ _ hrange] at hp
        exact hp
    · rintro (⟨⟨e0, p0⟩, ⟨hsh, hp⟩, heq⟩ | ⟨hne, hsh, hnone⟩)
      · simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        refine ⟨hsh, ?_⟩
        rw [hA]; exact hp
      · refine ⟨hsh, ?_⟩
        rw [hB _ _ hne]; exact hnone
  rw [h_inner_eq]
  refine MeasurableSet.union ?_ ?_
  · refine (hE.prodMap MeasurableEmbedding.id).measurableSet_image' ?_
    exact ih hU
  · by_cases hnoneU : (none : Option (Exp rT)) ∈ U
    · have hB_eq2 : {q : Exp rT × Pat rT | q.1 ∉ Set.range ctorE ∧
          Pat.shape q.2 = s' ∧ (none : Option (Exp rT)) ∈ U}
          = (((Set.range ctorE)ᶜ ×ˢ (Set.univ : Set (Pat rT)))
              ∩ {q : Exp rT × Pat rT | Pat.shape q.2 = s'}) := by
        ext ⟨e, p'⟩
        simp [hnoneU]
      rw [hB_eq2]
      exact (MeasurableSet.prod hE.measurableSet_range.compl MeasurableSet.univ).inter
        (tryMatch.measurableSet_shape_preimage ih measurable_id)
    · have hB_eq2 : {q : Exp rT × Pat rT | q.1 ∉ Set.range ctorE ∧
          Pat.shape q.2 = s' ∧ (none : Option (Exp rT)) ∈ U} = ∅ := by
        ext ⟨e, p'⟩
        simp [hnoneU]
      rw [hB_eq2]
      exact MeasurableSet.empty


/-- Unlike `tryMatch.measurable`, needs no `Countable rT`. `tryMatch` recurses on both
arguments, so each `Pat.shape` cell is computed by hand: the pattern constructor's
embedding factors out, and the `Exp` argument splits into the matching constructor's
range (handled by the cell IH) and its complement (`none`). -/
theorem tryMatch.measurable_joint [LawfulProbLangℝ rT] :
    Measurable (Function.uncurry (fun (p : Pat rT) (e : Exp rT) => Pat.tryMatch p e)) := by
  have hjoint : Measurable
      (Function.uncurry (fun (e : Exp rT) (p : Pat rT) => Pat.tryMatch p e)) := by
    apply _root_.StructRec.measurable_of_cells_param (β := Exp rT) (T := Pat rT)
      (α := Option (Exp rT)) Pat.shape
    intro s
    induction s with
    | wildcard =>
      intro U hU
      have hcell : {q : Exp rT × Pat rT | Pat.shape q.2 = Pat.Shape.wildcard ∧
          Function.uncurry (fun (e : Exp rT) (p : Pat rT) => Pat.tryMatch p e) q ∈ U}
          = ((Option.some : Exp rT → Option (Exp rT)) ⁻¹' U) ×ˢ
            ({Pat.wildcard} : Set (Pat rT)) := by
        ext ⟨e, p⟩
        simp only [Set.mem_ofPred_eq, Function.uncurry, Set.mem_prod, Set.mem_preimage,
          Set.mem_singleton_iff]
        cases p <;> simp [Pat.tryMatch]
      rw [hcell]
      refine MeasurableSet.prod ?_ (by simp)
      exact MeasurableEmbedding.some_mk.measurable hU
    | lit =>
      intro U hU
      refine _root_.StructRec.cell_dataLeaf_param Pat.shape
        (γ := BaseLit rT) (ctor := Pat.lit)
        (c := fun (e : Exp rT) (b : BaseLit rT) => Pat.tryMatch (.lit b) e)
        Pat.lit.measurableEmbedding
        (fun p => by cases p <;> simp)
        (fun _ _ => rfl)
        ?_ hU
      have hrw : Function.uncurry
            (fun (e : Exp rT) (b : BaseLit rT) => Pat.tryMatch (.lit b) e)
          = fun q : Exp rT × BaseLit rT =>
            Exp.casesOn (motive := fun _ => Option (Exp rT)) q.1
              (fun _ => none) (fun _ => none)
              (fun l' => if (q.2 == l') = true then some (Exp.lit BaseLit.unit) else none)
              (fun _ => none) (fun _ => none)
              (fun _ _ => none) (fun _ _ => none) (fun _ _ _ => none) (fun _ _ _ => none)
              (fun _ _ => none) (fun _ => none) (fun _ => none) (fun _ => none) (fun _ => none)
              (fun _ _ _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
              (fun _ => none) (fun _ _ => none) none none (fun _ _ => none) := by
        funext q; obtain ⟨e, b⟩ := q; cases e <;> rfl
      rw [hrw]
      apply Exp.measurable_casesOn_param
        (β := BaseLit rT)
        (c_bvar := fun _ => none) (c_fvar := fun _ => none)
        (c_lit := fun q : BaseLit rT × BaseLit rT =>
          if (q.1 == q.2) = true then some (Exp.lit BaseLit.unit) else none)
        (c_lam := fun _ => none) (c_fix := fun _ => none)
        (c_app := fun _ => none) (c_unop := fun _ => none) (c_binop := fun _ => none)
        (c_cond := fun _ => none) (c_pair := fun _ => none)
        (c_fst := fun _ => none) (c_snd := fun _ => none)
        (c_inl := fun _ => none) (c_inr := fun _ => none) (c_case := fun _ => none)
        (c_alloc := fun _ => none) (c_load := fun _ => none) (c_store := fun _ => none)
        (c_tape := fun _ => none) (c_rand := fun _ => none) (c_fail := fun _ => none)
        (c_urand := fun _ => none)
        (c_scrut := fun _ => none)
      all_goals first | exact measurable_const | skip
      intro S hS
      have hrw' : (fun q : BaseLit rT × BaseLit rT =>
          if (q.1 == q.2) = true then (some (Exp.lit BaseLit.unit) : Option (Exp rT))
            else none) ⁻¹' S
          = (if (some (Exp.lit BaseLit.unit) : Option (Exp rT)) ∈ S
              then {q : BaseLit rT × BaseLit rT | q.1 = q.2} else ∅)
            ∪ (if (none : Option (Exp rT)) ∈ S
              then {q : BaseLit rT × BaseLit rT | q.1 = q.2}ᶜ else ∅) := by
        ext ⟨b, l'⟩
        by_cases hll : b = l'
        · subst hll; simp
        · simp [hll]
      rw [hrw']
      refine MeasurableSet.union ?_ ?_ <;> split_ifs
      · exact measurableSet_eq_fun (by fun_prop) (by fun_prop)
      · exact MeasurableSet.empty
      · exact (measurableSet_eq_fun (by fun_prop) (by fun_prop)).compl
      · exact MeasurableSet.empty
    | inl s' ih =>
      intro U hU
      refine tryMatch.measurableSet_wrap Exp.inl.measurableEmbedding Pat.inl.measurableEmbedding
        (fun p hsh => by cases p <;> simp_all) (fun p' => by simp) (fun _ _ => rfl) ?_ ih hU
      intro e p' h
      cases e <;> first | rfl | (rename_i e'; exact absurd ⟨e', rfl⟩ h)
    | inr s' ih =>
      intro U hU
      refine tryMatch.measurableSet_wrap Exp.inr.measurableEmbedding Pat.inr.measurableEmbedding
        (fun p hsh => by cases p <;> simp_all) (fun p' => by simp) (fun _ _ => rfl) ?_ ih hU
      intro e p' h
      cases e <;> first | rfl | (rename_i e'; exact absurd ⟨e', rfl⟩ h)
    | pair s1 s2 ih1 ih2 =>
      intro U hU
      have hcell : {q : Exp rT × Pat rT | Pat.shape q.2 = Pat.Shape.pair s1 s2 ∧
            Function.uncurry (fun (e : Exp rT) (p : Pat rT) => Pat.tryMatch p e) q ∈ U}
          = (fun (q : Exp rT × Pat rT × Pat rT) => (q.1, Pat.pair q.2.1 q.2.2)) ''
            {q : Exp rT × Pat rT × Pat rT |
              Pat.shape q.2.1 = s1 ∧ Pat.shape q.2.2 = s2 ∧
              Pat.tryMatch (Pat.pair q.2.1 q.2.2) q.1 ∈ U} := by
        ext ⟨e, p⟩
        constructor
        · rintro ⟨hsh, hp⟩
          cases p
          case wildcard => simp at hsh
          case lit b => simp at hsh
          case pair p1 p2 =>
            simp only [Pat.shape_pair, Pat.Shape.pair.injEq] at hsh
            obtain ⟨hs1, hs2⟩ := hsh
            exact ⟨(e, p1, p2), ⟨hs1, hs2, hp⟩, by simp⟩
          case inl p' => simp at hsh
          case inr p' => simp at hsh
        · rintro ⟨⟨e0, p1, p2⟩, ⟨hs1, hs2, hp⟩, hheq⟩
          simp only [Prod.mk.injEq] at hheq
          obtain ⟨rfl, rfl⟩ := hheq
          exact ⟨by simp [hs1, hs2], hp⟩
      rw [hcell]
      have hemb : MeasurableEmbedding
          (fun (q : Exp rT × Pat rT × Pat rT) => (q.1, Pat.pair q.2.1 q.2.2)) :=
        MeasurableEmbedding.id.prodMap Pat.pair.measurableEmbedding
      refine hemb.measurableSet_image' ?_
      have hA_eq : ∀ (e1 e2 : Exp rT) (p1 p2 : Pat rT),
          Pat.tryMatch (Pat.pair p1 p2) (Exp.pair e1 e2)
            = (Pat.tryMatch p1 e1).bind (fun b1 =>
              (Pat.tryMatch p2 e2).bind (fun b2 => some (Exp.pair b1 b2))) := fun _ _ _ _ => rfl
      have hB_eq : ∀ (e : Exp rT) (p1 p2 : Pat rT),
          (¬ ∃ ee : Exp rT × Exp rT, Function.uncurry Exp.pair ee = e) →
          Pat.tryMatch (Pat.pair p1 p2) e = none := by
        intro e p1 p2 h
        cases e
        all_goals first
          | rfl
          | (rename_i e1 e2; exact absurd ⟨(e1, e2), rfl⟩ h)
      have h_inner_eq : {q : Exp rT × Pat rT × Pat rT |
            Pat.shape q.2.1 = s1 ∧ Pat.shape q.2.2 = s2 ∧
            Pat.tryMatch (Pat.pair q.2.1 q.2.2) q.1 ∈ U}
          = (((fun (q : (Exp rT × Exp rT) × (Pat rT × Pat rT)) =>
                (Exp.pair q.1.1 q.1.2, q.2.1, q.2.2))) ''
              {q : (Exp rT × Exp rT) × (Pat rT × Pat rT) |
                Pat.shape q.2.1 = s1 ∧ Pat.shape q.2.2 = s2 ∧
                ((Pat.tryMatch q.2.1 q.1.1).bind fun b1 =>
                  (Pat.tryMatch q.2.2 q.1.2).bind fun b2 => some (Exp.pair b1 b2)) ∈ U})
            ∪ ({q : Exp rT × Pat rT × Pat rT |
                q.1 ∉ (Set.range (Function.uncurry (Exp.pair : Exp rT → Exp rT → Exp rT))) ∧
                Pat.shape q.2.1 = s1 ∧ Pat.shape q.2.2 = s2 ∧ (none : Option (Exp rT)) ∈ U}) := by
        ext ⟨e, p1, p2⟩
        simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, Set.mem_range,
          Function.uncurry, Prod.mk.injEq]
        constructor
        · rintro ⟨hs1, hs2, hp⟩
          by_cases hrange : ∃ ee : Exp rT × Exp rT, Function.uncurry Exp.pair ee = e
          · left
            obtain ⟨⟨e1, e2⟩, he⟩ := hrange
            simp only [Function.uncurry] at he
            subst he
            refine ⟨((e1, e2), (p1, p2)), ⟨hs1, hs2, ?_⟩, ?_⟩
            · show ((Pat.tryMatch p1 e1).bind _) ∈ U
              rw [← hA_eq]; exact hp
            · simp
          · right
            refine ⟨hrange, hs1, hs2, ?_⟩
            rw [hB_eq _ _ _ hrange] at hp; exact hp
        · rintro (⟨⟨⟨e1, e2⟩, p1', p2'⟩, ⟨hs1, hs2, hp⟩, heq⟩ | ⟨hne, hs1, hs2, hnone⟩)
          · obtain ⟨rfl, rfl, rfl⟩ := heq
            refine ⟨hs1, hs2, ?_⟩
            rw [hA_eq]; exact hp
          · refine ⟨hs1, hs2, ?_⟩
            rw [hB_eq _ _ _ hne]; exact hnone
      rw [h_inner_eq]
      refine MeasurableSet.union ?_ ?_
      · have hemb_inner : MeasurableEmbedding
            (fun (q : (Exp rT × Exp rT) × (Pat rT × Pat rT)) =>
              (Exp.pair q.1.1 q.1.2, q.2.1, q.2.2)) :=
          Exp.pair.measurableEmbedding.prodMap MeasurableEmbedding.id
        refine hemb_inner.measurableSet_image' ?_
        set qfun : Option (Exp rT) × Option (Exp rT) → Option (Exp rT) :=
          fun p => p.1.bind fun b1 => p.2.bind fun b2 => some (Exp.pair b1 b2) with hqfun
        have hqfun_meas : Measurable qfun := by
          let _ : MeasurableSpace (Option (Exp rT)) := instLocalOption
          refine Option.measurable_bind_param (β := Exp rT) (γ := Exp rT)
            (f := fun p : Option (Exp rT) × Option (Exp rT) => p.1)
            (some_branch := fun (s : (Option (Exp rT) × Option (Exp rT)) × Exp rT) =>
              s.1.2.bind fun b2 => some (Exp.pair s.2 b2)) ?_ ?_
          · exact measurable_fst
          · refine Option.measurable_bind_param (β := Exp rT) (γ := Exp rT)
              (f := fun s : (Option (Exp rT) × Option (Exp rT)) × Exp rT => s.1.2)
              (some_branch := fun r : ((Option (Exp rT) × Option (Exp rT)) × Exp rT) × Exp rT =>
                (some (Exp.pair r.1.2 r.2) : Option (Exp rT))) ?_ ?_
            · exact measurable_snd.comp measurable_fst
            · exact MeasurableEmbedding.some_mk.measurable.comp (Exp.pair.measurable.comp
                ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
        set V : Set (Option (Exp rT) × Option (Exp rT)) := qfun ⁻¹' U with hV_def
        have hV : MeasurableSet V := hqfun_meas hU
        have hconv : {q : (Exp rT × Exp rT) × (Pat rT × Pat rT) |
                Pat.shape q.2.1 = s1 ∧ Pat.shape q.2.2 = s2 ∧
                ((Pat.tryMatch q.2.1 q.1.1).bind fun b1 =>
                  (Pat.tryMatch q.2.2 q.1.2).bind fun b2 => some (Exp.pair b1 b2)) ∈ U}
            = {q : (Exp rT × Exp rT) × (Pat rT × Pat rT) |
                Pat.shape q.2.1 = s1 ∧ Pat.shape q.2.2 = s2 ∧
                (Pat.tryMatch q.2.1 q.1.1, Pat.tryMatch q.2.2 q.1.2) ∈ V} := by
          ext q; simp [hV_def, hqfun]
        rw [hconv]
        have hgen : (Prod.instMeasurableSpace : MeasurableSpace (Option (Exp rT) × Option (Exp rT)))
            = .generateFrom (Set.image2 (· ×ˢ ·) {S : Set (Option (Exp rT)) | MeasurableSet S}
                                                  {S : Set (Option (Exp rT)) | MeasurableSet S}) :=
          generateFrom_prod.symm
        have hpi : IsPiSystem
            (Set.image2 (· ×ˢ ·) {S : Set (Option (Exp rT)) | MeasurableSet S}
                                  {S : Set (Option (Exp rT)) | MeasurableSet S}) :=
          MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
        set Joint : Set (Option (Exp rT) × Option (Exp rT)) →
            Set ((Exp rT × Exp rT) × (Pat rT × Pat rT)) :=
          fun V'' => {q : (Exp rT × Exp rT) × (Pat rT × Pat rT) |
            Pat.shape q.2.1 = s1 ∧ Pat.shape q.2.2 = s2 ∧
            (Pat.tryMatch q.2.1 q.1.1, Pat.tryMatch q.2.2 q.1.2) ∈ V''} with hJoint_def
        suffices h : ∀ V'', MeasurableSet V'' → MeasurableSet (Joint V'') by exact h V hV
        intro V'' hV''
        refine MeasurableSpace.induction_on_inter
          (C := fun V''' _ => MeasurableSet (Joint V''')) hgen hpi ?_ ?_ ?_ ?_ V'' hV''
        · show MeasurableSet (Joint ∅)
          convert MeasurableSet.empty
          ext q; simp [hJoint_def]
        · rintro _ ⟨A, hA, B, hB, rfl⟩
          show MeasurableSet (Joint (A ×ˢ B))
          have heq : Joint (A ×ˢ B)
              = ((fun q : (Exp rT × Exp rT) × (Pat rT × Pat rT) =>
                  (q.1.1, q.2.1)) ⁻¹'
                  {x : Exp rT × Pat rT | Pat.shape x.2 = s1 ∧
                    Function.uncurry (fun e p => Pat.tryMatch p e) x ∈ A})
                ∩ ((fun q : (Exp rT × Exp rT) × (Pat rT × Pat rT) =>
                    (q.1.2, q.2.2)) ⁻¹'
                    {x : Exp rT × Pat rT | Pat.shape x.2 = s2 ∧
                      Function.uncurry (fun e p => Pat.tryMatch p e) x ∈ B}) := by
            ext q; simp [hJoint_def, Function.uncurry]; tauto
          rw [heq]
          refine MeasurableSet.inter ?_ ?_
          · exact MeasurableSet.preimage (ih1 hA) (by fun_prop)
          · exact MeasurableSet.preimage (ih2 hB) (by fun_prop)
        · intro V''' _ IH
          show MeasurableSet (Joint V'''ᶜ)
          have heq : Joint V'''ᶜ
              = ({q : (Exp rT × Exp rT) × (Pat rT × Pat rT) |
                  Pat.shape q.2.1 = s1 ∧ Pat.shape q.2.2 = s2}) \ Joint V''' := by
            ext q; simp [hJoint_def]; tauto
          rw [heq]
          refine MeasurableSet.diff ?_ IH
          have h1 : MeasurableSet
              {q : (Exp rT × Exp rT) × (Pat rT × Pat rT) | Pat.shape q.2.1 = s1} :=
            tryMatch.measurableSet_shape_preimage ih1
              (g := fun q : (Exp rT × Exp rT) × (Pat rT × Pat rT) => (q.1.1, q.2.1)) (by fun_prop)
          have h2 : MeasurableSet
              {q : (Exp rT × Exp rT) × (Pat rT × Pat rT) | Pat.shape q.2.2 = s2} :=
            tryMatch.measurableSet_shape_preimage ih2
              (g := fun q : (Exp rT × Exp rT) × (Pat rT × Pat rT) => (q.1.2, q.2.2)) (by fun_prop)
          convert h1.inter h2 using 1
          measurability
        · intro F _ _ IH
          show MeasurableSet (Joint (⋃ i, F i))
          have heq : Joint (⋃ i, F i) = ⋃ i, Joint (F i) := by
            ext q
            simp only [hJoint_def, Set.mem_iUnion, Set.mem_ofPred_eq]
            tauto
          rw [heq]
          exact MeasurableSet.iUnion IH
      · by_cases hnoneU : (none : Option (Exp rT)) ∈ U
        · have hB_eq2 : {q : Exp rT × Pat rT × Pat rT |
                q.1 ∉ Set.range (Function.uncurry (Exp.pair : Exp rT → Exp rT → Exp rT)) ∧
                Pat.shape q.2.1 = s1 ∧ Pat.shape q.2.2 = s2 ∧ (none : Option (Exp rT)) ∈ U}
              = (((Set.range (Function.uncurry (Exp.pair : Exp rT → Exp rT → Exp rT)))ᶜ ×ˢ
                  (Set.univ : Set (Pat rT × Pat rT)))
                 ∩ {q : Exp rT × Pat rT × Pat rT |
                    Pat.shape q.2.1 = s1 ∧ Pat.shape q.2.2 = s2}) := by
            ext ⟨e, p1, p2⟩; simp [hnoneU]
          rw [hB_eq2]
          refine MeasurableSet.inter (MeasurableSet.prod ?_ MeasurableSet.univ) ?_
          · exact Exp.pair.measurableEmbedding.measurableSet_range.compl
          · have h1 : MeasurableSet {q : Exp rT × Pat rT × Pat rT | Pat.shape q.2.1 = s1} :=
              tryMatch.measurableSet_shape_preimage ih1
                (g := fun q : Exp rT × Pat rT × Pat rT => (q.1, q.2.1)) (by fun_prop)
            have h2 : MeasurableSet {q : Exp rT × Pat rT × Pat rT | Pat.shape q.2.2 = s2} :=
              tryMatch.measurableSet_shape_preimage ih2
                (g := fun q : Exp rT × Pat rT × Pat rT => (q.1, q.2.2)) (by fun_prop)
            convert h1.inter h2 using 1
            measurability
        · have hB_eq2 : {q : Exp rT × Pat rT × Pat rT |
                q.1 ∉ Set.range (Function.uncurry (Exp.pair : Exp rT → Exp rT → Exp rT)) ∧
                Pat.shape q.2.1 = s1 ∧ Pat.shape q.2.2 = s2 ∧
                (none : Option (Exp rT)) ∈ U} = ∅ := by
            ext ⟨e, p1, p2⟩; simp [hnoneU]
          rw [hB_eq2]
          exact MeasurableSet.empty
  rw [show (Function.uncurry (fun (p : Pat rT) (e : Exp rT) => Pat.tryMatch p e))
        = (Function.uncurry (fun (e : Exp rT) (p : Pat rT) => Pat.tryMatch p e)) ∘ Prod.swap from
      funext fun _ => rfl]
  exact hjoint.comp measurable_swap

end Exp
end ProbLang
end ProbLangMeasures
