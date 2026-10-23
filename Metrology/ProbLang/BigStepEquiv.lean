module

public import Metrology.ProbLang.BigStep
public import Metrology.ProbLang.Exec

@[expose] public section

/-! # The big-step semantics agrees with the reduction semantics

`bigStep_eq_limExec`, for countable `rT`, where every map out of `Cfg rT` is measurable. -/

noncomputable section
open MeasureTheory Measure

namespace ProbLang

open Exp
open Cfg (uniform uniformReal)
open Pat (tryMatch)
open Measurable (of_discrete)
open OrderHom (lfp map_lfp lfp_le)

variable {rT : Type _}

/-- The number of evaluation positions of `e` still holding a non-value, which drops each time one
is evaluated and orders the induction in `bigStepF_limExec_le`. -/
def Exp.pendingArgs : Exp rT → Nat
  | .app e1 e2 | .binop _ e1 e2 | .pair e1 e2 | .store e1 e2 | .allocN e1 e2 | .rand e1 e2 =>
    pending e1 + pending e2
  | .unop _ e | .fst e | .snd e | .inl e | .inr e | .alloc e | .load e | .tape e
  | .scrut e _ | .cond e _ _ | .case e _ _ => pending e
  | _ => 0
where pending (e : Exp rT) : Nat := if e.isValue then 0 else 1

/-- Filling a hole with a value instead of a non-value lowers `pendingArgs`. -/
theorem Exp.pendingArgs_fillItem_lt (Ki : EctxItem rT) {e v : Exp rT} (he : ¬e.isValue)
    (hv : v.isValue) : (Ki.fillItem v).pendingArgs < (Ki.fillItem e).pendingArgs := by
  cases Ki <;>
    simp [EctxItem.fillItem, Exp.pendingArgs, pendingArgs.pending, ofVal, he, hv]

/-- A `casesOn` that returns `none` came from the `some` branch returning `none`. -/
private theorem Option.casesOn_some_eq_none {α β : Type _} {o : Option α} {b : β}
    {f : α → Option β} (h : o.casesOn (some b) f = none) : ∃ a, o = some a ∧ f a = none := by
  cases o <;> simp_all

/-- If the decomposition of a one-argument redex is `none`, the argument is a value. -/
private theorem Exp.isValue_of_decompItem₁ {β : Type _} {e1 : Exp rT} {b : β}
    (h : e1.toVal?.casesOn (some b) (fun _ => none) = none) : e1.isValue :=
  let ⟨_, hv1, _⟩ := Option.casesOn_some_eq_none h
  toVal?_isValue hv1

/-- If the decomposition of a two-argument redex is `none`, both arguments are values. -/
private theorem Exp.isValue_of_decompItem₂ {β : Type _} {e1 e2 : Exp rT} {b : β}
    {f : Val rT → β}
    (h : e2.toVal?.casesOn (some b) (fun v2 => e1.toVal?.casesOn (some (f v2)) fun _ => none) =
      none) : e1.isValue ∧ e2.isValue :=
  let ⟨_, hv2, h⟩ := Option.casesOn_some_eq_none h
  ⟨isValue_of_decompItem₁ h, toVal?_isValue hv2⟩

variable [MeasurableSpace rT]

/-! ## Evaluators that return values -/

/-- `R` returns a value configuration unchanged. -/
def RetVal (R : Cfg rT → Measure (Cfg rT)) : Prop :=
  ∀ e σ, e.isValue → R ⟨e, σ⟩ = dirac ⟨e, σ⟩

/-- `R` only produces value configurations. -/
def OnlyVal (R : Cfg rT → Measure (Cfg rT)) : Prop :=
  ∀ ρ, ∀ᵐ c ∂(R ρ), c.expr.isValue

/-- Two continuations that agree on values give equal binds against an `OnlyVal` kernel. -/
theorem OnlyVal.bind_congr {R : Cfg rT → Measure (Cfg rT)} (hR : OnlyVal R) (ρ : Cfg rT)
    {f g : Cfg rT → Measure (Cfg rT)} (h : ∀ c : Cfg rT, c.expr.isValue → f c = g c) :
    (R ρ).bind f = (R ρ).bind g :=
  bind_congr_right ((hR ρ).mono fun c hc => h c hc)

variable [LawfulProbLangℝ rT]

/-- `bigStepF` read in the Giry monad. -/
def measureOps : EvalOps rT (Measure (Cfg rT)) where
  ret := dirac
  bind := bind
  stuck _ := 0
  uniform := uniform
  uniformReal := uniformReal

/-! ## Head reducts that are values -/

theorem UnOp.eval_isValue {op : UnOp} {v r : Exp rT} (h : op.eval v = some r) : r.isValue := by
  unfold UnOp.eval at h
  split at h <;> cases h <;> exact ⟨.lit⟩

theorem BinOp.eval_isValue {op : BinOp} {v1 v2 r : Exp rT} (h : op.eval v1 v2 = some r) :
    r.isValue := by
  unfold BinOp.eval at h
  split at h <;> cases h <;> exact ⟨.lit⟩

theorem Pat.tryMatch_isValue {p : Pat rT} {v b : Exp rT} (hv : v.isValue)
    (h : p.tryMatch v = some b) : b.isValue := by
  induction p generalizing v b with
  | wildcard => cases h; exact hv
  | lit l =>
    cases v <;> simp only [tryMatch, reduceCtorEq] at h
    split at h <;> cases h; exact ⟨.lit⟩
  | pair p1 p2 ih1 ih2 =>
    obtain ⟨w⟩ := hv
    cases w <;> simp only [tryMatch, reduceCtorEq] at h
    rename_i w1 w2
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b1, h1, b2, h2, rfl⟩ := h
    obtain ⟨w1'⟩ := ih1 w1.toIsValue h1
    obtain ⟨w2'⟩ := ih2 w2.toIsValue h2
    exact ⟨.pair w1' w2'⟩
  | inl p ih =>
    obtain ⟨w⟩ := hv
    cases w <;> simp only [tryMatch, reduceCtorEq] at h
    rename_i w; exact ih w.toIsValue h
  | inr p ih =>
    obtain ⟨w⟩ := hv
    cases w <;> simp only [tryMatch, reduceCtorEq] at h
    rename_i w; exact ih w.toIsValue h

/-- Monotone convergence for a countable sum over configurations (via counting measure). -/
theorem Cfg.tsum_iSup_of_monotone {f : ℕ → Cfg rT → ENNReal}
    (hf : ∀ a, Monotone (f · a)) (hm : ∀ x, Measurable (f x)) :
    ∑' a, ⨆ n, f n a = ⨆ n, ∑' a, f n a := by
  simp_rw [← MeasureTheory.lintegral_count]
  exact MeasureTheory.lintegral_iSup (fun _ => hm _) (fun _ _ hmn a => hf a hmn)

/-! ## `limExec` on values and head redexes -/

/-- `limExec` returns value configurations unchanged. -/
theorem limExec_retVal : RetVal (limExec (rT := rT)) :=
  fun _ _ ⟨w⟩ => limExec_of_isVal w

/-- `limExec` at a head redex runs the head step and continues. -/
theorem limExec_head {e : Exp rT} {σ : State rT} (hdec : e.decompItem = none)
    (hnv : ¬e.isValue) : limExec ⟨e, σ⟩ = (headStep ⟨e, σ⟩).bind limExec := by
  rw [limExec_not_final hnv, primStep_eq_headStep hdec]
section Discrete

variable [Countable rT]

/-! ## `Measure.bind` on a discrete space -/

theorem bind_mono_discrete {μ ν : Measure (Cfg rT)} {f g : Cfg rT → Measure (Cfg rT)}
    (hμ : μ ≤ ν) (hfg : ∀ c, f c ≤ g c) : μ.bind f ≤ ν.bind g := by
  refine le_iff.mpr fun s hs => ?_
  rw [bind_apply hs of_discrete.aemeasurable,
    bind_apply hs of_discrete.aemeasurable]
  exact lintegral_mono' hμ fun c => hfg c s

theorem bind_mono_ae_discrete {μ : Measure (Cfg rT)} {f g : Cfg rT → Measure (Cfg rT)}
    (hfg : ∀ᵐ c ∂μ, f c ≤ g c) : μ.bind f ≤ μ.bind g := by
  refine le_iff.mpr fun s hs => ?_
  rw [bind_apply hs of_discrete.aemeasurable,
    bind_apply hs of_discrete.aemeasurable]
  exact lintegral_mono_ae (hfg.mono fun c h => h s)

theorem dirac_bind_discrete (c : Cfg rT) (f : Cfg rT → Measure (Cfg rT)) :
    (dirac c).bind f = f c :=
  dirac_bind of_discrete c

theorem bind_bind_discrete (μ : Measure (Cfg rT)) (f g : Cfg rT → Measure (Cfg rT)) :
    (μ.bind f).bind g = μ.bind fun c => (f c).bind g :=
  bind_bind of_discrete.aemeasurable of_discrete.aemeasurable

theorem map_bind_discrete (μ : Measure (Cfg rT)) (f : Cfg rT → Cfg rT)
    (g : Cfg rT → Measure (Cfg rT)) : (μ.map f).bind g = μ.bind (g ∘ f) := by
  rw [Measure.bind, Measure.bind, map_map of_discrete of_discrete]

/-- `bind` is continuous in its measure argument. -/
theorem iSup_bind_discrete {μ : ℕ → Measure (Cfg rT)} (hμ : Monotone μ)
    (f : Cfg rT → Measure (Cfg rT)) : (⨆ n, μ n).bind f = ⨆ n, (μ n).bind f := by
  have hbind : Monotone fun n => (μ n).bind f :=
    fun _ _ h => bind_mono_discrete (hμ h) fun _ => le_rfl
  ext s hs
  rw [iSup_measure_apply hbind hs, bind_apply hs of_discrete.aemeasurable,
    lintegral_countable']
  simp_rw [bind_apply hs of_discrete.aemeasurable, lintegral_countable',
    iSup_measure_apply hμ (MeasurableSet.singleton _), ENNReal.mul_iSup]
  exact Cfg.tsum_iSup_of_monotone (fun c _ _ h => mul_le_mul_right (hμ h _) _)
    fun _ => of_discrete

/-! ## The big-step semantics -/

/-- `bigStepF` is monotone, so `bigStep` is well defined. -/
theorem bigStepF_mono : Monotone (bigStepF (measureOps (rT := rT))) := by
  intro R R' hR ρ
  obtain ⟨e, σ⟩ := ρ
  cases e <;> simp only [bigStepF, measureOps] <;>
    repeat' first
      | exact le_rfl
      | exact hR _
      | apply bind_mono_discrete
      | rintro ⟨_, _⟩
      | split

/-- The big-step semantics: the least fixed point of `bigStepF` in the Giry monad. -/
def bigStep : Cfg rT → Measure (Cfg rT) :=
  lfp ⟨bigStepF measureOps, bigStepF_mono⟩

/-- `bigStep` is a fixed point of `bigStepF`. -/
theorem bigStep_unfold : bigStep (rT := rT) = bigStepF measureOps bigStep :=
  (map_lfp _).symm

section RetValRules
variable {R : Cfg rT → Measure (Cfg rT)} (hR : RetVal R) {e : Exp rT}
include hR

/-- Binding a value-returning kernel at a value just applies the continuation. -/
theorem RetVal.bind_eq {σ : State rT} (he : e.isValue) (f : Cfg rT → Measure (Cfg rT)) :
    (R ⟨e, σ⟩).bind f = f ⟨e, σ⟩ := by
  rw [hR e σ he, dirac_bind_discrete]

/-- Pushing a measure of values through a value-returning `R` changes nothing. -/
theorem RetVal.map_bind {α : Type _}
    [MeasurableSpace α] [DiscreteMeasurableSpace α] (μ : Measure α) (f : α → Cfg rT)
    (hf : ∀ a, (f a).expr.isValue) : (μ.map f).bind R = μ.map f := by
  have hfm : Measurable f := .of_discrete
  calc (μ.map f).bind R = (μ.map f).bind dirac :=
        bind_congr_right <| (ae_map_iff hfm.aemeasurable .of_discrete).mpr <|
          ae_of_all _ fun a => hR _ _ (hf a)
    _ = μ.map f := bind_dirac

/-- Binding a value-returning kernel after an integer draw changes nothing. -/
theorem RetVal.uniform_bind (z : Int)
    (σ : State rT) : (uniform z σ).bind R = uniform z σ := by
  unfold Cfg.uniform
  split
  · exact hR.map_bind _ _ fun _ => ⟨.lit⟩
  · rw [dirac_bind_discrete]; exact hR _ _ ⟨.lit⟩

/-- Binding a value-returning kernel after a real draw changes nothing. -/
theorem RetVal.uniformReal_bind
    (σ : State rT) : (uniformReal σ).bind R = uniformReal σ :=
  hR.map_bind _ _ fun _ => ⟨.lit⟩

/-- One unfolding of the evaluator returns values unchanged, if `R` does. -/
theorem bigStepF_val
    (σ : State rT) (he : e.isValue) : bigStepF measureOps R ⟨e, σ⟩ = dirac ⟨e, σ⟩ := by
  obtain ⟨w⟩ := he
  cases w with
  | lit => rfl
  | lam h => exact ite_eq_left ⟨.lam h⟩
  | fix h => exact ite_eq_left ⟨.fix h⟩
  | pair w1 w2 =>
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq w2.toIsValue, hR.bind_eq w1.toIsValue]
  | inl w => simp only [bigStepF, measureOps]; rw [hR.bind_eq w.toIsValue]
  | inr w => simp only [bigStepF, measureOps]; rw [hR.bind_eq w.toIsValue]

/-- On a head redex, one unfolding of the evaluator takes exactly the head step. -/
theorem bigStepF_head
    {σ : State rT} (hdec : e.decompItem = none) (hnv : ¬e.isValue) :
    bigStepF measureOps R ⟨e, σ⟩ = (headStep ⟨e, σ⟩).bind R := by
  cases e with
  | bvar | fvar | fail => simp [bigStepF, measureOps, headStep]
  | lit => exact absurd ⟨.lit⟩ hnv
  | lam e => simp only [bigStepF, measureOps, ite_eq_right hnv]; simp [headStep]
  | fix e => simp only [bigStepF, measureOps, ite_eq_right hnv]; simp [headStep]
  | urand => exact (hR.uniformReal_bind σ).symm
  | pair e1 e2 =>
    simp only [decompItem] at hdec
    obtain ⟨⟨w1⟩, ⟨w2⟩⟩ := isValue_of_decompItem₂ hdec
    exact absurd ⟨.pair w1 w2⟩ hnv
  | inl e1 =>
    simp only [decompItem] at hdec
    obtain ⟨w1⟩ := isValue_of_decompItem₁ hdec
    exact absurd ⟨.inl w1⟩ hnv
  | inr e1 =>
    simp only [decompItem] at hdec
    obtain ⟨w1⟩ := isValue_of_decompItem₁ hdec
    exact absurd ⟨.inr w1⟩ hnv
  | app e1 e2 =>
    simp only [decompItem] at hdec
    obtain ⟨h1, h2⟩ := isValue_of_decompItem₂ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h2]
    dsimp only
    rw [hR.bind_eq h1]
    dsimp only
    obtain ⟨w1⟩ := h1
    cases w1 <;> simp [headStep, h2, dirac_bind_discrete]
  | binop op e1 e2 =>
    simp only [decompItem] at hdec
    obtain ⟨h1, h2⟩ := isValue_of_decompItem₂ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h2]
    dsimp only
    rw [hR.bind_eq h1]
    dsimp only
    simp only [headStep, isValM_some h1, isValM_some h2]
    cases hop : op.eval e1 e2 with
    | none => simp [Option.unwrapM]
    | some r =>
      simp only [Option.unwrapM, dirac_bind_discrete]
      exact (hR _ _ (BinOp.eval_isValue hop)).symm
  | allocN e1 e2 =>
    simp only [decompItem] at hdec
    obtain ⟨v2, hv2, hdec'⟩ := Option.casesOn_some_eq_none hdec
    obtain ⟨v1, hv1, -⟩ := Option.casesOn_some_eq_none hdec'
    have h1 := toVal?_isValue hv1
    have h2 := toVal?_isValue hv2
    clear hdec hdec' hv1 hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h2]
    dsimp only
    rw [hR.bind_eq h1]
    dsimp only
    rw [hv2]
    obtain ⟨w1⟩ := h1
    cases w1 with
    | @lit b =>
      cases b with
      | int n =>
        simp only [headStep, asValM, hv2]
        split_ifs
        · simp only [dirac_bind_discrete]
          exact (hR _ _ ⟨.lit⟩).symm
        · simp
      | _ => simp [headStep]
    | _ => simp [headStep]
  | store e1 e2 =>
    simp only [decompItem] at hdec
    obtain ⟨v2, hv2, hdec'⟩ := Option.casesOn_some_eq_none hdec
    obtain ⟨v1, hv1, -⟩ := Option.casesOn_some_eq_none hdec'
    have h1 := toVal?_isValue hv1
    have h2 := toVal?_isValue hv2
    clear hdec hdec' hv1 hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h2]
    dsimp only
    rw [hR.bind_eq h1]
    dsimp only
    rw [hv2]
    obtain ⟨w1⟩ := h1
    cases w1 with
    | @lit b =>
      cases b with
      | loc ℓ =>
        simp only [headStep, asValM, hv2]
        split
        · rename_i h; rw [h]; simp only [dirac_bind_discrete]; exact (hR _ _ ⟨.lit⟩).symm
        · rename_i h; rw [h]; simp
      | _ => simp [headStep]
    | _ => simp [headStep]
  | rand e1 e2 =>
    simp only [decompItem] at hdec
    obtain ⟨h1, h2⟩ := isValue_of_decompItem₂ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h2]
    dsimp only
    rw [hR.bind_eq h1]
    dsimp only
    obtain ⟨w1⟩ := h1
    obtain ⟨w2⟩ := h2
    cases w1 with
    | @lit b =>
      cases b with
      | int z =>
        cases w2 with
        | @lit b2 =>
          cases b2 with
          | unit => exact (hR.uniform_bind z σ).symm
          | lbl α =>
            simp only [headStep]
            split
            · rename_i h; rw [h]; simp
            · rename_i bound ns h
              rw [h]
              simp only
              split
              · split
                · exact (hR.uniform_bind z σ).symm
                · simp only [dirac_bind_discrete]; exact (hR _ _ ⟨.lit⟩).symm
              · exact (hR.uniform_bind z σ).symm
          | _ => simp [headStep]
        | _ => simp [headStep]
      | _ => simp [headStep]
    | _ => simp [headStep]
  | unop op e1 =>
    simp only [decompItem] at hdec
    have h1 := isValue_of_decompItem₁ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h1]
    dsimp only
    simp only [headStep, isValM_some h1]
    cases hop : op.eval e1 with
    | none => simp [Option.unwrapM]
    | some r =>
      simp only [Option.unwrapM, dirac_bind_discrete]
      exact (hR _ _ (UnOp.eval_isValue hop)).symm
  | cond e1 et ef =>
    simp only [decompItem] at hdec
    have h1 := isValue_of_decompItem₁ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h1]
    dsimp only
    obtain ⟨w1⟩ := h1
    cases w1 with
    | @lit b =>
      cases b with
      | bool b => cases b <;> simp [headStep, dirac_bind_discrete]
      | _ => simp [headStep]
    | _ => simp [headStep]
  | fst e1 =>
    simp only [decompItem] at hdec
    have h1 := isValue_of_decompItem₁ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h1]
    dsimp only
    obtain ⟨w1⟩ := h1
    cases w1 with
    | pair w1 w2 =>
      simp only [headStep, isValM_some w1.toIsValue, isValM_some w2.toIsValue,
        dirac_bind_discrete]
      exact (hR _ _ w1.toIsValue).symm
    | _ => simp [headStep]
  | snd e1 =>
    simp only [decompItem] at hdec
    have h1 := isValue_of_decompItem₁ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h1]
    dsimp only
    obtain ⟨w1⟩ := h1
    cases w1 with
    | pair w1 w2 =>
      simp only [headStep, isValM_some w1.toIsValue, isValM_some w2.toIsValue,
        dirac_bind_discrete]
      exact (hR _ _ w2.toIsValue).symm
    | _ => simp [headStep]
  | case e1 el er =>
    simp only [decompItem] at hdec
    have h1 := isValue_of_decompItem₁ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h1]
    dsimp only
    obtain ⟨w1⟩ := h1
    cases w1 with
    | inl w => simp [headStep, isValM_some w.toIsValue, dirac_bind_discrete]
    | inr w => simp [headStep, isValM_some w.toIsValue, dirac_bind_discrete]
    | _ => simp [headStep]
  | alloc e1 =>
    simp only [decompItem] at hdec
    obtain ⟨v1, hv1, -⟩ := Option.casesOn_some_eq_none hdec
    have h1 := toVal?_isValue hv1
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h1]
    dsimp only
    simp only [headStep, asValM, hv1, dirac_bind_discrete]
    exact (hR _ _ ⟨.lit⟩).symm
  | load e1 =>
    simp only [decompItem] at hdec
    have h1 := isValue_of_decompItem₁ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h1]
    dsimp only
    obtain ⟨w1⟩ := h1
    cases w1 with
    | @lit b =>
      cases b with
      | loc ℓ =>
        simp only [headStep]
        cases h : σ.heap[ℓ]? with
        | none => simp
        | some v =>
          simp only [dirac_bind_discrete]
          exact (hR _ _ (Val.isValue v)).symm
      | _ => simp [headStep]
    | _ => simp [headStep]
  | tape e1 =>
    simp only [decompItem] at hdec
    have h1 := isValue_of_decompItem₁ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h1]
    dsimp only
    obtain ⟨w1⟩ := h1
    cases w1 with
    | @lit b =>
      cases b with
      | int z => simp only [headStep, dirac_bind_discrete]; exact (hR _ _ ⟨.lit⟩).symm
      | _ => simp [headStep]
    | _ => simp [headStep]
  | scrut e1 p =>
    simp only [decompItem] at hdec
    have h1 := isValue_of_decompItem₁ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h1]
    dsimp only
    simp only [headStep, isValM_some h1]
    cases hp : p.tryMatch e1 with
    | none => simp only [dirac_bind_discrete]; exact (hR _ _ ⟨.inr .lit⟩).symm
    | some b =>
      obtain ⟨w⟩ := Pat.tryMatch_isValue h1 hp
      simp only [dirac_bind_discrete]; exact (hR _ _ ⟨.inl w⟩).symm

end RetValRules

section FillItem
variable {R : Cfg rT → Measure (Cfg rT)} (hV : RetVal R) (hC : OnlyVal R) (Ki : EctxItem rT)
  (e : Exp rT) (σ : State rT)

include hV hC in
/-- One unfolding of the evaluator at `Ki[e]` first evaluates `e`, then continues at
`Ki[v]`. -/
theorem bigStepF_fillItem :
    bigStepF measureOps R ⟨Ki.fillItem e, σ⟩ =
      (R ⟨e, σ⟩).bind fun c => bigStepF measureOps R ⟨Ki.fillItem c.expr, c.state⟩ := by
  cases Ki <;> simp only [EctxItem.fillItem, bigStepF, measureOps, ofVal] <;>
    (try rw [hV.bind_eq (Val.isValue _)]) <;>
    refine hC.bind_congr _ fun ⟨v, σ'⟩ hv => ?_ <;> dsimp only <;>
    (try rw [hV.bind_eq (Val.isValue _)]) <;> rw [hV.bind_eq hv]

/-- `bigStep` returns value configurations unchanged. -/
theorem bigStep_retVal : RetVal (bigStep (rT := rT)) := by
  rintro e σ ⟨w⟩
  induction w generalizing σ with
  | lit => rw [bigStep_unfold]; rfl
  | lam h => rw [bigStep_unfold]; exact ite_eq_left ⟨.lam h⟩
  | fix h => rw [bigStep_unfold]; exact ite_eq_left ⟨.fix h⟩
  | pair w1 w2 ih1 ih2 =>
    rw [bigStep_unfold]
    simp only [bigStepF, measureOps]
    rw [ih2, dirac_bind_discrete]; dsimp only; rw [ih1, dirac_bind_discrete]
  | inl w ih => rw [bigStep_unfold]; simp only [bigStepF, measureOps]; rw [ih, dirac_bind_discrete]
  | inr w ih => rw [bigStep_unfold]; simp only [bigStepF, measureOps]; rw [ih, dirac_bind_discrete]

/-! ## `limExec` composes through contexts -/

theorem execN_nonvalue (n : ℕ) (ρ : Cfg rT) : execN n ρ {c | ¬c.expr.isValue} = 0 := by
  induction n generalizing ρ with
  | zero => rfl
  | succ n ih =>
    simp only [execN]
    split_ifs with hv
    · simpa [dirac_apply' _ MeasurableSet.of_discrete] using hv
    · rw [bind_apply MeasurableSet.of_discrete of_discrete.aemeasurable]
      simp [ih]

/-- `limExec` only produces value configurations. -/
theorem limExec_onlyVal : OnlyVal (limExec (rT := rT)) := fun ρ => by
  rw [ae_iff, limExec, iSup_measure_apply execN_monotone MeasurableSet.of_discrete]
  simp [execN_nonvalue]

/-- Running `e` to a value and then `Ki[v]` is part of running `Ki[e]`. -/
theorem limExec_fillItem_ge :
    (limExec ⟨e, σ⟩).bind (fun c => limExec ⟨Ki.fillItem c.expr, c.state⟩) ≤
      limExec ⟨Ki.fillItem e, σ⟩ := by
  have hN : ∀ n e σ, (execN n ⟨e, σ⟩).bind (fun c => limExec ⟨Ki.fillItem c.expr, c.state⟩) ≤
      limExec ⟨Ki.fillItem e, σ⟩ := by
    intro n
    induction n with
    | zero => intro e σ; simp only [execN, bind_zero_left]; exact bot_le
    | succ n ih =>
      intro e σ
      simp only [execN]
      split_ifs with hv
      · rw [dirac_bind_discrete]
      · rw [bind_bind_discrete, limExec_not_final (EctxItem.fillItem_noVal hv),
          primStep_fillItem Ki hv, map_bind_discrete]
        exact bind_mono_discrete le_rfl fun ρ => ih ρ.expr ρ.state
  rw [limExec, iSup_bind_discrete execN_monotone]
  exact iSup_le fun n => hN n e σ

/-! ## `bigStep ≤ limExec` -/

/-- One unfolding of the evaluator over `limExec` is below `limExec`. -/
theorem bigStepF_limExec_le :
    bigStepF measureOps limExec ⟨e, σ⟩ ≤ limExec ⟨e, σ⟩ := by
  induction h : e.pendingArgs using Nat.strong_induction_on generalizing e σ with
  | _ k ih =>
  cases hdec : e.decompItem with
  | none =>
    by_cases hv : e.isValue
    · rw [bigStepF_val limExec_retVal σ hv, limExec_retVal _ _ hv]
    · rw [bigStepF_head limExec_retVal hdec hv, ← limExec_head hdec hv]
  | some p =>
    obtain ⟨Ki, e'⟩ := p
    obtain ⟨rfl, hnv⟩ := decompItem_fill hdec
    rw [bigStepF_fillItem limExec_retVal limExec_onlyVal]
    refine le_trans (bind_mono_ae_discrete ((limExec_onlyVal _).mono fun c hc => ?_))
      (limExec_fillItem_ge Ki e' σ)
    exact ih _ (h ▸ pendingArgs_fillItem_lt Ki hnv hc) _ _ rfl

/-- `bigStep` is below `limExec`. -/
theorem bigStep_le_limExec : bigStep (rT := rT) ≤ limExec :=
  lfp_le _ fun ⟨e, σ⟩ => bigStepF_limExec_le e σ

/-- `bigStep` only produces value configurations. -/
theorem bigStep_onlyVal : OnlyVal (bigStep (rT := rT)) :=
  fun ρ => ae_mono (bigStep_le_limExec ρ) (limExec_onlyVal ρ)

/-! ## `limExec ≤ bigStep` -/

/-- `bigStep` at `Ki[e]` first evaluates `e`, then continues at `Ki[v]`. -/
theorem bigStep_fillItem :
    bigStep ⟨Ki.fillItem e, σ⟩ =
      (bigStep ⟨e, σ⟩).bind fun c => bigStep ⟨Ki.fillItem c.expr, c.state⟩ := by
  conv_lhs => rw [bigStep_unfold]
  rw [bigStepF_fillItem bigStep_retVal bigStep_onlyVal, ← bigStep_unfold]

end FillItem

/-- `bigStep` is closed under small steps. -/
theorem bigStep_primStep {e : Exp rT} {σ : State rT} (hnv : ¬e.isValue) :
    (primStep ⟨e, σ⟩).bind bigStep = bigStep ⟨e, σ⟩ := by
  induction h : e.size using Nat.strong_induction_on generalizing e σ with
  | _ k ih =>
  cases hdec : e.decompItem with
  | none =>
    rw [primStep_eq_headStep hdec]
    conv_rhs => rw [bigStep_unfold]
    rw [bigStepF_head bigStep_retVal hdec hnv]
  | some p =>
    obtain ⟨Ki, e'⟩ := p
    have hlt := h ▸ decompItem_size hdec
    obtain ⟨rfl, hnv'⟩ := decompItem_fill hdec
    rw [primStep_fillItem Ki hnv', map_bind_discrete, bigStep_fillItem, ← ih _ hlt hnv' rfl,
      bind_bind_discrete]
    congr 1
    funext ρ
    exact bigStep_fillItem Ki ρ.expr ρ.state

theorem execN_le_bigStep (n : ℕ) (ρ : Cfg rT) : execN n ρ ≤ bigStep ρ := by
  induction n generalizing ρ with
  | zero => exact bot_le
  | succ n ih =>
    obtain ⟨e, σ⟩ := ρ
    simp only [execN]
    split_ifs with hv
    · rw [bigStep_retVal _ _ hv]
    · rw [← bigStep_primStep hv]
      exact bind_mono_discrete le_rfl ih

/-- `limExec` is below `bigStep`. -/
theorem limExec_le_bigStep : limExec (rT := rT) ≤ bigStep :=
  fun ρ => iSup_le fun n => execN_le_bigStep n ρ

/-! ## The main theorem -/

/-- The big-step semantics equals the limit of the reduction semantics. -/
theorem bigStep_eq_limExec : bigStep (rT := rT) = limExec :=
  le_antisymm bigStep_le_limExec limExec_le_bigStep

end Discrete

end ProbLang
