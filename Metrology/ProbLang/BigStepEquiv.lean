module

public import Metrology.ProbLang.BigStep
public import Metrology.ProbLang.Exec

@[expose] public section

/-! # The big-step semantics agrees with the reduction semantics

`bigStep_eq_limExec`. Discrete-only: `[Countable rT] [MeasurableSingletonClass rT]` make every
map out of `Cfg rT` measurable and `Measure.bind` monotone.
-/

noncomputable section
open MeasureTheory Measure

namespace ProbLang

variable {rT : Type _} [LawfulProbLangℝ rT]

/-- `bigStepF` read in the Giry monad. -/
def measureOps : EvalOps rT (Measure (Cfg rT)) where
  ret := dirac
  bind := Measure.bind
  stuck _ := 0
  uniform := Cfg.uniform
  uniformReal := Cfg.uniformReal

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
    cases v <;> simp only [Pat.tryMatch, reduceCtorEq] at h
    split at h <;> cases h; exact ⟨.lit⟩
  | pair p1 p2 ih1 ih2 =>
    obtain ⟨w⟩ := hv
    cases w <;> simp only [Pat.tryMatch, reduceCtorEq] at h
    rename_i w1 w2
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b1, h1, b2, h2, rfl⟩ := h
    obtain ⟨w1'⟩ := ih1 w1.toIsValue h1
    obtain ⟨w2'⟩ := ih2 w2.toIsValue h2
    exact ⟨.pair w1' w2'⟩
  | inl p ih =>
    obtain ⟨w⟩ := hv
    cases w <;> simp only [Pat.tryMatch, reduceCtorEq] at h
    rename_i w; exact ih w.toIsValue h
  | inr p ih =>
    obtain ⟨w⟩ := hv
    cases w <;> simp only [Pat.tryMatch, reduceCtorEq] at h
    rename_i w; exact ih w.toIsValue h

section Discrete

variable [Countable rT] [MeasurableSingletonClass rT]

/-! ## `Measure.bind` on a discrete space -/

theorem bind_mono_discrete {μ ν : Measure (Cfg rT)} {f g : Cfg rT → Measure (Cfg rT)}
    (hμ : μ ≤ ν) (hfg : ∀ c, f c ≤ g c) : μ.bind f ≤ ν.bind g := by
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [bind_apply hs Measurable.of_discrete.aemeasurable,
    bind_apply hs Measurable.of_discrete.aemeasurable]
  exact lintegral_mono' hμ fun c => hfg c s

theorem bind_mono_ae_discrete {μ : Measure (Cfg rT)} {f g : Cfg rT → Measure (Cfg rT)}
    (hfg : ∀ᵐ c ∂μ, f c ≤ g c) : μ.bind f ≤ μ.bind g := by
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [bind_apply hs Measurable.of_discrete.aemeasurable,
    bind_apply hs Measurable.of_discrete.aemeasurable]
  exact lintegral_mono_ae (hfg.mono fun c h => h s)

theorem dirac_bind_discrete (c : Cfg rT) (f : Cfg rT → Measure (Cfg rT)) :
    (dirac c).bind f = f c :=
  dirac_bind Measurable.of_discrete c

theorem bind_bind_discrete (μ : Measure (Cfg rT)) (f g : Cfg rT → Measure (Cfg rT)) :
    (μ.bind f).bind g = μ.bind fun c => (f c).bind g :=
  bind_bind Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable

theorem map_bind_discrete (μ : Measure (Cfg rT)) (f : Cfg rT → Cfg rT)
    (g : Cfg rT → Measure (Cfg rT)) : (μ.map f).bind g = μ.bind (g ∘ f) := by
  rw [Measure.bind, Measure.bind, Measure.map_map Measurable.of_discrete Measurable.of_discrete]

/-- `bind` is continuous in its measure argument. -/
theorem iSup_bind_discrete {μ : ℕ → Measure (Cfg rT)} (hμ : Monotone μ)
    (f : Cfg rT → Measure (Cfg rT)) : (⨆ n, μ n).bind f = ⨆ n, (μ n).bind f := by
  have hbind : Monotone fun n => (μ n).bind f :=
    fun _ _ h => bind_mono_discrete (hμ h) fun _ => le_rfl
  ext s hs
  rw [iSup_measure_apply hbind hs, bind_apply hs Measurable.of_discrete.aemeasurable,
    lintegral_countable']
  simp_rw [bind_apply hs Measurable.of_discrete.aemeasurable, lintegral_countable',
    iSup_measure_apply hμ (MeasurableSet.singleton _), ENNReal.mul_iSup]
  exact ENNReal.tsum_iSup_of_monotone_cts (fun c _ _ h => mul_le_mul_right (hμ h _) _)
    fun _ => Measurable.of_discrete

/-! ## The big-step semantics -/

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
  OrderHom.lfp ⟨bigStepF measureOps, bigStepF_mono⟩

theorem bigStep_unfold : bigStep (rT := rT) = bigStepF measureOps bigStep :=
  (OrderHom.map_lfp _).symm

/-! ## Evaluators that return values -/

/-- `R` returns a value configuration unchanged. -/
def RetVal (R : Cfg rT → Measure (Cfg rT)) : Prop :=
  ∀ e σ, e.isValue → R ⟨e, σ⟩ = dirac ⟨e, σ⟩

/-- `R` only produces value configurations. -/
def OnlyVal (R : Cfg rT → Measure (Cfg rT)) : Prop :=
  ∀ ρ, ∀ᵐ c ∂(R ρ), c.expr.isValue

theorem RetVal.bind_eq {R : Cfg rT → Measure (Cfg rT)} (hR : RetVal R) {e : Exp rT}
    {σ : State rT} (he : e.isValue) (f : Cfg rT → Measure (Cfg rT)) :
    (R ⟨e, σ⟩).bind f = f ⟨e, σ⟩ := by
  rw [hR e σ he, dirac_bind_discrete]

omit [Countable rT] [MeasurableSingletonClass rT] in
theorem OnlyVal.bind_congr {R : Cfg rT → Measure (Cfg rT)} (hR : OnlyVal R) (ρ : Cfg rT)
    {f g : Cfg rT → Measure (Cfg rT)} (h : ∀ c : Cfg rT, c.expr.isValue → f c = g c) :
    (R ρ).bind f = (R ρ).bind g :=
  bind_congr_right ((hR ρ).mono fun c hc => h c hc)

/-- Pushing a measure of values through a value-returning `R` changes nothing. -/
theorem RetVal.map_bind {R : Cfg rT → Measure (Cfg rT)} (hR : RetVal R) {α : Type _}
    [MeasurableSpace α] [DiscreteMeasurableSpace α] (μ : Measure α) (f : α → Cfg rT)
    (hf : ∀ a, (f a).expr.isValue) : (μ.map f).bind R = μ.map f := by
  have hfm : Measurable f := .of_discrete
  calc (μ.map f).bind R = (μ.map f).bind dirac :=
        bind_congr_right <| (ae_map_iff hfm.aemeasurable .of_discrete).mpr <|
          ae_of_all _ fun a => hR _ _ (hf a)
    _ = μ.map f := bind_dirac

theorem RetVal.uniform_bind {R : Cfg rT → Measure (Cfg rT)} (hR : RetVal R) (z : Int)
    (σ : State rT) : (Cfg.uniform z σ).bind R = Cfg.uniform z σ := by
  unfold Cfg.uniform
  split
  · exact hR.map_bind _ _ fun _ => ⟨.lit⟩
  · rw [dirac_bind_discrete]; exact hR _ _ ⟨.lit⟩

theorem RetVal.uniformReal_bind {R : Cfg rT → Measure (Cfg rT)} (hR : RetVal R)
    (σ : State rT) : (Cfg.uniformReal σ).bind R = Cfg.uniformReal σ :=
  hR.map_bind _ _ fun _ => ⟨.lit⟩

/-- One unfolding of the evaluator returns values unchanged, if `R` does. -/
theorem bigStepF_val {R : Cfg rT → Measure (Cfg rT)} (hR : RetVal R) {e : Exp rT}
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

omit [LawfulProbLangℝ rT] in
private theorem Option.casesOn_some_eq_none {α β : Type _} {o : Option α} {b : β}
    {f : α → Option β} (h : o.casesOn (some b) f = none) : ∃ a, o = some a ∧ f a = none := by
  cases o <;> simp_all

omit [LawfulProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT] in
private theorem Exp.isValue_of_decompItem₁ {β : Type _} {e1 : Exp rT} {b : β}
    (h : e1.toVal?.casesOn (some b) (fun _ => none) = none) : e1.isValue :=
  let ⟨_, hv1, _⟩ := Option.casesOn_some_eq_none h
  Exp.toVal?_isValue hv1

omit [LawfulProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT] in
private theorem Exp.isValue_of_decompItem₂ {β : Type _} {e1 e2 : Exp rT} {b : β}
    {f : Val rT → β}
    (h : e2.toVal?.casesOn (some b) (fun v2 => e1.toVal?.casesOn (some (f v2)) fun _ => none) =
      none) : e1.isValue ∧ e2.isValue :=
  let ⟨_, hv2, h⟩ := Option.casesOn_some_eq_none h
  ⟨Exp.isValue_of_decompItem₁ h, Exp.toVal?_isValue hv2⟩

/-- On a head redex, one unfolding of the evaluator takes exactly the head step. -/
theorem bigStepF_head {R : Cfg rT → Measure (Cfg rT)} (hR : RetVal R) {e : Exp rT}
    {σ : State rT} (hdec : e.decompItem = none) (hnv : ¬e.isValue) :
    bigStepF measureOps R ⟨e, σ⟩ = (headStep ⟨e, σ⟩).bind R := by
  cases e with
  | bvar | fvar | fail => simp [bigStepF, measureOps, headStep]
  | lit => exact absurd ⟨.lit⟩ hnv
  | lam e => simp only [bigStepF, measureOps, ite_eq_right hnv]; simp [headStep]
  | fix e => simp only [bigStepF, measureOps, ite_eq_right hnv]; simp [headStep]
  | urand => exact (hR.uniformReal_bind σ).symm
  | pair e1 e2 =>
    simp only [Exp.decompItem] at hdec
    obtain ⟨⟨w1⟩, ⟨w2⟩⟩ := Exp.isValue_of_decompItem₂ hdec
    exact absurd ⟨.pair w1 w2⟩ hnv
  | inl e1 =>
    simp only [Exp.decompItem] at hdec
    obtain ⟨w1⟩ := Exp.isValue_of_decompItem₁ hdec
    exact absurd ⟨.inl w1⟩ hnv
  | inr e1 =>
    simp only [Exp.decompItem] at hdec
    obtain ⟨w1⟩ := Exp.isValue_of_decompItem₁ hdec
    exact absurd ⟨.inr w1⟩ hnv
  | app e1 e2 =>
    simp only [Exp.decompItem] at hdec
    obtain ⟨h1, h2⟩ := Exp.isValue_of_decompItem₂ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h2]; dsimp only; rw [hR.bind_eq h1]; dsimp only
    obtain ⟨w1⟩ := h1
    cases w1 <;> simp [headStep, h2, dirac_bind_discrete]
  | binop op e1 e2 =>
    simp only [Exp.decompItem] at hdec
    obtain ⟨h1, h2⟩ := Exp.isValue_of_decompItem₂ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h2]; dsimp only; rw [hR.bind_eq h1]; dsimp only
    simp only [headStep, Exp.isValM_some h1, Exp.isValM_some h2]
    cases hop : op.eval e1 e2 with
    | none => simp [Option.unwrapM]
    | some r =>
      simp only [Option.unwrapM, dirac_bind_discrete]
      exact (hR _ _ (BinOp.eval_isValue hop)).symm
  | store e1 e2 =>
    simp only [Exp.decompItem] at hdec
    obtain ⟨v2, hv2, hdec'⟩ := Option.casesOn_some_eq_none hdec
    obtain ⟨v1, hv1, -⟩ := Option.casesOn_some_eq_none hdec'
    have h1 := Exp.toVal?_isValue hv1
    have h2 := Exp.toVal?_isValue hv2
    clear hdec hdec' hv1 hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h2]; dsimp only; rw [hR.bind_eq h1]; dsimp only
    rw [hv2]
    obtain ⟨w1⟩ := h1
    cases w1 with
    | @lit b =>
      cases b with
      | loc ℓ =>
        simp only [headStep, Exp.asValM, hv2]
        split
        · rename_i h; rw [h]; simp only [dirac_bind_discrete]; exact (hR _ _ ⟨.lit⟩).symm
        · rename_i h; rw [h]; simp
      | _ => simp [headStep]
    | _ => simp [headStep]
  | rand e1 e2 =>
    simp only [Exp.decompItem] at hdec
    obtain ⟨h1, h2⟩ := Exp.isValue_of_decompItem₂ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h2]; dsimp only; rw [hR.bind_eq h1]; dsimp only
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
              rw [h]; simp only
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
    simp only [Exp.decompItem] at hdec
    have h1 := Exp.isValue_of_decompItem₁ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h1]; dsimp only
    simp only [headStep, Exp.isValM_some h1]
    cases hop : op.eval e1 with
    | none => simp [Option.unwrapM]
    | some r =>
      simp only [Option.unwrapM, dirac_bind_discrete]
      exact (hR _ _ (UnOp.eval_isValue hop)).symm
  | cond e1 et ef =>
    simp only [Exp.decompItem] at hdec
    have h1 := Exp.isValue_of_decompItem₁ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h1]; dsimp only
    obtain ⟨w1⟩ := h1
    cases w1 with
    | @lit b =>
      cases b with
      | bool b => cases b <;> simp [headStep, dirac_bind_discrete]
      | _ => simp [headStep]
    | _ => simp [headStep]
  | fst e1 =>
    simp only [Exp.decompItem] at hdec
    have h1 := Exp.isValue_of_decompItem₁ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h1]; dsimp only
    obtain ⟨w1⟩ := h1
    cases w1 with
    | pair w1 w2 =>
      simp only [headStep, Exp.isValM_some w1.toIsValue, Exp.isValM_some w2.toIsValue,
        dirac_bind_discrete]
      exact (hR _ _ w1.toIsValue).symm
    | _ => simp [headStep]
  | snd e1 =>
    simp only [Exp.decompItem] at hdec
    have h1 := Exp.isValue_of_decompItem₁ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h1]; dsimp only
    obtain ⟨w1⟩ := h1
    cases w1 with
    | pair w1 w2 =>
      simp only [headStep, Exp.isValM_some w1.toIsValue, Exp.isValM_some w2.toIsValue,
        dirac_bind_discrete]
      exact (hR _ _ w2.toIsValue).symm
    | _ => simp [headStep]
  | case e1 el er =>
    simp only [Exp.decompItem] at hdec
    have h1 := Exp.isValue_of_decompItem₁ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h1]; dsimp only
    obtain ⟨w1⟩ := h1
    cases w1 with
    | inl w => simp [headStep, Exp.isValM_some w.toIsValue, dirac_bind_discrete]
    | inr w => simp [headStep, Exp.isValM_some w.toIsValue, dirac_bind_discrete]
    | _ => simp [headStep]
  | alloc e1 =>
    simp only [Exp.decompItem] at hdec
    obtain ⟨v1, hv1, -⟩ := Option.casesOn_some_eq_none hdec
    have h1 := Exp.toVal?_isValue hv1
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h1]; dsimp only
    simp only [headStep, Exp.asValM, hv1, dirac_bind_discrete]
    exact (hR _ _ ⟨.lit⟩).symm
  | load e1 =>
    simp only [Exp.decompItem] at hdec
    have h1 := Exp.isValue_of_decompItem₁ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h1]; dsimp only
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
    simp only [Exp.decompItem] at hdec
    have h1 := Exp.isValue_of_decompItem₁ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h1]; dsimp only
    obtain ⟨w1⟩ := h1
    cases w1 with
    | @lit b =>
      cases b with
      | int z => simp only [headStep, dirac_bind_discrete]; exact (hR _ _ ⟨.lit⟩).symm
      | _ => simp [headStep]
    | _ => simp [headStep]
  | scrut e1 p =>
    simp only [Exp.decompItem] at hdec
    have h1 := Exp.isValue_of_decompItem₁ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h1]; dsimp only
    simp only [headStep, Exp.isValM_some h1]
    cases hp : p.tryMatch e1 with
    | none => simp only [dirac_bind_discrete]; exact (hR _ _ ⟨.inr .lit⟩).symm
    | some b =>
      obtain ⟨w⟩ := Pat.tryMatch_isValue h1 hp
      simp only [dirac_bind_discrete]; exact (hR _ _ ⟨.inl w⟩).symm

/-- One unfolding of the evaluator at `Ki[e]` first evaluates `e`, then continues at
`Ki[v]`. -/
theorem bigStepF_fillItem {R : Cfg rT → Measure (Cfg rT)} (hV : RetVal R) (hC : OnlyVal R)
    (Ki : EctxItem rT) (e : Exp rT) (σ : State rT) :
    bigStepF measureOps R ⟨Ki.fillItem e, σ⟩ =
      (R ⟨e, σ⟩).bind fun c => bigStepF measureOps R ⟨Ki.fillItem c.expr, c.state⟩ := by
  cases Ki <;> simp only [EctxItem.fillItem, bigStepF, measureOps, Exp.ofVal] <;>
    (try rw [hV.bind_eq (Val.isValue _)]) <;>
    refine hC.bind_congr _ fun ⟨v, σ'⟩ hv => ?_ <;> dsimp only <;>
    (try rw [hV.bind_eq (Val.isValue _)]) <;> rw [hV.bind_eq hv]

theorem bigStep_retVal : RetVal (bigStep (rT := rT)) := by
  rintro e σ ⟨w⟩
  induction w generalizing σ with
  | lit => rw [bigStep_unfold]; rfl
  | lam h => rw [bigStep_unfold]; exact ite_eq_left ⟨.lam h⟩
  | fix h => rw [bigStep_unfold]; exact ite_eq_left ⟨.fix h⟩
  | pair w1 w2 ih1 ih2 =>
    rw [bigStep_unfold]; simp only [bigStepF, measureOps]
    rw [ih2, dirac_bind_discrete]; dsimp only; rw [ih1, dirac_bind_discrete]
  | inl w ih => rw [bigStep_unfold]; simp only [bigStepF, measureOps]; rw [ih, dirac_bind_discrete]
  | inr w ih => rw [bigStep_unfold]; simp only [bigStepF, measureOps]; rw [ih, dirac_bind_discrete]

/-! ## `limExec` returns values, takes head steps, and composes through contexts -/

omit [Countable rT] [MeasurableSingletonClass rT] in
theorem limExec_retVal : RetVal (limExec (rT := rT)) :=
  fun _ _ ⟨w⟩ => limExec_of_isVal w

theorem execN_nonvalue (n : ℕ) (ρ : Cfg rT) : execN n ρ {c | ¬c.expr.isValue} = 0 := by
  induction n generalizing ρ with
  | zero => rfl
  | succ n ih =>
    simp only [execN]
    split_ifs with hv
    · simpa [dirac_apply' _ MeasurableSet.of_discrete] using hv
    · rw [bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
      simp [ih]

theorem limExec_onlyVal : OnlyVal (limExec (rT := rT)) := fun ρ => by
  rw [ae_iff, limExec, iSup_measure_apply execN_monotone MeasurableSet.of_discrete]
  simp [execN_nonvalue]

omit [Countable rT] [MeasurableSingletonClass rT] in
theorem limExec_head {e : Exp rT} {σ : State rT} (hdec : e.decompItem = none)
    (hnv : ¬e.isValue) : limExec ⟨e, σ⟩ = (headStep ⟨e, σ⟩).bind limExec := by
  rw [limExec_not_final hnv, primStep_eq_headStep hdec]

/-- Running `e` to a value and then `Ki[v]` is part of running `Ki[e]`. -/
theorem limExec_fillItem_ge (Ki : EctxItem rT) (e : Exp rT) (σ : State rT) :
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

/-- The number of evaluation positions of `e` that still hold a non-value. It drops each
time one of them is evaluated, which orders the induction in `bigStepF_limExec_le`. -/
def Exp.pendingArgs : Exp rT → Nat
  | .app e1 e2 | .binop _ e1 e2 | .pair e1 e2 | .store e1 e2 | .rand e1 e2 =>
    pending e1 + pending e2
  | .unop _ e | .fst e | .snd e | .inl e | .inr e | .alloc e | .load e | .tape e
  | .scrut e _ | .cond e _ _ | .case e _ _ => pending e
  | _ => 0
where pending (e : Exp rT) : Nat := if e.isValue then 0 else 1

omit [LawfulProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT] in
theorem Exp.pendingArgs_fillItem_lt (Ki : EctxItem rT) {e v : Exp rT} (he : ¬e.isValue)
    (hv : v.isValue) : (Ki.fillItem v).pendingArgs < (Ki.fillItem e).pendingArgs := by
  cases Ki <;>
    simp [EctxItem.fillItem, Exp.pendingArgs, Exp.pendingArgs.pending, Exp.ofVal, he, hv]

theorem bigStepF_limExec_le (e : Exp rT) (σ : State rT) :
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
    obtain ⟨rfl, hnv⟩ := Exp.decompItem_fill hdec
    rw [bigStepF_fillItem limExec_retVal limExec_onlyVal]
    refine le_trans (bind_mono_ae_discrete ((limExec_onlyVal _).mono fun c hc => ?_))
      (limExec_fillItem_ge Ki e' σ)
    exact ih _ (h ▸ Exp.pendingArgs_fillItem_lt Ki hnv hc) _ _ rfl

theorem bigStep_le_limExec : bigStep (rT := rT) ≤ limExec :=
  OrderHom.lfp_le _ fun ⟨e, σ⟩ => bigStepF_limExec_le e σ

theorem bigStep_onlyVal : OnlyVal (bigStep (rT := rT)) :=
  fun ρ => ae_mono (bigStep_le_limExec ρ) (limExec_onlyVal ρ)

/-! ## `limExec ≤ bigStep` -/

theorem bigStep_fillItem (Ki : EctxItem rT) (e : Exp rT) (σ : State rT) :
    bigStep ⟨Ki.fillItem e, σ⟩ =
      (bigStep ⟨e, σ⟩).bind fun c => bigStep ⟨Ki.fillItem c.expr, c.state⟩ := by
  conv_lhs => rw [bigStep_unfold]
  rw [bigStepF_fillItem bigStep_retVal bigStep_onlyVal, ← bigStep_unfold]

/-- `bigStep` is closed under small steps. -/
theorem bigStep_primStep {e : Exp rT} {σ : State rT} (hnv : ¬e.isValue) :
    (primStep ⟨e, σ⟩).bind bigStep = bigStep ⟨e, σ⟩ := by
  induction h : e.height using Nat.strong_induction_on generalizing e σ with
  | _ k ih =>
  cases hdec : e.decompItem with
  | none =>
    rw [primStep_eq_headStep hdec]
    conv_rhs => rw [bigStep_unfold]
    rw [bigStepF_head bigStep_retVal hdec hnv]
  | some p =>
    obtain ⟨Ki, e'⟩ := p
    have hlt := h ▸ Exp.decompItem_height hdec
    obtain ⟨rfl, hnv'⟩ := Exp.decompItem_fill hdec
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

theorem limExec_le_bigStep : limExec (rT := rT) ≤ bigStep :=
  fun ρ => iSup_le fun n => execN_le_bigStep n ρ

/-! ## The main theorem -/

theorem bigStep_eq_limExec : bigStep (rT := rT) = limExec :=
  le_antisymm bigStep_le_limExec limExec_le_bigStep

end Discrete

end ProbLang
