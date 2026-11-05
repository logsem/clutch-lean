module

public import Metrology.ProbLang.BigStep
public import Metrology.ProbLang.Exec

@[expose] public section

/-! # The big-step semantics agrees with the reduction semantics

`bigStep_eq_limExec`, for countable `rT` and stuck foreign code. -/

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
  | .app e1 e2 | .binop _ e1 e2 | .pair e1 e2 | .store e1 e2 | .allocN e1 e2
  | .sample _ e1 e2 | .test _ e1 e2 => pending e1 + pending e2
  | .unop _ e | .fst e | .snd e | .inl e | .inr e | .alloc e | .load e | .tape _ e
  | .ffi e | .scrut e _ | .cond e _ _ | .case e _ _ | .randvar _ e => pending e
  | _ => 0
where pending (e : Exp rT) : Nat := if e.isValue then 0 else 1

/-- Filling a hole with a value gives a smaller `pendingArgs` than filling it with a non-value. -/
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

section Lawful

variable [LawfulProbLangℝ rT]

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

end Lawful

/-! ## Countably supported measures -/

/-- A measure is countably supported when it is concentrated on some countable set. -/
def CountablySupported (μ : Measure (Cfg rT)) : Prop :=
  ∃ S : Set (Cfg rT), S.Countable ∧ Concentrated μ S

/-- Every function is a.e.-measurable for a countably supported measure. -/
theorem CountablySupported.aemeasurable [MeasurableSingletonClass rT]
    {Y : Type _} [MeasurableSpace Y]
    {μ : Measure (Cfg rT)} (hμ : CountablySupported μ) (f : Cfg rT → Y) :
    AEMeasurable f μ := by
  classical
  obtain ⟨S, hSc, hS⟩ := hμ
  let c₀ : Cfg rT := ⟨.bvar 0, default⟩
  let g : Cfg rT → Y := fun c => if c ∈ S then f c else f c₀
  have hg : Measurable g := by
    apply measurable_of_measurable_on_compl_countable S hSc
    have heq : Sᶜ.domRestrict g = fun _ => f c₀ := by
      funext c
      have hc : (c : Cfg rT) ∉ S := c.property
      simp [g, hc]
    rw [heq]
    exact measurable_const
  refine ⟨g, hg, ?_⟩
  rw [Filter.EventuallyEq, ae_iff]
  unfold Concentrated at hS
  refine measure_mono_null ?_ hS
  intro c hc hcS
  exact hc (by simp [g, hcS])

/-- The zero measure is countably supported. -/
theorem countablySupported_zero : CountablySupported (0 : Measure (Cfg rT)) :=
  ⟨∅, Set.countable_empty, by simp [Concentrated]⟩

/-- A Dirac measure is countably supported. -/
theorem countablySupported_dirac [MeasurableSingletonClass rT]
    (c : Cfg rT) : CountablySupported (dirac c) :=
  ⟨{c}, Set.countable_singleton c, by simp [Concentrated]⟩

/-- A measurable pushforward of a measure on a countable type is countably supported. -/
theorem countablySupported_map {X : Type _} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass rT] (μ : Measure X) (f : X → Cfg rT)
    (hf : Measurable f) : CountablySupported (μ.map f) := by
  refine ⟨Set.range f, Set.countable_range f, ?_⟩
  simpa only [Set.image_univ] using
    (Concentrated.map (T := Set.univ) hf
      (by simpa only [Set.image_univ] using (Set.countable_range f).measurableSet)
      (Concentrated.univ (μ := μ)))

/-- Binding countably supported measures preserves countable support. -/
theorem CountablySupported.bind [MeasurableSingletonClass rT]
    {μ : Measure (Cfg rT)} (hμ : CountablySupported μ)
    (f : Cfg rT → Measure (Cfg rT)) (hf : ∀ c, CountablySupported (f c)) :
    CountablySupported (μ.bind f) := by
  classical
  obtain ⟨S, hSc, hS⟩ := hμ
  choose T hTc hT using hf
  let U : Set (Cfg rT) := ⋃ c ∈ S, T c
  have hUc : U.Countable := hSc.biUnion fun c _ => hTc c
  have hμsupp : CountablySupported μ := ⟨S, hSc, hS⟩
  refine ⟨U, hUc, ?_⟩
  rw [Concentrated, bind_apply hUc.measurableSet.compl (hμsupp.aemeasurable f)]
  have hmeas : AEMeasurable (fun c => f c Uᶜ) μ :=
    (measurable_coe hUc.measurableSet.compl).comp_aemeasurable (hμsupp.aemeasurable f)
  rw [lintegral_eq_zero_iff' hmeas, Filter.EventuallyEq]
  have hmem : ∀ᵐ c ∂μ, c ∈ S := by
    rw [ae_iff]
    exact hS
  filter_upwards [hmem] with c hc
  unfold Concentrated at hT
  exact measure_mono_null (Set.compl_subset_compl.mpr <| Set.subset_iUnion_of_subset c <|
    Set.subset_iUnion_of_subset hc le_rfl) (hT c)

/-- A measurable pushforward of a countably supported measure is countably supported. -/
theorem CountablySupported.map [MeasurableSingletonClass rT]
    {μ : Measure (Cfg rT)} (hμ : CountablySupported μ)
    (f : Cfg rT → Cfg rT) (hf : Measurable f) : CountablySupported (μ.map f) := by
  obtain ⟨S, hSc, hS⟩ := hμ
  exact ⟨f '' S, hSc.image f, Concentrated.map hf (hSc.image f).measurableSet hS⟩

/-! ## `Measure.bind` with measurable or countably supported kernels -/

theorem bind_mono_measurable {μ ν : Measure (Cfg rT)} {f g : Cfg rT → Measure (Cfg rT)}
    (hμ : μ ≤ ν) (hf : Measurable f) (hg : Measurable g) (hfg : ∀ c, f c ≤ g c) :
    μ.bind f ≤ ν.bind g := by
  refine le_iff.mpr fun s hs => ?_
  rw [bind_apply hs hf.aemeasurable, bind_apply hs hg.aemeasurable]
  exact lintegral_mono' hμ fun c => hfg c s

theorem bind_mono_ae_measurable {μ : Measure (Cfg rT)} {f g : Cfg rT → Measure (Cfg rT)}
    (hf : Measurable f) (hg : Measurable g) (hfg : ∀ᵐ c ∂μ, f c ≤ g c) :
    μ.bind f ≤ μ.bind g := by
  refine le_iff.mpr fun s hs => ?_
  rw [bind_apply hs hf.aemeasurable, bind_apply hs hg.aemeasurable]
  exact lintegral_mono_ae (hfg.mono fun c h => h s)

/-- Binding is monotone when both source measures are countably supported. -/
theorem bind_mono_supported [MeasurableSingletonClass rT]
    {μ ν : Measure (Cfg rT)} {f g : Cfg rT → Measure (Cfg rT)}
    (hμs : CountablySupported μ) (hνs : CountablySupported ν) (hμ : μ ≤ ν)
    (hfg : ∀ c, f c ≤ g c) : μ.bind f ≤ ν.bind g := by
  refine le_iff.mpr fun s hs => ?_
  rw [bind_apply hs (hμs.aemeasurable f), bind_apply hs (hνs.aemeasurable g)]
  exact lintegral_mono' hμ fun c => hfg c s

/-- Binding is monotone a.e. for a countably supported source measure. -/
theorem bind_mono_ae_supported [MeasurableSingletonClass rT]
    {μ : Measure (Cfg rT)} {f g : Cfg rT → Measure (Cfg rT)}
    (hμs : CountablySupported μ) (hfg : ∀ᵐ c ∂μ, f c ≤ g c) :
    μ.bind f ≤ μ.bind g := by
  refine le_iff.mpr fun s hs => ?_
  rw [bind_apply hs (hμs.aemeasurable f), bind_apply hs (hμs.aemeasurable g)]
  exact lintegral_mono_ae (hfg.mono fun c h => h s)

theorem dirac_bind_any [MeasurableSingletonClass rT]
    (c : Cfg rT) (f : Cfg rT → Measure (Cfg rT)) :
    (dirac c).bind f = f c := by
  have hf : AEMeasurable f (dirac c) :=
    ⟨fun _ => f c, measurable_const, ae_eq_dirac f⟩
  ext s hs
  rw [bind_apply hs hf, lintegral_dirac]

theorem bind_bind_measurable (μ : Measure (Cfg rT)) (f g : Cfg rT → Measure (Cfg rT))
    (hf : Measurable f) (hg : Measurable g) :
    (μ.bind f).bind g = μ.bind fun c => (f c).bind g :=
  bind_bind hf.aemeasurable hg.aemeasurable

/-- Associativity of bind for countably supported intermediate measures. -/
theorem bind_bind_supported [MeasurableSingletonClass rT]
    (μ : Measure (Cfg rT)) (f g : Cfg rT → Measure (Cfg rT))
    (hμ : CountablySupported μ) (hf : ∀ c, CountablySupported (f c)) :
    (μ.bind f).bind g = μ.bind fun c => (f c).bind g :=
  bind_bind (hμ.aemeasurable f) ((hμ.bind f hf).aemeasurable g)

theorem map_bind_measurable (μ : Measure (Cfg rT)) (f : Cfg rT → Cfg rT)
    (g : Cfg rT → Measure (Cfg rT)) (hf : Measurable f) (hg : Measurable g) :
    (μ.map f).bind g = μ.bind (g ∘ f) :=
  bind_map hf.aemeasurable hg.aemeasurable

theorem map_bind_supported [MeasurableSingletonClass rT]
    {μ : Measure (Cfg rT)} (hμ : CountablySupported μ)
    (f : Cfg rT → Cfg rT) (g : Cfg rT → Measure (Cfg rT)) (hf : Measurable f) :
    (μ.map f).bind g = μ.bind (g ∘ f) :=
  bind_map (hμ.aemeasurable f) ((hμ.map f hf).aemeasurable g)

/-- `bind` is continuous in its measure argument for a measurable kernel. -/
theorem iSup_bind_measurable {μ : ℕ → Measure (Cfg rT)} (hμ : Monotone μ)
    (f : Cfg rT → Measure (Cfg rT)) (hf : Measurable f) :
    (⨆ n, μ n).bind f = ⨆ n, (μ n).bind f :=
  iSup_bind_of_monotone hμ hf

/-- An increasing supremum of countably supported measures is countably supported. -/
theorem countablySupported_iSup [MeasurableSingletonClass rT]
    {μ : ℕ → Measure (Cfg rT)} (hμ : Monotone μ)
    (hsupp : ∀ n, CountablySupported (μ n)) : CountablySupported (⨆ n, μ n) := by
  choose S hSc hS using hsupp
  refine ⟨⋃ n, S n, Set.countable_iUnion hSc, ?_⟩
  rw [Concentrated, iSup_apply_of_monotone hμ (Set.countable_iUnion hSc).measurableSet.compl]
  apply bot_unique
  refine iSup_le fun n => ?_
  exact (measure_mono_null (Set.compl_subset_compl.mpr <| Set.subset_iUnion S n)
    (hS n)).le

/-- Binding a supremum of countably supported measures commutes with that supremum. -/
theorem iSup_bind_supported [MeasurableSingletonClass rT]
    {μ : ℕ → Measure (Cfg rT)} (hμ : Monotone μ)
    (hsupp : ∀ n, CountablySupported (μ n)) (f : Cfg rT → Measure (Cfg rT)) :
    (⨆ n, μ n).bind f = ⨆ n, (μ n).bind f := by
  have hsup := countablySupported_iSup hμ hsupp
  let hf := hsup.aemeasurable f
  let g := hf.mk f
  have hg : Measurable g := hf.measurable_mk
  calc
    (⨆ n, μ n).bind f = (⨆ n, μ n).bind g := bind_congr_right hf.ae_eq_mk
    _ = ⨆ n, (μ n).bind g := iSup_bind_of_monotone hμ hg
    _ = ⨆ n, (μ n).bind f := by
      congr 1
      funext n
      exact bind_congr_right <|
        Filter.EventuallyEq.symm (ae_mono (le_iSup μ n) hf.ae_eq_mk)

/-- Monotone convergence in the measure argument for an arbitrary function on a countably
supported supremum. -/
theorem lintegral_iSup_supported [MeasurableSingletonClass rT]
    {μ : ℕ → Measure (Cfg rT)} (hμ : Monotone μ)
    (hsupp : ∀ n, CountablySupported (μ n)) (f : Cfg rT → ENNReal) :
    ∫⁻ c, f c ∂(⨆ n, μ n) = ⨆ n, ∫⁻ c, f c ∂μ n := by
  have hsup := countablySupported_iSup hμ hsupp
  have hfm : AEMeasurable f (⨆ n, μ n) := hsup.aemeasurable f
  let g := hfm.mk f
  have hg : Measurable g := hfm.measurable_mk
  calc
    ∫⁻ c, f c ∂(⨆ n, μ n) = ∫⁻ c, g c ∂(⨆ n, μ n) :=
      lintegral_congr_ae hfm.ae_eq_mk
    _ = ⨆ n, ∫⁻ c, g c ∂μ n := lintegral_iSup_of_monotone hμ hg
    _ = ⨆ n, ∫⁻ c, f c ∂μ n := by
      congr 1
      funext n
      exact lintegral_congr_ae <|
        Filter.EventuallyEq.symm (ae_mono (le_iSup μ n) hfm.ae_eq_mk)

/-- `bind` is continuous along monotone sequences in both arguments when the source measures are
countably supported. -/
theorem bind_iSup_iSup_supported [MeasurableSingletonClass rT]
    {μ : ℕ → Measure (Cfg rT)} (hμ : Monotone μ)
    (hμs : ∀ n, CountablySupported (μ n)) {f : ℕ → Cfg rT → Measure (Cfg rT)}
    (hf : Monotone f) :
    (⨆ n, μ n).bind (fun c => ⨆ n, f n c) = ⨆ n, (μ n).bind (f n) := by
  have hμsup := countablySupported_iSup hμ hμs
  have hbind : Monotone fun n => (μ n).bind (f n) :=
    fun _ _ h => bind_mono_supported (hμs _) (hμs _) (hμ h) fun c => hf h c
  apply le_antisymm
  · refine le_iff.mpr fun s hs => ?_
    rw [bind_apply hs (hμsup.aemeasurable _), iSup_apply_of_monotone hbind hs]
    simp_rw [iSup_apply_of_monotone (fun _ _ h => hf h _) hs]
    rw [lintegral_iSup' (fun _ => hμsup.aemeasurable _)
      (ae_of_all _ fun c _ _ h => hf h c s)]
    refine iSup_le fun n => ?_
    rw [lintegral_iSup_supported hμ hμs]
    refine iSup_le fun m => le_iSup_of_le (max n m) ?_
    rw [bind_apply hs ((hμs _).aemeasurable _)]
    exact lintegral_mono' (hμ (le_max_right _ _)) fun c => hf (le_max_left _ _) c s
  · refine iSup_le fun n => bind_mono_supported (hμs n) hμsup (le_iSup μ n) ?_
    exact fun c => le_iSup (fun m => f m c) n

/-- A monotone sequence of countably supported measures. -/
def MeasureChain (μ : ℕ → Measure (Cfg rT)) : Prop :=
  Monotone μ ∧ ∀ n, CountablySupported (μ n)

theorem MeasureChain.bind [MeasurableSingletonClass rT]
    {μ : ℕ → Measure (Cfg rT)} {f : ℕ → Cfg rT → Measure (Cfg rT)}
    (hμ : MeasureChain μ) (hf : ∀ c, MeasureChain fun n => f n c) :
    MeasureChain fun n => (μ n).bind (f n) := by
  refine ⟨fun _ _ h => bind_mono_supported (hμ.2 _) (hμ.2 _) (hμ.1 h) ?_, ?_⟩
  · exact fun c => (hf c).1 h
  · exact fun n => (hμ.2 n).bind _ fun c => (hf c).2 n

theorem MeasureChain.bind_iSup [MeasurableSingletonClass rT]
    {μ : ℕ → Measure (Cfg rT)}
    {f : ℕ → Cfg rT → Measure (Cfg rT)} (hμ : MeasureChain μ)
    (hf : ∀ c, MeasureChain fun n => f n c) :
    (⨆ n, μ n).bind (fun c => ⨆ n, f n c) = ⨆ n, (μ n).bind (f n) :=
  bind_iSup_iSup_supported hμ.1 hμ.2 fun _ _ h c => (hf c).1 h

theorem measureChain_const {μ : Measure (Cfg rT)} (hμ : CountablySupported μ) :
    MeasureChain fun _ => μ :=
  ⟨fun _ _ _ => le_rfl, fun _ => hμ⟩

/-- `μ` is the supremum of the supported monotone chain `ν`. -/
def IsSupChain (μ : Measure (Cfg rT)) (ν : ℕ → Measure (Cfg rT)) : Prop :=
  MeasureChain ν ∧ μ = ⨆ n, ν n

theorem IsSupChain.bind [MeasurableSingletonClass rT]
    {μ : Measure (Cfg rT)} {ν : ℕ → Measure (Cfg rT)}
    {f : Cfg rT → Measure (Cfg rT)} {g : ℕ → Cfg rT → Measure (Cfg rT)}
    (hμ : IsSupChain μ ν) (hf : ∀ c, IsSupChain (f c) fun n => g n c) :
    IsSupChain (μ.bind f) fun n => (ν n).bind (g n) := by
  refine ⟨hμ.1.bind fun c => (hf c).1, ?_⟩
  rw [hμ.2]
  have hfun : f = fun c => ⨆ n, g n c := funext fun c => (hf c).2
  rw [hfun, MeasureChain.bind_iSup hμ.1 fun c => (hf c).1]

theorem isSupChain_const {μ : Measure (Cfg rT)} (hμ : CountablySupported μ) :
    IsSupChain μ fun _ => μ :=
  ⟨measureChain_const hμ, iSup_const.symm⟩

section RetValRules

variable [LawfulProbLangℝ rT]
variable {R : Cfg rT → Measure (Cfg rT)} (hR : RetVal R) {e : Exp rT}
include hR

/-- Binding a value-returning kernel at a value just applies the continuation. -/
theorem RetVal.bind_eq {σ : State rT} (he : e.isValue)
    (f : Cfg rT → Measure (Cfg rT)) :
    (R ⟨e, σ⟩).bind f = f ⟨e, σ⟩ := by
  rw [hR e σ he, dirac_bind_any]

/-- Pushing a measure of values through a value-returning `R` changes nothing. -/
theorem RetVal.map_bind {α : Type _}
    [MeasurableSpace α] [DiscreteMeasurableSpace α] [Countable α]
    (μ : Measure α) (f : α → Cfg rT)
    (hf : ∀ a, (f a).expr.isValue) : (μ.map f).bind R = μ.map f := by
  have hfm : Measurable f := .of_discrete
  calc (μ.map f).bind R = (μ.map f).bind dirac := bind_congr_right <|
        (ae_map_mem_range (Set.countable_range f).measurableSet hfm.aemeasurable).mono <|
          fun c ⟨a, ha⟩ => ha ▸ hR _ _ (hf a)
    _ = μ.map f := bind_dirac

/-- Binding a value-returning kernel after an integer draw changes nothing. -/
theorem RetVal.uniform_bind (z : Int)
    (σ : State rT) : (uniform z σ).bind R = uniform z σ := by
  unfold Cfg.uniform
  split
  · exact hR.map_bind _ _ fun _ => ⟨.lit⟩
  · rw [dirac_bind_any]; exact hR _ _ ⟨.lit⟩

/-- Binding a value-returning kernel after a real draw changes nothing. -/
theorem RetVal.uniformReal_bind
    [Countable rT]
    (σ : State rT) : (uniformReal σ).bind R = uniformReal σ :=
  hR.map_bind _ _ fun _ => ⟨.lit⟩

/-- Binding a value-returning kernel after a `sample` draw changes nothing. -/
theorem RetVal.sample_bind [Countable rT] [ProbLangDist rT] (n : ℕ) (v : Val rT)
    (σ : State rT) : (Cfg.sample n v σ).bind R = Cfg.sample n v σ :=
  hR.map_bind _ _ fun w => w.isValue

end RetValRules

/-- `bigStepF` read in the Giry monad. -/
def measureOps [LawfulProbLangℝ rT] [ProbLangDist rT] [ProbLangObs rT] :
    EvalOps rT (Measure (Cfg rT)) where
  ret := dirac
  bind := bind
  stuck _ := 0
  uniform := uniform
  uniformReal := uniformReal
  sample := Cfg.sample
  test := Cfg.test

/-! ## `limExec` on values and head redexes -/

/-- `limExec` returns value configurations unchanged. -/
theorem limExec_retVal [LawfulProbLangℝ rT] [ProbLangDist rT] [ProbLangObs rT]
    [ProbLangFFI rT] : RetVal (limExec (rT := rT)) :=
  fun _ _ ⟨w⟩ => limExec_of_isVal w

/-- `limExec` at a head redex runs the head step and continues. -/
theorem limExec_head [LawfulProbLangℝ rT] [ProbLangDist rT] [ProbLangObs rT]
    [ProbLangFFI rT] {e : Exp rT} {σ : State rT} (hdec : e.decompItem = none)
    (hnv : ¬e.isValue) : limExec ⟨e, σ⟩ = (headStep ⟨e, σ⟩).bind limExec := by
  rw [limExec_not_final hnv, primStep_eq_headStep hdec]

section Discrete

/-! ## The big-step semantics -/

theorem countablySupported_uniform [LawfulProbLangℝ rT] (z : Int) (σ : State rT) :
    CountablySupported (Cfg.uniform z σ) := by
  unfold Cfg.uniform
  split
  · exact countablySupported_map _ _ (by fun_prop)
  · exact countablySupported_dirac _

theorem countablySupported_uniformReal [LawfulProbLangℝ rT] [Countable rT]
    (σ : State rT) :
    CountablySupported (Cfg.uniformReal σ) :=
  countablySupported_map _ _ (by fun_prop)

theorem countablySupported_sample [LawfulProbLangℝ rT] [ProbLangDist rT] [Countable rT]
    (n : ℕ) (v : Val rT) (σ : State rT) :
    CountablySupported (Cfg.sample n v σ) :=
  countablySupported_map _ _ (by fun_prop)

theorem countablySupported_test [LawfulProbLangℝ rT] [ProbLangDist rT]
    [ProbLangObs rT] [Countable rT] (k : ℕ) (a : Val rT) (l : Lbl) (σ : State rT) :
    CountablySupported (Cfg.test k a l σ) := by
  unfold Cfg.test
  split
  · exact countablySupported_zero
  · exact countablySupported_map _ _ Measurable.of_discrete

theorem countablySupported_isValM (e : Exp rT) {m : Measure (Cfg rT)}
    (hm : CountablySupported m) : CountablySupported (e.isValM m) := by
  unfold Exp.isValM
  split <;> first | exact hm | exact countablySupported_zero

theorem countablySupported_asValM (e : Exp rT) {f : Val rT → Measure (Cfg rT)}
    (hf : ∀ v, CountablySupported (f v)) : CountablySupported (e.asValM f) := by
  unfold Exp.asValM
  split <;> first | exact hf _ | exact countablySupported_zero

theorem countablySupported_unwrapM {β : Type _} (o : Option β)
    (f : β → Measure (Cfg rT)) (hf : ∀ a, CountablySupported (f a)) :
    CountablySupported (Option.unwrapM f o) := by
  cases o <;> first | exact countablySupported_zero | exact hf _

/-- Every head step is countably supported when the language's values are countable. -/
theorem headStep_supported [LawfulProbLangℝ rT] [ProbLangDist rT] [ProbLangObs rT]
    [Countable rT] [ProbLangFFI rT] (e : Exp rT) (σ : State rT) :
    CountablySupported (headStep ⟨e, σ⟩) := by
  head_case_names
  case beta.lam | beta.fix | case.left | case.right =>
    exact countablySupported_isValM _ (countablySupported_dirac _)
  case fst | snd =>
    exact countablySupported_isValM _
      (countablySupported_isValM _ (countablySupported_dirac _))
  case unop =>
    exact countablySupported_isValM _
      (countablySupported_unwrapM _ _ fun _ => countablySupported_dirac _)
  case binop =>
    exact countablySupported_isValM _ (countablySupported_isValM _
      (countablySupported_unwrapM _ _ fun _ => countablySupported_dirac _))
  case cond.true | cond.false => exact countablySupported_dirac _
  case tape | alloc | randvar =>
    exact countablySupported_asValM _ fun _ => countablySupported_dirac _
  case allocN =>
    apply countablySupported_asValM
    intro v
    split <;> first | exact countablySupported_dirac _ | exact countablySupported_zero
  case load => split <;> first | exact countablySupported_zero | exact countablySupported_dirac _
  case store =>
    apply countablySupported_asValM
    intro v
    split <;> first | exact countablySupported_zero | exact countablySupported_dirac _
  case scrut =>
    apply countablySupported_isValM
    split <;> exact countablySupported_dirac _
  case ffi => exact countablySupported_asValM _ fun _ =>
    countablySupported_unwrapM _ _ fun _ => countablySupported_dirac _
  case sample.plain =>
    exact countablySupported_asValM _ fun v => countablySupported_sample _ v _
  case sample.tape =>
    apply countablySupported_asValM
    intro v
    split
    · exact countablySupported_zero
    · split
      · split
        · exact countablySupported_sample _ v _
        · exact countablySupported_dirac _
      · exact countablySupported_sample _ v _
  case test => exact countablySupported_asValM _ fun _ => countablySupported_test _ _ _ _
  case default => exact countablySupported_zero

theorem primStep_supported [LawfulProbLangℝ rT] [ProbLangDist rT] [ProbLangObs rT]
    [Countable rT] [ProbLangFFI rT] (c : Cfg rT) : CountablySupported (primStep c) := by
  obtain ⟨e, σ⟩ := c
  unfold primStep
  exact (headStep_supported e.decomp.2 σ).map _ (Ectx.fillCfg.measurable _)

theorem execN_supported [LawfulProbLangℝ rT] [ProbLangDist rT] [ProbLangObs rT]
    [Countable rT] [ProbLangFFI rT] (n : ℕ) (c : Cfg rT) :
    CountablySupported (execN n c) := by
  induction n generalizing c with
  | zero => exact countablySupported_zero
  | succ n ih =>
    obtain ⟨e, σ⟩ := c
    simp only [execN]
    split
    · exact countablySupported_dirac _
    · exact (primStep_supported _).bind _ ih

theorem limExec_supported [LawfulProbLangℝ rT] [ProbLangDist rT] [ProbLangObs rT]
    [Countable rT] [ProbLangFFI rT] (c : Cfg rT) : CountablySupported (limExec c) := by
  rw [limExec]
  exact countablySupported_iSup (fun _ _ h => execN_monotone (rT := rT) h)
    fun n => execN_supported n c

variable [LawfulProbLangℝ rT] [ProbLangDist rT] [ProbLangObs rT]

/-- `bigStepF` is monotone on countably supported evaluation kernels. -/
theorem bigStepF_mono {R R' : Cfg rT → Measure (Cfg rT)}
    (hRs : ∀ c, CountablySupported (R c)) (hR's : ∀ c, CountablySupported (R' c))
    (hR : R ≤ R') :
    bigStepF measureOps R ≤ bigStepF measureOps R' := by
  intro ρ
  obtain ⟨e, σ⟩ := ρ
  cases e <;> simp only [bigStepF, measureOps] <;>
    repeat' first
      | exact le_rfl
      | exact hR _
      | apply bind_mono_supported
      | exact hRs _
      | exact hR's _
      | rintro ⟨_, _⟩
      | split

section Countable

variable [Countable rT]

/-- One evaluator unfolding preserves countable support. -/
theorem bigStepF_supported {R : Cfg rT → Measure (Cfg rT)}
    (hR : ∀ c, CountablySupported (R c)) (ρ : Cfg rT) :
    CountablySupported (bigStepF measureOps R ρ) := by
  obtain ⟨e, σ⟩ := ρ
  cases e with
  | bvar n => exact countablySupported_zero
  | fvar x => exact countablySupported_zero
  | fail => exact countablySupported_zero
  | lit b => exact countablySupported_dirac _
  | lam e | fix e =>
    simp only [bigStepF, measureOps]
    split
    · exact countablySupported_dirac _
    · exact countablySupported_zero
  | pair e1 e2 =>
    simp only [bigStepF, measureOps]
    apply CountablySupported.bind
    · exact hR _
    · rintro ⟨v2, τ⟩
      apply CountablySupported.bind
      · exact hR _
      · intro c
        exact countablySupported_dirac _
  | inl e | inr e =>
    simp only [bigStepF, measureOps]
    apply CountablySupported.bind
    · exact hR _
    · intro c
      exact countablySupported_dirac _
  | app e1 e2 =>
    simp only [bigStepF, measureOps]
    apply CountablySupported.bind
    · exact hR _
    · rintro ⟨v2, τ⟩
      apply CountablySupported.bind
      · exact hR _
      · rintro ⟨v1, τ⟩
        cases v1 <;> simp only
        all_goals first | exact hR _ | exact countablySupported_zero
  | unop op e | fst e | snd e | alloc e | load e | tape _ e | randvar _ e =>
    simp only [bigStepF, measureOps]
    apply CountablySupported.bind
    · exact hR _
    · rintro ⟨v, τ⟩
      repeat' first
        | split
        | exact countablySupported_dirac _
        | exact countablySupported_zero
  | ffi e =>
    simp only [bigStepF, measureOps]
    apply CountablySupported.bind
    · exact hR _
    · intro c
      exact countablySupported_zero
  | binop op e1 e2 | allocN e1 e2 | store e1 e2 =>
    simp only [bigStepF, measureOps]
    apply CountablySupported.bind
    · exact hR _
    · rintro ⟨v2, τ⟩
      apply CountablySupported.bind
      · exact hR _
      · rintro ⟨v1, τ⟩
        repeat' first
          | split
          | exact countablySupported_dirac _
          | exact countablySupported_zero
  | cond ec et ef | case ec et ef =>
    simp only [bigStepF, measureOps]
    apply CountablySupported.bind
    · exact hR _
    · rintro ⟨v, τ⟩
      repeat' first
        | split
        | exact hR _
        | exact countablySupported_zero
  | scrut e p =>
    simp only [bigStepF, measureOps]
    apply CountablySupported.bind
    · exact hR _
    · rintro ⟨v, τ⟩
      split <;> exact countablySupported_dirac _
  | sample n e et =>
    simp only [bigStepF, measureOps]
    apply CountablySupported.bind
    · exact hR _
    · rintro ⟨vt, τ⟩
      apply CountablySupported.bind
      · exact hR _
      · rintro ⟨ve, τ⟩
        repeat' first
          | split
          | exact countablySupported_sample _ _ _
          | exact countablySupported_dirac _
          | exact countablySupported_zero
  | test k ec ea =>
    simp only [bigStepF, measureOps]
    apply CountablySupported.bind
    · exact hR _
    · rintro ⟨va, τ⟩
      apply CountablySupported.bind
      · exact hR _
      · rintro ⟨vc, τ⟩
        repeat' first
          | split
          | exact countablySupported_test _ _ _ _
          | exact countablySupported_zero

/-- One evaluator unfolding commutes with an increasing supremum of countably supported
evaluation kernels. -/
theorem bigStepF_iSup {R : ℕ → Cfg rT → Measure (Cfg rT)} (hR : Monotone R)
    (hRs : ∀ n c, CountablySupported (R n c)) :
    bigStepF measureOps (fun c => ⨆ n, R n c) = fun c => ⨆ n, bigStepF measureOps (R n) c := by
  have hRc (c : Cfg rT) : IsSupChain (⨆ n, R n c) fun n => R n c :=
    ⟨⟨fun _ _ h => hR h c, fun n => hRs n c⟩, rfl⟩
  funext ρ
  obtain ⟨e, σ⟩ := ρ
  suffices IsSupChain (bigStepF measureOps (fun c => ⨆ n, R n c) ⟨e, σ⟩)
      (fun n => bigStepF measureOps (R n) ⟨e, σ⟩) by
    exact this.2
  cases e with
  | bvar n => exact isSupChain_const countablySupported_zero
  | fvar x => exact isSupChain_const countablySupported_zero
  | fail => exact isSupChain_const countablySupported_zero
  | lit b => exact isSupChain_const (countablySupported_dirac _)
  | lam e | fix e =>
    simp only [bigStepF, measureOps]
    split
    · exact isSupChain_const (countablySupported_dirac _)
    · exact isSupChain_const countablySupported_zero
  | pair e1 e2 =>
    simp only [bigStepF, measureOps]
    apply IsSupChain.bind (hRc _)
    rintro ⟨v2, τ⟩
    apply IsSupChain.bind (hRc _)
    intro c
    exact isSupChain_const (countablySupported_dirac _)
  | inl e | inr e =>
    simp only [bigStepF, measureOps]
    apply IsSupChain.bind (hRc _)
    intro c
    exact isSupChain_const (countablySupported_dirac _)
  | app e1 e2 =>
    simp only [bigStepF, measureOps]
    apply IsSupChain.bind (hRc _)
    rintro ⟨v2, τ⟩
    apply IsSupChain.bind (hRc _)
    rintro ⟨v1, τ⟩
    cases v1 <;> simp only
    all_goals first | exact hRc _ | exact isSupChain_const countablySupported_zero
  | unop op e | fst e | snd e | alloc e | load e | tape _ e | randvar _ e =>
    simp only [bigStepF, measureOps]
    apply IsSupChain.bind (hRc _)
    rintro ⟨v, τ⟩
    repeat' first
      | split
      | exact isSupChain_const (countablySupported_dirac _)
      | exact isSupChain_const countablySupported_zero
  | ffi e =>
    simp only [bigStepF, measureOps]
    apply IsSupChain.bind (hRc _)
    intro c
    exact isSupChain_const countablySupported_zero
  | binop op e1 e2 | allocN e1 e2 | store e1 e2 =>
    simp only [bigStepF, measureOps]
    apply IsSupChain.bind (hRc _)
    rintro ⟨v2, τ⟩
    apply IsSupChain.bind (hRc _)
    rintro ⟨v1, τ⟩
    repeat' first
      | split
      | exact isSupChain_const (countablySupported_dirac _)
      | exact isSupChain_const countablySupported_zero
  | cond ec et ef | case ec et ef =>
    simp only [bigStepF, measureOps]
    apply IsSupChain.bind (hRc _)
    rintro ⟨v, τ⟩
    repeat' first
      | split
      | exact hRc _
      | exact isSupChain_const countablySupported_zero
  | scrut e p =>
    simp only [bigStepF, measureOps]
    apply IsSupChain.bind (hRc _)
    rintro ⟨v, τ⟩
    split <;> exact isSupChain_const (countablySupported_dirac _)
  | sample n e et =>
    simp only [bigStepF, measureOps]
    apply IsSupChain.bind (hRc _)
    rintro ⟨vt, τ⟩
    apply IsSupChain.bind (hRc _)
    rintro ⟨ve, τ⟩
    repeat' first
      | split
      | exact isSupChain_const (countablySupported_sample _ _ _)
      | exact isSupChain_const (countablySupported_dirac _)
      | exact isSupChain_const countablySupported_zero
  | test k ec ea =>
    simp only [bigStepF, measureOps]
    apply IsSupChain.bind (hRc _)
    rintro ⟨va, τ⟩
    apply IsSupChain.bind (hRc _)
    rintro ⟨vc, τ⟩
    repeat' first
      | split
      | exact isSupChain_const (countablySupported_test _ _ _ _)
      | exact isSupChain_const countablySupported_zero

/-- The `n`th approximation to the big-step semantics. -/
def bigStepApprox : ℕ → Cfg rT → Measure (Cfg rT)
  | 0 => ⊥
  | n + 1 => bigStepF measureOps (bigStepApprox n)

/-- Every finite approximation is pointwise countably supported. -/
theorem bigStepApprox_supported (n : ℕ) :
    ∀ c, CountablySupported (bigStepApprox (rT := rT) n c) := by
  induction n with
  | zero => exact fun _ => countablySupported_zero
  | succ n ih =>
    exact fun c => bigStepF_supported ih c

/-- The finite approximations form an increasing chain. -/
theorem bigStepApprox_monotone : Monotone (bigStepApprox (rT := rT)) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => exact bot_le
  | succ n ih =>
    exact bigStepF_mono (bigStepApprox_supported n)
      (bigStepApprox_supported (n + 1)) ih

/-- The big-step semantics is the supremum of its finite approximations. -/
def bigStep : Cfg rT → Measure (Cfg rT) := fun ρ => ⨆ n, bigStepApprox n ρ

/-- The big-step semantics is pointwise countably supported. -/
theorem bigStep_supported (c : Cfg rT) : CountablySupported (bigStep (rT := rT) c) :=
  countablySupported_iSup (fun _ _ h => bigStepApprox_monotone h c)
    fun n => bigStepApprox_supported n c

/-- `bigStep` is a fixed point of one evaluator unfolding. -/
theorem bigStep_unfold : bigStep (rT := rT) = bigStepF measureOps bigStep := by
  unfold bigStep
  rw [bigStepF_iSup bigStepApprox_monotone bigStepApprox_supported]
  funext c
  change (⨆ n, bigStepApprox n c) = ⨆ n, bigStepApprox (n + 1) c
  apply le_antisymm
  · refine iSup_le fun n => ?_
    cases n with
    | zero => exact bot_le
    | succ n => exact le_iSup (fun m => bigStepApprox (m + 1) c) n
  · exact iSup_le fun n => le_iSup (fun m => bigStepApprox m c) (n + 1)

end Countable

section RetValRules
variable {R : Cfg rT → Measure (Cfg rT)} (hR : RetVal R) {e : Exp rT}
include hR

section Countable

variable [Countable rT]

/-- Binding a value-returning kernel after a test changes nothing. -/
theorem RetVal.test_bind (k : ℕ) (a : Val rT) (l : Lbl)
    (σ : State rT) : (Cfg.test k a l σ).bind R = Cfg.test k a l σ := by
  rcases hc : σ.rvs[l]? with _ | c
  · simp [Cfg.test, hc]
  · rw [Cfg.test_eq_map hc]
    exact hR.map_bind _ _ fun _ => ⟨.lit⟩

end Countable

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

section Countable

variable [Countable rT]

/-- On a head redex other than a foreign call, one unfolding of the evaluator takes exactly the
head step. -/
theorem bigStepF_head_of_ne_ffi [ProbLangFFI rT] {σ : State rT} (hdec : e.decompItem = none)
    (hnv : ¬e.isValue) (hf : ∀ e', e ≠ .ffi e') :
    bigStepF measureOps R ⟨e, σ⟩ = (headStep ⟨e, σ⟩).bind R := by
  have hdirac (c : Cfg rT) : (dirac c).bind R = R c := dirac_bind_any c R
  cases e with
  | bvar | fvar | fail => simp [bigStepF, measureOps, headStep]
  | lit => exact absurd ⟨.lit⟩ hnv
  | lam e => simp only [bigStepF, measureOps, ite_eq_right hnv]; simp [headStep]
  | fix e => simp only [bigStepF, measureOps, ite_eq_right hnv]; simp [headStep]
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
    cases w1 <;> simp [headStep, h2, hdirac]
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
      simp only [Option.unwrapM, hdirac]
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
        · simp only [hdirac]
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
        · rename_i h; rw [h]; simp only [hdirac]; exact (hR _ _ ⟨.lit⟩).symm
        · rename_i h; rw [h]; simp
      | _ => simp [headStep]
    | _ => simp [headStep]
  | sample n e1 e2 =>
    simp only [decompItem] at hdec
    obtain ⟨h1, h2⟩ := isValue_of_decompItem₂ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h2]
    dsimp only
    rw [hR.bind_eq h1]
    dsimp only
    obtain ⟨v1, hv1⟩ := Exp.toVal?_eq_some_of_isValue h1
    obtain ⟨w2⟩ := h2
    simp only [hv1]
    cases w2 with
    | @lit b =>
      cases b with
      | unit =>
        simp only [headStep, Exp.asValM, hv1]
        exact (hR.sample_bind n v1 σ).symm
      | lbl α =>
        simp only [headStep, Exp.asValM, hv1]
        cases htape : σ.tapes[α]? with
        | none => simp
        | some t =>
          simp only
          by_cases hfamily : t.name = n ∧ t.arg = v1
          · simp only [ite_eq_left hfamily]
            cases hhead : t.head? with
            | none => exact (hR.sample_bind n v1 _).symm
            | some w =>
              simp only [hdirac]
              exact (hR _ _ (Val.isValue w)).symm
          · simp only [ite_eq_right hfamily]
            exact (hR.sample_bind n v1 σ).symm
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
      simp only [Option.unwrapM, hdirac]
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
      | bool b => cases b <;> simp [headStep, hdirac]
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
        hdirac]
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
        hdirac]
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
    | inl w => simp [headStep, isValM_some w.toIsValue, hdirac]
    | inr w => simp [headStep, isValM_some w.toIsValue, hdirac]
    | _ => simp [headStep]
  | alloc e1 =>
    simp only [decompItem] at hdec
    obtain ⟨v1, hv1, -⟩ := Option.casesOn_some_eq_none hdec
    have h1 := toVal?_isValue hv1
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h1]
    dsimp only
    simp only [headStep, asValM, hv1, hdirac]
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
          simp only [hdirac]
          exact (hR _ _ (Val.isValue v)).symm
      | _ => simp [headStep]
    | _ => simp [headStep]
  | tape n e1 =>
    simp only [decompItem] at hdec
    have h1 := isValue_of_decompItem₁ hdec
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h1]
    dsimp only
    obtain ⟨v1, hv1⟩ := Exp.toVal?_eq_some_of_isValue h1
    simp only [headStep, asValM, hv1, hdirac]
    exact (hR _ _ ⟨.lit⟩).symm
  | ffi e1 => exact absurd rfl (hf e1)
  | randvar n e1 =>
    simp only [decompItem] at hdec
    obtain ⟨v1, hv1, -⟩ := Option.casesOn_some_eq_none hdec
    have h1 := toVal?_isValue hv1
    clear hdec hnv
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq h1]
    dsimp only
    simp only [headStep, asValM, hv1, Cfg.randvar, hdirac]
    exact (hR _ _ ⟨.lit⟩).symm
  | test k e1 e2 =>
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
      | lbl l =>
        simp only [headStep, asValM, hv2]
        exact (hR.test_bind k v2 l σ).symm
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
    | none => simp only [hdirac]; exact (hR _ _ ⟨.inr .lit⟩).symm
    | some b =>
      obtain ⟨w⟩ := Pat.tryMatch_isValue h1 hp
      simp only [hdirac]; exact (hR _ _ ⟨.inl w⟩).symm

/-- With stuck foreign code, on a head redex one unfolding of the evaluator takes exactly the head
step. -/
theorem bigStepF_head [ProbLangFFI rT] [ProbLangFFI.Stuck rT] {σ : State rT}
    (hdec : e.decompItem = none) (hnv : ¬e.isValue) :
    bigStepF measureOps R ⟨e, σ⟩ = (headStep ⟨e, σ⟩).bind R := by
  by_cases hf : ∃ e', e = .ffi e'
  · obtain ⟨e1, rfl⟩ := hf
    simp only [decompItem] at hdec
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq (isValue_of_decompItem₁ hdec)]
    have h0 : headStep ⟨.ffi e1, σ⟩ = 0 := by
      simp only [headStep, asValM, Cfg.ffi_of_stuck]
      split <;> rfl
    simp [h0]
  · exact bigStepF_head_of_ne_ffi hR hdec hnv fun e' h => hf ⟨e', h⟩

/-- On a head redex, one unfolding of the evaluator is below the head step. -/
theorem bigStepF_head_le [ProbLangFFI rT] {σ : State rT} (hdec : e.decompItem = none)
    (hnv : ¬e.isValue) : bigStepF measureOps R ⟨e, σ⟩ ≤ (headStep ⟨e, σ⟩).bind R := by
  by_cases hf : ∃ e', e = .ffi e'
  · obtain ⟨e1, rfl⟩ := hf
    simp only [decompItem] at hdec
    simp only [bigStepF, measureOps]
    rw [hR.bind_eq (isValue_of_decompItem₁ hdec)]
    exact bot_le
  · exact (bigStepF_head_of_ne_ffi hR hdec hnv fun e' h => hf ⟨e', h⟩).le

end Countable

end RetValRules

section FillItem
variable {R : Cfg rT → Measure (Cfg rT)} (hV : RetVal R) (hC : OnlyVal R)
  (Ki : EctxItem rT) (e : Exp rT) (σ : State rT)

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

section Countable

variable [Countable rT]

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
    rw [ih2, dirac_bind_any]; dsimp only; rw [ih1, dirac_bind_any]
  | inl w ih => rw [bigStep_unfold]; simp only [bigStepF, measureOps]; rw [ih, dirac_bind_any]
  | inr w ih => rw [bigStep_unfold]; simp only [bigStepF, measureOps]; rw [ih, dirac_bind_any]

end Countable

/-! ## `limExec` composes through contexts -/

section

variable [ProbLangFFI rT]

section Countable

variable [Countable rT]

theorem execN_nonvalue (n : ℕ) (ρ : Cfg rT) : execN n ρ {c | ¬c.expr.isValue} = 0 := by
  have hnonvalue : MeasurableSet {c : Cfg rT | ¬c.expr.isValue} :=
    Cfg.measurable_expr (MeasurableSet.of_discrete : MeasurableSet {e : Exp rT | ¬e.isValue})
  induction n generalizing ρ with
  | zero => rfl
  | succ n ih =>
    simp only [execN]
    split_ifs with hv
    · simpa [dirac_apply' _ hnonvalue] using hv
    · rw [bind_apply hnonvalue (execN_measurable n).aemeasurable]
      simp [ih]

/-- `limExec` only produces value configurations. -/
theorem limExec_onlyVal : OnlyVal (limExec (rT := rT)) := fun ρ => by
  have hnonvalue : MeasurableSet {c : Cfg rT | ¬c.expr.isValue} :=
    Cfg.measurable_expr (MeasurableSet.of_discrete : MeasurableSet {e : Exp rT | ¬e.isValue})
  rw [ae_iff, limExec, iSup_measure_apply execN_monotone hnonvalue]
  simp [execN_nonvalue]

end Countable

/-- Running `e` to a value and then `Ki[v]` is part of running `Ki[e]`. -/
theorem limExec_fillItem_ge :
    (limExec ⟨e, σ⟩).bind (fun c => limExec ⟨Ki.fillItem c.expr, c.state⟩) ≤
      limExec ⟨Ki.fillItem e, σ⟩ := by
  let fill : Cfg rT → Cfg rT := fun c => ⟨Ki.fillItem c.expr, c.state⟩
  have hfill : Measurable fill := Cfg.measurable_iff.mpr
    ⟨(EctxItem.fillItem.measurableEmbedding Ki).measurable.comp Cfg.measurable_expr,
      Cfg.measurable_state⟩
  have hcont : Measurable (limExec ∘ fill) := limExec.measurable.comp hfill
  have hN : ∀ n e σ, (execN n ⟨e, σ⟩).bind (fun c => limExec ⟨Ki.fillItem c.expr, c.state⟩) ≤
      limExec ⟨Ki.fillItem e, σ⟩ := by
    intro n
    induction n with
    | zero => intro e σ; simp only [execN, bind_zero_left]; exact bot_le
    | succ n ih =>
      intro e σ
      simp only [execN]
      split_ifs with hv
      · rw [dirac_bind_any]
      · change (((primStep ⟨e, σ⟩).bind (execN n)).bind (limExec ∘ fill)) ≤ _
        rw [bind_bind_measurable _ _ _ (execN_measurable n) hcont,
          limExec_not_final (EctxItem.fillItem_noVal hv), primStep_fillItem Ki hv,
          map_bind_measurable _ fill limExec hfill limExec.measurable]
        exact bind_mono_measurable le_rfl
          ((measurable_bind' hcont).comp (execN_measurable n)) hcont
          fun ρ => ih ρ.expr ρ.state
  change ((limExec ⟨e, σ⟩).bind (limExec ∘ fill)) ≤ _
  rw [limExec, iSup_bind_measurable execN_monotone _ hcont]
  exact iSup_le fun n => hN n e σ

section Countable

variable [Countable rT]

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
    · exact (bigStepF_head_le limExec_retVal hdec hv).trans_eq
        (limExec_head hdec hv).symm
  | some p =>
    obtain ⟨Ki, e'⟩ := p
    obtain ⟨rfl, hnv⟩ := decompItem_fill hdec
    rw [bigStepF_fillItem limExec_retVal limExec_onlyVal]
    let fill : Cfg rT → Cfg rT := fun c => ⟨Ki.fillItem c.expr, c.state⟩
    have hfill : Measurable fill := Cfg.measurable_iff.mpr
      ⟨(EctxItem.fillItem.measurableEmbedding Ki).measurable.comp Cfg.measurable_expr,
        Cfg.measurable_state⟩
    refine le_trans (bind_mono_ae_supported (limExec_supported _)
      ((limExec_onlyVal _).mono fun c hc => ?_))
      (limExec_fillItem_ge Ki e' σ)
    exact ih _ (h ▸ pendingArgs_fillItem_lt Ki hnv hc) _ _ rfl

/-- `bigStep` is below `limExec`. -/
theorem bigStep_le_limExec : bigStep (rT := rT) ≤ limExec := by
  intro ρ
  refine iSup_le fun n => ?_
  induction n generalizing ρ with
  | zero => exact bot_le
  | succ n ih =>
    exact (bigStepF_mono (bigStepApprox_supported n) limExec_supported ih ρ).trans
      (bigStepF_limExec_le ρ.expr ρ.state)

end Countable

end

section Countable

variable [Countable rT]

/-- `bigStep` only produces value configurations. -/
theorem bigStep_onlyVal : OnlyVal (bigStep (rT := rT)) :=
  letI : ProbLangFFI rT := .stuck
  fun ρ => ae_mono (bigStep_le_limExec ρ) (limExec_onlyVal ρ)

/-! ## `limExec ≤ bigStep` -/

/-- `bigStep` at `Ki[e]` first evaluates `e`, then continues at `Ki[v]`. -/
theorem bigStep_fillItem :
    bigStep ⟨Ki.fillItem e, σ⟩ =
      (bigStep ⟨e, σ⟩).bind fun c => bigStep ⟨Ki.fillItem c.expr, c.state⟩ := by
  conv_lhs => rw [bigStep_unfold]
  rw [bigStepF_fillItem bigStep_retVal bigStep_onlyVal, ← bigStep_unfold]

end Countable

end FillItem

section Countable

variable [Countable rT]

variable [ProbLangFFI rT] [ProbLangFFI.Stuck rT]

/-- With stuck foreign code, `bigStep` is closed under small steps. -/
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
    rw [primStep_fillItem Ki hnv',
      map_bind_supported (primStep_supported _) _ _ (by fun_prop),
      bigStep_fillItem, ← ih _ hlt hnv' rfl,
      bind_bind_supported _ _ _ (primStep_supported _) bigStep_supported]
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
      exact bind_mono_supported (primStep_supported _) (primStep_supported _) le_rfl ih

/-- With stuck foreign code, `limExec` is below `bigStep`. -/
theorem limExec_le_bigStep : limExec (rT := rT) ≤ bigStep :=
  fun ρ => iSup_le fun n => execN_le_bigStep n ρ

/-! ## The main theorem -/

/-- With stuck foreign code, the big-step semantics equals the limit of the reduction semantics.
-/
theorem bigStep_eq_limExec : bigStep (rT := rT) = limExec :=
  le_antisymm bigStep_le_limExec limExec_le_bigStep

end Countable

end Discrete

end ProbLang
