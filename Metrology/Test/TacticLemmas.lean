module

public import Metrology.Micrometer.WpTactics
public import Metrology.TotalEris.WpTactics

/-! # Signatures of the lemmas the `wp` tactics apply

A signature change here must be made together with the tactic that applies the lemma. -/

/-- info: @ProbLang.MicrometerWpGS.wp_bind : ∀ {rT : Type} [inst : MeasurableSpace rT] [inst_1 :
ProbLang.LawfulProbLangℝ rT] {B : Type} [inst_2 : PartialOrder B] [inst_3 : OrderTop B] {L :
GradedLifting B} {GF : Iris.BundledGFunctors} [inst_4 : ProbLang.MicrometerWpGS GF] [inst_5 :
ProbLang.BudgetGS B GF] {E : CoPset} {e : ProbLang.Exp rT} {K : ProbLang.Ectx rT} {Φ : ProbLang.Val
rT → Iris.IProp GF} [inst_6 : Add B] [L.IsLawful] [L.IsTopAbsorbing], WP[L] e @ E {{ v, WP[L]
(K.fill (ProbLang.Exp.ofVal v)) @ E {{ Φ }} }} ⊢ WP[L] (K.fill e) @ E {{ Φ }} -/
#guard_msgs (whitespace := lax) in
#check @ProbLang.MicrometerWpGS.wp_bind

/-- info: @ProbLang.MicrometerWpGS.wp_pure_step_ctx : ∀ {rT : Type} [inst : MeasurableSpace rT]
[inst_1 : ProbLang.LawfulProbLangℝ rT] {GF : Iris.BundledGFunctors} {B : Type} [inst_2 :
PartialOrder B] [inst_3 : OrderTop B] {L : GradedLifting B} [inst_4 : ProbLang.MicrometerWpGS GF]
[inst_5 : ProbLang.BudgetGS B GF] {E : CoPset} {Φ : ProbLang.Val rT → Iris.IProp GF} [inst_6 : Add
B] [L.IsLawful] [L.IsTopAbsorbing] (K : ProbLang.Ectx rT) (φ : Prop) {n : ℕ} {e₁ e₂ : ProbLang.Exp
rT} [ProbLang.PureExec φ n e₁ e₂], φ → WP[L] (K.fill e₂) @ E {{ Φ }} ⊢ WP[L] (K.fill e₁) @ E {{ Φ }}
-/
#guard_msgs (whitespace := lax) in
#check @ProbLang.MicrometerWpGS.wp_pure_step_ctx

/-- info: @ProbLang.MicrometerWpGS.wp_value_of_toVal : ∀ {rT : Type} [inst : MeasurableSpace rT]
[inst_1 : ProbLang.LawfulProbLangℝ rT] {B : Type} [inst_2 : PartialOrder B] [inst_3 : OrderTop B] {L
: GradedLifting B} {GF : Iris.BundledGFunctors} [inst_4 : ProbLang.MicrometerWpGS GF] [inst_5 :
ProbLang.BudgetGS B GF] {E : CoPset} {e : ProbLang.Exp rT} {v : ProbLang.Val rT} {Φ : ProbLang.Val
rT → Iris.IProp GF}, e.toVal? = some v → Φ v ⊢ WP[L] e @ E {{ Φ }} -/
#guard_msgs (whitespace := lax) in
#check @ProbLang.MicrometerWpGS.wp_value_of_toVal

/-- info: @ProbLang.MicrometerWpGS.wp_value_fupd_of_toVal : ∀ {rT : Type} [inst : MeasurableSpace
rT] [inst_1 : ProbLang.LawfulProbLangℝ rT] {B : Type} [inst_2 : PartialOrder B] [inst_3 : OrderTop
B] {L : GradedLifting B} {GF : Iris.BundledGFunctors} [inst_4 : ProbLang.MicrometerWpGS GF] [inst_5
: ProbLang.BudgetGS B GF] {E : CoPset} {e : ProbLang.Exp rT} {v : ProbLang.Val rT} {Φ : ProbLang.Val
rT → Iris.IProp GF}, e.toVal? = some v → (|={E}=> Φ v) ⊢ WP[L] e @ E {{ Φ }} -/
#guard_msgs (whitespace := lax) in
#check @ProbLang.MicrometerWpGS.wp_value_fupd_of_toVal

/-- info: @ProbLang.TotalEris.ErisWpGS.tglWp_bind : ∀ {rT : Type} [inst : MeasurableSpace rT]
[inst_1 : ProbLang.LawfulProbLangℝ rT] {GF : Iris.BundledGFunctors} [inst_2 :
ProbLang.TotalEris.ErisWpGS GF] {E : CoPset} {Φ : ProbLang.Val rT → Iris.IProp GF} {e : ProbLang.Exp
rT} {K : ProbLang.Ectx rT}, (ProbLang.TotalEris.ErisWpGS.tglWp E e fun v ↦
ProbLang.TotalEris.ErisWpGS.tglWp E (K.fill (ProbLang.Exp.ofVal v)) Φ) ⊢
ProbLang.TotalEris.ErisWpGS.tglWp E (K.fill e) Φ -/
#guard_msgs (whitespace := lax) in
#check @ProbLang.TotalEris.ErisWpGS.tglWp_bind

/-- info: @ProbLang.TotalEris.ErisWpGS.twp_pure_step_ctx : ∀ {rT : Type} [inst : MeasurableSpace rT]
[inst_1 : ProbLang.LawfulProbLangℝ rT] {GF : Iris.BundledGFunctors} [inst_2 :
ProbLang.TotalEris.ErisWpGS GF] (K : ProbLang.Ectx rT) (φ : Prop) {n : ℕ} {e₁ e₂ : ProbLang.Exp rT}
[ProbLang.PureExec φ n e₁ e₂], φ → ∀ {E : CoPset} {Φ : ProbLang.Val rT → Iris.IProp GF},
ProbLang.TotalEris.ErisWpGS.tglWp E (K.fill e₂) Φ ⊢ ProbLang.TotalEris.ErisWpGS.tglWp E (K.fill e₁)
Φ -/
#guard_msgs (whitespace := lax) in
#check @ProbLang.TotalEris.ErisWpGS.twp_pure_step_ctx

/-- info: @ProbLang.TotalEris.ErisWpGS.tglWp_value_of_toVal : ∀ {rT : Type} [inst : MeasurableSpace
rT] [inst_1 : ProbLang.LawfulProbLangℝ rT] {GF : Iris.BundledGFunctors} [inst_2 :
ProbLang.TotalEris.ErisWpGS GF] {E : CoPset} {Φ : ProbLang.Val rT → Iris.IProp GF} {e : ProbLang.Exp
rT} {v : ProbLang.Val rT}, e.toVal? = some v → Φ v ⊢ ProbLang.TotalEris.ErisWpGS.tglWp E e Φ -/
#guard_msgs (whitespace := lax) in
#check @ProbLang.TotalEris.ErisWpGS.tglWp_value_of_toVal

/-- info: @ProbLang.TotalEris.ErisWpGS.tglWp_value_fupd_of_toVal : ∀ {rT : Type} [inst :
MeasurableSpace rT] [inst_1 : ProbLang.LawfulProbLangℝ rT] {GF : Iris.BundledGFunctors} [inst_2 :
ProbLang.TotalEris.ErisWpGS GF] {E : CoPset} {Φ : ProbLang.Val rT → Iris.IProp GF} {e : ProbLang.Exp
rT} {v : ProbLang.Val rT}, e.toVal? = some v → (|={E}=> Φ v) ⊢ ProbLang.TotalEris.ErisWpGS.tglWp E e
Φ -/
#guard_msgs (whitespace := lax) in
#check @ProbLang.TotalEris.ErisWpGS.tglWp_value_fupd_of_toVal
