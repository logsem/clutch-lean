module

public import Metrology.ProbLang.HeadStep
import Metrology.ProbLang.Syntax.Notation

/-! # Assembly syntax and base-language boundary checks -/

@[expose] public section

namespace ProbLang.Test.Asm

open _root_.ProbLang.Asm

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]

example (c : Code) (σ : State rT) :
    headStep ⟨pl(asm(#(.code c), #())), σ⟩ = 0 := rfl

example (archive : Replay) (σ : State rT) :
    headStep ⟨.asmResume archive (.lit .unit), σ⟩ = 0 := rfl

example (l₁ l₂ : Loc) :
    (Exp.asm (.load (.lit (.loc l₁))) (.load (.lit (.loc l₂))) : Exp rT).decompItem =
      some (.asmR (.load (.lit (.loc l₁))), .load (.lit (.loc l₂))) := rfl

example (archive : Replay) (l : Loc) :
    (Exp.asmResume archive (.load (.lit (.loc l))) : Exp rT).decompItem =
      some (.asmResume archive, .load (.lit (.loc l))) := rfl

example : Measurable (fun c : Code => (.lit (.code c) : Exp rT)) := by
  fun_prop

example : Measurable (fun archive : Replay =>
    (.asmResume archive (.lit .unit) : Exp rT)) := by
  fun_prop

end ProbLang.Test.Asm
