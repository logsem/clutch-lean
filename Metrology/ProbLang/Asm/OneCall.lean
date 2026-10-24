module

public import Metrology.ProbLang.Asm.Semantics

/-! # Unique evaluation of one-call interaction trees -/

@[expose] public section

namespace ProbLang.Asm.AsmSemantics

variable {C V : Type} (M : AsmSemantics C V) (c : C) (entryArgs : List V) (F : Finset Loc)

/-- Trees followed with one entry frame and current state agree when one is a return. -/
theorem followsFrom_ret_unique
    (hagree : ∀ ι t P Q, M.runs ι c t P → M.runs ι c t Q → ∃ t', P t' ∧ Q t')
    (hdet : ∀ ι origin paused s u, M.ExitCompat ι c entryArgs F origin paused s →
      M.ExitCompat ι c entryArgs F origin paused u → s = u)
    {ι : Placement} {origin current : M.Mach} {value : V} {output : LocHeap V}
    {other : Interaction V}
    (hret : M.FollowsFrom c entryArgs F origin ι current (.ret value output))
    (hother : M.FollowsFrom c entryArgs F origin ι current other) :
    other = .ret value output := by
  cases other with
  | ret _ _ =>
    obtain ⟨paused, ho, hr⟩ := hagree ι current _ _ hother hret
    cases hdet ι origin paused _ _ ho hr
    rfl
  | call _ _ _ _ =>
    obtain ⟨paused, ho, hr⟩ := hagree ι current _ _ hother hret
    cases hdet ι origin paused _ _ ho.1 hr

/-- A canonical one-call specification determines evaluation using only its local resumptions. -/
theorem eval_one_call_eq_some (heap : LocHeap V) (name : String) (callArgs : List V)
    (callHeap : LocHeap V) (next : V → LocHeap V → Interaction V)
    (hagree : ∀ ι t P Q, M.runs ι c t P → M.runs ι c t Q → ∃ t', P t' ∧ Q t')
    (hdet : ∀ ι origin paused s u, M.ExitCompat ι c entryArgs F origin paused s →
      M.ExitCompat ι c entryArgs F origin paused u → s = u)
    (hentry : ∃ ι origin, M.Compat ι c entryArgs heap origin)
    (hcanonical : M.Canonical c entryArgs F (.call name callArgs callHeap next))
    (hspec : M.Spec c entryArgs F heap (.call name callArgs callHeap next))
    (hreturns : ∀ r h, M.ResponseOK c entryArgs F name r h →
      ∃ value output, next r h = .ret value output)
    (hresume : ∀ ι origin paused, M.Compat ι c entryArgs heap origin →
      M.ExitCompat ι c entryArgs F origin paused (.call name callArgs callHeap) →
      ∀ r h, M.ResponseOK c entryArgs F name r h →
        ∃ current, M.Resume ι c entryArgs F paused r h current) :
    M.eval c entryArgs F heap = some (.call name callArgs callHeap next) := by
  classical
  apply M.eval_eq_some_of_unique c entryArgs F ⟨hentry, hcanonical, hspec⟩
  intro other hother
  obtain ⟨ι, origin, hcompat⟩ := hentry
  have hs := hspec ι origin hcompat
  have ho := hother.2.2 ι origin hcompat
  cases other with
  | ret _ _ =>
    obtain ⟨paused, hs, ho⟩ := hagree ι origin _ _ hs ho
    cases hdet ι origin paused _ _ hs.1 ho
  | call _ _ _ _ =>
    obtain ⟨paused, hs, ho⟩ := hagree ι origin _ _ hs ho
    have he := hdet ι origin paused _ _ hs.1 ho.1
    cases he
    congr 1
    funext r h
    by_cases hr : M.ResponseOK c entryArgs F name r h
    · obtain ⟨current, hcurrent⟩ := hresume ι origin paused hcompat hs.1 r h hr
      obtain ⟨value, output, hbranch⟩ := hreturns r h hr
      have hret := hs.2 r h hr current hcurrent
      rw [hbranch] at hret
      exact (M.followsFrom_ret_unique c entryArgs F hagree hdet hret
        (ho.2 r h hr current hcurrent)).trans hbranch.symm
    · exact ((hother.2.1 r h).2 hr).trans ((hcanonical r h).2 hr).symm

end ProbLang.Asm.AsmSemantics
