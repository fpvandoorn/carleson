import Mathlib.Order.CompleteLattice.Basic
import Carleson.ToMathlib.Order.ConditionallyCompleteLattice.Basic


--currently unused
theorem iSup_eq_iSup {α : Type*} {ι ι' : Sort*} [CompleteLattice α] {f : ι → α} {g : ι' → α}
  (h₀ : ∀ i, ∃ j, f i ≤ g j) (h₁ : ∀ j, ∃ i, g j ≤ f i) :
    ⨆ i, f i = ⨆ j, g j := by
  apply le_antisymm
  · apply iSup_le
    intro i
    rcases h₀ i with ⟨j, hj⟩
    apply le_iSup_of_le _ hj
  · apply iSup_le
    intro j
    rcases h₁ j with ⟨i, hi⟩
    apply le_iSup_of_le _ hi
