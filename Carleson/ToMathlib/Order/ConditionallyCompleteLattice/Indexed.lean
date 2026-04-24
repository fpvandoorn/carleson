import Mathlib.Order.ConditionallyCompleteLattice.Indexed

section ConditionallyCompleteLinearOrderBot

variable {α : Type*} {ι : Sort*} {κ : ι → Sort*}
variable [ConditionallyCompleteLinearOrderBot α] {a : α}

theorem ciSup₂_le' {f : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ a) : ⨆ (i) (j), f i j ≤ a :=
  ciSup_le' fun i => ciSup_le' <| h i

theorem exists_lt_of_lt_ciSup₂' {f : ∀ i, κ i → α} (h : a < ⨆ (i) (j), f i j) :
    ∃ i j, a < f i j := by
  contrapose! h
  exact ciSup₂_le' h

end ConditionallyCompleteLinearOrderBot
