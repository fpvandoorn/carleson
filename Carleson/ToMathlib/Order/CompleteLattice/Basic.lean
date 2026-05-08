module

public import Mathlib.Order.CompleteLattice.Basic
public import Carleson.ToMathlib.Order.ConditionallyCompleteLattice.Basic

public section

-- Upstreaming status: under active development by @ldiedering
-- Wait for the file to stabilise first.

--currently unused
theorem iSup_eq_iSup {α : Type*} {ι ι' : Sort*} [CompleteLattice α] {f : ι → α} {g : ι' → α}
  (h₀ : ∀ i, ∃ j, f i ≤ g j) (h₁ : ∀ j, ∃ i, g j ≤ f i) :
    ⨆ i, f i = ⨆ j, g j := le_antisymm (iSup_mono' h₀) (iSup_mono' h₁)
