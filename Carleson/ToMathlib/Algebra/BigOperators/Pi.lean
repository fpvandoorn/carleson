import Mathlib.Algebra.BigOperators.Pi

@[to_additive]
lemma prod_mulIndicator_eq_mulIndicator_prod {α β ι : Type*} [CommMonoid β]
    (s : Finset ι) (t : Set α) (f : ι → α → β) :
    ∏ i ∈ s, t.mulIndicator (f i) = t.mulIndicator (∏ i ∈ s, f i) := by
  ext x; by_cases hx : x ∈ t <;> simp [hx]
