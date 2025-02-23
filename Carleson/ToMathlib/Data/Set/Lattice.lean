import Mathlib.Data.Set.Lattice

lemma DirectedOn.pairwise_iUnion₂ {α : Type*} (c : Set (Set α)) (hc : DirectedOn (· ⊆ ·) c)
    (r : α → α → Prop) (h : ∀ s ∈ c, s.Pairwise r) : (⋃ s ∈ c, s).Pairwise r := by
  simp only [Set.Pairwise, Set.mem_iUnion, exists_prop, forall_exists_index, and_imp]
  intro x S hS hx y T hT hy hne
  obtain ⟨U, hU, hSU, hTU⟩ := hc S hS T hT
  exact h U hU (hSU hx) (hTU hy) hne
