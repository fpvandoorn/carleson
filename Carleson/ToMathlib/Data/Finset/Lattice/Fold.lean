import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Data.Set.Finite.Lattice

-- currently unused
-- proof could probably be simplified if there were more mathlib lemmas about `ciSup` (in `ConditionallyCompleteLinearOrderBot`)
theorem Finset.sup_eq_iSup' {α : Type*} {β : Type*} [ConditionallyCompleteLinearOrderBot β] (s : Finset α) (f : α → β) :
    s.sup f = ⨆ a ∈ s, f a := by
  apply le_antisymm
  · apply Finset.sup_le
    intro a ha
    refine le_ciSup_of_le ?_ a ?_
    · have : (Set.range fun a ↦ ⨆ (_ : a ∈ s), f a) ⊆ insert ⊥ (s.image f) := by
        intro b
        simp only [Set.mem_range, coe_image, Set.mem_insert_iff, Set.mem_image, mem_coe,
          forall_exists_index]
        intro a ha'
        by_cases ha : Nonempty (a ∈ s)
        · right
          rw [ciSup_const] at ha'
          rw [nonempty_prop] at ha
          use a, ha, ha'
        · left
          rw [not_nonempty_iff] at ha
          rw [ciSup_of_empty] at ha'
          exact ha'.symm
      apply BddAbove.mono this
      apply BddAbove.insert
      exact Finset.bddAbove (image f s)
    refine le_ciSup_of_le ?_ ha (le_refl (f a))
    by_cases ha : Nonempty (a ∈ s)
    · rw [Set.range_const]
      exact bddAbove_singleton
    · rw [not_nonempty_iff] at ha
      rw [Set.range_eq_empty]
      exact bddAbove_empty
  · by_cases h : Nonempty α
    · apply ciSup_le
      intro a
      by_cases ha : Nonempty (a ∈ s)
      · apply ciSup_le
        simp only [nonempty_prop] at ha
        apply Finset.le_sup
      · rw [not_nonempty_iff] at ha
        rw [ciSup_of_empty]
        exact bot_le
    · rw [not_nonempty_iff] at h
      rw [ciSup_of_empty]
      exact bot_le
