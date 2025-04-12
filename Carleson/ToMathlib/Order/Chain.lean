import Mathlib.Order.Chain
import Mathlib.Data.Set.Lattice

lemma IsChain.pairwiseDisjoint_iUnion₂ {α β : Type*} [PartialOrder β] [OrderBot β]
    (c : Set (Set α)) (hc : IsChain (· ⊆ ·) c) (f : α → β)
    (h : ∀ s ∈ c, s.PairwiseDisjoint f) : (⋃ s ∈ c, s).PairwiseDisjoint f := by
  apply Set.pairwise_iUnion₂ (directedOn hc)
  exact fun s hs ↦ h s hs
