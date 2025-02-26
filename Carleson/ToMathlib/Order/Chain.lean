import Mathlib.Order.Chain
import Carleson.ToMathlib.Data.Set.Lattice

lemma IsChain.pairwiseDisjoint_iUnion₂ {α β : Type*} [PartialOrder β] [OrderBot β]
    (c : Set (Set α)) (hc : IsChain (· ⊆ ·) c) (f : α → β)
    (h : ∀ s ∈ c, s.PairwiseDisjoint f) : (⋃ s ∈ c, s).PairwiseDisjoint f :=
  hc.directedOn.pairwise_iUnion₂ _ _ h
