import Mathlib.Topology.Algebra.Support

open Function Set Filter Topology

variable {α β : Type*} [TopologicalSpace α] [One β]

/- Move just after `continuous_of_mulTSupport` -/
@[to_additive]
lemma ContinuousOn.continuous_of_mulTSupport_subset [TopologicalSpace β] {f : α → β}
    {s : Set α} (hs : ContinuousOn f s) (h's : IsOpen s) (h''s : mulTSupport f ⊆ s) :
    Continuous f :=
  continuous_of_mulTSupport fun _ hx ↦ h's.continuousOn_iff.mp hs <| h''s hx
