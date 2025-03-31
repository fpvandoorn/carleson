import Mathlib.Topology.Algebra.Support

open Function Set Filter Topology

variable {α β : Type*} [TopologicalSpace α] [One β]

/- Move just after `continuous_of_mulTSupport` -/
@[to_additive]
lemma ContinuousOn.continuous_of_mulTSupport_subset [TopologicalSpace β] {f : α → β}
    {s : Set α} (hs : ContinuousOn f s) (h's : IsOpen s) (h''s : mulTSupport f ⊆ s) :
    Continuous f := by
  apply continuous_iff_continuousAt.2 (fun x ↦ ?_)
  by_cases hx : x ∈ s
  · exact (hs x hx).continuousAt (h's.mem_nhds hx)
  · have h'x : x ∈ (mulTSupport f)ᶜ := fun h ↦ hx (h''s h)
    have : ContinuousOn f (mulTSupport f)ᶜ :=
      (continuousOn_const (c := 1)).congr (fun x hx ↦ image_eq_one_of_nmem_mulTSupport hx)
    apply (this x h'x).continuousAt (IsOpen.mem_nhds (by simp [isClosed_mulTSupport f]) h'x)
