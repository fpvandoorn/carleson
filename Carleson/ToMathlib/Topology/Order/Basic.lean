import Mathlib.Topology.Order.Basic


theorem nonempty_nhds_inter_Ioi {α : Type*} [LinearOrder α] [DenselyOrdered α]
    [TopologicalSpace α] [OrderTopology α]
    {x : α} {u : Set α} (hu : u ∈ nhds x) (hx : ¬ IsMax x) :
    (u ∩ Set.Ioi x).Nonempty := by
  rw [not_isMax_iff] at hx
  rcases hx with ⟨b, hx⟩
  rcases exists_Ico_subset_of_mem_nhds' hu hx with ⟨b, hb, Ico_sub⟩
  rcases exists_between hb.1 with ⟨a, x_lt_a, a_lt_b⟩
  use a
  simp only [Set.mem_inter_iff, Set.mem_Ioi]
  constructor
  · apply Ico_sub
    exact ⟨x_lt_a.le, a_lt_b⟩
  · exact x_lt_a
