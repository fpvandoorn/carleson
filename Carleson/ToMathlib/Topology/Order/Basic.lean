import Mathlib.Topology.Order.Basic

-- Upstreaming status: perhaps, the hypotheses can be weakened, but otherwise looks ready

theorem nonempty_nhds_inter_Ioi {α : Type*} [LinearOrder α] [DenselyOrdered α]
    [TopologicalSpace α] [OrderTopology α]
    {x : α} {u : Set α} (hu : u ∈ nhds x) (hx : ¬ IsMax x) :
    (u ∩ Set.Ioi x).Nonempty := by
  obtain ⟨b, hx⟩ := not_isMax_iff.mp hx
  obtain ⟨b, hb, Ico_sub⟩ := exists_Ico_subset_of_mem_nhds' hu hx
  obtain ⟨a, x_lt_a, a_lt_b⟩ := exists_between hb.1
  use a
  simpa only [Set.mem_inter_iff, Set.mem_Ioi] using
    ⟨Ico_sub ⟨x_lt_a.le, a_lt_b⟩, by assumption⟩
