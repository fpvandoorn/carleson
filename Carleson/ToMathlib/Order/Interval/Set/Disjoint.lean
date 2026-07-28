module
public import Mathlib.Order.Interval.Set.Disjoint

-- Upstreaming status: ready

public section

open Set

-- TODO: check if this has been upstreamed also, perhaps under a different name!
theorem IsGLB.biUnion_Ioi_eq_Ioi {α : Type*} [LinearOrder α] {s : Set α} {a : α}
  (a_glb : IsGLB s a) :
    ⋃ x ∈ s, Ioi x = Ioi a := by
  refine (iUnion₂_subset fun x hx => ?_).antisymm fun x hx => ?_
  · exact Ioi_subset_Ioi_iff.mpr (a_glb.1 hx)
  · rcases a_glb.exists_between hx with ⟨y, hys, _, hyx⟩
    rw [mem_iUnion₂]
    exact ⟨y, hys, hyx⟩
