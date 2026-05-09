module
public import Mathlib.Order.Interval.Set.Disjoint

--Upstreaming status: ready

public section

open Set

@[simp]
theorem iUnion_Icc_eq_Ici_self_iff {ι : Sort*} {α : Type*} [LinearOrder α] {f : ι → α} {a : α} :
    ⋃ i, Icc a (f i) = Ici a ↔ ∀ (x : α), a ≤ x → ∃ i, x ≤ f i := by
  simp [← Ici_inter_Iic, ← inter_iUnion, subset_def]

theorem IsGLB.biUnion_Ioi_eq_Ioi {α : Type*} [LinearOrder α] {s : Set α} {a : α}
  (a_glb : IsGLB s a) :
    ⋃ x ∈ s, Ioi x = Ioi a := by
  refine (iUnion₂_subset fun x hx => ?_).antisymm fun x hx => ?_
  · exact Ioi_subset_Ioi_iff.mpr (a_glb.1 hx)
  · rcases a_glb.exists_between hx with ⟨y, hys, _, hyx⟩
    rw [mem_iUnion₂]
    exact ⟨y, hys, hyx⟩

theorem iUnion_Ioi_eq_Ioi_iInf {ι : Sort*} {R : Type*} [CompleteLinearOrder R] {f : ι → R} :
    ⋃ i : ι, Ioi (f i) = Ioi (⨅ i, f i) := by
  simp only [← IsGLB.biUnion_Ioi_eq_Ioi (@isGLB_iInf _ _ _ f), mem_range,
    iUnion_exists, iUnion_iUnion_eq']

theorem iUnion_Iio_eq_Iio_iSup {ι : Sort*} {R : Type*} [CompleteLinearOrder R] {f : ι → R}
     : ⋃ i : ι, Iio (f i) = Iio (⨆ i, f i) :=
  @iUnion_Ioi_eq_Ioi_iInf ι (OrderDual R) _ f
