import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open Set TopologicalSpace ENNReal

variable {ι X : Type*} [PseudoEMetricSpace ι] [SeparableSpace ι] [MeasurableSpace X]

/-- Given `T : Set ι` over a separable pseudometric space `ι`, let `f : ι → X → ℝ≥0∞` be
* measurable in `x` for all `t ∈ T`
* **continuous** on `T` for all `x`

Then the supremum of `f` over `T` is measurable.
The proof follows https://math.stackexchange.com/a/4685735/357390. -/
lemma measurable_biSup_of_continuousOn {T : Set ι} {f : ι → X → ℝ≥0∞}
    (mf : ∀ t ∈ T, Measurable (f t)) (cf : ∀ x, ContinuousOn (f · x) T) :
    Measurable (⨆ t ∈ T, f t) := by
  refine measurable_of_Ioi fun c ↦ ?_
  obtain ⟨J, sJ, cJ, dJ⟩ := (IsSeparable.of_separableSpace T).exists_countable_dense_subset
  suffices (⨆ t ∈ T, f t) ⁻¹' Ioi c = ⋃ j ∈ J, {x | c < f j x} by
    rw [this]; refine MeasurableSet.biUnion cJ fun j mj ↦ ?_
    exact measurableSet_lt measurable_const (mf j (sJ mj))
  ext x
  simp_rw [mem_preimage, mem_Ioi, iSup_apply, lt_biSup_iff, mem_iUnion₂, mem_setOf_eq, exists_prop]
  constructor <;> rintro ⟨t, mt, ht⟩
  · simp_rw [continuousOn_iff] at cf
    obtain ⟨u, ou, mu, hu⟩ := cf _ _ mt _ isOpen_Ioi ht
    specialize dJ mt; rw [mem_closure_iff] at dJ
    specialize dJ u ou mu; obtain ⟨j, mj⟩ := dJ; use j, mj.2
    simpa using (inter_subset_inter subset_rfl sJ).trans hu mj
  · use t, sJ mt
