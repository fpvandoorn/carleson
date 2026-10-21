/-
Copyright (c) 2026 Leo Diedering. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leo Diedering
-/
module

public import Carleson.ToMathlib.MeasureTheory.Measure.NoAtoms.Defs
public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Inner regular measures without atoms

A σ-finite, inner regular measure on a Hausdorff space which vanishes on singletons has no
atoms. In particular, this applies to locally finite measures on σ-compact metrizable spaces.
-/

-- Upstreaming status: to be determined

public section

namespace MeasureTheory

open Set Measure Filter TopologicalSpace Topology ENNReal

namespace NoAtoms'

/-- Given a measure `μ` that is inner regular with respect to compact sets, every measurable set `s`
of finite positive measure contains a point `x ∈ s` such that `s ∩ U` has positive measure for
all neighborhoods `U` of `x`. -/
--TODO: move to mathlib `Measure/Regular.lean`?
theorem exists_forall_nhds_measure_pos {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {μ : Measure α} [μ.InnerRegularCompactLTTop] {s : Set α} (meas_s : MeasurableSet s)
    (hs : 0 < μ s) (hfin : μ s ≠ ∞) :
    ∃ x ∈ s, ∀ U ∈ 𝓝 x, 0 < μ (s ∩ U) := by
  obtain ⟨K, hKs, hK, hK_pos⟩ := meas_s.exists_lt_isCompact_of_ne_top hfin hs
  by_contra! h
  apply hK_pos.ne'
  apply hK.measure_zero_of_nhdsWithin
  intro a ha
  obtain ⟨U, haU, hμU⟩ := h a (hKs ha)
  rw [nonpos_iff_eq_zero] at hμU
  use K ∩ U, inter_mem_nhdsWithin K haU, measure_mono_null (inter_subset_inter_left U hKs) hμU

/-- A σ-finite measure on a Hausdorff space which is inner regular with respect to compact sets
and vanishes on singletons has no atoms.
See https://math.stackexchange.com/questions/3881683/does-mu-x-0-imply-non-atomic-for-radon-measure

Proof sketch: an atom `s` has finite measure by σ-finiteness and thus by
`exists_forall_nhds_measure_pos` contains some `x ∈ s` such that `s ∩ U` has positive (hence full)
measure for every neighborhood `U` of `x`. Now `s \ {x}` contains a compact `L` of positive measure,
and separating `x` from `L` by disjoint open sets yields two disjoint subsets of `s` of full
measure, a contradiction. -/
theorem of_innerRegularCompactLTTop {α : Type*} [TopologicalSpace α] [T2Space α]
    [MeasurableSpace α] [OpensMeasurableSpace α] {μ : Measure α} [NullSingletonClass μ]
    [μ.InnerRegularCompactLTTop] [SigmaFinite μ] : NoAtoms' μ := by
  constructor
  rintro s ⟨meas_s, hs, hsub⟩
  -- every measurable subset of `s` of positive measure has full measure
  have full : ∀ t ⊆ s, MeasurableSet t → μ t ≠ 0 → μ t = μ s := fun t hts ht h ↦
    (hsub t hts ht).resolve_left h
  -- `s` has finite measure
  have hfin : μ s ≠ ∞ := by
    obtain ⟨n, hn⟩ : ∃ n, μ (s ∩ spanningSets μ n) ≠ 0 := by
      by_contra! h
      apply hs.ne'
      rw [← inter_univ s, ← iUnion_spanningSets μ, inter_iUnion]
      exact measure_iUnion_null h
    rw [← full _ inter_subset_left (meas_s.inter (measurableSet_spanningSets μ n)) hn]
    exact (measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n) |>.ne
  obtain ⟨x, -, hx⟩ : ∃ x ∈ s, ∀ U ∈ 𝓝 x, 0 < μ (s ∩ U) :=
    exists_forall_nhds_measure_pos meas_s hs hfin
  -- a compact subset of `s \ {x}` of positive measure
  have hsx : μ (s \ {x}) = μ s := measure_sdiff_null (measure_singleton x)
  obtain ⟨L, hLs, hL, hL_pos⟩ :=
    (meas_s.diff (measurableSet_singleton x)).exists_lt_isCompact_of_ne_top (hsx ▸ hfin) (hsx ▸ hs)
  obtain ⟨U, V, hU, hV, hLU, hxV, hUV⟩ := hL.separation_of_notMem (fun h ↦ (hLs h).2 rfl)
  have hsU : μ (s ∩ U) = μ s := full _ inter_subset_left (meas_s.inter hU.measurableSet)
    (hL_pos.trans_le (measure_mono (subset_inter (hLs.trans sdiff_subset) hLU))).ne'
  have hsV : μ (s ∩ V) = μ s :=
    full _ inter_subset_left (meas_s.inter hV.measurableSet) (hx V (hV.mem_nhds_iff.mpr hxV)).ne'
  have : μ s + μ s ≤ μ s + 0 := calc
    _ = μ (s ∩ U) + μ (s ∩ V) := by rw [hsU, hsV]
    _ = μ ((s ∩ U) ∪ (s ∩ V)) := by
      symm
      apply measure_union
      · exact hUV.mono inter_subset_right inter_subset_right
      · exact meas_s.inter hV.measurableSet
    _ ≤ μ s := measure_mono (union_subset inter_subset_left inter_subset_left)
    _ = μ s + 0 := (add_zero _).symm
  exact hs.ne' (nonpos_iff_eq_zero.mp (ENNReal.le_of_add_le_add_left hfin this))

end NoAtoms'

end MeasureTheory
