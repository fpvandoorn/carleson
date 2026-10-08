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

open Set Measure Filter TopologicalSpace ENNReal

namespace NoAtoms'

/-- A σ-finite measure on a Hausdorff space which is inner regular with respect to compact sets
and vanishes on singletons has no atoms.
See https://math.stackexchange.com/questions/3881683/does-mu-x-0-imply-non-atomic-for-radon-measure

Proof sketch: an atom `s` has finite measure by σ-finiteness and contains a compact `K` of positive
measure. By compactness, there is `x ∈ K` such that `s ∩ U` has positive (hence full) measure for
all open `U ∋ x`. Now `s \ {x}` contains a compact `L` of positive measure, and separating `x` from
`L` by disjoint open sets yields two disjoint subsets of `s` of full measure, a contradiction. -/
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
  -- a compact subset of positive measure
  obtain ⟨K, hKs, hK, hK_pos⟩ := meas_s.exists_lt_isCompact_of_ne_top hfin hs
  -- a point all of whose neighborhoods meet `s` in positive measure
  obtain ⟨x, -, hx⟩ : ∃ x ∈ K, ∀ U, IsOpen U → x ∈ U → μ (s ∩ U) ≠ 0 := by
    by_contra! h
    apply hK_pos.ne'
    apply hK.measure_zero_of_nhdsWithin
    intro a ha
    obtain ⟨U, hU, haU, hμU⟩ := h a ha
    exact ⟨K ∩ U, inter_mem_nhdsWithin K (hU.mem_nhds haU),
      measure_mono_null (inter_subset_inter_left U hKs) hμU⟩
  -- a compact subset of `s \ {x}` of positive measure
  have hsx : μ (s \ {x}) = μ s := measure_sdiff_null (measure_singleton x)
  obtain ⟨L, hLs, hL, hL_pos⟩ :=
    (meas_s.diff (measurableSet_singleton x)).exists_lt_isCompact_of_ne_top (hsx ▸ hfin) (hsx ▸ hs)
  obtain ⟨U, V, hU, hV, hLU, hxV, hUV⟩ := hL.separation_of_notMem (fun h ↦ (hLs h).2 rfl)
  have hsU : μ (s ∩ U) = μ s := full _ inter_subset_left (meas_s.inter hU.measurableSet)
    (hL_pos.trans_le (measure_mono (subset_inter (hLs.trans sdiff_subset) hLU))).ne'
  have hsV : μ (s ∩ V) = μ s :=
    full _ inter_subset_left (meas_s.inter hV.measurableSet) (hx V hV hxV)
  have : μ s + μ s ≤ μ s + 0 := calc
    _ = μ (s ∩ U) + μ (s ∩ V) := by rw [hsU, hsV]
    _ = μ ((s ∩ U) ∪ (s ∩ V)) := (measure_union
      (hUV.mono inter_subset_right inter_subset_right) (meas_s.inter hV.measurableSet)).symm
    _ ≤ μ s := measure_mono (union_subset inter_subset_left inter_subset_left)
    _ = μ s + 0 := (add_zero _).symm
  exact hs.ne' (nonpos_iff_eq_zero.mp (ENNReal.le_of_add_le_add_left hfin this))

/-- A locally finite measure on a σ-compact metrizable space which vanishes on singletons has no
atoms. This is not an instance, as it would make instance search for `NoAtoms'` loop through
`instNullSingletonClass'`. -/
theorem of_isLocallyFiniteMeasure {α : Type*} [TopologicalSpace α] [T2Space α]
    [PseudoMetrizableSpace α] [SigmaCompactSpace α] [MeasurableSpace α] [BorelSpace α]
    {μ : Measure α} [IsLocallyFiniteMeasure μ] [NullSingletonClass μ] : NoAtoms' μ :=
  of_innerRegularCompactLTTop

end NoAtoms'

end MeasureTheory
