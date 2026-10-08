/-
Copyright (c) 2026 Leo Diedering. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leo Diedering
-/
module

public import Carleson.ToMathlib.MeasureTheory.Measure.NoAtoms.Regular
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Measures with density without atoms

TODO: prove a version without topological assumptions, e.g. for σ-finite `μ` with `NoAtoms' μ`
and `f < ∞` almost everywhere.
-/

-- Upstreaming status: to be determined

public section

namespace MeasureTheory

open Set Measure Filter TopologicalSpace ENNReal

namespace NoAtoms'

/-- A version of `MeasureTheory.Measure.nullSingletonClass_withDensity` for `NoAtoms'`.
Some assumption on `f` is needed: for `f = ∞`, every set of positive measure is an atom of
`μ.withDensity f`. -/
theorem withDensity {α : Type*} [TopologicalSpace α] [T2Space α]
    [PseudoMetrizableSpace α] [SigmaCompactSpace α] [MeasurableSpace α] [BorelSpace α]
    {μ : Measure α} [NullSingletonClass μ] {f : α → ℝ≥0∞} (hf : LocallyIntegrable f μ) :
    NoAtoms' (μ.withDensity f) := by
  have : IsLocallyFiniteMeasure (μ.withDensity f) := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨U, hU, hfU⟩ := hf x
    refine ⟨interior U, interior_mem_nhds.mpr hU, ?_⟩
    rw [withDensity_apply _ isOpen_interior.measurableSet]
    refine (lintegral_mono_set interior_subset).trans_lt ?_
    simpa [HasFiniteIntegral] using hfU.2
  exact of_isLocallyFiniteMeasure

end NoAtoms'

end MeasureTheory
