/-
Copyright (c) 2026 Leo Diedering. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leo Diedering
-/
module

public import Carleson.ToMathlib.MeasureTheory.Measure.NoAtoms.Basics
public import Carleson.ToMathlib.MeasureTheory.Measure.NoAtoms.Regular
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Haar measures without atoms

σ-finite, inner regular Haar measures on non-discrete groups have no atoms. In particular, this
gives `NoAtoms'` instances for additive Haar measures on finite-dimensional real vector spaces
and for the Lebesgue measure on the unit interval.
-/

-- Upstreaming status: to be determined

public section

namespace MeasureTheory

open Set Measure Filter TopologicalSpace ENNReal
open scoped Topology

namespace NoAtoms'

/-- Analogue of `MeasureTheory.Measure.IsHaarMeasure.nullSingletonClass` for `NoAtoms'`.
Without σ-finiteness, this fails: for the Haar measure on `ℝ × ℝ_discrete`, the set
`{0} × ℝ_discrete` is an atom of infinite measure. -/
@[to_additive
/-- Analogue of `MeasureTheory.Measure.IsAddHaarMeasure.nullSingletonClass` for `NoAtoms'`.
Without σ-finiteness, this fails: for the Haar measure on `ℝ × ℝ_discrete`, the set
`{0} × ℝ_discrete` is an atom of infinite measure. -/]
theorem of_isHaarMeasure {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [IsTopologicalGroup G] [BorelSpace G] [T1Space G] [WeaklyLocallyCompactSpace G]
    [(𝓝[≠] (1 : G)).NeBot] (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegularCompactLTTop]
    [SigmaFinite μ] : NoAtoms' μ :=
  of_innerRegularCompactLTTop

instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure] [Nontrivial E] : NoAtoms' μ :=
  of_isAddHaarMeasure μ

instance : NoAtoms' (volume : Measure unitInterval) := subtype measurableSet_Icc

end NoAtoms'

end MeasureTheory
