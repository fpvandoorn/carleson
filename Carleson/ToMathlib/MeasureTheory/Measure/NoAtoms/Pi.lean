/-
Copyright (c) 2026 Leo Diedering. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leo Diedering
-/
module

public import Carleson.ToMathlib.MeasureTheory.Measure.NoAtoms.Regular
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Finite products of measures without atoms

TODO: prove a version without topological assumptions.
-/

-- Upstreaming status: to be determined

public section

namespace MeasureTheory

open Set Measure Filter TopologicalSpace ENNReal

namespace NoAtoms'

/-- Analogue of `MeasureTheory.Measure.pi_nullSingletonClass'` for `NoAtoms'`. -/
theorem pi {ι : Type*} [Fintype ι] [Nonempty ι] {X : ι → Type*} [∀ i, MetricSpace (X i)]
    [∀ i, ProperSpace (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsLocallyFiniteMeasure (μ i)] [∀ i, SigmaFinite (μ i)]
    [∀ i, NullSingletonClass (μ i)] : NoAtoms' (Measure.pi μ) :=
  of_isLocallyFiniteMeasure

end NoAtoms'

end MeasureTheory
