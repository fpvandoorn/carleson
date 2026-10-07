/-
Copyright (c) 2026 Leo Diedering. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leo Diedering
-/
module

public import Carleson.ToMathlib.MeasureTheory.Measure.NoAtoms.Regular
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian distributions have no atoms

This is kept in a separate file to avoid importing probability theory elsewhere.
-/

-- Upstreaming status: to be determined

public section

namespace MeasureTheory

open Set Measure Filter TopologicalSpace ENNReal
open scoped NNReal

namespace NoAtoms'

/-- Analogue of `ProbabilityTheory.nullSingletonClass_gaussianReal` for `NoAtoms'`. -/
theorem gaussianReal {μ : ℝ} {v : ℝ≥0} (h : v ≠ 0) :
    NoAtoms' (ProbabilityTheory.gaussianReal μ v) :=
  have := ProbabilityTheory.nullSingletonClass_gaussianReal (μ := μ) h
  of_isLocallyFiniteMeasure

end NoAtoms'

end MeasureTheory
