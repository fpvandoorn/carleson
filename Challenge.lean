module

public import Carleson.Defs

/-! # Challenge file for using comparator -/

public noncomputable section

open MeasureTheory Set
open scoped NNReal

-- Carleson's theorem asserting a.e. convergence of the partial Fourier sums for continous functions
open Real in
theorem classical_carleson' : ClassicalCarleson := sorry

theorem metric_carleson'' : MetricSpaceCarleson :=
  sorry

theorem linearized_metric_carleson' : LinearizedMetricCarleson :=
  sorry
