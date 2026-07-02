module

public import Carleson.Classical.ClassicalCarleson
public import Carleson.MetricCarleson.Main
public import Carleson.Defs

/-! # Solution file for using comparator -/

public noncomputable section

open MeasureTheory Set
open scoped NNReal

open Real in
theorem classical_carleson' : ClassicalCarleson := @classical_carleson

theorem metric_carleson'' : MetricSpaceCarleson := @metric_carleson

theorem linearized_metric_carleson' : LinearizedMetricCarleson := @linearized_metric_carleson
