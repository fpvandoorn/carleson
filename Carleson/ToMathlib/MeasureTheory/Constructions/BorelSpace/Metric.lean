module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

public section

open Set

namespace MeasureTheory

theorem lowerSemicontinuous_measure_ball {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
    (μ : Measure α) : LowerSemicontinuous fun p : α × ℝ ↦ μ (Metric.ball p.1 p.2) := by
  rintro ⟨x, r⟩ y (hy : y < μ (Metric.ball x r))
  have hmono : Monotone fun r' : Iio r ↦ Metric.ball x r' := fun _ _ h ↦ Metric.ball_subset_ball h
  have hU : ⋃ r' : Iio r, Metric.ball x r' = Metric.ball x r :=
    (iUnion_subtype _ _).trans (Metric.biUnion_lt_ball x r)
  rw [← hU, hmono.measure_iUnion] at hy
  obtain ⟨⟨r', hr'⟩, hn⟩ := lt_iSup_iff.mp hy
  have hopen : IsOpen {p : α × ℝ | r' + dist x p.1 < p.2} := isOpen_lt (by fun_prop) (by fun_prop)
  filter_upwards [hopen.mem_nhds (by simpa using hr')] with p hp
  grw [hn, Metric.ball_subset_ball' hp.le]

theorem measurable_measure_ball {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {μ : Measure α} : Measurable fun p : α × ℝ ↦ μ (Metric.ball p.1 p.2) :=
  (lowerSemicontinuous_measure_ball μ).measurable

end MeasureTheory
