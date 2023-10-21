import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Topology.MetricSpace.Holder
import Carleson.QuasiMetricSpace

open MeasureTheory Measure NNReal ENNReal Metric
noncomputable section

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

/-- A space of homogenous type. -/
class IsSpaceOfHomogenousType (X : Type*) (A : outParam ℝ≥0) [fact : Fact (1 ≤ A)] extends
  QuasiMetricSpace X A, MeasureSpace X, LocallyCompactSpace X, CompleteSpace X,
  SigmaFinite (volume : Measure X) /- maybe? -/, BorelSpace X where
  volume_ball_le : ∀ (x : X) r, volume (ball x (2 * r)) ≤ A * volume (ball x r)

variable {X : Type*} {A : ℝ≥0} [fact : Fact (1 ≤ A)] [IsSpaceOfHomogenousType X A]
export IsSpaceOfHomogenousType (volume_ball_le)

lemma test (x : X) (r : ℝ) : volume (ball x (4 * r)) ≤ A ^ 2 * volume (ball x r) := by
  calc volume (ball x (4 * r))
      = volume (ball x (2 * (2 * r))) := by ring_nf
    _ ≤ A * volume (ball x (2 * r)) := by apply volume_ball_le
    _ ≤ A * (A * volume (ball x r)) := by gcongr; apply volume_ball_le
    _ = A ^ 2 * volume (ball x r) := by ring_nf; norm_cast; ring_nf

example (x : X) (r : ℝ) : ∃ S : Finset X, ball x (2 * r) ⊆ ⋃ y ∈ S, ball y r :=
  sorry