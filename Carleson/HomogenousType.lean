import Carleson.CoverByBalls

open MeasureTheory Measure NNReal ENNReal Metric
noncomputable section

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

/-! Question(F): should a space of homogenous type extend `PseudoQuasiMetricSpace` or
`QuasiMetricSpace`? -/

/-- A space of homogenous type. -/
class IsSpaceOfHomogenousType (X : Type*) (A : outParam ℝ≥0) [fact : Fact (1 ≤ A)] extends
  PseudoQuasiMetricSpace X A, MeasureSpace X, LocallyCompactSpace X, CompleteSpace X,
  BorelSpace X, IsFiniteMeasureOnCompacts (volume : Measure X) where
  volume_ball_le : ∀ (x : X) r, volume (ball x (2 * r)) ≤ A * volume (ball x r)

export IsSpaceOfHomogenousType (volume_ball_le)

variable {X : Type*} {A : ℝ≥0} [fact : Fact (1 ≤ A)] [IsSpaceOfHomogenousType X A]

instance : SigmaFinite (volume : Measure X) := sorry
instance : ProperSpace X := sorry

lemma test (x : X) (r : ℝ) : volume (ball x (4 * r)) ≤ A ^ 2 * volume (ball x r) := by
  calc volume (ball x (4 * r))
      = volume (ball x (2 * (2 * r))) := by ring_nf
    _ ≤ A * volume (ball x (2 * r)) := by apply volume_ball_le
    _ ≤ A * (A * volume (ball x r)) := by gcongr; apply volume_ball_le
    _ = A ^ 2 * volume (ball x r) := by ring_nf; norm_cast; ring_nf


example (x : X) (r : ℝ) : volume (ball x r) < ∞ := measure_ball_lt_top

example : ∃ n : ℕ, BallsCoverBalls X (2 * r) r n :=
  sorry
