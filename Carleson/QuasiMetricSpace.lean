import Mathlib.Topology.MetricSpace.Basic

open NNReal

instance : Fact ((1 : ℝ≥0) ≤ 1) := .mk le_rfl

/-- For now we are cheating: we are defining PseudoQuasiMetricSpaces to be pseudo metric spaces. -/
class PseudoQuasiMetricSpace (α : Type*) (A : outParam ℝ≥0) [fact : Fact (1 ≤ A)] extends
    PseudoMetricSpace α where

/-- For now we are cheating: we are defining QuasiMetricSpaces to be metric spaces.
  We can manually make sure that we don't use the metric space axioms.
  At some point we'll properly define quasi metric spaces.
  For now, this is useful, so that we can already use definitions of metric spaces (like balls)
  from mathlib that should be generalized to quasi metric spaces. -/
class QuasiMetricSpace (α : Type*) (A : outParam ℝ≥0) [fact : Fact (1 ≤ A)] extends
    MetricSpace α, PseudoQuasiMetricSpace α A where

variable {X : Type*} {A : ℝ≥0} [fact : Fact (1 ≤ A)] [PseudoQuasiMetricSpace X A]

/-- We are allowed to use this for quasi metric spaces, but not `dist_triangle`. -/
lemma dist_quasi_triangle (x y z : X) : dist x z ≤ A * (dist x y + dist y z) :=
  calc dist x z ≤ dist x y + dist y z := dist_triangle x y z
      _ ≤ 1 * (dist x y + dist y z) := by rw [one_mul]
      _ ≤ A * (dist x y + dist y z) := by have : 1 ≤ A := Fact.out; gcongr; norm_cast

lemma qdist_comm (x y : X) : dist x y = dist y x := by rw [dist_comm]

example {Y} [QuasiMetricSpace Y A] (x y z : Y) : dist x z ≤ A * (dist x y + dist y z) :=
  dist_quasi_triangle x y z
