import Carleson.Defs

open MeasureTheory Measure NNReal Metric Complex Set
open scoped ENNReal
noncomputable section
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

variable {X : Type*} {A : ℝ} [fact : Fact (1 ≤ A)] [IsSpaceOfHomogeneousType X A]

/- TODO: state Propositions 2.4 -/
