import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Set Bornology Function ENNReal Metric

-- TODO: Not needed, but good for completeness
-- theorem strictConvexOn_rpow_left (b : ℝ) (hb : 0 < b) :
--     StrictConvexOn ℝ Set.univ (fun (x : ℝ) => b ^ x) := by

@[deprecated convexOn_rpow_left (since := "today")]
theorem ConvexOn_rpow_left (b : ℝ) (hb : 0 < b) : ConvexOn ℝ Set.univ (fun (x : ℝ) => b ^ x) :=
  convexOn_rpow_left hb
