import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Set Bornology Function ENNReal Metric

-- TODO: Not needed, but good for completeness
-- theorem strictConvexOn_rpow_left (b : ℝ) (hb : 0 < b) :
--     StrictConvexOn ℝ Set.univ (fun (x : ℝ) => b ^ x) := by


theorem ConvexOn_rpow_left (b : ℝ) (hb : 0 < b) :
    ConvexOn ℝ Set.univ (fun (x : ℝ) => b ^ x) := by
  have : (fun x => b ^ x) = (Real.exp ∘ (Real.log b * ·)) := by
    ext x
    simp [Real.rpow_def_of_pos hb]
  exact this ▸ ConvexOn.comp_linearMap convexOn_exp (LinearMap.mul ℝ ℝ (Real.log b))
