import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

-- move next to HasDerivAt.rpow
theorem deriv_const_rpow {a f' x : ℝ} {f : ℝ → ℝ} (hf : HasDerivAt f f' x) (ha : 0 < a) :
    deriv (a ^ f ·) x = (Real.log a) * f' * (a ^ f x) := by
  apply HasDerivAt.deriv
  convert HasDerivAt.rpow (hasDerivAt_const x a) hf ha using 1
  ring
