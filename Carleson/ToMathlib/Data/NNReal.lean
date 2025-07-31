import Mathlib.Analysis.Normed.Ring.Basic

namespace NNReal

lemma div_self_eq_ite {x : ℝ≥0} : x / x = if 0 < x then 1 else 0 := by
  split_ifs with h
  · exact div_self h.ne'
  · aesop

end NNReal

/-- Transfer an inequality over `ℝ` to one of `NNNorm`s over `ℝ≥0`. -/
lemma Real.nnnorm_le_nnnorm {x y : ℝ} (hx : 0 ≤ x) (hy : x ≤ y) : ‖x‖₊ ≤ ‖y‖₊ := by
  rw [Real.nnnorm_of_nonneg hx, Real.nnnorm_of_nonneg (hx.trans hy)]
  assumption
