import Mathlib.MeasureTheory.Integral.IntervalIntegral

open MeasureTheory Set

namespace intervalIntegral

variable {μ : Measure ℝ} {a b : ℝ} {f g : ℝ → ℝ} (hab : a ≤ b)
(hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b)
include hab hf hg

/-- To put just after `integral_mono_on`. -/
theorem integral_mono_on_of_le_Ioo [NoAtoms μ] (h : ∀ x ∈ Ioo a b, f x ≤ g x) :
    (∫ u in a..b, f u ∂μ) ≤ ∫ u in a..b, g u ∂μ := by
  simp only [integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_mono_on
  · apply hf.1.mono Ioo_subset_Ioc_self le_rfl
  · apply hg.1.mono Ioo_subset_Ioc_self le_rfl
  · exact measurableSet_Ioo
  · exact h

end intervalIntegral
