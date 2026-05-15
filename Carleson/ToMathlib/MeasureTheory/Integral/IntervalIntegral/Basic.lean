module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

public section

namespace intervalIntegral

open MeasureTheory Set Filter Function TopologicalSpace

open scoped Topology Filter ENNReal Interval NNReal

variable {E : Type*} [NormedAddCommGroup E]

variable [NormedSpace ℝ E]

variable {a b : ℝ} {f g : ℝ → E} {μ : Measure ℝ}

theorem enorm_integral_min_max (f : ℝ → E) :
    ‖∫ x in min a b..max a b, f x ∂μ‖ₑ = ‖∫ x in a..b, f x ∂μ‖ₑ := by
  cases le_total a b <;> simp [*, integral_symm a b]

theorem enorm_integral_eq_enorm_integral_uIoc (f : ℝ → E) :
    ‖∫ x in a..b, f x ∂μ‖ₑ = ‖∫ x in Ι a b, f x ∂μ‖ₑ := by
  rw [← enorm_integral_min_max, integral_of_le min_le_max, uIoc]

theorem enorm_integral_le_lintegral_enorm_uIoc : ‖∫ x in a..b, f x ∂μ‖ₑ ≤ ∫⁻ x in Ι a b, ‖f x‖ₑ ∂μ :=
  calc
    ‖∫ x in a..b, f x ∂μ‖ₑ = ‖∫ x in Ι a b, f x ∂μ‖ₑ := enorm_integral_eq_enorm_integral_uIoc f
    _ ≤ ∫⁻ x in Ι a b, ‖f x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm f

end intervalIntegral
