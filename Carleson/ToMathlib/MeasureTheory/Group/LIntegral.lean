import Mathlib.MeasureTheory.Group.LIntegral

namespace MeasureTheory

open Measure
open scoped ENNReal

variable {G : Type*} [MeasurableSpace G] {μ : Measure G}

section MeasurableMul

variable [Group G] [MeasurableMul G]

/- MATHLIB PR: https://github.com/leanprover-community/mathlib4/pull/23341 -/
@[to_additive]
theorem lintegral_div_left_eq_self [IsMulLeftInvariant μ] [MeasurableInv G] [IsInvInvariant μ]
    (f : G → ℝ≥0∞) (g : G) : (∫⁻ x, f (g / x) ∂μ) = ∫⁻ x, f x ∂μ := by
  simp_rw [div_eq_mul_inv, lintegral_inv_eq_self (f <| g * ·), lintegral_mul_left_eq_self]

end MeasurableMul

end MeasureTheory
