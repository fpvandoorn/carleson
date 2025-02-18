import Mathlib.MeasureTheory.Group.LIntegral

namespace MeasureTheory

open Measure
open scoped ENNReal

variable {G : Type*} [MeasurableSpace G] {μ : Measure G}

section MeasurableInv
variable [Group G] [MeasurableInv G]

/-- If `μ` is invariant under inversion, then `∫⁻ x, f x ∂μ` is unchanged by replacing
`x` with `x⁻¹` -/
@[to_additive
  "If `μ` is invariant under negation, then `∫⁻ x, f x ∂μ` is unchanged by replacing `x` with `-x`"]
theorem lintegral_inv_eq_self [μ.IsInvInvariant] (f : G → ℝ≥0∞) :
    ∫⁻ (x : G), f x⁻¹ ∂μ = ∫⁻ (x : G), f x ∂μ := by
  simpa using (lintegral_map_equiv f (μ := μ) <| MeasurableEquiv.inv G).symm

end MeasurableInv

section MeasurableMul

variable [Group G] [MeasurableMul G]

@[to_additive]
theorem lintegral_div_left_eq_self [IsMulLeftInvariant μ] [MeasurableInv G] [IsInvInvariant μ]
    (f : G → ℝ≥0∞) (g : G) : (∫⁻ x, f (g / x) ∂μ) = ∫⁻ x, f x ∂μ := by
  simp_rw [div_eq_mul_inv, lintegral_inv_eq_self (f <| g * ·), lintegral_mul_left_eq_self]

end MeasurableMul

end MeasureTheory
