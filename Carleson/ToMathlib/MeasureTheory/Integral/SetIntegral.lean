import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory

-- Put after `setIntegral_re_add_im`

lemma starRingEnd_div_mul_eq_norm {α 𝕜 : Type*} [RCLike 𝕜] {f : α → 𝕜} (x : α) :
    starRingEnd 𝕜 (f x / ‖f x‖) * f x = ‖f x‖ := by
  simp only [div_eq_inv_mul, map_mul, map_inv₀, RCLike.conj_ofReal, mul_assoc, RCLike.conj_mul]
  norm_cast
  rcases eq_or_ne (‖f x‖) 0 with hx | hx
  · simp [hx]
  · rw [pow_two, inv_mul_cancel_left₀ hx]

-- move to Mathlib.Analysis.Normed.Module.Basic, next to nnnorm_algebraMap'
lemma enorm_algebraMap' {𝕜 : Type*} (𝕜' : Type*) [NormedField 𝕜] [SeminormedRing 𝕜']
    [NormedAlgebra 𝕜 𝕜'] [NormOneClass 𝕜'] (x : 𝕜) : ‖(algebraMap 𝕜 𝕜') x‖ₑ = ‖x‖ₑ := by
  simp [enorm_eq_nnnorm]

lemma enorm_integral_norm_eq_integral_enorm {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜]
    {μ : Measure α} {f : α → 𝕜} (hf : Integrable f μ) : ‖∫ x, ‖f x‖ ∂μ‖ₑ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
  simp_rw [enorm_eq_nnnorm]
  rw [lintegral_coe_eq_integral]
  · simp only [coe_nnnorm, ENNReal.ofReal, ENNReal.coe_inj]
    have : |∫ (a : α), ‖f a‖ ∂μ| = ∫ (a : α), ‖f a‖ ∂μ :=
      abs_eq_self.2 (integral_nonneg (fun _ ↦ by positivity))
    aesop
  · simpa only [coe_nnnorm] using hf.norm

lemma enorm_integral_starRingEnd_mul_eq_lintegral_enorm
    {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → 𝕜}
    (hf : Integrable f μ) :
    ‖∫ x, starRingEnd 𝕜 (f x / ‖f x‖) * f x ∂μ‖ₑ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
  simp_rw [starRingEnd_div_mul_eq_norm, integral_ofReal, enorm_algebraMap',
    enorm_integral_norm_eq_integral_enorm hf]
