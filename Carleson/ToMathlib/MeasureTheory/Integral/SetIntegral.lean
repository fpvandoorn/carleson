import Mathlib.MeasureTheory.Integral.SetIntegral

open MeasureTheory

/- Put after `setIntegral_re_add_im`, but probably refactor first to use `enorm` -/

lemma ennnorm_integral_starRingEnd_mul_eq_lintegral_ennnorm
    {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → 𝕜}
    (hf : Integrable f μ) :
    ‖∫ x, starRingEnd 𝕜 (f x / ‖f x‖) * f x ∂μ‖₊ = ∫⁻ x, ‖f x‖₊ ∂μ := by
  have A x : starRingEnd 𝕜 (f x / ‖f x‖) * f x = ‖f x‖ := by
    simp only [div_eq_inv_mul, map_mul, map_inv₀, RCLike.conj_ofReal, mul_assoc, RCLike.conj_mul]
    norm_cast
    rcases eq_or_ne (‖f x‖) 0 with hx | hx
    · simp [hx]
    · rw [pow_two, inv_mul_cancel_left₀ hx]
  simp_rw [A, integral_ofReal, nnnorm_algebraMap']
  rw [lintegral_coe_eq_integral]; swap
  · simpa only [coe_nnnorm] using hf.norm
  simp only [coe_nnnorm, ENNReal.ofReal, ENNReal.coe_inj]
  have : |∫ (a : α), ‖f a‖ ∂μ| = ∫ (a : α), ‖f a‖ ∂μ := by
    apply abs_eq_self.2
    exact integral_nonneg (fun x ↦ by positivity)
  conv_rhs => rw [← this]
  simp only [Real.norm_eq_abs, Real.toNNReal_abs]
  rfl

-- move to Mathlib.Analysis.Normed.Module.Basic, next to nnnorm_algebraMap'
lemma enorm_algebraMap' {𝕜 : Type*} (𝕜' : Type*) [NormedField 𝕜] [SeminormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜']
    [NormOneClass 𝕜'] (x : 𝕜) : ‖(algebraMap 𝕜 𝕜') x‖ₑ = ‖x‖ₑ := by
  simp_rw [enorm_eq_nnnorm]; rw [nnnorm_algebraMap']

lemma enorm_integral_starRingEnd_mul_eq_lintegral_enorm
    {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → 𝕜}
    (hf : Integrable f μ) :
    ‖∫ x, starRingEnd 𝕜 (f x / ‖f x‖) * f x ∂μ‖ₑ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
  have A x : starRingEnd 𝕜 (f x / ‖f x‖) * f x = ‖f x‖ := by
    simp only [div_eq_inv_mul, map_mul, map_inv₀, RCLike.conj_ofReal, mul_assoc, RCLike.conj_mul]
    norm_cast
    rcases eq_or_ne (‖f x‖) 0 with hx | hx
    · simp [hx]
    · rw [pow_two, inv_mul_cancel_left₀ hx]
  simp_rw [A, integral_ofReal, enorm_algebraMap']
  simp_rw [enorm_eq_nnnorm]; rw [lintegral_coe_eq_integral]; swap
  · simpa only [coe_nnnorm] using hf.norm
  simp only [coe_nnnorm, ENNReal.ofReal, ENNReal.coe_inj]
  have : |∫ (a : α), ‖f a‖ ∂μ| = ∫ (a : α), ‖f a‖ ∂μ := by
    apply abs_eq_self.2
    exact integral_nonneg (fun x ↦ by positivity)
  conv_rhs => rw [← this]
  simp only [Real.norm_eq_abs, Real.toNNReal_abs]
  rfl
