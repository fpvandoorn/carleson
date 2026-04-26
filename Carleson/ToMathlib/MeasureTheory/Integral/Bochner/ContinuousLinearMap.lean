import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory

-- Upstreaming status: looks ready for upstreaming; pay attention to the correct file to move to!
-- `exists_ne_zero_of_setIntegral_ne_zero` and `exists_ne_zero_of_integral_ne_zero` upstreamed in
-- https://github.com/leanprover-community/mathlib4/pull/37568

-- Put after `setIntegral_re_add_im`

lemma starRingEnd_div_mul_eq_norm {α 𝕜 : Type*} [RCLike 𝕜] {f : α → 𝕜} (x : α) :
    starRingEnd 𝕜 (f x / ‖f x‖) * f x = ‖f x‖ := by
  simp only [div_eq_inv_mul, map_mul, map_inv₀, RCLike.conj_ofReal, mul_assoc, RCLike.conj_mul]
  norm_cast
  rcases eq_or_ne (‖f x‖) 0 with hx | hx
  · simp [hx]
  · field_simp

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

lemma enorm_integral_mul_starRingEnd_comm
    {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → 𝕜} :
    ‖∫ x, f x * starRingEnd 𝕜 (g x) ∂μ‖ₑ = ‖∫ x, g x * starRingEnd 𝕜 (f x) ∂μ‖ₑ := by
  rw [← RCLike.enorm_conj, ← integral_conj]; congr! 3; simp [mul_comm]

-- Like this it fits copy-paste next to setIntegral_union
section SetIntegral_Union_2

variable {X E : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : X → E} {s t : Set X} {μ : Measure X}

theorem MeasureTheory.setIntegral_union_2
    (hst : Disjoint s t) (ht : MeasurableSet t) (hfst : IntegrableOn f (s ∪ t) μ) :
    ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ + ∫ x in t, f x ∂μ :=
  setIntegral_union hst ht hfst.left_of_union hfst.right_of_union

end SetIntegral_Union_2

-- move to Mathlib.MeasureTheory.Integral.Bochner.Set
theorem MeasureTheory.exists_ne_zero_of_setIntegral_ne_zero {α E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace α] {μ : MeasureTheory.Measure α} {f : α → E} {U : Set α}
    (hU : ∫ (u : α) in U, f u ∂μ ≠ 0) : ∃ u : α, u ∈ U ∧ f u ≠ 0 := by
  contrapose! hU
  exact setIntegral_eq_zero_of_forall_eq_zero hU

-- move to Mathlib.MeasureTheory.Integral.Bochner.Basic
theorem MeasureTheory.exists_ne_zero_of_integral_ne_zero {α E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace α] {μ : MeasureTheory.Measure α} {f : α → E}
    (h : ∫ (u : α), f u ∂μ ≠ 0) : ∃ u : α, f u ≠ 0 := by
  contrapose! h
  exact integral_eq_zero_of_ae ((Set.eqOn_univ f 0).mp fun ⦃x⦄ a ↦ h x).eventuallyEq
