import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Carleson.ToMathlib.MeasureTheory.Measure.NNReal
import Carleson.ToMathlib.MeasureTheory.Measure.AEMeasurable

noncomputable section

open scoped NNReal ENNReal

variable {α ε : Type*} {m : MeasurableSpace α} [ENorm ε] {f : α → ε}

namespace MeasureTheory


lemma eLpNormEssSup_congr_measure {μ ν : Measure α} (h : ae ν = ae μ) :
    eLpNormEssSup f ν = eLpNormEssSup f μ := by
  unfold eLpNormEssSup essSup
  congr 1

lemma eLpNormEssSup_withDensity {μ : Measure α} {d : α → ℝ≥0∞} (hd : AEMeasurable d μ) (hd' : ∀ᵐ (x : α) ∂μ, d x ≠ 0) :
    eLpNormEssSup f (μ.withDensity d) = eLpNormEssSup f μ := by
  apply eLpNormEssSup_congr_measure
  apply le_antisymm
  · rw [Measure.ae_le_iff_absolutelyContinuous]
    apply withDensity_absolutelyContinuous
  · rw [Measure.ae_le_iff_absolutelyContinuous]
    apply withDensity_absolutelyContinuous' hd  hd'

lemma eLpNormEssSup_nnreal_scale_constant' {f : ℝ≥0 → ℝ≥0∞} {a : ℝ≥0} (h : a ≠ 0)
  (hf : AEStronglyMeasurable f) :
    eLpNormEssSup (fun x ↦ f (a * x)) volume = eLpNormEssSup f volume := by
  calc _
    _ = eLpNormEssSup (f ∘ fun x ↦ a * x) volume := by congr
  rw [← eLpNormEssSup_map_measure _ (by fun_prop)]
  · apply eLpNormEssSup_congr_measure
    rw [NNReal.map_volume_mul_left h]
    apply Measure.ae_ennreal_smul_measure_eq (by simpa)
  · rw [NNReal.map_volume_mul_left h]
    apply AEStronglyMeasurable.smul_measure hf

lemma eLpNorm_withDensity_scale_constant' {f : ℝ≥0 → ℝ≥0∞} (hf : AEStronglyMeasurable f) {p : ℝ≥0∞} {a : ℝ≥0} (h : a ≠ 0) :
  eLpNorm (fun t ↦ f (a * t)) p (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹))
    = eLpNorm f p (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹))  := by
  unfold eLpNorm
  split_ifs with p_zero p_top
  · rfl
  · rw [eLpNormEssSup_withDensity (by fun_prop) (by simp),
        eLpNormEssSup_withDensity (by fun_prop) (by simp),
        eLpNormEssSup_nnreal_scale_constant' h hf]
  · symm
    rw [eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm]
    rw [lintegral_withDensity_eq_lintegral_mul₀' (by measurability)
          (by apply aeMeasurable_withDensity_inv; apply AEMeasurable.pow_const; exact AEStronglyMeasurable.enorm hf),
        lintegral_withDensity_eq_lintegral_mul₀' (by measurability)]
    rotate_left
    · apply aeMeasurable_withDensity_inv
      apply AEMeasurable.pow_const
      apply AEStronglyMeasurable.enorm
      apply AEStronglyMeasurable.comp_aemeasurable
      · rw [NNReal.map_volume_mul_left h]
        apply hf.smul_measure
      fun_prop
    simp only [enorm_eq_self, Pi.mul_apply, one_div]
    rw [← lintegral_nnreal_scale_constant' h, ← lintegral_const_mul' _ _ (by simp)]
    have : ∀ {t : ℝ≥0}, (ENNReal.ofNNReal t)⁻¹ = a * (ENNReal.ofNNReal (a * t))⁻¹ := by
      intro t
      rw [ENNReal.coe_mul, ENNReal.mul_inv, ← mul_assoc, ENNReal.mul_inv_cancel, one_mul]
      · simpa
      · simp
      · right
        simp
      · left
        simp
    simp_rw [← mul_assoc, ← this]

end MeasureTheory
