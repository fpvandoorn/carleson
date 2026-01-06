import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

namespace ENNReal

theorem rpow_add_le_mul_rpow_add_rpow' (z₁ z₂ : ℝ≥0∞) {p : ℝ} (hp : 0 ≤ p) :
    (z₁ + z₂) ^ p ≤ MeasureTheory.LpAddConst (ENNReal.ofReal p)⁻¹ * (z₁ ^ p + z₂ ^ p) := by
  unfold MeasureTheory.LpAddConst
  split_ifs with h
  · simp at h
    simp only [toReal_inv, div_inv_eq_mul, one_mul]
    rw [toReal_ofReal hp]
    apply ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ h.le
  · rw [one_mul]
    apply ENNReal.rpow_add_le_add_rpow _ _ hp
    simp at h
    assumption

theorem rpow_add_le_mul_rpow_add_rpow'' (z₁ z₂ : ℝ≥0∞) {p : ℝ≥0∞} :
    (z₁ + z₂) ^ p.toReal⁻¹ ≤ MeasureTheory.LpAddConst p * (z₁ ^ p.toReal⁻¹ + z₂ ^ p.toReal⁻¹) := by
  by_cases p_zero : p = 0
  · rw [p_zero]
    simp only [toReal_zero, _root_.inv_zero, rpow_zero]
    rw [MeasureTheory.LpAddConst_zero]
    norm_num
  convert rpow_add_le_mul_rpow_add_rpow' z₁ z₂ (p := p.toReal⁻¹) (by simp)
  rw [← toReal_inv, ENNReal.ofReal_toReal (by simpa), inv_inv]

end ENNReal
