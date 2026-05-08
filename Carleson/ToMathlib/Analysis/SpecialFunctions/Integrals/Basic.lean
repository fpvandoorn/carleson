module

public import Carleson.ToMathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Carleson.ToMathlib.MeasureTheory.Measure.NNReal

public section

--Upstreaming status: ready

namespace MeasureTheory

open ENNReal

theorem setLIntegral_Ioo_rpow {p : ℝ} {a b : ℝ≥0∞} (hp : -1 < p) :
    ∫⁻ (t : ℝ≥0∞) in Set.Ioo a b, t ^ p = (b ^ (p + 1) - a ^ (p + 1)) / ENNReal.ofReal (p + 1) := by
  have hp' : 0 < p + 1 := by linarith
  by_cases! a_le_b : a ≤ b
  rotate_left
  · rw [Set.Ioo_eq_empty_of_le a_le_b.le]
    simp only [Measure.restrict_empty, lintegral_zero_measure]
    symm
    rw [ENNReal.div_eq_zero_iff]
    left
    apply tsub_eq_zero_of_le
    gcongr
  rw [← lintegral_indicator measurableSet_Ioo, lintegral_ennreal_eq_lintegral_Ioi_ofReal]
  simp_rw [← Set.indicator_comp_right]
  rw [setLIntegral_indicator (by measurability), ENNReal.ofReal_Ioo_eq]
  simp only [Function.comp_apply]
  split_ifs with ha hab
  · rw [ha, ENNReal.top_rpow_of_pos hp', ENNReal.sub_top, ENNReal.zero_div]
    simp
  · rw [Set.Ioi_inter_Ioi, max_eq_left (by simp), hab.2, ENNReal.top_rpow_of_pos hp',
      ENNReal.top_sub (ENNReal.rpow_ne_top_of_nonneg hp'.le ha),
      ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
    calc _
      _ = ∫⁻ (a : ℝ) in Set.Ioi a.toReal, ENNReal.ofReal (a ^ p) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro x hx
        apply ENNReal.ofReal_rpow_of_pos (ENNReal.toReal_nonneg.trans_lt hx)
    have := not_integrableOn_Ioi_rpow' (@ENNReal.toReal_nonneg a) hp.le
    contrapose! this
    constructor
    · fun_prop
    rwa [hasFiniteIntegral_iff_ofReal, lt_top_iff_ne_top]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact Real.rpow_nonneg (ENNReal.toReal_nonneg.trans hx.le) p
  · simp only [not_and] at hab
    have hb := hab a_le_b
    have a_le_b' := (ENNReal.toReal_le_toReal ha (hab a_le_b)).mpr a_le_b
    rw [Set.Ioo_inter_Ioi, max_eq_left (by simp)]
    have : ∫ (x : ℝ) in a.toReal..b.toReal, x ^ p = (b.toReal ^ (p + 1) - a.toReal ^ (p + 1)) / (p + 1) := by
      apply integral_rpow
      left
      exact hp
    unfold intervalIntegral at this
    rw [Set.Ioc_eq_empty_of_le a_le_b', integral_Ioc_eq_integral_Ioo] at this
    simp only [Measure.restrict_empty, integral_zero_measure, sub_zero] at this
    calc _
      _ = ∫⁻ (a : ℝ) in Set.Ioo a.toReal b.toReal, ENNReal.ofReal (a ^ p) := by
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro x hx
        apply ENNReal.ofReal_rpow_of_pos (ENNReal.toReal_nonneg.trans_lt hx.1)
    rw [← ofReal_integral_eq_lintegral_ofReal, this]
    rotate_left
    · rw [← IntegrableOn, ← intervalIntegrable_iff_integrableOn_Ioo_of_le a_le_b']
      exact intervalIntegral.intervalIntegrable_rpow' hp
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
      exact Real.rpow_nonneg (ENNReal.toReal_nonneg.trans hx.1.le) p
    rw [ENNReal.ofReal_div_of_pos hp']
    congr
    rw [ENNReal.ofReal_sub _ (Real.rpow_nonneg ENNReal.toReal_nonneg _),
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp'.le,
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp'.le,
      ENNReal.ofReal_toReal ha, ENNReal.ofReal_toReal hb]

theorem setLIntegral_Iio_rpow {p : ℝ} {b : ℝ≥0∞} (hp : -1 < p) :
    ∫⁻ (t : ℝ≥0∞) in Set.Iio b, t ^ p = b ^ (p + 1) / ENNReal.ofReal (p + 1) := by
  have := setLIntegral_Ioo_rpow (a := 0) (b := b) hp
  rw [ENNReal.zero_rpow_of_pos (by linarith), tsub_zero] at this
  convert this using 1
  apply setLIntegral_congr
  rw [← Set.Ico_bot]
  exact Ioo_ae_eq_Ico.symm

end MeasureTheory
