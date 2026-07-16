module

public import Carleson.Classical.CarlesonOnTheRealLine
public import Carleson.Classical.ControlApproximationEffectBasic

@[expose] public section

/- This file contains parts of Section 11.6 (The error bound) from the blueprint.
   The main result is `control_approximation_effect`.
-/

noncomputable section

local notation "T" => carlesonOperatorReal K
local notation "S_" => partialFourierSum

open Real NNReal Complex ComplexConjugate MeasureTheory

section TwoPiPos

local instance : Fact (0 < 2 * π) where
  out := Real.two_pi_pos

lemma rcarleson'_restrict {p : ℝ≥0} (hp : p ∈ Set.Ioo 1 2) {f : ℝ → ℂ}
  (f_periodic : f.Periodic (2 * π)) (hf : MemLp f p (volume.restrict (Set.Ioc 0 (2 * π)))) :
    eLpNorm (T f) p (volume.restrict (Set.Ioc 0 (2 * π)))
      ≤ 2 * (C_carleson_hasStrongType 4 p) * eLpNorm f p (volume.restrict (Set.Ioc 0 (2 * π))) := by
  have meas_f : AEStronglyMeasurable f := by
    rw [← zero_add (2 * π)] at hf
    exact (f_periodic.aestronglyMeasurable hf.1)
  have h : eLpNorm ((Set.Ioo (-1) (2 * π + 1)).indicator f) (↑p) volume
      ≤ 2 * eLpNorm f (↑p) (volume.restrict (Set.Ioc 0 (2 * π))) := by
    calc _
        _ ≤ eLpNorm ((Set.Ioc (-1) (-1 + 2 * π)).indicator f) (↑p) volume
            + eLpNorm ((Set.Ioc (-1 + 2 * π) (-1 + 2 * π + 2 * π)).indicator f) (↑p) volume := by
          apply (eLpNorm_add_le _ _ (by simp [hp.1.le])).trans'
          · apply eLpNorm_mono
            intro x
            rw [← Set.indicator_union_add_inter, Set.Ioc_inter_Ioc, Set.Ioc_union_Ioc_eq_Ioc]
            · nth_rw 2 [Set.Ioc_eq_empty_of_le]
              · simp only [Set.indicator_empty, Pi.add_apply, add_zero]
                rw [norm_indicator_eq_indicator_norm, norm_indicator_eq_indicator_norm]
                gcongr
                intro x hx
                use hx.1
                linarith [hx.2, Real.two_le_pi]
              · apply le_max_of_le_right
                apply min_le_left
            · linarith [Real.two_pi_pos]
            · linarith [Real.two_pi_pos]
          · rw [aestronglyMeasurable_indicator_iff measurableSet_Ioc]
            exact meas_f.restrict
          · rw [aestronglyMeasurable_indicator_iff measurableSet_Ioc]
            exact meas_f.restrict
        _ = 2 * eLpNorm f p (volume.restrict (Set.Ioc 0 (2 * π))) := by
          rw [two_mul (eLpNorm _ _ _)]
          rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc,
            eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc]
          congr 1
          · nth_rw 2 [← zero_add (2 * π)]
            exact f_periodic.eLpNorm (by simp)
          · nth_rw 4 [← zero_add (2 * π)]
            exact f_periodic.eLpNorm (by simp)
  calc _
    _ = eLpNorm (T ((Set.Ioo (0 - 1) (2 * π + 1)).indicator f)) p (volume.restrict (Set.Ioc 0 (2 * π))) := by
      apply eLpNorm_congr_ae
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with x hx
      exact carlesonOperatorReal_eq_of_restrict_interval (Set.Ioc_subset_Icc_self hx)
    _ ≤ eLpNorm (T ((Set.Ioo (-1) (2 * π + 1)).indicator f)) p volume := by
      simp only [zero_sub]
      exact eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ (C_carleson_hasStrongType 4 p) * eLpNorm ((Set.Ioo (-1) (2 * π + 1)).indicator f) p volume := by
      apply rcarleson' hp
      rw [memLp_indicator_iff_restrict measurableSet_Ioo]
      use meas_f.restrict
      rw [← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo]
      apply h.trans_lt
      apply ENNReal.mul_lt_top (by simp) hf.2
    _ ≤ 2 * (C_carleson_hasStrongType 4 p) * eLpNorm f p (volume.restrict (Set.Ioc 0 (2 * π))) := by
      rw [mul_comm 2 (ENNReal.ofNNReal _), mul_assoc]
      gcongr

end TwoPiPos

/-- The constant used in `C_distribution_carlesonOperatorReal_le`. -/
def C_distribution_carlesonOperatorReal_le (δ ε p : ℝ≥0) : ℝ≥0 :=
  (2 * (C_carleson_hasStrongType 4 p))⁻¹ * C_distribution_le_of_eLpNorm_le δ ε p

lemma C_distribution_carlesonOperatorReal_le_pos {δ ε p : ℝ≥0} (δpos : 0 < δ) (εpos : 0 < ε) :
    0 < C_distribution_carlesonOperatorReal_le δ ε p := by
  unfold C_distribution_carlesonOperatorReal_le
  apply mul_pos _ (C_distribution_le_of_eLpNorm_le_pos δpos εpos)
  simp [C_carleson_hasStrongType_pos]

lemma distribution_carlesonOperatorReal_le {δ ε p : ℝ≥0} (δpos : 0 < δ)
  (hp : p ∈ Set.Ioo 1 2) {g : ℝ → ℂ}
  (g_periodic : g.Periodic (2 * π)) (g_measurable : AEStronglyMeasurable g)
  (hg : eLpNorm g p (volume.restrict (Set.Ioc 0 (2 * π))) ≤ C_distribution_carlesonOperatorReal_le δ ε p) :
    distribution (T g) δ (volume.restrict (Set.Ioc 0 (2 * π))) ≤ ε := by
  apply distribution_le_of_eLpNorm_le δpos (zero_lt_one.trans hp.1)
  · apply (carlesonOperatorReal_measurable g_measurable _).aestronglyMeasurable
    intro x
    have : Set.Ioo x (x + 2) ⊆ Set.Ioc x (x + (2 * π)) := by
      apply Set.Ioo_subset_Ioc_self.trans'
      apply Set.Ioo_subset_Ioo_right
      linarith [Real.two_le_pi]
    apply IntegrableOn.mono_set _ this
    apply MemLp.integrable (q := p) (by simp [hp.1.le])
    use g_measurable.restrict
    rw [g_periodic.eLpNorm (s := 0) (by simp), zero_add]
    apply hg.trans_lt
    simp
  · apply (rcarleson'_restrict hp g_periodic _).trans
    · calc _
        _ ≤ 2 * ↑(C_carleson_hasStrongType 4 p)
              * ENNReal.ofNNReal (C_distribution_carlesonOperatorReal_le δ ε p) := by
          gcongr
        _ = C_distribution_le_of_eLpNorm_le δ ε p := by
          unfold C_distribution_carlesonOperatorReal_le
          norm_cast
          rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero (by simp) C_carleson_hasStrongType_pos.ne'),
            one_mul]
    · use g_measurable.restrict, hg.trans_lt (by simp)

/-- The constant used in `C_control_approximation_effect`. -/
def C_control_approximation_effect (δ ε p : ℝ≥0) : ℝ≥0 :=
  min (2 * (↑δ / 2) * ((2 * Real.toNNReal π) ^ (1 - p.toReal⁻¹))⁻¹)
    (C_distribution_carlesonOperatorReal_le (2 * π * (↑δ / 2) / 2).toNNReal (ε / 2) p)

lemma C_control_approximation_effect_pos {δ ε p : ℝ≥0} (δpos : 0 < δ) (εpos : 0 < ε) :
    0 < C_control_approximation_effect δ ε p :=
  lt_min (by positivity)
    (C_distribution_carlesonOperatorReal_le_pos (by positivity) (by positivity))

lemma C_control_approximation_effect_property {δ ε p : ℝ≥0} (hp : 1 ≤ p) :
    C_control_approximation_effect δ ε p * (2 * ENNReal.ofReal π) ^ (1 - p.toReal⁻¹) ≤ 2 * (↑δ / 2) := by
  calc _
    _ ≤ 2 * (↑δ / 2) * ((2 * Real.toNNReal π) ^ (1 - p.toReal⁻¹))⁻¹ * (2 * ENNReal.ofReal π) ^ (1 - p.toReal⁻¹) := by
      gcongr
      norm_cast
      exact min_le_left _ _
    _ = 2 * (↑δ / 2) := by
      rw [ENNReal.coe_inv (by simp [Real.pi_pos]), ENNReal.coe_rpow_of_nonneg _
        (by simp only [sub_nonneg]; exact inv_le_one_of_one_le₀ hp),
        ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.ofNNReal_toNNReal,
        ENNReal.inv_mul_cancel_right (by positivity) (ENNReal.rpow_ne_top' (by positivity)
        (ENNReal.mul_ne_top (by simp) (by simp)))]

lemma C_control_approximation_effect_le {δ ε p : ℝ≥0} :
  ENNReal.ofNNReal (C_control_approximation_effect δ ε p) ≤
    (C_distribution_carlesonOperatorReal_le (2 * π * (↑δ / 2) / 2).toNNReal (ε / 2) p) := by
  simp only [ENNReal.coe_le_coe]
  exact min_le_right _ _

/- This is Lemma 11.6.4 (partial Fourier sums of small) in the blueprint.-/
lemma control_approximation_effect {δ ε : ℝ≥0} (δpos : 0 < δ)
  {g : ℝ → ℂ} (g_measurable : AEStronglyMeasurable g)
  (g_periodic : g.Periodic (2 * π))
  {p : ℝ≥0} (hp : p ∈ Set.Ioo 1 2)
  (g_bound : eLpNorm g p (volume.restrict (Set.Ioc 0 (2 * π))) ≤ C_control_approximation_effect δ ε p) :
    distribution (fun x ↦ ⨆ N, ‖S_ N g x‖ₑ) δ (volume.restrict (Set.Ioc 0 (2 * π))) ≤ ε := by
  calc _
    _ ≤ distribution (operatorBound g) δ (volume.restrict (Set.Ioc 0 (2 * π))) := by
      apply distribution_mono_left
      rw [ae_restrict_iff' (measurableSet_Ioc)]
      filter_upwards with x hx
      simp only [enorm_eq_self, iSup_le_iff]
      intro N
      apply partialFourierSum_bound g_periodic _ (Set.Ioc_subset_Icc_self hx)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le, IntegrableOn]
      apply MemLp.integrable (q := p) (by simp [hp.1.le])
      use g_measurable.restrict
      exact g_bound.trans_lt (by simp)
    _ = distribution (operatorBound g) (δ / 2 + δ / 2) (volume.restrict (Set.Ioc 0 (2 * π))) := by
      congr
      simp
    _ ≤ distribution (fun x ↦ (T g x + T (conj ∘ g) x) / ENNReal.ofReal (2 * π)) (δ / 2) (volume.restrict (Set.Ioc 0 (2 * π)))
          + distribution (fun x ↦ eLpNorm g 1 (volume.restrict (Set.Ioc 0 (2 * π))) / 2) (δ / 2) (volume.restrict (Set.Ioc 0 (2 * π))) := by
      apply distribution_add_le
    _ ≤ ε + 0 := by
      gcongr
      · rw [← distribution_mul (by left; exact ENNReal.ofReal_ne_top) (by left; simp [Real.pi_pos])]
        calc _
          _ ≤ distribution (T g) (ENNReal.ofReal (2 * π) * (↑δ / 2) / 2) (volume.restrict (Set.Ioc 0 (2 * π)))
                + distribution (T (conj ∘ g)) (ENNReal.ofReal (2 * π) * (↑δ / 2) / 2) (volume.restrict (Set.Ioc 0 (2 * π))) := by
            apply distribution_add_le.trans'
            gcongr
            · simp
            rw [← two_mul, ENNReal.mul_div_cancel (by simp) (by simp)]
          _ ≤ ENNReal.ofNNReal (ε / 2) + ENNReal.ofNNReal  (ε / 2) := by
            have : ENNReal.ofReal (2 * π) * (↑δ / 2) / 2 = ENNReal.ofReal ((2 * π) * (↑δ / 2) / 2) := by
              rw [ENNReal.ofReal_div_of_pos (by simp), ENNReal.ofReal_mul (by simp),
                ENNReal.ofReal_mul Real.two_pi_pos.le, ENNReal.ofReal_mul (by simp),
                ENNReal.ofReal_ofNat, ENNReal.ofReal_div_of_pos (by simp),
                ENNReal.ofReal_ofNat]
              simp
            rw [this]
            gcongr
            · apply distribution_carlesonOperatorReal_le (by positivity) hp g_periodic
                g_measurable
              exact g_bound.trans C_control_approximation_effect_le
            · have conj_g_periodic : (conj ∘ g).Periodic (2 * π) := by
                intro x
                simp only [Function.comp_apply]
                congr 1
                apply g_periodic
              have conj_g_measurable : AEStronglyMeasurable (conj ∘ g) := by fun_prop
              have conj_g_bound : eLpNorm (conj ∘ g) p (volume.restrict (Set.Ioc 0 (2 * π)))
                  ≤ C_control_approximation_effect δ ε p := by
                convert g_bound using 1
                apply eLpNorm_congr_norm_ae
                simp
              apply distribution_carlesonOperatorReal_le (by positivity) hp
                conj_g_periodic conj_g_measurable
              exact conj_g_bound.trans C_control_approximation_effect_le
          _ = ε := by simp
      · rw [← distribution_mul (by simp) (by simp)]
        simp only [nonpos_iff_eq_zero]
        rw [Function.const_def, distribution_const, Set.indicator_of_notMem]
        simp only [enorm_eq_self, Set.mem_Iio, not_lt]
        have hp' : (1 : ENNReal) ≤ p := by simp [hp.1.le]
        apply (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp' g_measurable.restrict).trans
        rw [Measure.restrict_apply_univ, Real.volume_Ioc]
        simp only [sub_zero, Nat.ofNat_nonneg, ENNReal.ofReal_mul, ENNReal.ofReal_ofNat,
          ENNReal.toReal_one, ne_eq, one_ne_zero, not_false_eq_true, div_self, ENNReal.coe_toReal,
          one_div]
        apply (C_control_approximation_effect_property hp.1.le).trans'
        gcongr
    _ = ε := by simp

end
