module

public import Carleson.Classical.ControlApproximationEffectBasic
public import Carleson.Classical.CarlesonOnTheRealLineContinuous



/- This file contains parts of Section 11.6 (The error bound) from the blueprint.
   The main result is `control_approximation_effect'`.

   TODO: This file can be removed once `two_sided_metric_carleson_hasStrongType` no longer depends
   on `sorryAx`
-/

public noncomputable section

local notation "T" => carlesonOperatorReal K
local notation "S_" => partialFourierSum

open NNReal Real Complex ComplexConjugate MeasureTheory

lemma rcarleson_exceptional_set_estimate {δ C : ℝ≥0} (Cpos : 0 < C) {f : ℝ → ℂ}
  (hmf : Measurable f) {F : Set ℝ} (measurableSetF : MeasurableSet F)
  (hf : ∀ x, ‖f x‖ ≤ C * F.indicator 1 x) {E : Set ℝ} (measurableSetE : MeasurableSet E)
  (hE : ∀ x ∈ E, δ ≤ T f x) :
    δ * volume E ≤ C * C10_0_1 4 2 * volume F ^ (2 : ℝ)⁻¹ * volume E ^ (2 : ℝ)⁻¹ := by
  calc δ * volume E
    _ = ∫⁻ _ in E, δ := by
      symm
      apply setLIntegral_const
    _ ≤ ∫⁻ x in E, T f x := by
      apply setLIntegral_mono' measurableSetE hE
    _ = C * ∫⁻ x in E, T (fun x ↦ (1 / C) * f x) x := by
      rw [← lintegral_const_mul']
      swap; · exact ENNReal.coe_ne_top
      congr with x
      rw [carlesonOperatorReal_mul Cpos]
      simp
    _ ≤ C * (C10_0_1 4 2 * (volume E) ^ (2 : ℝ)⁻¹ * (volume F) ^ (2 : ℝ)⁻¹) := by
      gcongr
      apply rcarleson measurableSetF measurableSetE _ (by fun_prop)
      intro x
      simp only [one_div, Complex.norm_mul, norm_inv, norm_real, norm_eq_abs, NNReal.abs_eq]
      rw [inv_mul_le_iff₀ (by simp [Cpos])]
      exact hf x
    _ = C * C10_0_1 4 2 * (volume F) ^ (2 : ℝ)⁻¹ * (volume E) ^ (2 : ℝ)⁻¹ := by
      ring

--TODO: can be removed once `two_sided_metric_carleson_hasStrongType` no longer depends on `sorryAx`
lemma rcarleson_exceptional_set_estimate_specific {δ C : ℝ≥0} (Cpos : 0 < C) {f : ℝ → ℂ}
  (hmf : Measurable f) (hf : ∀ x, ‖f x‖ ≤ C) {E : Set ℝ} (measurableSetE : MeasurableSet E)
  (E_subset : E ⊆ Set.Icc 0 (2 * π)) (hE : ∀ x ∈ E, δ ≤ T f x) :
    δ * volume E ≤ C * C10_0_1 4 2 * ENNReal.ofReal (2 * π + 2) ^ (2 : ℝ)⁻¹ * volume E ^ (2 : ℝ)⁻¹ := by
  set F := (Set.Ioo (0 - 1) (2 * π + 1))
  set h := F.indicator f with hdef
  have hh : ∀ x, ‖h x‖ ≤ C * F.indicator 1 x := by
    intro x
    rw [hdef, norm_indicator_eq_indicator_norm, Set.indicator, Set.indicator]
    split_ifs with hx
    · simp only [Pi.one_apply, mul_one]; exact hf x
    · simp
  convert rcarleson_exceptional_set_estimate Cpos (hmf.indicator measurableSet_Ioo)
    measurableSet_Ioo hh measurableSetE ?_
  · rw [Real.volume_Ioo]
    ring_nf
  · intro x hx
    rw [← carlesonOperatorReal_eq_of_restrict_interval (E_subset hx)]
    exact hE x hx

--TODO: can be removed once `two_sided_metric_carleson_hasStrongType` no longer depends on `sorryAx`
lemma rcarleson_exceptional_set_estimate_specific' {δ C : ℝ≥0} (Cpos : 0 < C) {f : ℝ → ℂ}
  (hmf : Measurable f) (hf : ∀ x, ‖f x‖ ≤ C) {E : Set ℝ} (measurableSetE : MeasurableSet E)
  (E_subset : E ⊆ Set.Icc 0 (2 * π)) (hE : ∀ x ∈ E, δ ≤ T f x) :
    δ * volume E ^ (2 : ℝ)⁻¹ ≤ C * C10_0_1 4 2 * ENNReal.ofReal (2 * π + 2) ^ (2 : ℝ)⁻¹ := by
  by_cases E_zero : volume E = 0
  · rw [E_zero]
    simp
  have E_pow_ne_zero : volume E ^ (2 : ℝ)⁻¹ ≠ 0 := by positivity
  have E_pow_finite : volume E ^ (2 : ℝ)⁻¹ < ⊤ := by
    rw [ENNReal.rpow_lt_top_iff_of_pos (by simp)]
    apply (measure_mono E_subset).trans_lt
    rw [Real.volume_Icc]
    finiteness
  rw [← ENNReal.mul_le_mul_iff_left E_pow_ne_zero E_pow_finite.ne, mul_assoc,
    ← ENNReal.rpow_add_of_pos _ _ _ (by simp) (by simp), ← two_mul, mul_inv_cancel₀ (by simp),
    ENNReal.rpow_one]
  exact rcarleson_exceptional_set_estimate_specific Cpos hmf hf measurableSetE E_subset hE

--TODO: can be removed once `two_sided_metric_carleson_hasStrongType` no longer depends on `sorryAx`
lemma rcarleson_exceptional_set_estimate_specific'' {δ C : ℝ≥0} (Cpos : 0 < C) {f : ℝ → ℂ}
  (hmf : Measurable f) (hf : ∀ x, ‖f x‖ ≤ C) {E : Set ℝ} (measurableSetE : MeasurableSet E)
  (E_subset : E ⊆ Set.Icc 0 (2 * π)) (hE : ∀ x ∈ E, δ ≤ T f x) :
    volume E ≤ C ^ (2 : ℝ) * C10_0_1 4 2 ^ (2 : ℝ) * ENNReal.ofReal (2 * π + 2) / δ ^ (2 : ℝ) := by
  rw [ENNReal.le_div_iff_mul_le (by right; positivity [C10_0_1_pos one_lt_two (a := 4)]) (by simp),
    mul_comm]
  have : 0 < (2 : ℝ)⁻¹ := by positivity
  rw [← ENNReal.rpow_le_rpow_iff this, ENNReal.mul_rpow_of_nonneg _ _ this.le,
    ENNReal.mul_rpow_of_nonneg _ _ this.le, ENNReal.mul_rpow_of_nonneg _ _ this.le,
    ENNReal.rpow_rpow_inv (by simp), ENNReal.rpow_rpow_inv (by simp),
    ENNReal.rpow_rpow_inv (by simp)]
  exact rcarleson_exceptional_set_estimate_specific' Cpos hmf hf measurableSetE E_subset hE

--TODO: can be removed once `two_sided_metric_carleson_hasStrongType` no longer depends on `sorryAx`
/-- The constant used in `C_distribution_carlesonOperatorReal_le'`. -/
def C_distribution_carlesonOperatorReal_le' (δ ε : ℝ≥0) : ℝ≥0 :=
  (ε / ((C10_0_1 4 2) ^ (2 : ℝ) * toNNReal (2 * π + 2) / δ ^ (2 : ℝ))) ^ (2 : ℝ)⁻¹

--TODO: can be removed once `two_sided_metric_carleson_hasStrongType` no longer depends on `sorryAx`
lemma C_distribution_carlesonOperatorReal_le'_pos {δ ε : ℝ≥0} (δpos : 0 < δ) (εpos : 0 < ε) :
    0 < C_distribution_carlesonOperatorReal_le' δ ε := by
  unfold C_distribution_carlesonOperatorReal_le'
  positivity [C10_0_1_pos one_lt_two (a := 4)]

--TODO: can be removed once `two_sided_metric_carleson_hasStrongType` no longer depends on `sorryAx`
theorem C_distribution_carlesonOperatorReal_le'_property {δ ε : ℝ≥0} (δpos : 0 < δ) :
    ↑ε = ↑(C_distribution_carlesonOperatorReal_le' δ ε) ^ (2 : ℝ)
          * ↑(C10_0_1 4 2) ^ (2 : ℝ) * ENNReal.ofReal (2 * π + 2) / ↑δ ^ (2 : ℝ) := by
  unfold C_distribution_carlesonOperatorReal_le'
  rw [ENNReal.coe_rpow_of_nonneg _ (by simp), ENNReal.rpow_inv_rpow (by simp),
    ENNReal.coe_div (by positivity [C10_0_1_pos one_lt_two (a := 4)]),
    ENNReal.coe_div (by positivity), ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ (by simp),
    ENNReal.coe_rpow_of_nonneg _ (by simp), ENNReal.ofReal,
    mul_assoc, mul_div_assoc, ENNReal.div_mul_cancel _ (ENNReal.div_ne_top
      (ENNReal.mul_ne_top (by simp) (by simp)) (by positivity))]
  apply ENNReal.div_ne_zero.mpr
  use by positivity [C10_0_1_pos one_lt_two (a := 4)], by norm_num

--TODO: can be removed once `two_sided_metric_carleson_hasStrongType` no longer depends on `sorryAx`
lemma distribution_carlesonOperatorReal_le' {δ ε : ℝ≥0} (δpos : 0 < δ) (εpos : 0 < ε) {g : ℝ → ℂ}
  (hmg : Measurable g) (hg : ∀ x, ‖g x‖ ≤ C_distribution_carlesonOperatorReal_le' δ ε) :
    distribution (T g) δ (volume.restrict (Set.Ioc 0 (2 * π))) ≤ ε := by
  rw [distribution_eq_measure_superlevelSet, Measure.restrict_apply' measurableSet_Ioc]
  convert rcarleson_exceptional_set_estimate_specific'' (δ := δ)
    (C_distribution_carlesonOperatorReal_le'_pos δpos εpos) hmg hg ?_ ?_ ?_
  · exact C_distribution_carlesonOperatorReal_le'_property δpos
  · apply MeasurableSet.inter _ measurableSet_Ioc
    apply measurableSet_superlevelSet
    apply carlesonOperatorReal_measurable hmg.aestronglyMeasurable
    intro x
    apply Measure.integrableOn_of_bounded _ hmg.aestronglyMeasurable
    · filter_upwards
      exact hg
    · rw [Real.volume_Ioo]
      finiteness
  · exact Set.inter_subset_right.trans Set.Ioc_subset_Icc_self
  · intro x hx
    exact hx.1.le

--TODO: can be removed once `two_sided_metric_carleson_hasStrongType` no longer depends on `sorryAx`
/-- The constant used in `C_control_approximation_effect'`. -/
def C_control_approximation_effect' (δ ε : ℝ≥0) : ℝ≥0 :=
  min (δ / toNNReal (2 * π))
    (C_distribution_carlesonOperatorReal_le' (2 * π * (↑δ / 2) / 2).toNNReal (ε / 2))

--TODO: can be removed once `two_sided_metric_carleson_hasStrongType` no longer depends on `sorryAx`
lemma C_control_approximation_effect'_pos {δ ε : ℝ≥0} (δpos : 0 < δ) (εpos : 0 < ε) :
    0 < C_control_approximation_effect' δ ε :=
  lt_min (by positivity)
    (C_distribution_carlesonOperatorReal_le'_pos (by positivity) (by positivity))

--TODO: can be removed once `two_sided_metric_carleson_hasStrongType` no longer depends on `sorryAx`
lemma C_control_approximation_effect'_property {δ ε : ℝ≥0} :
    C_control_approximation_effect' δ ε * ENNReal.ofReal (2 * π) ≤ δ := by
  unfold C_control_approximation_effect'
  rw [ENNReal.coe_min, min_mul, ENNReal.coe_div (by positivity), ENNReal.ofReal,
    ENNReal.div_mul_cancel (by positivity) (by simp)]
  exact min_le_left _ _

--TODO: can be removed once `two_sided_metric_carleson_hasStrongType` no longer depends on `sorryAx`
lemma C_control_approximation_effect'_le {δ ε : ℝ≥0} :
  C_control_approximation_effect' δ ε
    ≤ C_distribution_carlesonOperatorReal_le' (2 * π * (↑δ / 2) / 2).toNNReal (ε / 2) := by
  exact min_le_right _ _

--TODO: can be removed once `two_sided_metric_carleson_hasStrongType` no longer depends on `sorryAx`
/- This is Lemma 11.6.4 (partial Fourier sums of small) in the blueprint.-/
lemma control_approximation_effect' {δ ε : ℝ≥0} (δpos : 0 < δ) (εpos : 0 < ε)
  {g : ℝ → ℂ} (g_measurable : Measurable g)
  (g_periodic : g.Periodic (2 * π))
  (g_bound : ∀ x, ‖g x‖ ≤ C_control_approximation_effect' δ ε) :
    distribution (fun x ↦ ⨆ N, ‖S_ N g x‖ₑ) δ (volume.restrict (Set.Ioc 0 (2 * π))) ≤ ε := by
  calc _
    _ ≤ distribution (operatorBound g) δ (volume.restrict (Set.Ioc 0 (2 * π))) := by
      apply distribution_mono_left
      rw [ae_restrict_iff' (measurableSet_Ioc)]
      filter_upwards with x hx
      simp only [enorm_eq_self, iSup_le_iff]
      intro N
      apply partialFourierSum_bound g_periodic _ (Set.Ioc_subset_Icc_self hx)
      exact intervalIntegrable_of_bdd g_measurable g_bound
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
                ENNReal.ofReal_mul two_pi_pos.le, ENNReal.ofReal_mul (by simp),
                ENNReal.ofReal_ofNat, ENNReal.ofReal_div_of_pos (by simp),
                ENNReal.ofReal_ofNat]
              simp
            rw [this]
            gcongr
            · apply distribution_carlesonOperatorReal_le' (by positivity) (by positivity)
                g_measurable
              intro x
              exact (g_bound x).trans C_control_approximation_effect'_le
            · have conj_g_periodic : (conj ∘ g).Periodic (2 * π) := by
                intro x
                simp only [Function.comp_apply]
                congr 1
                apply g_periodic
              have conj_g_measurable : Measurable (conj ∘ g) := by fun_prop
              have conj_g_bound :  ∀ (x : ℝ), ‖(conj ∘ g) x‖ ≤ ↑(C_control_approximation_effect' δ ε) := by
                simpa
              apply distribution_carlesonOperatorReal_le' (by positivity) (by positivity)
                conj_g_measurable
              intro x
              exact (conj_g_bound x).trans C_control_approximation_effect'_le
          _ = ε := by simp
      · rw [← distribution_mul (by simp) (by simp)]
        simp only [nonpos_iff_eq_zero]
        rw [Function.const_def, distribution_const, Set.indicator_of_notMem]
        simp only [enorm_eq_self, Set.mem_Iio, not_lt]
        rw [eLpNorm_one_eq_lintegral_enorm]
        calc _
          _ ≤ ∫⁻ (x : ℝ) in Set.Ioc 0 (2 * π), ↑(C_control_approximation_effect' δ ε) := by
            apply setLIntegral_mono measurable_const
            intro x _
            rw [← ofReal_norm, ENNReal.ofReal_le_coe]
            exact g_bound x
          _ ≤ ↑(C_control_approximation_effect' δ ε) * ENNReal.ofReal (2 * π) := by
            rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
          _ ≤ δ := C_control_approximation_effect'_property
          _ = 2 * (δ / 2) := by
            rw [ENNReal.mul_div_cancel (by simp) (by simp)]
    _ = ε := by simp

end
