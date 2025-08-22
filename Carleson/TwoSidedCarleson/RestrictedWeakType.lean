import Carleson.ToMathlib.RealInterpolation.LorentzInterpolation
import Carleson.ToMathlib.MeasureTheory.Function.LocallyIntegrable
import Carleson.TwoSidedCarleson.MainTheorem

/-! This file contains a reformulation of Theorem 10.0.1.
It is not officially part of the blueprint. -/


open MeasureTheory Set Bornology Function ENNReal Metric
open scoped NNReal

noncomputable section

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {τ C r R : ℝ} {q q' : ℝ≥0}
variable {F G : Set X}
variable {K : X → X → ℂ} {x x' : X} [IsTwoSidedKernel a K]
variable [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)]

/-! ## Reformulations of Theorem 10.0.1 -/

/- Theorem 10.0.1, reformulation -/
theorem two_sided_metric_carleson_restricted_weak_type (ha : 4 ≤ a) (hq : q ∈ Ioc 1 2)
  (hqq' : q.HolderConjugate q')
  (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a)) :
      HasRestrictedWeakType (carlesonOperator K) q q' volume volume (C10_0_1 a q) := by
  unfold HasRestrictedWeakType
  intro F G hF F_finite hG G_finite
  constructor
  · sorry --TODO: hopefully, this is already done somewhere
    -- or check if maybe this can be removed from the definition of HasRestrictedWeakType
  rw [eLpNorm_one_eq_lintegral_enorm, mul_assoc, mul_comm (volume _ ^ _), ← mul_assoc]
  simp_rw [enorm_eq_self]
  simp only [toReal_inv, coe_toReal]
  apply two_sided_metric_carleson ha hq hqq' hF hG hT
  · exact (measurable_indicator_const_iff 1).mpr hF
  · intro x
    unfold indicator
    split_ifs <;> simp


theorem two_sided_metric_carleson_lorentz_type (ha : 4 ≤ a)
  (hq : q ∈ Ioo 1 2)
  (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a)) :
    HasLorentzType (carlesonOperator K) q 1 q ⊤ volume volume (4 * (C10_0_1 a q) / q) := by
  have hqq' := NNReal.HolderConjugate.conjExponent hq.1
  rename_i m d kernel cf cancel
  have : IsOneSidedKernel a K := by infer_instance
  set kpd : KernelProofData a K := KernelProofData.mk d ha cf this
  apply (two_sided_metric_carleson_restricted_weak_type ha (mem_Ioc_of_Ioo hq) hqq' hT).hasLorentzType
  · simpa
  · intro f g x hf hg
    simp only [enorm_eq_self]
    apply carlesonOperator_add_le_add_carlesonOperator
    · apply (hf.memLp _).locallyIntegrable <;> simp [hq.1.le]
    · apply (hg.memLp _).locallyIntegrable <;> simp [hq.1.le]
  · intro a f x
    simp only [enorm_eq_self]
    apply le_of_eq
    rw [carlesonOperator_const_smul']
    rfl
  · intro f fs f_locInt h_meas h_norm_monotone h_lim G
    calc _
      _ ≤ eLpNorm (fun x ↦ Filter.liminf (fun n ↦ carlesonOperator K (fs n) x) Filter.atTop) 1 (volume.restrict G) := by
        apply eLpNorm_mono_enorm
        intro x
        simp only [enorm_eq_self]
        apply carlesonOperator_le_liminf_carlesonOperator_of_tendsto (norm ∘ f)
          (Filter.Eventually.of_forall h_meas) _ f_locInt.norm (Filter.Eventually.of_forall h_lim)
        apply Filter.Eventually.of_forall
        intro n
        apply Filter.Eventually.of_forall
        intro x
        simp only [comp_apply]
        have h_lim := (h_lim x).norm
        have h_norm_monotone := h_norm_monotone x
        apply h_norm_monotone.ge_of_tendsto h_lim
      _ ≤ Filter.liminf (fun n ↦ eLpNorm (carlesonOperator K (fs n)) 1 (volume.restrict G)) Filter.atTop := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        simp_rw [eLpNorm_one_eq_lintegral_enorm, enorm_eq_self]
        apply lintegral_liminf_le'
        intro n
        apply AEMeasurable.restrict
        sorry --TODO: find / show lemma about measurability of the Carleson operator
    apply Filter.liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)

--TODO: move
def interpolation_param (t₀ t₁ t : ℝ) := (t - t₀) / (t₁ - t₀)

--TODO: move
lemma interpolation_param_interpolation {t₀ t₁ t : ℝ} (h : t₀ ≠ t₁) :
    t = (1 - interpolation_param t₀ t₁ t) * t₀ + interpolation_param t₀ t₁ t * t₁ := by
  have : t₁ - t₀ ≠ 0 := sub_ne_zero_of_ne (id (Ne.symm h))
  unfold interpolation_param
  rw [← div_self this, div_sub_div_same]
  symm
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_add_div_same, div_eq_iff this]
  ring

--TODO: move
lemma interpolation_param_mem_Ioo {t₀ t₁ t : ℝ} (h : t ∈ Ioo t₀ t₁) :
    interpolation_param t₀ t₁ t ∈ Ioo 0 1 := by
  have : t₀ < t₁ := h.1.trans h.2
  unfold interpolation_param
  constructor
  · apply div_pos (by simp [h.1]) (by simpa)
  · rw [div_lt_one (by simpa)]
    simp [h.2]


/- Theorem 10.0.1, reformulation -/
theorem two_sided_metric_carleson_strong_type (ha : 4 ≤ a) (hq : q ∈ Ioo 1 2)
    --(hqq' : q.HolderConjugate q')
    (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a)) :
      let q₀ := (q + 2) / 2;
      let q₁ := (q + 1) / 2;
      let t := (interpolation_param q₀⁻¹ q₁⁻¹ q⁻¹).toNNReal;
      HasStrongType (carlesonOperator K) q q volume volume
        ((C_LorentzInterpolation q₀ q₁ q₀ q₁ q (4 * C10_0_1 a q₀ / q₀) (4 * C10_0_1 a q₁ / q₁) 1 t)) := by
  --TODO: change parameters of constant to something reasonable
  set q₀ := (q + 2) / 2
  set q₁ := (q + 1) / 2
  set t := (interpolation_param q₀⁻¹ q₁⁻¹ q⁻¹).toNNReal
  have one_eq : (1 : ℝ≥0) = 1 / 2 + 1 / 2 := by rw [← add_div]; simp
  have two_eq : (2 : ℝ≥0) = 3 / 2 + 1 / 2 := by rw [← add_div]; refine NNReal.eq ?_; norm_num
  have hq₀ : q₀ ∈ Ioo 1 2 := by
    unfold q₀
    rw [add_div]
    constructor
    · norm_num
      exact zero_lt_one.trans hq.1
    · norm_num
      nth_rw 2 [← one_add_one_eq_two]
      gcongr
      rw [← div_self_of_invertible 2]
      gcongr
      exact hq.2
  have hq₁ : q₁ ∈ Ioo 1 2 := by
    unfold q₁
    rw [add_div]
    constructor
    · nth_rw 1 [one_eq]
      gcongr
      exact hq.1
    · nth_rw 3 [two_eq]
      gcongr
      apply hq.2.trans
      norm_num
  have q₀_ne_q₁ : q₀ ≠ q₁ := by
    unfold q₀ q₁
    rw [ne_eq, div_eq_div_iff (by norm_num) (by norm_num)]
    simp
  have q_pos : 0 < q := lt_trans zero_lt_one hq.1
  have q₀_pos : 0 < q₀ := lt_trans zero_lt_one hq₀.1
  have q₁_pos : 0 < q₁ := lt_trans zero_lt_one hq₁.1
  have h : interpolation_param (↑q₀)⁻¹ (↑q₁)⁻¹ (↑q)⁻¹ ∈ Ioo 0 1 := by
    apply interpolation_param_mem_Ioo
    simp only [mem_Ioo]
    rw [← NNReal.coe_inv, ← NNReal.coe_inv, ← NNReal.coe_inv]
    rw [NNReal.coe_lt_coe, NNReal.coe_lt_coe, inv_lt_inv₀ q₀_pos q_pos, inv_lt_inv₀ q_pos q₁_pos]
    constructor
    · unfold q₀
      rw [lt_div_iff₀ zero_lt_two, mul_two]
      gcongr
      exact hq.2
    · unfold q₁
      rw [div_lt_iff₀ zero_lt_two, mul_two]
      gcongr
      exact hq.1
  have ht : t ∈ Ioo 0 1 := by
    unfold t
    simp only [mem_Ioo, Real.toNNReal_pos, Real.toNNReal_lt_one]
    rwa [← mem_Ioo]
  have hqq₀q₁ : q⁻¹ = (1 - t) / q₀ + t / q₁ := by
    have : q⁻¹.toReal = ((1 - t) / q₀ + t / q₁).toReal := by
      push_cast
      rw [NNReal.coe_sub ht.2.le]
      simp only [NNReal.coe_one]
      have := @interpolation_param_interpolation q₀⁻¹ q₁⁻¹ q⁻¹
      simp only [ne_eq, inv_inj, NNReal.coe_inj] at this
      have := this q₀_ne_q₁
      unfold t
      rw [Real.coe_toNNReal _ h.1.le]
      exact this
    rwa [← Real.toNNReal_eq_toNNReal_iff, Real.toNNReal_coe, Real.toNNReal_coe] at this
    simp
    positivity
  have lorentzType_q₀ :
      HasLorentzType (carlesonOperator K) q₀ 1 q₀ ⊤ volume volume (4 * (C10_0_1 a q₀) / q₀) := by
    apply two_sided_metric_carleson_lorentz_type ha hq₀ hT
  have lorentzType_q₁ :
      HasLorentzType (carlesonOperator K) q₁ 1 q₁ ⊤ volume volume (4 * (C10_0_1 a q₁) / q₁) := by
    apply two_sided_metric_carleson_lorentz_type ha hq₁ hT

  have helper {p : ℝ≥0} (hp : 0 < p): (4 * (C10_0_1 a p) / p) = ENNReal.ofNNReal (4 * (C10_0_1 a p) / p) := by
    norm_cast
    rw [ENNReal.coe_div hp.ne.symm]
  rw [helper q₀_pos] at lorentzType_q₀
  rw [helper q₁_pos] at lorentzType_q₁

  -- use interpolation for Lorentz spaces
  rw [hasStrongType_iff_hasLorentzType]
  convert exists_hasLorentzType_real_interpolation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lorentzType_q₀ lorentzType_q₁ _ _
  · simp [hq₀.1.le]
  · simp [hq₁.1.le]
  · rfl
  · rfl
  · simp [hq₀.1.le]
  · simp [hq₁.1.le]
  · exact OrderTop.le_top 1
  · exact OrderTop.le_top 1
  · rw [coe_ne_coe]
    exact q₀_ne_q₁
  · rw [coe_ne_coe]
    exact q₀_ne_q₁
  · exact zero_lt_one' ℝ≥0
  · exact ht
  · apply div_pos _ q₀_pos
    apply @_root_.mul_pos
    · norm_num
    apply C10_0_1_pos hq₀.1
  · apply div_pos _ q₁_pos
    apply @_root_.mul_pos
    · norm_num
    apply C10_0_1_pos hq₁.1
  · norm_cast
    rw [← ENNReal.coe_div q₁_pos.ne.symm, ← ENNReal.coe_div q₀_pos.ne.symm,
        ← ENNReal.coe_inv q_pos.ne.symm, ← ENNReal.coe_add]
    norm_cast
  · norm_cast
    rw [← ENNReal.coe_div q₀_pos.ne.symm, ← ENNReal.coe_div q₁_pos.ne.symm, ← ENNReal.coe_inv q_pos.ne.symm, ← ENNReal.coe_add]
    norm_cast
  · sorry --TODO: get this from lemma about measurability of the carlesonOperator
  · unfold AESubadditiveOn
    intro f g hf hg
    simp only [enorm_eq_self, coe_one, one_mul]
    apply Filter.Eventually.of_forall
    intro x
    rename_i m d kernel cf cancel
    have : IsOneSidedKernel a K := by infer_instance
    set kpd : KernelProofData a K := KernelProofData.mk d ha cf this
    apply carlesonOperator_add_le_add_carlesonOperator
    · rcases hf with hf | hf
      · apply (hf.memLp _).locallyIntegrable <;> simp [hq₀.1.le]
      · apply (hf.memLp _).locallyIntegrable <;> simp [hq₁.1.le]
    · rcases hg with hg | hg
      · apply (hg.memLp _).locallyIntegrable <;> simp [hq₀.1.le]
      · apply (hg.memLp _).locallyIntegrable <;> simp [hq₁.1.le]

  · simp only [coe_pos]
    exact lt_trans (zero_lt_one' ℝ≥0) hq.1


end
