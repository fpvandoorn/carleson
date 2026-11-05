module

public import Carleson.ToMathlib.MeasureTheory.Function.LorentzSeminorm.Basic
public import Carleson.ToMathlib.Rearrangement

/-!
# Lorentz seminorm via the decreasing rearrangement

This file expresses `eLorentzNorm` in terms of the decreasing rearrangement `rearrangement f`:
`‖f‖_{L^{p,q}} = ‖t ↦ t ^ (1/p) * f^*(t)‖_{L^q(dt/t)}` for `0 < p < ∞`.
These formulas are used to prove the triangle inequality.

All results which do not need the rearrangement live in
`Carleson.ToMathlib.MeasureTheory.Function.LorentzSeminorm.Basic`.
-/

-- Upstreaming status: depends on `Carleson.ToMathlib.Rearrangement`, which needs to be upstreamed
-- first.

public section

noncomputable section

open TopologicalSpace MeasureTheory Filter

open scoped NNReal ENNReal Topology

variable {α ε : Type*} {m0 : MeasurableSpace α} {p q : ℝ≥0∞} {μ : Measure α} [ENorm ε]

namespace MeasureTheory

theorem iSup_mul_distribution_rpow_eq_iSup_rpow_mul_rearrangement {p : ℝ} (hp : 0 < p)
    {f : α → ε} {μ : Measure α} :
    ⨆ t : ℝ≥0, t * distribution f t μ ^ p⁻¹ = ⨆ t : ℝ≥0, t ^ p⁻¹ * rearrangement f t μ := by
  have hp' : 0 < p⁻¹ := by simpa
  calc _
    _ = ⨆ t, t * distribution f t μ ^ p⁻¹ := by
      rw [ENNReal.iSup_ennreal]
      simp only [distibution_top, left_eq_sup]
      rw [ENNReal.zero_rpow_of_pos hp', mul_zero]
      exact zero_le
  symm
  calc _
    _ = ⨆ t, t ^ p⁻¹ * rearrangement f t μ := by
      rw [ENNReal.iSup_ennreal]
      simp
  symm
  apply le_antisymm
  · apply iSup_le
    intro t
    apply le_of_forall_lt
    intro a ha
    by_cases! a_ne_zero : a = 0
    · rw [a_ne_zero]
      rw [a_ne_zero] at ha
      rw [lt_iSup_iff]
      contrapose! ha
      simp only [nonpos_iff_eq_zero, mul_eq_zero] at *
      simp_rw [ENNReal.rpow_eq_zero_iff_of_pos hp'] at *
      by_cases ht : t = 0
      · left
        assumption
      · right
        rw [← nonpos_iff_eq_zero]
        apply _root_.le_of_forall_pos_le_add
        intro ε hε
        rw [zero_add, ← rearrangement_le_iff_distribution_le]
        rcases ha ε with h | h
        · order
        rw [h]
        exact zero_le
    have a_ne_top : a ≠ ∞ := ha.ne_top
    rw [lt_iSup_iff]
    use (a / t) ^ p
    rw [ENNReal.rpow_rpow_inv hp.ne']
    rw [ENNReal.mul_comm_div]
    nth_rw 1 [← mul_one a]
    gcongr
    rw [ENNReal.lt_div_iff_mul_lt (by simp) (by simp), one_mul,
      lt_rearrangement_iff_lt_distribution]
    apply (ENNReal.lt_rpow_inv_iff hp).mp
    rwa [ENNReal.div_lt_iff (by right; assumption) (by right; assumption), mul_comm]
  · apply iSup_le
    intro t
    apply le_of_forall_lt
    intro a ha
    by_cases! a_ne_zero : a = 0
    · rw [a_ne_zero]
      rw [a_ne_zero] at ha
      rw [lt_iSup_iff]
      contrapose! ha
      simp only [nonpos_iff_eq_zero, mul_eq_zero] at *
      simp_rw [ENNReal.rpow_eq_zero_iff_of_pos hp'] at *
      by_cases ht : t = 0
      · left
        assumption
      · right
        rw [← nonpos_iff_eq_zero]
        apply _root_.le_of_forall_pos_le_add
        intro ε hε
        rw [zero_add, rearrangement_le_iff_distribution_le]
        rcases ha ε with h | h
        · order
        rw [h]
        exact zero_le
    have a_ne_top : a ≠ ∞ := ha.ne_top
    rw [lt_iSup_iff]
    use a / t ^ p⁻¹
    rw [ENNReal.mul_comm_div]
    nth_rw 1 [← mul_one a]
    gcongr
    rw [ENNReal.lt_div_iff_mul_lt (by simp) (by simp), one_mul]
    gcongr
    rw [← lt_rearrangement_iff_lt_distribution]
    rwa [ENNReal.div_lt_iff (by right; assumption) (by right; assumption), mul_comm]

--Theorem 6.6 in https://doi.org/10.1007/978-3-319-30034-4
lemma eLorentzNorm'_eq (p_nonzero : p ≠ 0) (p_ne_top : p ≠ ⊤) {f : α → ε} {μ : Measure α} :
  eLorentzNorm' f p q μ
    = eLpNorm (fun (t : ℝ≥0) ↦ t ^ p⁻¹.toReal * rearrangement f t μ) q
        (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹)) := by
  by_cases q_zero : q = 0
  · rw [q_zero, eLorentzNorm'_exponent_zero', eLpNorm_exponent_zero (by fun_prop)]
  by_cases q_top : q = ⊤
  · rw [q_top, eLorentzNorm'_exponent_top,
      iSup_mul_distribution_rpow_eq_iSup_rpow_mul_rearrangement
        (ENNReal.toReal_pos p_nonzero p_ne_top)]
    simp only [ENNReal.toReal_inv]
    symm
    rw [eLpNorm_exponent_top (by fun_prop), eLpNormEssSup_withDensity (by fun_prop) (by simp)]
    apply eLpNormEssSup_nnreal_eq_iSup_nnreal (f := fun t ↦ t ^ p.toReal⁻¹ * rearrangement f t μ)
    intro a x ha
    apply ContinuousWithinAt.ennreal_mul
    · fun_prop
    · apply continuousWithinAt_rearrangement.congr_mono (Set.eqOn_refl _ _)
      · simp
      · simp
    · rw [or_iff_not_imp_left]
      push Not
      intro h
      exfalso
      rw [h] at ha
      simp at ha
    · right
      simp
  unfold eLorentzNorm'
  rw [← eLpNorm_const_smul'' (by simp; aesop),
      eLpNorm_eq_lintegral_rpow_enorm_toReal q_zero q_top (by fun_prop),
      eLpNorm_eq_lintegral_rpow_enorm_toReal q_zero q_top (by fun_prop),
      lintegral_withDensity_eq_lintegral_mul₀ (by fun_prop) (by fun_prop),
      lintegral_withDensity_eq_lintegral_mul₀ (by fun_prop) (by fun_prop)]
  congr 1
  simp only [ENNReal.toReal_inv, Pi.smul_apply, smul_eq_mul, enorm_eq_self]
  conv =>
    lhs
    congr
    rfl
    intro t
    simp
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp),
        ENNReal.rpow_inv_rpow (ENNReal.toReal_ne_zero.mpr ⟨q_zero, q_top⟩),
        ENNReal.mul_rpow_of_nonneg _ _ (by simp),
        ← mul_assoc, ← mul_assoc, mul_comm _ p, mul_assoc p, ← ENNReal.rpow_neg_one]
  conv =>
    rhs
    congr
    rfl
    intro t
    simp
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_neg_one, ← mul_assoc]
  symm
  calc _
    _ = ∫⁻ t, t ^ ((q / p).toReal - 1) * rearrangement f t μ ^ q.toReal := by
      rw [lintegral_nnreal_eq_lintegral_Ioi_ofReal
            (f := fun t => t ^ (-1) * t ^ (p.toReal⁻¹ * q.toReal) * rearrangement f t μ ^ q.toReal),
          lintegral_ennreal_eq_lintegral_Ioi_ofReal
            (f := fun t => t ^ ((q / p).toReal - 1) * rearrangement f t μ ^ q.toReal)]
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [ENNReal.toReal_div]
      congr
      rw [inv_mul_eq_div, ← ENNReal.toReal_div, ← ENNReal.rpow_add _ _ (by simpa) (by simp)]
      ring_nf
    _ = ∫⁻ t, t ^ ((q / p).toReal - 1)
          * (∫⁻ l in Set.Iio (rearrangement f t μ), q * l ^ (q.toReal - 1)) := by
      congr with t
      congr
      rw [lintegral_const_mul _ (by fun_prop)]
      rw [setLIntegral_Iio_rpow, sub_add_cancel, ENNReal.ofReal_toReal q_top,
        ENNReal.mul_div_cancel q_zero q_top]
      simp only [neg_lt_sub_iff_lt_add, lt_add_iff_pos_right]
      exact ENNReal.toReal_pos q_zero q_top
    _ = ∫⁻ t, (∫⁻ l, t ^ ((q / p).toReal - 1)
          * (Set.Iio (rearrangement f t μ)).indicator (fun l ↦ q * l ^ (q.toReal - 1)) l) := by
      congr with t
      rw [← lintegral_indicator measurableSet_Iio,
          ← lintegral_const_mul _ (Measurable.indicator (by fun_prop) measurableSet_Iio)]
    _ = ∫⁻ l, (∫⁻ t, t ^ ((q / p).toReal - 1)
          * (Set.Iio (rearrangement f t μ)).indicator (fun l ↦ q * l ^ (q.toReal - 1)) l) := by
      rw [lintegral_lintegral_swap]
      apply Measurable.aemeasurable
      apply Measurable.mul (by fun_prop)
      apply Measurable.indicator (f := fun a : ℝ≥0∞ × ℝ≥0∞ ↦ q * a.2 ^ (q.toReal - 1))
        (s := {a | a.2 < rearrangement f a.1 μ}) (by fun_prop)
      exact measurableSet_lt (by fun_prop) (by fun_prop)
    _ = ∫⁻ l, (∫⁻ t, t ^ ((q / p).toReal - 1)
          * (Set.Iio (distribution f l μ)).indicator 1 t * (q * l ^ (q.toReal - 1))) := by
      congr with l
      congr with t
      rw [mul_assoc (_ ^ _)]
      congr
      rw [← Set.indicator_mul_const]
      simp only [Pi.one_apply, one_mul]
      apply Set.indicator_const_eq_indicator_const
      simp only [Set.mem_Iio]
      apply lt_rearrangement_iff_lt_distribution
    _ = ∫⁻ l, (∫⁻ t in Set.Iio (distribution f l μ), t ^ ((q / p).toReal - 1)) * (q * l ^ (q.toReal - 1)) := by
      congr with l
      rw [← lintegral_mul_const _ (by fun_prop), ← lintegral_indicator measurableSet_Iio]
      congr with t
      rw [Set.indicator_mul_right, mul_assoc, ← Set.indicator_mul_const]
      simp
    _ = ∫⁻ l, (distribution f l μ ^ (q / p).toReal / (q / p)) * (q * l ^ (q.toReal - 1)) := by
      congr with l
      rw [setLIntegral_Iio_rpow, sub_add_cancel,
        ENNReal.ofReal_toReal (ENNReal.div_ne_top q_top p_nonzero)]
      simp only [ENNReal.toReal_div, neg_lt_sub_iff_lt_add, lt_add_iff_pos_right]
      exact div_pos (ENNReal.toReal_pos q_zero q_top) (ENNReal.toReal_pos p_nonzero p_ne_top)
    _ = ∫⁻ l, p * l ^ (q.toReal - 1) * distribution f l μ ^ (q / p).toReal := by
      congr with l
      rw [← ENNReal.div_mul _ (by left; assumption) (by left; assumption), ENNReal.div_eq_inv_mul,
        mul_comm, mul_comm q, mul_assoc, ← mul_assoc q, ← mul_assoc q,
        ENNReal.mul_inv_cancel q_zero q_top]
      ring
    _ = ∫⁻ (l : ℝ≥0), p * (↑l ^ (-1 : ℝ) * ↑l ^ q.toReal) * (distribution f (↑l) μ ^ p.toReal⁻¹) ^ q.toReal := by
      rw [lintegral_ennreal_eq_lintegral_Ioi_ofReal
            (f := fun l => p * l ^ (q.toReal - 1) * distribution f l μ ^ (q / p).toReal),
          lintegral_nnreal_eq_lintegral_Ioi_ofReal
            (f := fun l => p * (l ^ (-1 : ℝ) * l ^ q.toReal) * (distribution f l μ ^ p.toReal⁻¹) ^ q.toReal)]
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro l hl
      simp only [ENNReal.toReal_div]
      rw [← ENNReal.rpow_mul, inv_mul_eq_div, ← ENNReal.rpow_add _ _ (by simpa) (by simp)]
      ring_nf

lemma eLorentzNorm'_eq' (p_nonzero : p ≠ 0) (p_ne_top : p ≠ ⊤) {f : α → ε} {μ : Measure α} :
  eLorentzNorm' f p q μ
    = eLpNorm (fun (t : ℝ≥0) ↦ t ^ (p⁻¹.toReal - q⁻¹.toReal) * rearrangement f t μ) q := by
  by_cases q_zero : q = 0
  · rw [q_zero, eLorentzNorm'_exponent_zero', eLpNorm_exponent_zero (by fun_prop)]
  rw [eLorentzNorm'_eq p_nonzero p_ne_top]
  by_cases q_top : q = ⊤
  · rw [q_top, ENNReal.toReal_inv, ENNReal.inv_top, ENNReal.toReal_zero, sub_zero,
      eLpNorm_exponent_top (by fun_prop), eLpNorm_exponent_top (by fun_prop),
      eLpNormEssSup_withDensity (by fun_prop) (by simp)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal q_zero q_top (by fun_prop),
    eLpNorm_eq_lintegral_rpow_enorm_toReal q_zero q_top (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul₀ (by fun_prop) (by fun_prop)]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [Measure.ae_ne volume 0]
  intro t ht
  simp only [ENNReal.toReal_inv, enorm_eq_self, Pi.mul_apply]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp), ENNReal.mul_rpow_of_nonneg _ _ (by simp),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← mul_assoc, sub_mul,
      inv_mul_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨q_zero, q_top⟩)]
  congr
  rw [ENNReal.rpow_sub _ _ (by simpa) (by simp), ENNReal.rpow_one, ENNReal.div_eq_inv_mul]

--TODO: remove this?
lemma eLorentzNorm_eq [TopologicalSpace ε] (p_nonzero : p ≠ 0) (p_ne_top : p ≠ ⊤) {f : α → ε}
  (hf : AEStronglyMeasurable f μ) :
  eLorentzNorm f p q μ
    = eLpNorm (fun (t : ℝ≥0) ↦ t ^ p⁻¹.toReal * rearrangement f t μ) q
        (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹)) := by
  rw [eLorentzNorm_eq_eLorentzNorm' p_nonzero p_ne_top hf]
  exact eLorentzNorm'_eq p_nonzero p_ne_top

end MeasureTheory
