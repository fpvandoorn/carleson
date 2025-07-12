import Carleson.MetricCarleson.Main
import Carleson.TwoSidedCarleson.NontangentialOperator

open MeasureTheory Set Bornology Function ENNReal Metric
open scoped NNReal

noncomputable section

/-- The constant used in `two_sided_metric_carleson`.
Has value `2 ^ (452 * a ^ 3) / (q - 1) ^ 6` in the blueprint. -/
-- todo: put C_K in NNReal?
def C10_0_1 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := (C_K a) ^ 2 * C1_0_2 a q

lemma C10_0_1_pos {a : ℕ} {q : ℝ≥0} (hq : 1 < q) : 0 < C10_0_1 a q :=
  mul_pos (pow_two_pos_of_ne_zero <| by simp_rw [ne_eq, C_K_pos.ne', not_false_eq_true])
    (C1_0_2_pos hq)

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {τ C r R : ℝ} {q q' : ℝ≥0}
variable {F G : Set X}
variable {K : X → X → ℂ} {x x' : X} [IsTwoSidedKernel a K]
variable [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)]

/-! ## Theorem 10.0.1 -/

/- Theorem 10.0.1 -/
theorem two_sided_metric_carleson (ha : 4 ≤ a) (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q')
    (hF : MeasurableSet F) (hG : MeasurableSet G)
    (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a))
    {f : X → ℂ} (hmf : Measurable f) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    ∫⁻ x in G, carlesonOperator K f x ≤
    C10_0_1 a q * (volume G) ^ (q' : ℝ)⁻¹ * (volume F) ^ (q : ℝ)⁻¹ := by
  by_cases hG0 : volume G = 0
  · rw [setLIntegral_measure_zero G _ hG0]; exact zero_le _
  by_cases hF_top : volume F = ∞
  · rw [hF_top, ← NNReal.val_eq_coe q, top_rpow_of_pos (inv_pos.mpr (lt_trans one_pos hq.1))]
    convert le_top
    exact mul_top <| by simp [C10_0_1, C1_0_2, hG0, hqq'.sub_one_ne_zero]
  let c := Complex.ofReal ((2 : ℝ) ^ ((-2 : ℝ) * a ^ 3))
  have two_pow_pos {y : ℝ} : 0 < ((2 : ℝ) ^ y) := Real.rpow_pos_of_pos two_pos y
  let K' := c • K
  have : IsOneSidedKernel a K' := by
    apply isOneSidedKernel_const_smul
    unfold c
    rw [neg_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_rpow_of_nonneg two_pos.le, abs_two]
    exact Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by norm_num)
  let : KernelProofData a K' := by constructor <;> assumption
  have HBST : HasBoundedStrongType (nontangentialOperator K') 2 2 volume volume (C_Ts a) := by
    rw [nontangentialOperator_const_smul, ← ofReal_norm_eq_enorm]
    convert HasBoundedStrongType.const_smul (nontangential_from_simple ha hT) ‖c‖.toNNReal
    unfold c
    rw [C_Ts, C10_0_2_def, coe_pow, coe_ofNat, neg_mul, Complex.norm_real, Real.norm_eq_abs]
    change _ = ENNReal.ofNNReal |(2 : ℝ) ^ (-(2 * (a : ℝ) ^ 3))|.toNNReal * (2 : ℝ≥0∞) ^ (3 * a ^ 3)
    rw [ENNReal.ofNNReal_toNNReal, abs_of_pos two_pow_pos, ← ENNReal.ofReal_rpow_of_pos two_pos]
    have : (2 : ℝ≥0∞) ^ (3 * a ^ 3) = (2 : ℝ≥0∞) ^ (3 * (a : ℝ) ^ 3) := by norm_cast
    rw [this, ofReal_ofNat 2, ← rpow_add _ _ (NeZero.ne 2) ENNReal.ofNat_ne_top]
    ring_nf
    rw [← rpow_natCast, Nat.cast_pow]
  have hc0 : ‖c‖ₑ ≠ 0 := enorm_ne_zero.mpr (Complex.ofReal_ne_zero.mpr two_pow_pos.ne')
  rw [← (ENNReal.mul_left_strictMono hc0 enorm_ne_top).le_iff_le]
  rw [← lintegral_const_mul' _ _ enorm_ne_top, mul_assoc, ← mul_assoc, ← mul_assoc]
  convert metric_carleson hq hqq' hF hG hmf hf HBST
  · exact congrFun (carlesonOperator_const_smul K f c) _ |>.symm
  have : ‖c‖ₑ = ENNReal.ofReal ((2 : ℝ) ^ ((-2 : ℝ) * a ^ 3)) := by
    simp [← ofReal_norm_eq_enorm, c, two_pow_pos.le]
  rw [← one_mul (C1_0_2 a q : ℝ≥0∞), C10_0_1, C_K, coe_mul, ← mul_assoc, this, ← ofReal_coe_nnreal,
    ← ofReal_mul two_pow_pos.le, neg_mul, NNReal.coe_pow, NNReal.coe_rpow, NNReal.coe_ofNat]
  congr
  rw [ofReal_eq_one, ← Real.rpow_mul_natCast two_pos.le, ← Real.rpow_add two_pos]
  ring_nf
  exact Real.rpow_zero 2

end
