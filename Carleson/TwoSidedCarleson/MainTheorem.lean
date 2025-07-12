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
  let c := (2 : ℝ) ^ (-2 * (a : ℝ) ^ 3)
  have c_pos : 0 < c := Real.rpow_pos_of_pos two_pos _
  have : IsOneSidedKernel a (c • K) := by
    apply isOneSidedKernel_const_smul
    unfold c
    rw [neg_mul, Real.abs_rpow_of_nonneg two_pos.le, abs_two]
    exact Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by norm_num)
  let : KernelProofData a (c • K) := by constructor <;> assumption
  have : nontangentialOperator (c • K) = ‖c‖ₑ • nontangentialOperator K := by
    convert nontangentialOperator_const_smul (c : ℂ)
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Complex.norm_real]
  have HBST : HasBoundedStrongType (nontangentialOperator (c • K)) 2 2 volume volume (C_Ts a) := by
    rw [this, ← ofReal_norm_eq_enorm]
    convert HasBoundedStrongType.const_smul (nontangential_from_simple ha hT) ‖c‖.toNNReal
    rw [C_Ts, C10_0_2_def, coe_pow, coe_ofNat, ← rpow_natCast, Nat.cast_pow, ENNReal.smul_def,
      Real.norm_eq_abs, ofNNReal_toNNReal, abs_of_pos c_pos, ← ofReal_rpow_of_pos two_pos,
      coe_pow, coe_ofNat, ← rpow_natCast, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
      ofReal_ofNat 2, smul_eq_mul, ← rpow_add _ _ (NeZero.ne 2) ENNReal.ofNat_ne_top]
    ring_nf
  rw [← ENNReal.mul_le_mul_left (enorm_ne_zero.mpr c_pos.ne') enorm_ne_top,
    ← lintegral_const_mul' _ _ enorm_ne_top, mul_assoc, ← mul_assoc, ← mul_assoc]
  convert metric_carleson hq hqq' hF hG hmf hf HBST
  · convert congrFun (carlesonOperator_const_smul K f (c : ℂ)) _ |>.symm; simp
  rw [C10_0_1, C_K, coe_mul, ← mul_assoc, ← ofReal_coe_nnreal, Real.enorm_eq_ofReal c_pos.le,
    ← ofReal_mul c_pos.le, NNReal.coe_pow, NNReal.coe_rpow, NNReal.coe_ofNat,
    ← Real.rpow_mul_natCast two_pos.le, ← Real.rpow_add two_pos,
    ofReal_eq_one.mpr (by ring_nf; exact Real.rpow_zero 2), one_mul]

end
