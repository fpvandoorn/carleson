import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Complex.ExponentialBounds

open scoped Nat
open Real MeasureTheory

lemma intervalIntegral_pow_mul_exp_neg_le {k : ℕ} {M c : ℝ} (hM : 0 ≤ M) (hc : 0 < c) :
    ∫ x in (0 : ℝ)..M, x ^ k * rexp (- (c * x)) ≤ k ! / c ^ (k + 1) := by
  have : ∫ x in (0 : ℝ)..M, x ^ k * rexp (- (c * x))
      = (∫ x in (0 : ℝ)..M, (c * x) ^ k * rexp (- (c * x))) / c ^ k := by
    rw [← intervalIntegral.integral_div]
    congr with x
    field_simp [mul_pow, hc.ne']
    ring
  rw [this, intervalIntegral.integral_comp_mul_left (fun x ↦ x ^ k * rexp (-x)) hc.ne']
  simp only [mul_zero, smul_eq_mul]
  rw [← div_eq_inv_mul, div_div, ← pow_succ']
  gcongr
  rw [intervalIntegral.integral_of_le (by positivity),
    ← Real.Gamma_nat_eq_factorial, Real.Gamma_eq_integral (by positivity)]
  simp only [mul_comm, add_sub_cancel_right, Real.rpow_natCast]
  apply setIntegral_mono_set
  · simpa [mul_comm] using Real.GammaIntegral_convergent (s := k + 1) (by positivity)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x)
    positivity
  · apply ae_of_all
    intro x hx
    exact hx.1

lemma sum_Ico_pow_mul_exp_neg_le {k : ℕ} {M : ℕ} {c : ℝ} (hc : 0 < c) :
    ∑ i ∈ Finset.Ico 0 M, i ^ k * rexp (- (c * i)) ≤ rexp c * k ! / c ^ (k + 1) := calc
  ∑ i ∈ Finset.Ico 0 M, i ^ k * rexp (- (c * i))
  _ ≤ ∫ x in (0 : ℕ).. M, x ^ k * rexp (- (c * (x - 1))) := by
    apply sum_mul_Ico_le_integral_of_monotone_antitone
      (f := fun x ↦ x ^ k) (g := fun x ↦ rexp (- (c * x)))
    · exact Nat.zero_le M
    · intro x hx y hy hxy
      apply pow_le_pow_left₀ (by simpa using hx.1) hxy
    · intro x hx y hy hxy
      apply exp_monotone
      simp only [neg_le_neg_iff]
      gcongr
    · simp
    · apply exp_nonneg
  _ ≤ (k ! / c ^ (k + 1)) * rexp c := by
    simp only [mul_sub, mul_one, neg_sub, CharP.cast_eq_zero]
    simp only [sub_eq_add_neg, Real.exp_add, mul_comm (rexp c), ← mul_assoc]
    rw [intervalIntegral.integral_mul_const]
    gcongr
    exact intervalIntegral_pow_mul_exp_neg_le (by simp) hc
  _ = _ := by ring

lemma sum_Iic_pow_mul_exp_neg_le {k : ℕ} {M : ℕ} {c : ℝ} (hc : 0 < c) :
    ∑ i ∈ Finset.Iic M, i ^ k * rexp (- (c * i)) ≤ rexp c * k ! / c ^ (k + 1) :=
  sum_Ico_pow_mul_exp_neg_le (M := M + 1) hc

lemma sum_Iic_pow_mul_two_pow_neg_le {k : ℕ} {M : ℕ} {c : ℝ} (hc : 0 < c) :
    ∑ i ∈ Finset.Iic M, i ^ k * (2 : ℝ) ^ (- (c * i))
      ≤ 2 ^ c * k ! / (Real.log 2 * c) ^ (k + 1) := by
  have A (i : ℕ) : (2 : ℝ) ^ (- (c * i)) = rexp (- (Real.log 2 * c) * i) := by
    conv_lhs => rw [← exp_log zero_lt_two, ← exp_mul]
    congr 1
    ring
  simp only [A, neg_mul]
  apply (sum_Iic_pow_mul_exp_neg_le (by positivity)).trans_eq
  rw [exp_mul, exp_log zero_lt_two]
