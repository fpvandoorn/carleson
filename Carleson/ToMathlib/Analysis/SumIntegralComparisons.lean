import Mathlib.Analysis.SumIntegralComparisons
import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.Basic
import Carleson.ToMathlib.MeasureTheory.Function.LocallyIntegrable
import Carleson.ToMathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Complex.ExponentialBounds


open MeasureTheory Set

open scoped ENNReal



variable {x₀ : ℝ} {a b : ℕ} {f g : ℝ → ℝ}

lemma sum_le_integral_of_le
    (hab : a ≤ b) (h : ∀ i ∈ Ico a b, ∀ x ∈ Ico (i : ℝ) (i + 1 : ℕ), f i ≤ g x)
    (hg : IntegrableOn g (Set.Ico a b)) :
    ∑ i ∈ Finset.Ico a b, f i ≤ ∫ x in a..b, g x := by
  have A i (hi : i ∈ Finset.Ico a b) : IntervalIntegrable g volume i (i + 1 : ℕ) := by
    rw [intervalIntegrable_iff_integrableOn_Ico_of_le (by simp)]
    apply hg.mono _ le_rfl
    rintro x ⟨hx, h'x⟩
    simp only [Finset.mem_Ico, mem_Ico] at hi ⊢
    exact ⟨le_trans (mod_cast hi.1) hx, h'x.trans_le (mod_cast hi.2)⟩
  calc
  ∑ i ∈ Finset.Ico a b, f i
  _ = ∑ i ∈ Finset.Ico a b, (∫ x in (i : ℝ)..(i + 1 : ℕ), f i) := by simp
  _ ≤ ∑ i ∈ Finset.Ico a b, (∫ x in (i : ℝ)..(i + 1 : ℕ), g x) := by
    apply Finset.sum_le_sum (fun i hi ↦ ?_)
    apply intervalIntegral.integral_mono_on_of_le_Ioo (by simp) (by simp) (A _ hi) (fun x hx ↦ ?_)
    exact h _ (by simpa using hi) _ (Ioo_subset_Ico_self hx)
  _ = ∫ x in a..b, g x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun i ↦ i) hab]
    intro i hi
    exact A _ (by simpa using hi)

lemma sum_mul_le_integral_of_monotone_antitone
    (hab : a ≤ b) (hf : MonotoneOn f (Icc a b)) (hg : AntitoneOn g (Icc (a - 1) (b - 1)))
    (fpos : 0 ≤ f a) (gpos : 0 ≤ g (b - 1)) :
    ∑ i ∈ Finset.Ico a b, f i * g i ≤ ∫ x in a..b, f x * g (x - 1) := by
  apply sum_le_integral_of_le (f := fun x ↦ f x * g x) hab
  · intro i hi x hx
    simp only [Nat.cast_add, Nat.cast_one, mem_Ico] at hx hi
    have I0 : (i : ℝ) ≤ b - 1 := by
      simp only [le_sub_iff_add_le]
      norm_cast
      omega
    have I1 : (i : ℝ) ∈ Icc (a - 1 : ℝ) (b - 1) := by
      simp only [mem_Icc, tsub_le_iff_right]
      exact ⟨by norm_cast; omega, I0⟩
    have I2 : x ∈ Icc (a : ℝ) b := by
      refine ⟨le_trans (mod_cast hi.1) hx.1, hx.2.le.trans ?_⟩
      norm_cast
      omega
    apply mul_le_mul
    · apply hf
      · simp only [mem_Icc, Nat.cast_le]
        exact ⟨hi.1, hi.2.le⟩
      · exact I2
      · exact hx.1
    · apply hg
      · simp only [mem_Icc, tsub_le_iff_right, sub_add_cancel]
        refine ⟨le_trans (mod_cast hi.1) hx.1, hx.2.le.trans ?_⟩
        norm_cast
        omega
      · exact I1
      · simpa [sub_le_iff_le_add] using hx.2.le
    · apply gpos.trans
      apply hg I1 (by simp [hab]) I0
    · apply fpos.trans
      apply hf (by simp [hab]) I2
      exact le_trans (mod_cast hi.1) hx.1
  · rw [IntegrableOn, ← memℒp_one_iff_integrable]
    apply Memℒp.mono_measure (μ := volume.restrict (Icc (a : ℝ) b))
    · apply Measure.restrict_mono_set
      exact Ico_subset_Icc_self
    apply Memℒp.memℒp_of_exponent_le_of_measure_support_ne_top (s := univ)
      _ (by simp) (by simp) le_top
    apply Memℒp.mul_of_top_left
    · apply AntitoneOn.memℒp_isCompact isCompact_Icc
      intro x hx y hy hxy
      apply hg
      · simpa using hx
      · simpa using hy
      · simpa using hxy
    · exact hf.memℒp_isCompact isCompact_Icc

/- The next two lemmas belong to another file (or should be kept in Carleson?)-/

open scoped Nat
open Real

lemma intervalIntegral_pow_mul_exp_neg_le {k : ℕ} {M c : ℝ} (hM : 0 ≤ M) (hc : 0 < c) :
    ∫ x in (0 : ℝ)..M, x ^ k * exp (- (c * x)) ≤ k ! / c ^ (k + 1) := by
  have : ∫ x in (0 : ℝ)..M, x ^ k * exp (- (c * x))
      = (∫ x in (0 : ℝ)..M, (c * x) ^ k * exp (- (c * x))) / c ^ k := by
    rw [← intervalIntegral.integral_div]
    congr with x
    field_simp [mul_pow, hc.ne']
    ring
  rw [this, intervalIntegral.integral_comp_mul_left (fun x ↦ x ^ k * exp (-x)) hc.ne']
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
    ∑ i ∈ Finset.Ico 0 M, i ^ k * exp (- (c * i)) ≤ exp c * k ! / c ^ (k + 1) := calc
  ∑ i ∈ Finset.Ico 0 M, i ^ k * exp (- (c * i))
  _ ≤ ∫ x in (0 : ℕ).. M, x ^ k * exp (- (c * (x - 1))) := by
    apply sum_mul_le_integral_of_monotone_antitone
      (f := fun x ↦ x ^ k) (g := fun x ↦ exp (- (c * x)))
    · exact Nat.zero_le M
    · intro x hx y hy hxy
      apply pow_le_pow_left₀ (by simpa using hx.1) hxy
    · intro x hx y hy hxy
      apply exp_monotone
      simp only [neg_le_neg_iff]
      gcongr
    · simp
    · apply exp_nonneg
  _ ≤ (k ! / c ^ (k + 1)) * exp c := by
    simp only [mul_sub, mul_one, neg_sub, CharP.cast_eq_zero]
    simp only [sub_eq_add_neg, exp_add, mul_comm (rexp c), ← mul_assoc]
    rw [intervalIntegral.integral_mul_const]
    gcongr
    exact intervalIntegral_pow_mul_exp_neg_le (by simp) hc
  _ = _ := by ring

lemma sum_Iic_pow_mul_exp_neg_le {k : ℕ} {M : ℕ} {c : ℝ} (hc : 0 < c) :
    ∑ i ∈ Finset.Iic M, i ^ k * exp (- (c * i)) ≤ exp c * k ! / c ^ (k + 1) :=
  sum_Ico_pow_mul_exp_neg_le (M := M + 1) hc

lemma sum_Iic_pow_mul_two_pow_neg_le {k : ℕ} {M : ℕ} {c : ℝ} (hc : 0 < c) :
    ∑ i ∈ Finset.Iic M, i ^ k * (2 : ℝ) ^ (- (c * i)) ≤ 2 ^ c * k ! / (log 2 * c) ^ (k + 1) := by
  have A (i : ℕ) : (2 : ℝ) ^ (- (c * i)) = exp (- (log 2 * c) * i) := by
    conv_lhs => rw [← exp_log zero_lt_two, ← exp_mul]
    congr 1
    ring
  simp only [A, neg_mul]
  apply (sum_Iic_pow_mul_exp_neg_le (by positivity)).trans_eq
  rw [exp_mul, exp_log zero_lt_two]

lemma foo (M : ℕ) (q : ℝ) (hq : 1 < q) (h'q : q ≤ 2) :
    ∑ n ≤ M, ∑ _k ≤ n, ∑ _j ≤ 2 * n + 3, ∑ _l < 4 * n + 12,
      (2 : ℝ) ^ (- ((q - 1) / q * n)) ≤ 13009 / (q - 1) ^ 4 := by
  have A (x : ℝ) : (x + 1) * (2 * x + 3 + 1) * (4 * x + 12)
      = 8 * x ^ 3 + 48 * x ^ 2 + 88 * x + 48:= by ring
  simp only [Finset.sum_const, Nat.card_Iio, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.card_Iic, Nat.cast_one, ← mul_assoc, A, ge_iff_le]
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  have : 0 ≤ q - 1 := by linarith
  have : q - 1 ≤ 1 := by linarith
  have : 0.6931471803 ≤ log 2 := Real.log_two_gt_d9.le
  let c := (q - 1) / q
  have hc : 0 < c := div_pos (by linarith) (by linarith)
  calc
  8 * ∑ i ∈ Finset.Iic M, i ^ 3 * (2 : ℝ) ^ (-(c * i))
    + 48 * ∑ i ∈ Finset.Iic M, i ^ 2 * (2 : ℝ) ^ (-(c * i))
    + 88 * ∑ i ∈ Finset.Iic M, i * (2 : ℝ) ^ (-(c * i))
    + 48 * ∑ i ∈ Finset.Iic M, (2 : ℝ) ^ (-(c * i))
  _ = 8 * ∑ i ∈ Finset.Iic M, i ^ 3 * (2 : ℝ) ^ (-(c * i))
      + 48 * ∑ i ∈ Finset.Iic M, i ^ 2 * (2 : ℝ) ^ (-(c * i))
      + 88 * ∑ i ∈ Finset.Iic M, i ^ 1  * (2 : ℝ) ^ (-(c * i))
      + 48 * ∑ i ∈ Finset.Iic M, i ^ 0 * (2 : ℝ) ^ (-(c * i)) := by simp
  _ ≤ 8 * (2 ^ c * 3 ! / (log 2 * c) ^ (3 + 1))
      + 48 * (2 ^ c * 2 ! / (log 2 * c) ^ (2 + 1))
      + 88 * (2 ^ c * 1 ! / (log 2 * c) ^ (1 + 1))
      + 48 * (2 ^ c * 0! / (log 2 * c) ^ (0 + 1)) := by
    gcongr <;> exact sum_Iic_pow_mul_two_pow_neg_le hc
  _ = (2 ^ c * (48 * q ^ 4 / (log 2) ^ 4 + 96 * q^3 * (q - 1) / (log 2) ^ 3
      + 88 * q ^ 2 * (q - 1) ^ 2 / (log 2) ^ 2 + 48 * q * (q - 1) ^ 3/ (log 2))) / (q - 1) ^ 4 := by
    simp only [Nat.factorial, Nat.succ_eq_add_one, Nat.reduceAdd, zero_add, mul_one, Nat.reduceMul,
      Nat.cast_ofNat, mul_pow, div_pow, Nat.cast_one, pow_one, c]
    have : q - 1 ≠ 0 := by linarith
    field_simp
    ring
  _ ≤ (2 ^ (1 : ℝ) * (48 * 2 ^ 4 / (log 2) ^ 4 + 96 * 2 ^ 3 * 1 / (log 2) ^ 3
      + 88 * 2 ^ 2 * 1 ^ 2 / (log 2) ^ 2 + 48 * 2 * 1 ^ 3 / (log 2))) / (q - 1) ^ 4 := by
    gcongr
    · exact one_le_two
    · rw [div_le_one (by linarith)]
      linarith
  _ ≤ (2 ^ (1 : ℝ) * (48 * 2 ^ 4 / 0.6931471803 ^ 4 + 96 * 2 ^ 3 * 1 / 0.6931471803 ^ 3
      + 88 * 2 ^ 2 * 1 ^ 2 / 0.6931471803 ^ 2 + 48 * 2 * 1 ^ 3 / 0.6931471803)) / (q - 1) ^ 4 := by
    gcongr
  _ ≤ 13009 / (q - 1) ^ 4 := by
    gcongr
    norm_num

lemma bar (M : ℕ) (q : ℝ) (hq : 1 < q) (h'q : q ≤ 2) :
    (∑ n ≤ M, ∑ _k ≤ n, ∑ _j ≤ 2 * n + 3, ∑ _l < 4 * n + 12,
      (2 : ℝ≥0∞) ^ (- ((q - 1) / q * n))) ≤ 13009 / (ENNReal.ofReal (q - 1)) ^ 4 := by
  have : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by simp
  simp_rw [this, ENNReal.ofReal_rpow_of_pos zero_lt_two]
  simp only [Finset.sum_const, Nat.card_Iio, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.card_Iic, Nat.cast_one, ge_iff_le]
  calc
  ∑ x ∈ Finset.Iic M, (↑x + 1) * ((2 * ↑x + 3 + 1) * ((4 * ↑x + 12) * ENNReal.ofReal (2 ^ (-((q - 1) / q * ↑x)))))
  _ = ∑ x ∈ Finset.Iic M, ENNReal.ofReal
      ((↑x + 1) * ((2 * ↑x + 3 + 1) * ((4 * ↑x + 12) * 2 ^ (-((q - 1) / q * ↑x))))) := by
    congr with i
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity)]
    congr <;> norm_cast
  _ = ENNReal.ofReal (∑ x ∈ Finset.Iic M,
      (↑x + 1) * ((2 * ↑x + 3 + 1) * ((4 * ↑x + 12) * 2 ^ (-((q - 1) / q * ↑x))))) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro i hi
    positivity
  _ = ENNReal.ofReal (∑ n ≤ M, ∑ _k ≤ n, ∑ _j ≤ 2 * n + 3, ∑ _l < 4 * n + 12,
      (2 : ℝ) ^ (- ((q - 1) / q * n))) := by simp
  _ ≤ ENNReal.ofReal (13009 / (q - 1) ^ 4) := by
    apply ENNReal.ofReal_le_ofReal
    exact foo M q hq h'q
  _ = 13009 / (ENNReal.ofReal (q - 1)) ^ 4 := by
    rw [ENNReal.ofReal_div_of_pos]; swap
    · have : 0 < q - 1 := by linarith
      positivity
    congr
    · norm_cast
    · rw [ENNReal.ofReal_pow]
      linarith
