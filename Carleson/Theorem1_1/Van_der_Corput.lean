/- This file formalizes section 10.6 (The proof of the van der Corput Lemma) from the paper. -/
import Carleson.Theorem1_1.Basic


noncomputable section

open Complex


lemma van_der_Corput {a b : ℝ} (hab : a ≤ b) {n : ℤ} {ϕ : ℝ → ℂ} {B K: NNReal} (h1 : LipschitzWith K ϕ) (h2 : ∀ x ∈ (Set.Ioo a b), ‖ϕ x‖ ≤ B) :
  ‖∫ (x : ℝ) in a..b, (I * n * x).exp * ϕ x‖ ≤
    2 * Real.pi * (b - a) * (B + K * (b - a) / 2) * (1 + |n| * (b - a))⁻¹ := by
  have hK : 0 ≤ K * (b - a) / 2 := by
    apply mul_nonneg _ (by norm_num)
    apply mul_nonneg (by simp) (by linarith)
  by_cases n_nonzero : n = 0
  . rw [n_nonzero]
    simp only [Int.cast_zero, mul_zero, zero_mul, exp_zero, one_mul, abs_zero,
      add_zero, inv_one, mul_one]
    calc ‖∫ (x : ℝ) in a..b, ϕ x‖
      _ = ‖∫ (x : ℝ) in Set.Ioo a b, ϕ x‖ := by
        rw [intervalIntegral.integral_of_le, ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
        linarith
      _ ≤ B * (MeasureTheory.volume (Set.Ioo a b)).toReal := by
        apply MeasureTheory.norm_setIntegral_le_of_norm_le_const' _ measurableSet_Ioo
        . intro x hx
          exact (h2 x hx)
        . rw [Real.volume_Ioo]
          apply ENNReal.ofReal_lt_top
      _ = B * (b - a) := by
        rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
      _ = 1 * (b - a) * B := by
        ring
      _ ≤ 2 * Real.pi * (b - a) * (↑B + ↑K * (b - a) / 2) := by
        gcongr
        . apply mul_nonneg Real.two_pi_pos.le (by linarith)
        . linarith
        . linarith [Real.two_le_pi]
        . simpa
  wlog n_pos : 0 < n generalizing n ϕ
  . --We could do calculations analogous to those below. Instead, we apply the positive case to the complex conjugate.
    push_neg at n_pos
    calc ‖∫ (x : ℝ) in a..b, cexp (I * ↑n * ↑x) * ϕ x‖
      _ = ‖(starRingEnd ℂ) (∫ (x : ℝ) in a..b, cexp (I * ↑n * ↑x) * ϕ x)‖ := Eq.symm RCLike.norm_conj
      _ = ‖∫ (x : ℝ) in a..b, cexp (I * ↑(-n) * ↑x) * ((starRingEnd ℂ) ∘ ϕ) x‖ := by
        rw [intervalIntegral.integral_of_le (by linarith), ← integral_conj, ← intervalIntegral.integral_of_le (by linarith)]
        congr
        ext x
        rw [map_mul, ← exp_conj]
        congr
        simp
        left
        apply conj_ofReal
      _ ≤ 2 * Real.pi * (b - a) * (↑B + ↑K * (b - a) / 2) * (1 + ↑|-n| * (b - a))⁻¹ := by
        apply this
        . intro x y
          simp only [Function.comp_apply]
          rw [edist_eq_coe_nnnorm_sub, ← map_sub, starRingEnd_apply, nnnorm_star, ← edist_eq_coe_nnnorm_sub]
          apply h1
        . intro x hx
          rw [Function.comp_apply, RCLike.norm_conj]
          apply (h2 x hx)
        . simp [n_nonzero]
        . simp
          apply lt_of_le_of_ne n_pos n_nonzero
    rw [abs_neg]
  --TODO: choose good case distinction so that it works
  by_cases h : b - a < Real.pi / n
  . have : 0 < 1 + ↑|n| * (b - a) := by
      apply add_pos_of_pos_of_nonneg zero_lt_one
      apply mul_nonneg (by simp) (by linarith)
    calc _
      _ = ‖∫ (x : ℝ) in Set.Ioo a b, cexp (I * ↑n * ↑x) * ϕ x‖ := by
        rw [intervalIntegral.integral_of_le, ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
        linarith
      _ ≤ B * (MeasureTheory.volume (Set.Ioo a b)).toReal := by
        apply MeasureTheory.norm_setIntegral_le_of_norm_le_const' _ measurableSet_Ioo
        . intro x hx
          rw [norm_mul, mul_assoc, mul_comm I]
          norm_cast
          rw [Complex.norm_exp_ofReal_mul_I, one_mul]
          exact (h2 x hx)
        . rw [Real.volume_Ioo]
          apply ENNReal.ofReal_lt_top
      _ = B * (b - a) := by
        rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
      _ = (1 + |n| * (b - a)) * (1 + |n| * (b - a))⁻¹ * (b - a) * B := by
        rw [mul_inv_cancel]
        ring
        apply ne_of_gt this
      _ ≤ (Real.pi + Real.pi) * (1 + |n| * (b - a))⁻¹ * (b - a) * (B + K * (b - a) / 2) := by
        gcongr
        . apply mul_nonneg
          apply mul_nonneg
          linarith [Real.two_pi_pos]
          exact inv_nonneg_of_nonneg this.le
          linarith
        . linarith
        . linarith [Real.two_le_pi]
        . rw [mul_comm, _root_.abs_of_nonneg n_pos.le]
          apply mul_le_of_nonneg_of_le_div Real.pi_pos.le (by norm_cast; exact n_pos.le)
          exact h.le
        . simpa
      _ = 2 * Real.pi * (b - a) * (B + K * (b - a) / 2) * (1 + |n| * (b - a))⁻¹ := by ring
  push_neg at h
  have pi_div_n_pos : 0 < Real.pi / n := by
    apply div_pos Real.pi_pos (by simpa)
  have integrand_continuous : Continuous (fun x ↦ cexp (I * ↑n * ↑x) * ϕ x)  := by
    apply Continuous.mul (by continuity) h1.continuous
  have integrand_continuous2 : Continuous (fun x ↦ cexp (I * ↑n * (↑x + ↑Real.pi / ↑n)) * ϕ x) := by
    apply Continuous.mul (by continuity) h1.continuous
  have integrand_continuous3 : Continuous (fun (x : ℝ) ↦ cexp (I * n * x) * ϕ (x - Real.pi / n)) := by
    apply Continuous.mul (by continuity)
    apply h1.continuous.comp (by continuity)
  calc _
    _ = ‖∫ (x : ℝ) in a..b, (1 / 2 * (I * n * x).exp - 1 / 2 * (I * ↑n * (↑x + ↑Real.pi / ↑n)).exp) * ϕ x‖ := by
      congr
      ext x
      congr
      rw [mul_add, mul_assoc I n (Real.pi / n), mul_div_cancel₀ _ (by simpa), exp_add, mul_comm I Real.pi, exp_pi_mul_I]
      ring
    _ = ‖1 / 2 * ∫ (x : ℝ) in a..b, cexp (I * ↑n * ↑x) * ϕ x - cexp (I * ↑n * (↑x + ↑Real.pi / ↑n)) * ϕ x‖ := by
      congr
      rw [← intervalIntegral.integral_const_mul]
      congr
      ext x
      ring
    _ = 1 / 2 * ‖(∫ (x : ℝ) in a..b, (I * n * x).exp * ϕ x) - (∫ (x : ℝ) in a..b, (I * n * (x + Real.pi / n)).exp * ϕ x)‖ := by
      rw [norm_mul]
      congr
      simp
      rw [← intervalIntegral.integral_sub]
      apply integrand_continuous.intervalIntegrable
      apply integrand_continuous2.intervalIntegrable
    _ = 1 / 2 * ‖  (∫ (x : ℝ) in a..(a + Real.pi / n), (I * n * x).exp * ϕ x)
                 + (∫ (x : ℝ) in (a + Real.pi / n)..b, (I * n * x).exp * ϕ x)
                 -((∫ (x : ℝ) in a..(b - Real.pi / n), (I * n * (x + Real.pi / n)).exp * ϕ x)
                 + (∫ (x : ℝ) in (b - Real.pi / n)..b, (I * n * (x + Real.pi / n)).exp * ϕ x))‖ := by
      congr 3
      rw [intervalIntegral.integral_add_adjacent_intervals]
      apply integrand_continuous.intervalIntegrable
      apply integrand_continuous.intervalIntegrable
      rw [intervalIntegral.integral_add_adjacent_intervals]
      apply integrand_continuous2.intervalIntegrable
      apply integrand_continuous2.intervalIntegrable
    _ = 1 / 2 * ‖  (∫ (x : ℝ) in a..(a + Real.pi / n), (I * n * x).exp * ϕ x)
                 + (∫ (x : ℝ) in (a + Real.pi / n)..b, (I * n * x).exp * ϕ x)
                 -((∫ (x : ℝ) in (a + Real.pi / n)..(b - Real.pi / n + Real.pi / n), (I * n * x).exp * ϕ (x - Real.pi / n))
                 + (∫ (x : ℝ) in (b - Real.pi / n)..b, (I * n * (x + Real.pi / n)).exp * ϕ x))‖ := by
      congr 4
      rw [← intervalIntegral.integral_comp_add_right]
      simp
    _ = 1 / 2 * ‖  (∫ (x : ℝ) in a..(a + Real.pi / n), (I * n * x).exp * ϕ x)
                 +((∫ (x : ℝ) in (a + Real.pi / n)..b, (I * n * x).exp * ϕ x)
                 - (∫ (x : ℝ) in (a + Real.pi / n)..b, (I * n * x).exp * ϕ (x - Real.pi / n)))
                 - (∫ (x : ℝ) in (b - Real.pi / n)..b, (I * n * (x + Real.pi / n)).exp * ϕ x)‖ := by
      congr 2
      rw [sub_add_cancel]
      ring
    _ = 1 / 2 * ‖  (∫ (x : ℝ) in a..(a + Real.pi / n), (I * n * x).exp * ϕ x)
                 + (∫ (x : ℝ) in (a + Real.pi / n)..b, (I * n * x).exp * (ϕ x - ϕ (x - Real.pi / n)))
                 - (∫ (x : ℝ) in (b - Real.pi / n)..b, (I * n * (x + Real.pi / n)).exp * ϕ x)‖ := by
      congr 4
      rw [← intervalIntegral.integral_sub]
      congr
      ext x
      ring
      apply integrand_continuous.intervalIntegrable
      apply integrand_continuous3.intervalIntegrable
    _ ≤ 1 / 2 * (  ‖(∫ (x : ℝ) in a..(a + Real.pi / n), (I * n * x).exp * ϕ x)
                 +  (∫ (x : ℝ) in (a + Real.pi / n)..b, (I * n * x).exp * (ϕ x - ϕ (x - Real.pi / n)))‖
                 + ‖∫ (x : ℝ) in (b - Real.pi / n)..b, (I * n * (x + Real.pi / n)).exp * ϕ x‖) := by
      gcongr
      apply norm_sub_le
    _ ≤ 1 / 2 * (  ‖(∫ (x : ℝ) in a..(a + Real.pi / n), (I * n * x).exp * ϕ x)‖
                 + ‖(∫ (x : ℝ) in (a + Real.pi / n)..b, (I * n * x).exp * (ϕ x - ϕ (x - Real.pi / n)))‖
                 + ‖∫ (x : ℝ) in (b - Real.pi / n)..b, (I * n * (x + Real.pi / n)).exp * ϕ x‖) := by
      gcongr
      apply norm_add_le
    _ = 1 / 2 * (  ‖∫ (x : ℝ) in Set.Ioo a (a + Real.pi / n), (I * n * x).exp * ϕ x‖
                 + ‖∫ (x : ℝ) in Set.Ioo (a + Real.pi / n) b, (I * n * x).exp * (ϕ x - ϕ (x - Real.pi / n))‖
                 + ‖∫ (x : ℝ) in Set.Ioo (b - Real.pi / n) b, (I * n * (x + Real.pi / n)).exp * ϕ x‖) := by
      congr
      all_goals
        rw [intervalIntegral.integral_of_le, ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
        linarith
    _ ≤ 1 / 2 * (  B * (MeasureTheory.volume (Set.Ioo a (a + Real.pi / n))).toReal
                 + (K * Real.pi / n) * (MeasureTheory.volume (Set.Ioo (a + Real.pi / n) b)).toReal
                 + B * (MeasureTheory.volume (Set.Ioo (b - Real.pi / n) b)).toReal) := by
      gcongr
      . apply MeasureTheory.norm_setIntegral_le_of_norm_le_const' _ measurableSet_Ioo
        . intro x hx
          rw [norm_mul, mul_assoc, mul_comm I]
          norm_cast
          rw [Complex.norm_exp_ofReal_mul_I, one_mul]
          apply h2
          constructor <;> linarith [hx.1, hx.2]
        . rw [Real.volume_Ioo]
          apply ENNReal.ofReal_lt_top
      . apply MeasureTheory.norm_setIntegral_le_of_norm_le_const' _ measurableSet_Ioo
        . intro x _
          rw [norm_mul, mul_assoc, mul_comm I]
          norm_cast
          rw [Complex.norm_exp_ofReal_mul_I, one_mul, ← dist_eq_norm]
          apply le_trans (h1.dist_le_mul _ _)
          . simp
            rw [_root_.abs_of_nonneg Real.pi_pos.le, _root_.abs_of_nonneg (by simp; linarith [n_pos])]
            apply le_of_eq
            ring
        . rw [Real.volume_Ioo]
          apply ENNReal.ofReal_lt_top
      . apply MeasureTheory.norm_setIntegral_le_of_norm_le_const' _ measurableSet_Ioo
        . intro x hx
          rw [norm_mul, mul_assoc, mul_comm I]
          norm_cast
          rw [Complex.norm_exp_ofReal_mul_I, one_mul]
          apply h2
          constructor <;> linarith [hx.1, hx.2]
        . rw [Real.volume_Ioo]
          apply ENNReal.ofReal_lt_top
    _ = Real.pi / n * (B + K * (b - (a + Real.pi / n)) / 2) := by
      rw [Real.volume_Ioo, Real.volume_Ioo, Real.volume_Ioo, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
      ring
      all_goals linarith
    _ ≤ Real.pi / n * (B + K * (b - a) / 2) := by
      gcongr
      linarith
    _ ≤ (2 * Real.pi / (1 + n * (b - a)) * (b - a)) * (B + K * (b - a) / 2) := by
      gcongr
      rw [mul_comm, ← mul_div_assoc, div_le_div_iff (by simpa)]
      calc Real.pi * (1 + n * (b - a))
        _ ≤ Real.pi * (Real.pi + n * (b - a)) := by
          gcongr
          linarith [Real.two_le_pi]
        _ ≤ Real.pi * (n * (b - a) + n * (b - a)) := by
          gcongr
          rwa [← div_le_iff' (by simpa)]
        _ = (b - a) * (2 * Real.pi) * n := by ring
      apply add_pos zero_lt_one
      apply mul_pos (by simpa) (by linarith)
    _ = 2 * Real.pi * (b - a) * (B + K * (b - a) / 2) * (1 + |n| * (b - a))⁻¹ := by
      rw [_root_.abs_of_nonneg n_pos.le]
      ring
