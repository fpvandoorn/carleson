/- This file formalizes section 11.4 (The proof of the van der Corput Lemma) from the paper. -/
import Carleson.Classical.Basic

noncomputable section

open scoped Real
open Complex MeasureTheory

lemma van_der_Corput {a b : ℝ} (hab : a ≤ b) {n : ℤ} {ϕ : ℝ → ℂ} {B K: NNReal}
    (h1 : LipschitzWith K ϕ) (h2 : ∀ x ∈ (Set.Ioo a b), ‖ϕ x‖ ≤ B) :
    ‖∫ (x : ℝ) in a..b, (I * n * x).exp * ϕ x‖ ≤
     2 * π * (b - a) * (B + K * (b - a) / 2) * (1 + |n| * (b - a))⁻¹ := by
  have hK : 0 ≤ K * (b - a) / 2 := by
    apply mul_nonneg (mul_nonneg (by simp) (by linarith)) (by norm_num)
  by_cases n_nonzero : n = 0
  · rw [n_nonzero]
    simp only [Int.cast_zero, mul_zero, zero_mul, exp_zero, one_mul, abs_zero,
      add_zero, inv_one, mul_one]
    calc ‖∫ (x : ℝ) in a..b, ϕ x‖
      _ = ‖∫ (x : ℝ) in Set.Ioo a b, ϕ x‖ := by
        rw [intervalIntegral.integral_of_le, ← integral_Ioc_eq_integral_Ioo]
        linarith
      _ ≤ B * (volume (Set.Ioo a b)).toReal := by
        apply norm_setIntegral_le_of_norm_le_const' _ measurableSet_Ioo
        · exact fun x hx ↦ (h2 x hx)
        · exact Real.volume_Ioo ▸ ENNReal.ofReal_lt_top
      _ = B * (b - a) := by rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
      _ = 1 * (b - a) * B := by ring
      _ ≤ 2 * π * (b - a) * (↑B + ↑K * (b - a) / 2) := by
        gcongr
        · exact mul_nonneg Real.two_pi_pos.le (by linarith)
        · exact sub_nonneg_of_le hab
        · linarith [Real.two_le_pi]
        · exact (le_add_iff_nonneg_right ↑B).mpr hK
  wlog n_pos : 0 < n generalizing n ϕ
  · /-We could do calculations analogous to those below. Instead, we apply the positive
    case to the complex conjugate.-/
    push_neg at n_pos
    calc ‖∫ (x : ℝ) in a..b, cexp (I * ↑n * ↑x) * ϕ x‖
      _ = ‖(starRingEnd ℂ) (∫ (x : ℝ) in a..b, cexp (I * ↑n * ↑x) * ϕ x)‖ := (RCLike.norm_conj _).symm
      _ = ‖∫ (x : ℝ) in a..b, cexp (I * ↑(-n) * ↑x) * ((starRingEnd ℂ) ∘ ϕ) x‖ := by
        rw [intervalIntegral.integral_of_le (by linarith), ← integral_conj, ← intervalIntegral.integral_of_le (by linarith)]
        congr
        ext x
        rw [map_mul, ← exp_conj]
        congr
        simp
        -- exact Or.inl (conj_ofReal _)
      _ ≤ 2 * π * (b - a) * (↑B + ↑K * (b - a) / 2) * (1 + ↑|-n| * (b - a))⁻¹ := by
        apply this
        · intro x y
          simp only [Function.comp_apply]
          rw [edist_eq_coe_nnnorm_sub, ← map_sub, starRingEnd_apply, nnnorm_star, ← edist_eq_coe_nnnorm_sub]
          exact h1 _ _
        · intro x hx
          rw [Function.comp_apply, RCLike.norm_conj]
          exact h2 x hx
        · exact Int.neg_ne_zero.mpr n_nonzero
        · rw [Left.neg_pos_iff]; exact lt_of_le_of_ne n_pos n_nonzero
    rw [abs_neg]
  --Case distinction such that splitting integrals in the second case works.
  by_cases h : b - a < π / n
  · have : 0 < 1 + ↑|n| * (b - a) := by
      apply add_pos_of_pos_of_nonneg zero_lt_one
      apply mul_nonneg (by simp) (by linarith)
    calc _
      _ = ‖∫ (x : ℝ) in Set.Ioo a b, cexp (I * ↑n * ↑x) * ϕ x‖ := by
        rw [intervalIntegral.integral_of_le, ← integral_Ioc_eq_integral_Ioo]
        linarith
      _ ≤ B * (volume (Set.Ioo a b)).toReal := by
        apply norm_setIntegral_le_of_norm_le_const' _ measurableSet_Ioo
        · intro x hx
          rw_mod_cast [norm_mul, mul_assoc, mul_comm I, Complex.norm_exp_ofReal_mul_I, one_mul]
          exact h2 x hx
        · exact Real.volume_Ioo ▸ ENNReal.ofReal_lt_top
      _ = B * (b - a) := by rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
      _ = (1 + |n| * (b - a)) * (1 + |n| * (b - a))⁻¹ * (b - a) * B := by
        rw [mul_inv_cancel₀]
        ring
        exact ne_of_gt this
      _ ≤ (π + π) * (1 + |n| * (b - a))⁻¹ * (b - a) * (B + K * (b - a) / 2) := by
        gcongr
        · apply mul_nonneg
          apply mul_nonneg
          linarith [Real.two_pi_pos]
          · exact inv_nonneg_of_nonneg this.le
          · linarith
        · linarith
        · linarith [Real.two_le_pi]
        · rw [mul_comm, _root_.abs_of_nonneg n_pos.le]
          exact mul_le_of_le_div₀ Real.pi_pos.le (by exact_mod_cast n_pos.le) h.le
        · simpa
      _ = 2 * π * (b - a) * (B + K * (b - a) / 2) * (1 + |n| * (b - a))⁻¹ := by ring
  push_neg at h
  have pi_div_n_pos : 0 < π / n := div_pos Real.pi_pos (Int.cast_pos.mpr n_pos)
  have integrand_continuous : Continuous (fun x ↦ cexp (I * ↑n * ↑x) * ϕ x)  :=
    Continuous.mul (by fun_prop) h1.continuous
  have integrand_continuous2 : Continuous (fun x ↦ cexp (I * ↑n * (↑x + ↑π / ↑n)) * ϕ x) :=
    Continuous.mul (by fun_prop) h1.continuous
  have integrand_continuous3 : Continuous (fun (x : ℝ) ↦ cexp (I * n * x) * ϕ (x - π / n)) :=
    Continuous.mul (by fun_prop) (h1.continuous.comp (by continuity))
  calc _
    _ = ‖∫ (x : ℝ) in a..b, (1 / 2 * (I * n * x).exp - 1 / 2 * (I * ↑n * (↑x + ↑π / ↑n)).exp) * ϕ x‖ := by
      congr
      ext x
      congr
      rw [mul_add, mul_assoc I n (π / n), mul_div_cancel₀ _ (by simpa), exp_add, mul_comm I π, exp_pi_mul_I]
      ring
    _ = ‖1 / 2 * ∫ (x : ℝ) in a..b, cexp (I * ↑n * ↑x) * ϕ x - cexp (I * ↑n * (↑x + ↑π / ↑n)) * ϕ x‖ := by
      congr
      rw [← intervalIntegral.integral_const_mul]
      congr
      ext x
      ring
    _ = 1 / 2 * ‖(∫ (x : ℝ) in a..b, (I * n * x).exp * ϕ x) - (∫ (x : ℝ) in a..b, (I * n * (x + π / n)).exp * ϕ x)‖ := by
      rw [norm_mul]
      congr
      simp
      rw [← intervalIntegral.integral_sub]
      · exact integrand_continuous.intervalIntegrable _ _
      · exact integrand_continuous2.intervalIntegrable _ _
    _ = 1 / 2 * ‖  (∫ (x : ℝ) in a..(a + π / n), (I * n * x).exp * ϕ x)
                 + (∫ (x : ℝ) in (a + π / n)..b, (I * n * x).exp * ϕ x)
                 -((∫ (x : ℝ) in a..(b - π / n), (I * n * (x + π / n)).exp * ϕ x)
                 + (∫ (x : ℝ) in (b - π / n)..b, (I * n * (x + π / n)).exp * ϕ x))‖ := by
      congr 3
      rw [intervalIntegral.integral_add_adjacent_intervals]
      · exact integrand_continuous.intervalIntegrable _ _
      · exact integrand_continuous.intervalIntegrable _ _
      rw [intervalIntegral.integral_add_adjacent_intervals]
      · exact integrand_continuous2.intervalIntegrable _ _
      · exact integrand_continuous2.intervalIntegrable _ _
    _ = 1 / 2 * ‖  (∫ (x : ℝ) in a..(a + π / n), (I * n * x).exp * ϕ x)
                 + (∫ (x : ℝ) in (a + π / n)..b, (I * n * x).exp * ϕ x)
                 -((∫ (x : ℝ) in (a + π / n)..(b - π / n + π / n), (I * n * x).exp * ϕ (x - π / n))
                 + (∫ (x : ℝ) in (b - π / n)..b, (I * n * (x + π / n)).exp * ϕ x))‖ := by
      congr 4
      rw [← intervalIntegral.integral_comp_add_right]
      simp
    _ = 1 / 2 * ‖  (∫ (x : ℝ) in a..(a + π / n), (I * n * x).exp * ϕ x)
                 +((∫ (x : ℝ) in (a + π / n)..b, (I * n * x).exp * ϕ x)
                 - (∫ (x : ℝ) in (a + π / n)..b, (I * n * x).exp * ϕ (x - π / n)))
                 - (∫ (x : ℝ) in (b - π / n)..b, (I * n * (x + π / n)).exp * ϕ x)‖ := by
      congr 2
      rw [sub_add_cancel]
      ring
    _ = 1 / 2 * ‖  (∫ (x : ℝ) in a..(a + π / n), (I * n * x).exp * ϕ x)
                 + (∫ (x : ℝ) in (a + π / n)..b, (I * n * x).exp * (ϕ x - ϕ (x - π / n)))
                 - (∫ (x : ℝ) in (b - π / n)..b, (I * n * (x + π / n)).exp * ϕ x)‖ := by
      congr 4
      rw [← intervalIntegral.integral_sub]
      congr
      ext x
      ring
      · exact integrand_continuous.intervalIntegrable _ _
      · exact integrand_continuous3.intervalIntegrable _ _
    _ ≤ 1 / 2 * (  ‖(∫ (x : ℝ) in a..(a + π / n), (I * n * x).exp * ϕ x)
                 +  (∫ (x : ℝ) in (a + π / n)..b, (I * n * x).exp * (ϕ x - ϕ (x - π / n)))‖
                 + ‖∫ (x : ℝ) in (b - π / n)..b, (I * n * (x + π / n)).exp * ϕ x‖) := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ 1 / 2 * (  ‖(∫ (x : ℝ) in a..(a + π / n), (I * n * x).exp * ϕ x)‖
                 + ‖(∫ (x : ℝ) in (a + π / n)..b, (I * n * x).exp * (ϕ x - ϕ (x - π / n)))‖
                 + ‖∫ (x : ℝ) in (b - π / n)..b, (I * n * (x + π / n)).exp * ϕ x‖) := by
      gcongr
      exact norm_add_le _ _
    _ = 1 / 2 * (  ‖∫ (x : ℝ) in Set.Ioo a (a + π / n), (I * n * x).exp * ϕ x‖
                 + ‖∫ (x : ℝ) in Set.Ioo (a + π / n) b, (I * n * x).exp * (ϕ x - ϕ (x - π / n))‖
                 + ‖∫ (x : ℝ) in Set.Ioo (b - π / n) b, (I * n * (x + π / n)).exp * ϕ x‖) := by
      congr
      all_goals
        rw [intervalIntegral.integral_of_le, ← integral_Ioc_eq_integral_Ioo]
        linarith
    _ ≤ 1 / 2 * (  B * (volume (Set.Ioo a (a + π / n))).toReal
                 + (K * π / n) * (volume (Set.Ioo (a + π / n) b)).toReal
                 + B * (volume (Set.Ioo (b - π / n) b)).toReal) := by
      gcongr
      · apply norm_setIntegral_le_of_norm_le_const' _ measurableSet_Ioo
        · intro x hx
          rw [norm_mul, mul_assoc, mul_comm I]
          rw_mod_cast [Complex.norm_exp_ofReal_mul_I, one_mul]
          apply h2
          constructor <;> linarith [hx.1, hx.2]
        · exact Real.volume_Ioo ▸ ENNReal.ofReal_lt_top
      · apply norm_setIntegral_le_of_norm_le_const' _ measurableSet_Ioo
        · intro x _
          rw [norm_mul, mul_assoc, mul_comm I]
          rw_mod_cast [Complex.norm_exp_ofReal_mul_I, one_mul, ← dist_eq_norm]
          apply le_trans (h1.dist_le_mul _ _)
          simp
          rw [_root_.abs_of_nonneg Real.pi_pos.le, _root_.abs_of_nonneg (by simp; linarith [n_pos])]
          apply le_of_eq
          ring
        · exact Real.volume_Ioo ▸ ENNReal.ofReal_lt_top
      · apply norm_setIntegral_le_of_norm_le_const' _ measurableSet_Ioo
        · intro x hx
          rw [norm_mul, mul_assoc, mul_comm I]
          rw_mod_cast [Complex.norm_exp_ofReal_mul_I, one_mul]
          apply h2
          constructor <;> linarith [hx.1, hx.2]
        · exact Real.volume_Ioo ▸ ENNReal.ofReal_lt_top
    _ = π / n * (B + K * (b - (a + π / n)) / 2) := by
      rw [Real.volume_Ioo, Real.volume_Ioo, Real.volume_Ioo, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
      ring
      all_goals linarith
    _ ≤ π / n * (B + K * (b - a) / 2) := by
      gcongr
      linarith
    _ ≤ (2 * π / (1 + n * (b - a)) * (b - a)) * (B + K * (b - a) / 2) := by
      gcongr
      rw [mul_comm, ← mul_div_assoc, div_le_div_iff (by simpa)]
      calc π * (1 + n * (b - a))
        _ ≤ π * (π + n * (b - a)) := by
          gcongr
          linarith [Real.two_le_pi]
        _ ≤ π * (n * (b - a) + n * (b - a)) := by
          gcongr
          rwa [← div_le_iff₀' (Int.cast_pos.mpr n_pos)]
        _ = (b - a) * (2 * π) * n := by ring
      exact add_pos zero_lt_one (mul_pos (Int.cast_pos.mpr n_pos) (gt_of_ge_of_gt h pi_div_n_pos))
    _ = 2 * π * (b - a) * (B + K * (b - a) / 2) * (1 + |n| * (b - a))⁻¹ := by
      rw [_root_.abs_of_nonneg n_pos.le]
      ring
