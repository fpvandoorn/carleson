import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/- This file formalizes section 11.4 (The proof of the van der Corput Lemma) from the paper. -/

noncomputable section

open scoped Real NNReal
open Complex MeasureTheory Set Bornology

lemma ContinuousOn.intervalIntegrable_Ioo_of_bound
    {a b : ℝ} {C : ℝ} {f : ℝ → ℂ} (hf : ContinuousOn f (Ioo a b))
    (hab : a ≤ b) (h'f : ∀ x ∈ Ioo a b, ‖f x‖ ≤ C) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  refine ⟨hf.aestronglyMeasurable measurableSet_Ioo, ?_⟩
  apply hasFiniteIntegral_restrict_of_bounded (by simp) (C := C)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] using h'f

lemma intervalIntegrable_continuous_mul_lipschitzOnWith
    {a b : ℝ} {K : ℝ≥0} {f g : ℝ → ℂ} (hab : a ≤ b) (hf : Continuous f)
    (hg : LipschitzOnWith K g (Set.Ioo a b)) :
    IntervalIntegrable (fun x ↦ f x * g x) volume a b := by
  rcases hab.eq_or_lt with rfl | h'ab
  · simp
  obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ f '' (Icc a b), ‖x‖ ≤ C :=
    IsBounded.exists_norm_le (isCompact_Icc.image_of_continuousOn hf.continuousOn).isBounded
  obtain ⟨D, hD⟩ : ∃ D, ∀ x ∈ Ioo a b, ‖g x‖ ≤ D := by
    let x₀ := (a + b) / 2
    have h₀ : x₀ ∈ Ioo a b := by simp only [x₀]; exact ⟨by linarith, by linarith⟩
    refine ⟨‖g x₀‖ + K * ((b - a) / 2), fun y hy ↦ ?_⟩
    calc ‖g y‖ = ‖g x₀ + (g y - g x₀)‖ := by congr; abel
    _ ≤ ‖g x₀‖ + ‖g y - g x₀‖ := norm_add_le _ _
    _ ≤ ‖g x₀‖ + K * ‖y - x₀‖ := by gcongr; apply hg.norm_sub_le hy h₀
    _ ≤ ‖g x₀‖ + K * ((b - a) / 2) := by
      gcongr
      rw [Real.Ioo_eq_ball] at hy
      simp only [Metric.mem_ball, dist_eq_norm] at hy
      exact hy.le
  apply (hf.continuousOn.mul hg.continuousOn).intervalIntegrable_Ioo_of_bound hab
    (C := C * D) (fun x hx ↦ ?_)
  rw [norm_mul, mul_comm, mul_comm C]
  gcongr
  · apply (norm_nonneg _).trans (hD x hx)
  · apply hD x hx
  · apply hC
    apply mem_image_of_mem
    exact Ioo_subset_Icc_self hx

lemma van_der_Corput {a b : ℝ} (hab : a ≤ b) {n : ℤ} {ϕ : ℝ → ℂ} {B K : ℝ≥0}
    (h1 : LipschitzOnWith K ϕ (Ioo a b)) (h2 : ∀ x ∈ Ioo a b, ‖ϕ x‖ ≤ B) :
    ‖∫ x in a..b, exp (I * n * x) * ϕ x‖ ≤
     2 * π * (b - a) * (B + K * (b - a) / 2) * (1 + |n| * (b - a))⁻¹ := by
  have hK : 0 ≤ K * (b - a) / 2 := by
    apply mul_nonneg (mul_nonneg (by simp) (by linarith)) (by norm_num)
  by_cases n_nonzero : n = 0
  · rw [n_nonzero]
    simp only [Int.cast_zero, mul_zero, zero_mul, exp_zero, one_mul, abs_zero,
      add_zero, inv_one, mul_one]
    calc ‖∫ x in a..b, ϕ x‖
      _ = ‖∫ x in Set.Ioo a b, ϕ x‖ := by
        rw [intervalIntegral.integral_of_le, ← integral_Ioc_eq_integral_Ioo]
        linarith
      _ ≤ B * (volume (Set.Ioo a b)).toReal := by
        apply norm_setIntegral_le_of_norm_le_const _
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
    calc ‖∫ x in a..b, cexp (I * ↑n * ↑x) * ϕ x‖
      _ = ‖(starRingEnd ℂ) (∫ x in a..b, cexp (I * ↑n * ↑x) * ϕ x)‖ :=
        (RCLike.norm_conj _).symm
      _ = ‖∫ x in a..b, cexp (I * ↑(-n) * ↑x) * ((starRingEnd ℂ) ∘ ϕ) x‖ := by
        rw [intervalIntegral.integral_of_le (by linarith), ← integral_conj,
          ← intervalIntegral.integral_of_le (by linarith)]
        congr
        ext x
        rw [map_mul, ← exp_conj]
        congr
        simp
        -- exact Or.inl (conj_ofReal _)
      _ ≤ 2 * π * (b - a) * (↑B + ↑K * (b - a) / 2) * (1 + ↑|-n| * (b - a))⁻¹ := by
        apply this
        · intro x hx y hy
          simp only [Function.comp_apply]
          rw [edist_eq_enorm_sub, ← map_sub, starRingEnd_apply,
            enorm_eq_nnnorm, nnnorm_star]
          apply h1 hx hy
        · intro x hx
          rw [Function.comp_apply, RCLike.norm_conj]
          exact h2 x hx
        · exact Int.neg_ne_zero.mpr n_nonzero
        · rw [Left.neg_pos_iff]; exact lt_of_le_of_ne n_pos n_nonzero
    rw [abs_neg]
  -- Case distinction such that splitting integrals in the second case works.
  by_cases h : b - a < π / n
  · have : 0 < 1 + ↑|n| * (b - a) := by
      apply add_pos_of_pos_of_nonneg zero_lt_one
      apply mul_nonneg (by simp) (by linarith)
    calc _
      _ = ‖∫ x in Set.Ioo a b, cexp (I * ↑n * ↑x) * ϕ x‖ := by
        rw [intervalIntegral.integral_of_le, ← integral_Ioc_eq_integral_Ioo]
        linarith
      _ ≤ B * (volume (Set.Ioo a b)).toReal := by
        apply norm_setIntegral_le_of_norm_le_const _
        · intro x hx
          rw_mod_cast [norm_mul, mul_assoc, mul_comm I, Complex.norm_exp_ofReal_mul_I, one_mul]
          exact h2 x hx
        · exact Real.volume_Ioo ▸ ENNReal.ofReal_lt_top
      _ = B * (b - a) := by rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
      _ = (1 + |n| * (b - a)) * (1 + |n| * (b - a))⁻¹ * (b - a) * B := by
        rw [mul_inv_cancel₀]
        · ring
        exact ne_of_gt this
      _ ≤ (π + π) * (1 + |n| * (b - a))⁻¹ * (b - a) * (B + K * (b - a) / 2) := by
        gcongr
        · apply mul_nonneg
          · apply mul_nonneg
            · linarith [Real.two_pi_pos]
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
  calc _
    _ = ‖∫ x in a..b, (1 / 2 * exp (I * n * x) - 1 / 2 * exp (I * ↑n * (↑x + ↑π / ↑n))) * ϕ x‖ := by
      congr
      ext x
      congr
      rw [mul_add, mul_assoc I n (π / n), mul_div_cancel₀ _ (by simpa), exp_add, mul_comm I π, exp_pi_mul_I]
      ring
    _ = ‖1 / 2 * ∫ x in a..b, cexp (I * ↑n * ↑x) * ϕ x - cexp (I * ↑n * (↑x + ↑π / ↑n)) * ϕ x‖ := by
      congr
      rw [← intervalIntegral.integral_const_mul]
      congr
      ext x
      ring
    _ = 1 / 2 * ‖(∫ x in a..b, exp (I * n * x) * ϕ x)
                      - (∫ x in a..b, exp (I * n * (x + π / n)) * ϕ x)‖ := by
      rw [norm_mul]
      congr
      · simp
      rw [← intervalIntegral.integral_sub]
      · exact intervalIntegrable_continuous_mul_lipschitzOnWith hab (by fun_prop) h1
      · exact intervalIntegrable_continuous_mul_lipschitzOnWith hab (by fun_prop) h1
    _ = 1 / 2 * ‖  (∫ x in a..(a + π / n), exp (I * n * x) * ϕ x)
                 + (∫ x in (a + π / n)..b, exp (I * n * x) * ϕ x)
                 -((∫ x in a..(b - π / n), exp (I * n * (x + π / n)) * ϕ x)
                 + (∫ x in (b - π / n)..b, exp (I * n * (x + π / n)) * ϕ x))‖ := by
      congr 3
      · rw [intervalIntegral.integral_add_adjacent_intervals]
        · exact intervalIntegrable_continuous_mul_lipschitzOnWith (by linarith) (by fun_prop)
            (h1.mono (Ioo_subset_Ioo le_rfl (by linarith)))
        · exact intervalIntegrable_continuous_mul_lipschitzOnWith (by linarith) (by fun_prop)
            (h1.mono (Ioo_subset_Ioo (by linarith) le_rfl))
      · rw [intervalIntegral.integral_add_adjacent_intervals]
        · exact intervalIntegrable_continuous_mul_lipschitzOnWith (by linarith) (by fun_prop)
            (h1.mono (Ioo_subset_Ioo le_rfl (by linarith)))
        · exact intervalIntegrable_continuous_mul_lipschitzOnWith (by linarith) (by fun_prop)
            (h1.mono (Ioo_subset_Ioo (by linarith) le_rfl))
    _ = 1 / 2 * ‖  (∫ x in a..(a + π / n), exp (I * n * x) * ϕ x)
                 + (∫ x in (a + π / n)..b, exp (I * n * x) * ϕ x)
                 -((∫ x in (a + π / n)..(b - π / n + π / n), exp (I * n * x) * ϕ (x - π / n))
                 + (∫ x in (b - π / n)..b, exp (I * n * (x + π / n)) * ϕ x))‖ := by
      congr 4
      rw [← intervalIntegral.integral_comp_add_right]
      simp
    _ = 1 / 2 * ‖  (∫ x in a..(a + π / n), exp (I * n * x) * ϕ x)
                 +((∫ x in (a + π / n)..b, exp (I * n * x) * ϕ x)
                 - (∫ x in (a + π / n)..b, exp (I * n * x) * ϕ (x - π / n)))
                 - (∫ x in (b - π / n)..b, exp (I * n * (x + π / n)) * ϕ x)‖ := by
      congr 2
      rw [sub_add_cancel]
      ring
    _ = 1 / 2 * ‖  (∫ x in a..(a + π / n), exp (I * n * x) * ϕ x)
                 + (∫ x in (a + π / n)..b, exp (I * n * x) * (ϕ x - ϕ (x - π / n)))
                 - (∫ x in (b - π / n)..b, exp (I * n * (x + π / n)) * ϕ x)‖ := by
      congr 4
      rw [← intervalIntegral.integral_sub]
      · congr
        ext x
        ring
      · exact intervalIntegrable_continuous_mul_lipschitzOnWith (by linarith) (by fun_prop)
          (h1.mono (Ioo_subset_Ioo (by linarith) le_rfl))
      · have : IntervalIntegrable (fun x ↦ cexp (I * ↑n * (x + π / n)) * ϕ x)
            volume a (b - π / n) := intervalIntegrable_continuous_mul_lipschitzOnWith
          (by linarith) (by fun_prop) (h1.mono (Ioo_subset_Ioo le_rfl (by linarith)))
        simpa using this.comp_sub_right (π / n)
    _ ≤ 1 / 2 * (  ‖(∫ x in a..(a + π / n), exp (I * n * x) * ϕ x)
                 +  (∫ x in (a + π / n)..b, exp (I * n * x) * (ϕ x - ϕ (x - π / n)))‖
                 + ‖∫ x in (b - π / n)..b, exp (I * n * (x + π / n)) * ϕ x‖) := by
      gcongr
      exact norm_sub_le ..
    _ ≤ 1 / 2 * (  ‖(∫ x in a..(a + π / n), exp (I * n * x) * ϕ x)‖
                 + ‖(∫ x in (a + π / n)..b, exp (I * n * x) * (ϕ x - ϕ (x - π / n)))‖
                 + ‖∫ x in (b - π / n)..b, exp (I * n * (x + π / n)) * ϕ x‖) := by
      gcongr
      exact norm_add_le ..
    _ = 1 / 2 * (  ‖∫ x in Ioo a (a + π / n), exp (I * n * x) * ϕ x‖
                 + ‖∫ x in Ioo (a + π / n) b, exp (I * n * x) * (ϕ x - ϕ (x - π / n))‖
                 + ‖∫ x in Ioo (b - π / n) b, exp (I * n * (x + π / n)) * ϕ x‖) := by
      congr
      all_goals
        rw [intervalIntegral.integral_of_le, ← integral_Ioc_eq_integral_Ioo]
        linarith
    _ ≤ 1 / 2 * (  B * (volume (Set.Ioo a (a + π / n))).toReal
                 + (K * π / n) * (volume (Set.Ioo (a + π / n) b)).toReal
                 + B * (volume (Set.Ioo (b - π / n) b)).toReal) := by
      gcongr
      · apply norm_setIntegral_le_of_norm_le_const _
        · intro x hx
          rw [norm_mul, mul_assoc, mul_comm I]
          rw_mod_cast [Complex.norm_exp_ofReal_mul_I, one_mul]
          apply h2
          constructor <;> linarith [hx.1, hx.2]
        · exact Real.volume_Ioo ▸ ENNReal.ofReal_lt_top
      · apply norm_setIntegral_le_of_norm_le_const _
        · intro x hx
          rw [norm_mul, mul_assoc, mul_comm I]
          rw_mod_cast [Complex.norm_exp_ofReal_mul_I, one_mul, ← dist_eq_norm]
          apply le_trans (h1.dist_le_mul ..)
          · simp only [dist_self_sub_right, norm_div, Real.norm_eq_abs]
            rw [_root_.abs_of_nonneg Real.pi_pos.le, _root_.abs_of_nonneg
              (by simp only [Int.cast_nonneg]; linarith [n_pos])]
            apply le_of_eq
            ring
          · exact ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
          · exact ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
        · exact Real.volume_Ioo ▸ ENNReal.ofReal_lt_top
      · apply norm_setIntegral_le_of_norm_le_const _
        · intro x hx
          rw [norm_mul, mul_assoc, mul_comm I]
          rw_mod_cast [Complex.norm_exp_ofReal_mul_I, one_mul]
          apply h2
          constructor <;> linarith [hx.1, hx.2]
        · exact Real.volume_Ioo ▸ ENNReal.ofReal_lt_top
    _ = π / n * (B + K * (b - (a + π / n)) / 2) := by
      rw [Real.volume_Ioo, Real.volume_Ioo, Real.volume_Ioo, ENNReal.toReal_ofReal,
        ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
      · ring
      all_goals linarith
    _ ≤ π / n * (B + K * (b - a) / 2) := by
      gcongr
      linarith
    _ ≤ (2 * π / (1 + n * (b - a)) * (b - a)) * (B + K * (b - a) / 2) := by
      gcongr
      rw [mul_comm, ← mul_div_assoc, div_le_div_iff₀ (by simpa)]
      · calc π * (1 + n * (b - a))
          _ ≤ π * (π + n * (b - a)) := by
            gcongr
            linarith [Real.two_le_pi]
          _ ≤ π * (n * (b - a) + n * (b - a)) := by
            gcongr
            rwa [← div_le_iff₀' (Int.cast_pos.mpr n_pos)]
          _ = (b - a) * (2 * π) * n := by ring
      · exact add_pos zero_lt_one (mul_pos (Int.cast_pos.mpr n_pos) (lt_of_lt_of_le pi_div_n_pos h))
    _ = 2 * π * (b - a) * (B + K * (b - a) / 2) * (1 + |n| * (b - a))⁻¹ := by
      rw [_root_.abs_of_nonneg n_pos.le]
      ring
