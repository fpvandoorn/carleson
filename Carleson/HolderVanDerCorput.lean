import Carleson.TileStructure

/-! This should roughly contain the contents of chapter 8. -/

open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G]

noncomputable section

open Set MeasureTheory Metric Function Complex Bornology TileStructure
open scoped NNReal ENNReal ComplexConjugate

/-- `cutoff R t x y` is `L(x, y)` in the proof of Lemma 8.0.1. -/
def cutoff (R t : ℝ) (x y : X) : ℝ :=
  max 0 (1 - dist x y / (t * R))

variable {R t : ℝ} {x y : X}

lemma cutoff_nonneg : 0 ≤ cutoff R t x y := by simp [cutoff]

lemma cutoff_comm : cutoff R t x y = cutoff R t y x := by
  unfold cutoff
  simp_rw [dist_comm x y]

lemma cutoff_Lipschitz (hR : 0 < R) (ht : 0 < t) :
    LipschitzWith ⟨(1 / (t * R)), by positivity⟩ (fun y ↦ cutoff R t x y) := by
  apply LipschitzWith.const_max
  apply LipschitzWith.of_le_add_mul
  intro a b
  simp only [one_div, NNReal.coe_mk, tsub_le_iff_right, div_eq_inv_mul, mul_one]
  have : (t * R) ⁻¹ * dist x b ≤ (t * R)⁻¹ * (dist x a + dist a b) := by
    gcongr
    exact dist_triangle _ _ _
  linarith

@[fun_prop]
lemma cutoff_continuous (hR : 0 < R) (ht : 0 < t) : Continuous (fun y ↦ cutoff R t x y) :=
  (cutoff_Lipschitz hR ht (X := X)).continuous

/-- `cutoff R t x` is measurable in `y`. -/
@[fun_prop]
lemma cutoff_measurable (hR : 0 < R) (ht : 0 < t) : Measurable (fun y ↦ cutoff R t x y) :=
  (cutoff_continuous hR ht).measurable

lemma hasCompactSupport_cutoff [ProperSpace X] (hR : 0 < R) (ht : 0 < t) {x : X} :
    HasCompactSupport (fun y ↦ cutoff R t x y) := by
  apply HasCompactSupport.intro (isCompact_closedBall x (t * R))
  intro y hy
  simp only [mem_closedBall, dist_comm, not_le] at hy
  simp only [cutoff, sup_eq_left, tsub_le_iff_right, zero_add]
  rw [one_le_div (by positivity)]
  exact hy.le

lemma integrable_cutoff (hR : 0 < R) (ht : 0 < t) {x : X} :
    Integrable (fun y ↦ cutoff R t x y) :=
  (cutoff_continuous hR ht).integrable_of_hasCompactSupport
    (hasCompactSupport_cutoff hR ht)

-- Is this useful for mathlib? neither exact? nor aesop can prove this. Same for the next lemma.
lemma leq_of_max_neq_left {a b : ℝ} (h : max a b ≠ a) : a < b := by
  by_contra! h'
  exact h (max_eq_left h')

lemma leq_of_max_neq_right {a b : ℝ} (h : max a b ≠ b) : b < a := by
  by_contra! h'
  exact h (max_eq_right h')

/-- Equation 8.0.4 from the blueprint -/
lemma aux_8_0_4 (hR : 0 < R) (ht : 0 < t) (h : cutoff R t x y ≠ 0) : y ∈ ball x (t * R) := by
  rw [mem_ball']
  have : 0 < 1 - dist x y / (t * R) := by
    apply leq_of_max_neq_left
    rwa [cutoff] at h
  exact (div_lt_one (by positivity)).mp (by linarith)

lemma aux_8_0_5 (hR : 0 < R) (ht : 0 < t) (h : y ∈ ball x (2⁻¹ * t * R)) :
    2⁻¹ ≤ cutoff R t x y := by
  rw [mem_ball', mul_assoc] at h
  have : dist x y / (t * R) < 2⁻¹ := (div_lt_iff₀ (by positivity)).mpr h
  calc 2 ⁻¹
    _ ≤ 1 - dist x y / (t * R) := by
      norm_num at *; linarith only [h, this]
    _ ≤ cutoff R t x y := le_max_right _ _

lemma aux_8_0_6 (hR : 0 < R) (ht : 0 < t) :
    2⁻¹ * volume.real (ball x (2⁻¹ * t * R)) ≤ ∫ y, cutoff R t x y := by
  calc 2 ⁻¹ * volume.real (ball x (2⁻¹ * t * R))
    _ = ∫ y in ball x (2⁻¹ * t * R), 2⁻¹ := by
      rw [setIntegral_const, mul_comm]
      rfl
    _ ≤ ∫ y in (ball x (2⁻¹ * t * R)), cutoff R t x y := by
      apply setIntegral_mono_on
      · apply integrableOn_const.2
        right
        exact measure_ball_lt_top
      · apply (integrable_cutoff hR ht).integrableOn
      · exact measurableSet_ball
      · intro y' hy'
        exact aux_8_0_5 hy' (hR := hR) (ht := ht)
    _ ≤ ∫ y, cutoff R t x y := by
      apply setIntegral_le_integral (integrable_cutoff hR ht)
      filter_upwards with x using (by simp [cutoff])

/-- The smallest integer `n` so that `2^n t ≥ 1`. -/
-- i.e., the real logarithm log₂ 1/t, rounded *up* to the nearest integer
private def n_8_0_7 (t : ℝ) : ℤ := Int.log 2 (1 / t) + 1

private lemma n_spec1 (ht : 0 < t) : 1 < 2 ^ (n_8_0_7 t) * t := calc
  1 = (1 / t) * t := by
    norm_num
    rw [mul_comm]
    exact (mul_inv_cancel₀ ht.ne').symm
  _ < 2 ^ (n_8_0_7 t) * t := by
    gcongr
    exact Int.lt_zpow_succ_log_self (by norm_num) (1 / t)

-- This lemma is probably not needed.
-- private lemma n_spec2 : ∀ n' < n_8_0_7 t, 2 ^ n' * t < 1 := sorry

/-- The constant occurring in Lemma 8.0.1. -/
def C8_0_1 (a : ℝ) (t : ℝ≥0) : ℝ≥0 := ⟨2 ^ (4 * a) * t ^ (- (a + 1)), by positivity⟩

/-- `ϕ ↦ \tilde{ϕ}` in the proof of Lemma 8.0.1. -/
def holderApprox (R t : ℝ) (ϕ : X → ℂ) (x : X) : ℂ :=
  (∫ y, cutoff R t x y * ϕ y) / (∫ y, cutoff R t x y)

-- This surely exists in mathlib; how is it named?
lemma foo {φ : X → ℂ} (hf : ∫ x, φ x ≠ 0) : ∃ z, φ z ≠ 0 := by
  by_contra! h
  exact hf (by simp [h])

/-- Part of Lemma 8.0.1. -/
lemma support_holderApprox_subset {z : X} {R t : ℝ} (hR : 0 < R)
    (ϕ : X → ℂ) (hϕ : ϕ.support ⊆ ball z R) (ht : t ∈ Ioc (0 : ℝ) 1) :
    support (holderApprox R t ϕ) ⊆ ball z (2 * R) := by
  intro x hx
  choose y hy using foo (left_ne_zero_of_mul hx)
  have : x ∈ ball y (t * R) := by
    apply aux_8_0_4 hR ht.1
    rw [cutoff_comm]
    simpa using left_ne_zero_of_mul hy
  have h : x ∈ ball y R := by
    refine Set.mem_of_mem_of_subset this ?_
    nth_rw 2 [← one_mul R]
    gcongr
    exact ht.2
  calc dist x z
    _ ≤ dist x y + dist y z := dist_triangle x y z
    _ < R + R := add_lt_add h (hϕ (right_ne_zero_of_mul hy))
    _ = 2 * R := by ring

-- XXX: inlining this does not work
lemma foobar (f : X → ℝ) : ∫ x, (f x : ℂ) = ((∫ x, f x : ℝ) : ℂ) := integral_ofReal

open Filter

/-- Part of Lemma 8.0.1. -/
lemma dist_holderApprox_le {z : X} {R t : ℝ} (hR : 0 < R) {C : ℝ≥0}
    (ϕ : X → ℂ) (hϕ : ϕ.support ⊆ ball z R)
    (h2ϕ : HolderWith C nnτ ϕ) (hτ : 0 < nnτ) (ht : t ∈ Ioc (0 : ℝ) 1) (x : X) :
    dist (ϕ x) (holderApprox R t ϕ x) ≤ (t * R) ^ τ * C := by
  have ht0 : 0 < t := ht.1
  have P : 0 < ∫ y, cutoff R t x y := by
    apply lt_of_lt_of_le _ (aux_8_0_6 hR ht.1)
    apply mul_pos (by positivity)
    apply measure_real_ball_pos
    positivity
  have : (∫ y, cutoff R t x y * ϕ x) / (∫ y, (cutoff R t x y : ℂ)) = ϕ x := by
    rw [integral_mul_right, mul_div_cancel_left₀]
    simpa only [ne_eq, ofReal_eq_zero, foobar] using P.ne'
  rw [dist_eq_norm, ← this, holderApprox, foobar, ← sub_div, ← integral_sub]; rotate_left
  · apply (integrable_cutoff hR ht0).ofReal.mul_const
  · apply Continuous.integrable_of_hasCompactSupport
    · apply Continuous.mul
      · have := cutoff_continuous hR ht0 (x := x)
        fun_prop
      · exact h2ϕ.continuous hτ
    · apply HasCompactSupport.mul_left
      apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall z R)
      apply hϕ.trans ball_subset_closedBall
  rw [norm_div, norm_real, div_le_iff₀]; swap
  · exact P.trans_le (le_abs_self _)
  calc
    ‖∫ y, cutoff R t x y * ϕ x - cutoff R t x y * ϕ y‖
  _ = ‖∫ y, cutoff R t x y * (ϕ x - ϕ y)‖ := by simp only [mul_sub]
  _ ≤ ∫ y, ‖cutoff R t x y * (ϕ x - ϕ y)‖ := norm_integral_le_integral_norm _
  _ ≤ ∫ y, cutoff R t x y * (C * (t * R) ^ τ) := by
    apply integral_mono_of_nonneg
    · filter_upwards with y using (by positivity)
    · apply (integrable_cutoff hR ht0).mul_const
    filter_upwards with y
    rcases le_total (dist x y) (t * R) with hy | hy
    -- Case 1: |x - y| ≤ t * R, then cutoff is non-negative.
    · simp only [norm_mul, norm_real, Real.norm_eq_abs, norm_eq_abs, defaultτ, abs_ofReal,
        _root_.abs_of_nonneg cutoff_nonneg]
      gcongr
      · exact cutoff_nonneg
      rw [← Complex.norm_eq_abs, ← dist_eq_norm]
      exact h2ϕ.dist_le_of_le hy
    -- Case 2: |x - y| > t * R, and cutoff is zero.
    · have : cutoff R t x y = 0 := by
        simp only [cutoff, sup_eq_left, tsub_le_iff_right, zero_add]
        rwa [one_le_div₀ (by positivity)]
      simp [this]
  _ = (t * R) ^τ * C * ∫ y, cutoff R t x y := by
    rw [integral_mul_right]
    ring
  _ ≤ (t * R) ^ τ * C * ‖∫ (x_1 : X), cutoff R t x x_1‖ := by
    gcongr
    exact Real.le_norm_self _

/-- Part of Lemma 8.0.1. -/
lemma lipschitzWith_holderApprox {z : X} {R t : ℝ} (hR : 0 < R) {C : ℝ≥0}
    (ϕ : X → ℂ) (hϕ : ϕ.support ⊆ ball z R)
    (h2ϕ : HolderWith C nnτ ϕ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    LipschitzWith (C8_0_1 a ⟨t, ht.1.le⟩) (holderApprox R t ϕ) := by
  -- equation 8.0.14, corrected
  have (x : X) : ‖∫ y, cutoff R t x y‖ * ‖holderApprox R t ϕ x‖
      = ‖∫ y, cutoff R t x y * ϕ y‖ := by
    --simp
    --rw [norm_eq_abs] -- second term is complex.abs, not the real norm... need to equate
    --simp_rw [norm_mul]
    sorry
  -- equation 8.0.15
  have (x : X) : ‖∫ y, cutoff R t x y‖ * ‖holderApprox R t ϕ x‖
      ≤ ‖∫ y, cutoff R t x y‖ * ⨆ x' : X, ‖ϕ x'‖ := by
    simp_rw [this, integral_mul_right, norm_mul]
    gcongr
    norm_cast
    simp_rw [integral_ofReal]
    simp_rw [← foobar]
    simp
    simp_rw [norm_eq_abs]
    simp_rw [← norm_mul]
    gcongr
    set F := fun (x'' : X) ↦ ‖holderApprox R t ϕ x''‖
    sorry -- apply le_iSup F x
  -- part 1 of 8.0.16
  have (x : X) : ‖holderApprox R t ϕ x‖ ≤ ⨆ x' : X, ‖holderApprox R t ϕ x'‖ := sorry -- proven above
  -- part 2 of 8.0.16
  sorry


/-- The constant occurring in Proposition 2.0.5. -/
def C2_0_5 (a : ℝ) : ℝ≥0 := 2 ^ (8 * a)

/-- Proposition 2.0.5. -/
theorem holder_van_der_corput {z : X} {R : ℝ≥0} (hR : 0 < R) {ϕ : X → ℂ}
    (hϕ : support ϕ ⊆ ball z R) (h2ϕ : hnorm (a := a) ϕ z R < ∞) {f g : Θ X} :
    ‖∫ x, exp (I * (f x - g x)) * ϕ x‖₊ ≤
    (C2_0_5 a : ℝ≥0∞) * volume (ball z R) * hnorm (a := a) ϕ z R *
    (1 + nndist_{z, R} f g) ^ (2 * a^2 + a^3 : ℝ)⁻¹ := sorry
