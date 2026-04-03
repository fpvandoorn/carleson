import Carleson.TileStructure
import Carleson.HolderNorm

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
  simp only [NNReal.coe_mk, tsub_le_iff_right, div_eq_inv_mul, mul_one]
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

lemma cutoff_eq_zero (hR : 0 < R) (ht : 0 < t) {x y : X} (hy : y ∉ ball x (t * R)) :
    cutoff R t x y = 0 := by
  simp only [mem_ball, dist_comm, not_lt] at hy
  simp only [cutoff, sup_eq_left, tsub_le_iff_right, zero_add]
  rwa [one_le_div (by positivity)]

lemma hasCompactSupport_cutoff [ProperSpace X] (hR : 0 < R) (ht : 0 < t) {x : X} :
    HasCompactSupport (fun y ↦ cutoff R t x y) := by
  apply HasCompactSupport.intro (isCompact_closedBall x (t * R))
  intro y hy
  apply cutoff_eq_zero hR ht
  contrapose! hy
  exact ball_subset_closedBall hy

lemma integrable_cutoff (hR : 0 < R) (ht : 0 < t) {x : X} :
    Integrable (fun y ↦ cutoff R t x y) :=
  (cutoff_continuous hR ht).integrable_of_hasCompactSupport
    (hasCompactSupport_cutoff hR ht)

lemma integrable_cutoff_mul {z : X} (hR : 0 < R) (ht : 0 < t) {x : X} {φ : X → ℂ}
    (hc : Continuous φ) (hφ : φ.support ⊆ ball z R) :
    Integrable (fun y ↦ cutoff R t x y * φ y) := by
  apply Continuous.integrable_of_hasCompactSupport
  · apply Continuous.mul
    · have := cutoff_continuous hR ht (x := x)
      fun_prop
    · exact hc
  · apply HasCompactSupport.mul_left
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall z R)
    apply hφ.trans ball_subset_closedBall

-- Is this useful for mathlib? neither exact? nor aesop can prove this. Same for the next lemma.
lemma leq_of_max_neq_left {a b : ℝ} (h : max a b ≠ a) : a < b := by
  by_contra! h'
  exact h (max_eq_left h')

lemma leq_of_max_neq_right {a b : ℝ} (h : max a b ≠ b) : b < a := by
  by_contra! h'
  exact h (max_eq_right h')

/-- Equation 8.0.4 from the blueprint -/
lemma aux_8_0_4 (hR : 0 < R) (ht : 0 < t) (h : cutoff R t x y ≠ 0) : y ∈ ball x (t * R) := by
  contrapose! h
  exact cutoff_eq_zero hR ht h

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
      · exact integrableOn_const (by finiteness)
      · exact (integrable_cutoff hR ht).integrableOn
      · exact measurableSet_ball
      · intro y' hy'
        exact aux_8_0_5 hy' (hR := hR) (ht := ht)
    _ ≤ ∫ y, cutoff R t x y := by
      apply setIntegral_le_integral (integrable_cutoff hR ht)
      filter_upwards with x using (by simp [cutoff])

lemma integral_cutoff_pos {R t : ℝ} (hR : 0 < R) (ht : 0 < t) : 0 < ∫ y, cutoff R t x y := by
  apply lt_of_lt_of_le _ (aux_8_0_6 hR ht)
  apply mul_pos (by positivity)
  exact measureReal_ball_pos _ (by positivity)

/-- The constant occurring in Lemma 8.0.1. -/
def C8_0_1 (a : ℝ) (t : ℝ≥0) : ℝ≥0 := ⟨2 ^ (4 * a) * t ^ (- (a + 1)), by positivity⟩

/-- `φ ↦ \tilde{φ}` in the proof of Lemma 8.0.1. -/
def holderApprox (R t : ℝ) (φ : X → ℂ) (x : X) : ℂ :=
  (∫ y, cutoff R t x y * φ y) / (∫ y, cutoff R t x y)

lemma integral_mul_holderApprox {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (φ : X → ℂ) :
    (∫ y, cutoff R t x y) * holderApprox R t φ x = ∫ y, cutoff R t x y * φ y := by
  rw [holderApprox, mul_div_cancel₀]
  simp only [ne_eq, ofReal_eq_zero]
  apply ne_of_gt
  exact integral_cutoff_pos hR ht

lemma support_holderApprox_subset_aux {z : X} {R R' t : ℝ} (hR : 0 < R)
    {φ : X → ℂ} (hφ : φ.support ⊆ ball z R') (ht : t ∈ Ioc (0 : ℝ) 1) :
    support (holderApprox R t φ) ⊆ ball z (R + R') := by
  intro x hx
  have : ∃ z, cutoff R t x z * φ z ≠ 0 := by
    suffices ∫ y, cutoff R t x y * φ y ≠ 0 by
      by_contra! h
      exact this (by simp only [h, integral_zero])
    apply left_ne_zero_of_mul hx
  choose y hy using this
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
    _ < R + R' := add_lt_add h (hφ (right_ne_zero_of_mul hy))

/-- Part of Lemma 8.0.1. -/
lemma support_holderApprox_subset {z : X} {R t : ℝ} (hR : 0 < R)
    {φ : X → ℂ} (hφ : φ.support ⊆ ball z R) (ht : t ∈ Ioc (0 : ℝ) 1) :
    support (holderApprox R t φ) ⊆ ball z (2 * R) := by
  convert support_holderApprox_subset_aux hR hφ ht using 2
  ring

open Filter

/-- Part of Lemma 8.0.1: Equation (8.0.1).
Note that the norm `||φ||_C^τ` is normalized by definition, i.e., on the ball `B (z, 2 * R)`,
it is `(2 * R) ^ τ` times the best Hölder constant of `φ`, so the Lean statement corresponds to the
blueprint statement.
-/
lemma dist_holderApprox_le {z : X} {R t : ℝ} (hR : 0 < R) {C : ℝ≥0} (ht : 0 < t) (h't : t ≤ 1)
    {φ : X → ℂ} (hφ : support φ ⊆ ball z R) (h2φ : HolderOnWith C nnτ φ (ball z (2 * R))) (x : X) :
    dist (φ x) (holderApprox R t φ x) ≤ (t/2) ^ τ * ((2 * R) ^ τ * C) := by
  have φ_cont : Continuous φ := by
    apply ContinuousOn.continuous_of_tsupport_subset (h2φ.continuousOn (nnτ_pos X)) isOpen_ball
    apply (closure_mono hφ).trans (closure_ball_subset_closedBall.trans ?_)
    exact closedBall_subset_ball (by linarith)
  have : (∫ y, cutoff R t x y * φ x) / (∫ y, (cutoff R t x y : ℂ)) = φ x := by
    rw [
      show ∫ y, (cutoff R t x y : ℂ) * φ x = (∫ y, (cutoff R t x y : ℂ)) * φ x from integral_mul_const (φ x) _,
      mul_div_cancel_left₀
    ]
    simpa only [ne_eq, ofReal_eq_zero, integral_complex_ofReal] using (integral_cutoff_pos hR ht).ne'
  rw [dist_eq_norm, ← this, holderApprox, integral_complex_ofReal, ← sub_div,
    ← integral_sub]; rotate_left
  · apply (integrable_cutoff hR ht).ofReal.mul_const
  · apply integrable_cutoff_mul hR ht φ_cont hφ
  rw [norm_div, norm_real, div_le_iff₀]; swap
  · exact ((integral_cutoff_pos hR ht)).trans_le (le_abs_self _)
  calc
    ‖∫ y, cutoff R t x y * φ x - cutoff R t x y * φ y‖
  _ = ‖∫ y, cutoff R t x y * (φ x - φ y)‖ := by simp only [mul_sub]
  _ ≤ ∫ y, ‖cutoff R t x y * (φ x - φ y)‖ := norm_integral_le_integral_norm _
  _ ≤ ∫ y, cutoff R t x y * (C * (t * R) ^ τ) := by
    apply integral_mono_of_nonneg
    · filter_upwards with y using (by positivity)
    · apply (integrable_cutoff hR ht).mul_const
    filter_upwards with y
    rcases le_total (dist x y) (t * R) with hxy | hxy
    -- Case 1: |x - y| ≤ t * R, then cutoff is non-negative.
    · simp only [norm_mul, norm_real, Real.norm_eq_abs, defaultτ, norm_real,
        _root_.abs_of_nonneg cutoff_nonneg]
      gcongr
      · exact cutoff_nonneg
      rcases le_or_gt (2 * R) (dist x z) with hx | hx
      · have : dist x y ≤ R := by nlinarith
        have : dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
        have xm : x ∉ support φ := fun h ↦ by linarith [mem_ball.1 (hφ h)]
        have ym : y ∉ support φ := fun h ↦ by linarith [mem_ball.1 (hφ h)]
        simp only [notMem_support.mp xm, notMem_support.mp ym, sub_self, norm_zero, ge_iff_le]
        positivity
      rcases le_or_gt (2 * R) (dist y z) with hy | hy
      · have : dist x y ≤ R := by nlinarith
        have : dist y z ≤ dist x y + dist x z := dist_triangle_left y z x
        have xm : x ∉ support φ := fun h ↦ by linarith [mem_ball.1 (hφ h)]
        have ym : y ∉ support φ := fun h ↦ by linarith [mem_ball.1 (hφ h)]
        simp only [notMem_support.mp xm, notMem_support.mp ym, sub_self, norm_zero, ge_iff_le]
        positivity
      rw [← dist_eq_norm]
      apply h2φ.dist_le_of_le hx hy hxy
    -- Case 2: |x - y| > t * R, and cutoff is zero.
    · have : cutoff R t x y = 0 := by
        simp only [cutoff, sup_eq_left, tsub_le_iff_right, zero_add]
        rwa [one_le_div₀ (by positivity)]
      simp [this]
  _ = ((t / 2) * (2 * R)) ^τ * C * ∫ y, cutoff R t x y := by
    rw [integral_mul_const, show (t / 2) * (2 * R) = t * R by ring]
    ring
  _ ≤ ((t / 2) * (2 * R)) ^ τ * C * ‖∫ (x_1 : X), cutoff R t x x_1‖ := by
    gcongr
    exact Real.le_norm_self _
  _ = (t / 2) ^ τ * ((2 * R) ^ τ * C) * ‖∫ (x_1 : X), cutoff R t x x_1‖ := by
    rw [Real.mul_rpow]
    · ring
    · positivity
    · positivity

lemma enorm_holderApprox_sub_le {z : X} {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (h't : t ≤ 1)
    {φ : X → ℂ} (hφ : support φ ⊆ ball z R) (x : X) :
    ‖φ x - holderApprox R t φ x‖ₑ ≤ ENNReal.ofReal (t/2) ^ τ * iHolENorm φ z (2 * R) τ := by
  rcases eq_or_ne (iHolENorm φ z (2 * R) τ) ∞ with h | h
  · apply le_top.trans_eq
    symm
    simp only [defaultτ] at h
    simp [h, ENNReal.mul_eq_top, ht]
  have : iHolENorm φ z (2 * R) τ = ENNReal.ofReal (iHolNNNorm φ z (2 * R) τ) := by
    simp only [iHolNNNorm, ENNReal.ofReal_coe_nnreal, ENNReal.coe_toNNReal h]
  rw [ENNReal.ofReal_rpow_of_pos (by linarith), this, ← ENNReal.ofReal_mul (by positivity),
    ← ofReal_norm_eq_enorm, ← dist_eq_norm]
  apply ENNReal.ofReal_le_ofReal
  apply dist_holderApprox_le hR ht h't hφ
    (by simpa [nnτ_def] using HolderOnWith.of_iHolENorm_ne_top (τ_nonneg X) h) x |>.trans_eq
  simp [field, NNReal.coe_div, hR.le]


/-- Part of Lemma 8.0.1: sup norm control in Equation (8.0.2). Note that it only uses the sup
norm of `φ`, no need for a Hölder control. -/
lemma holderApprox_le {R t : ℝ} (hR : 0 < R) {C : ℝ≥0} (ht : 0 < t)
    {φ : X → ℂ} (hC : ∀ x, ‖φ x‖ ≤ C) (x : X) :
    ‖holderApprox R t φ x‖ ≤ C := by
  rw [holderApprox, norm_div, norm_real, Real.norm_eq_abs]
  apply div_le_of_le_mul₀ (by positivity) (by positivity)
  apply (norm_integral_le_integral_norm _).trans
  rw [abs_of_pos (integral_cutoff_pos hR ht), ← integral_const_mul]
  apply integral_mono_of_nonneg
  · apply Eventually.of_forall (fun x ↦ by positivity)
  · apply (integrable_cutoff hR ht).const_mul
  apply Eventually.of_forall (fun y ↦ ?_)
  simp only [Complex.norm_mul, norm_real, Real.norm_eq_abs, cutoff_nonneg, abs_of_nonneg,
    mul_comm (C : ℝ)]
  gcongr
  · apply cutoff_nonneg
  · exact hC y

/-- Auxiliary lemma: part of the Lipschitz control in Equation (8.0.2), when the distance between
the points is at most `R`. -/
lemma norm_holderApprox_sub_le_aux {z : X} {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (h't : t ≤ 1)
    {C : ℝ≥0} {φ : X → ℂ} (hc : Continuous φ) (hφ : φ.support ⊆ ball z R)
    (hC : ∀ x, ‖φ x‖ ≤ C) {x x' : X} (h : dist x x' < R) :
    ‖holderApprox R t φ x' - holderApprox R t φ x‖ ≤
      2⁻¹ * 2 ^ (4 * a) * t ^ (-1 - a : ℝ) * C * dist x x' / (2 * R) := by
  have M : (2⁻¹ * volume.real (ball x (2⁻¹ * t * R))) *
        ‖holderApprox R t φ x' - holderApprox R t φ x‖ ≤
        2 * C * ∫ y, |cutoff R t x y - cutoff R t x' y| :=
    calc
      (2⁻¹ * volume.real (ball x (2⁻¹ * t * R))) * ‖holderApprox R t φ x' - holderApprox R t φ x‖
    _ ≤ (∫ y, cutoff R t x y) * ‖holderApprox R t φ x' - holderApprox R t φ x‖ := by
      gcongr
      apply aux_8_0_6 hR ht
    _ = ‖(∫ y, cutoff R t x y) * (holderApprox R t φ x' - holderApprox R t φ x)‖ := by
      rw [norm_mul, norm_real, Real.norm_eq_abs,
        abs_of_pos (integral_cutoff_pos hR ht)]
    _ = ‖((∫ y, cutoff R t x y)  - (∫ y, cutoff R t x' y)) * holderApprox R t φ x'
          + ((∫ y, cutoff R t x' y) * holderApprox R t φ x'
          - (∫ y, cutoff R t x y) * holderApprox R t φ x)‖ := by congr 1; ring
    _ ≤ ‖(∫ y, cutoff R t x y - cutoff R t x' y) * holderApprox R t φ x'‖
        + ‖(∫ y, cutoff R t x' y) * holderApprox R t φ x'
          - (∫ y, cutoff R t x y) * holderApprox R t φ x‖ := by
      rw [integral_sub (integrable_cutoff hR ht) (integrable_cutoff hR ht), ofReal_sub]
      exact norm_add_le _ _
    _ = ‖∫ y, cutoff R t x y - cutoff R t x' y‖ * ‖holderApprox R t φ x'‖ +
          ‖(∫ y, cutoff R t x' y * φ y) - (∫ y, cutoff R t x y * φ y)‖ := by
      simp [integral_mul_holderApprox hR ht]
    _ ≤ (∫ y, ‖cutoff R t x y - cutoff R t x' y‖) * C +
          ‖(∫ y, (cutoff R t x' y - cutoff R t x y) * φ y)‖ := by
      gcongr
      · apply norm_integral_le_integral_norm
      · apply holderApprox_le hR ht hC
      · apply le_of_eq
        rw [← integral_sub]
        · simp [sub_mul]
        · apply integrable_cutoff_mul hR ht hc hφ
        · apply integrable_cutoff_mul hR ht hc hφ
    _ ≤ (∫ y, ‖cutoff R t x y - cutoff R t x' y‖) * C +
          ∫ y, ‖cutoff R t x' y - cutoff R t x y‖ * C := by
      gcongr
      apply (norm_integral_le_integral_norm _).trans
      apply integral_mono_of_nonneg
      · apply Eventually.of_forall (fun x ↦ by positivity)
      · apply ((integrable_cutoff hR ht).sub (integrable_cutoff hR ht)).norm.mul_const
      · apply Eventually.of_forall (fun y ↦ ?_)
        simp only [← ofReal_sub, norm_mul, norm_real, Real.norm_eq_abs]
        gcongr
        apply hC
    _ = 2 * C * ∫ y, |cutoff R t x y - cutoff R t x' y| := by
      simp only [Real.norm_eq_abs, integral_mul_const, abs_sub_comm (cutoff R t x' _)]
      ring
  have N : ∫ y, |cutoff R t x y - cutoff R t x' y| ≤
      volume.real (ball x (2 * R)) * dist x x' / (t * R) := calc
    ∫ y, |cutoff R t x y - cutoff R t x' y|
    _ = ∫ y in ball x (t * R) ∪ ball x' (t * R), |cutoff R t x y - cutoff R t x' y| := by
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ ?_)).symm
      simp only [mem_union, not_or] at hy
      simp [cutoff_eq_zero hR ht hy.1, cutoff_eq_zero hR ht hy.2]
    _ ≤ ∫ y in ball x (t * R) ∪ ball x' (t * R), dist x x' / (t * R) := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun y ↦ by positivity))
      · apply (integrableOn_const_iff).2
        simp [measure_union_lt_top_iff, measure_ball_lt_top]
      apply Eventually.of_forall (fun y ↦ ?_)
      simp only [cutoff_comm (y := y)]
      simpa [div_eq_inv_mul, dist_eq_norm] using (cutoff_Lipschitz hR ht (x := y)).dist_le_mul x x'
    _ = volume.real (ball x (t * R) ∪ ball x' (t * R)) * dist x x' / (t * R) := by
      simp [Measure.real, mul_div_assoc]
    _ ≤ volume.real (ball x (2 * R)) * dist x x' / (t * R) := by
      gcongr
      · apply measure_ball_lt_top.ne
      apply union_subset
      · apply ball_subset_ball
        gcongr
        linarith
      · apply ball_subset_ball'
        rw [dist_comm]
        nlinarith
  calc
    ‖holderApprox R t φ x' - holderApprox R t φ x‖
  _ ≤ (2 * C * ∫ y, |cutoff R t x y - cutoff R t x' y|)
        / (2⁻¹ * volume.real (ball x (2⁻¹ * t * R))) := by
    rwa [← le_div_iff₀'] at M
    apply mul_pos (by positivity)
    apply measureReal_ball_pos
    positivity
  _ ≤ (2 * C * (volume.real (ball x (2 * R)) * dist x x' / (t * R))) /
      (2⁻¹ * volume.real (ball x (2⁻¹ * t * R))) := by gcongr
  _ ≤ (2 * C * (((defaultA a) * (4 ⁻¹ * t) ^ (- Real.logb 2 (defaultA a)) *
        volume.real (ball x ((4⁻¹ * t) * (2 * R)))) * dist x x' / (t * R))) /
      (2⁻¹ * volume.real (ball x (2⁻¹ * t * R))) := by
    gcongr
    exact measureReal_ball_le_same' (μ := (volume : Measure X)) (t := 4⁻¹ * t) (r := 2 * R) x
      (by positivity) (by linarith)
  _ = 2⁻¹ * 16 * C * (defaultA a) * t⁻¹ * (4 ⁻¹ * t) ^ (- Real.logb 2 (defaultA a))
        * (dist x x' / (2 * R)) *
        (volume.real (ball x ((4⁻¹ * t) * (2 * R))) / volume.real (ball x (2⁻¹ * t * R))) := by
    ring
  _ = 2⁻¹ * 16 * C * 2 ^ a * t⁻¹ * (4 ⁻¹ * t) ^ (- a : ℝ) * (dist x x' / (2 * R)) := by
    have : volume.real (ball x ((4⁻¹ * t) * (2 * R))) / volume.real (ball x (2⁻¹ * t * R)) = 1 := by
      rw [show (4⁻¹ * t) * (2 * R) = 2⁻¹ * t * R by ring, div_self]
      apply ne_of_gt
      apply measureReal_ball_pos
      positivity
    simp [defaultA, ← Real.rpow_natCast, this]
  _ ≤ 2⁻¹ * 2 ^ a * C * 2 ^ a * t⁻¹ * (4 ⁻¹ * t) ^ (- a : ℝ) * (dist x x' / (2 * R)) := by
    gcongr
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num]
    apply pow_le_pow_right₀ (by norm_num)
    apply le_trans (by norm_num) (four_le_a X)
  _ = 2⁻¹ * 2 ^ (a + a + 2 * a) * t ^ (- (1+a) : ℝ) * C * (dist x x' / (2 * R)) := by
    simp only [pow_add, neg_add_rev]
    rw [Real.mul_rpow (by norm_num) ht.le,
      Real.rpow_neg (by norm_num), Real.inv_rpow (by norm_num), inv_inv, Real.rpow_add ht,
      Real.rpow_neg_one, Real.rpow_natCast, pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num]
    ring
  _ = 2⁻¹ * 2 ^ (4 * a) * t ^ (-1 - a : ℝ) * C * (dist x x' / (2 * R)) := by
    congr <;> ring
  _ = _ := by ring

/-- Part of Lemma 8.0.1: Lipschitz norm control in Equation (8.0.2). Note that it only uses the sup
norm of `φ`, no need for a Hölder control. -/
lemma norm_holderApprox_sub_le {z : X} {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (h't : t ≤ 1)
    {C : ℝ≥0} {φ : X → ℂ} (hc : Continuous φ) (hφ : φ.support ⊆ ball z R)
    (hC : ∀ x, ‖φ x‖ ≤ C) {x x' : X} :
    ‖holderApprox R t φ x - holderApprox R t φ x'‖ ≤
    2⁻¹ * 2 ^ (4 * a) * t ^ (-1 - a : ℝ) * C * dist x x' / (2 * R) := by
  rcases lt_or_ge (dist x x') R with hx | hx
  · rw [norm_sub_rev]
    exact norm_holderApprox_sub_le_aux hR ht h't hc hφ hC hx
  calc
    ‖holderApprox R t φ x - holderApprox R t φ x'‖
  _ ≤ ‖holderApprox R t φ x‖ + ‖holderApprox R t φ x'‖ := norm_sub_le _ _
  _ ≤ C + C := by
    gcongr
    · exact holderApprox_le hR ht hC x
    · exact holderApprox_le hR ht hC x'
  _ = 2⁻¹ * 2 ^ 3 * 1 * C * 2⁻¹ := by ring
  _ ≤ 2⁻¹ * 2 ^ (4 * a) * t ^ (-1 - a : ℝ) * C * (dist x x' / (2 * R)) := by
    gcongr
    · exact one_le_two
    · have : 4 ≤ a := four_le_a X
      linarith
    · apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht h't
      have : (4 : ℝ) ≤ a := mod_cast (four_le_a X)
      linarith
    · simp only [inv_eq_one_div]
      apply (div_le_div_iff₀ (by norm_num) (by positivity)).2
      linarith
  _ = _ := by ring

lemma lipschitzWith_holderApprox {z : X} {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (h't : t ≤ 1)
    {C : ℝ≥0} {φ : X → ℂ} (hc : Continuous φ) (hφ : φ.support ⊆ ball z R)
    (hC : ∀ x, ‖φ x‖ ≤ C) :
    LipschitzWith (2⁻¹ * 2 ^ (4 * a) * t ^ (-1 - a : ℝ) * C / (2 * R)).toNNReal
      (holderApprox R t φ) := by
  apply LipschitzWith.of_dist_le' (fun x y ↦ ?_)
  rw [dist_eq_norm]
  convert norm_holderApprox_sub_le hR ht h't hc hφ hC using 1
  ring

lemma iLipENorm_holderApprox' {z : X} {R t : ℝ} (ht : 0 < t) (h't : t ≤ 1)
    {C : ℝ≥0} {φ : X → ℂ} (hc : Continuous φ) (hφ : φ.support ⊆ ball z R) (hC : ∀ x, ‖φ x‖ ≤ C) :
    iLipENorm (holderApprox R t φ) z (2 * R) ≤
      2 ^ (4 * a) * (ENNReal.ofReal t) ^ (-1 - a : ℝ) * C := by
  let C' : ℝ≥0 := 2 ^ (4 * a) * (t.toNNReal) ^ (-1 - a : ℝ) * C
  have : 2 ^ (4 * a) * (ENNReal.ofReal t) ^ (-1 - a : ℝ) * C = C' := by
    simp only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat, C', ENNReal.ofReal]
    congr
    rw [ENNReal.coe_rpow_of_ne_zero]
    simpa using ht
  rw [this]
  apply iLipENorm_le
  · intro x hx
    have h'R : 0 < 2 * R := pos_of_mem_ball hx
    have hR : 0 < R := by linarith
    apply (holderApprox_le hR ht hC x).trans
    simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_rpow, C', ← mul_assoc]
    have : (C : ℝ) = 1 * 1 * C := by simp
    conv_lhs => rw [this]
    gcongr
    · calc
        (1 : ℝ)
      _ = 2⁻¹ * (2 ^ 1) := by norm_num
      _ ≤ 2⁻¹ * (2 ^ (4 * a)) := by
        gcongr
        · norm_num
        · have := four_le_a X
          linarith
    · apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by simp [ht]) (by simp [h't])
      linarith
  · intro x hx x' hx' hne
    have h'R : 0 < 2 * R := pos_of_mem_ball hx
    have hR : 0 < R := by linarith
    simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_rpow,
      Real.coe_toNNReal', ht.le, sup_of_le_left, ← mul_assoc, C']
    exact norm_holderApprox_sub_le hR ht h't hc hφ hC

lemma iLipENorm_holderApprox_le {z : X} {R t : ℝ} (ht : 0 < t) (h't : t ≤ 1)
    {φ : X → ℂ} (hφ : support φ ⊆ ball z R) :
    iLipENorm (holderApprox R t φ) z (2 * R) ≤
      2 ^ (4 * a) * (ENNReal.ofReal t) ^ (-1 - a : ℝ) * iHolENorm φ z (2 * R) τ := by
  rcases eq_or_ne (iHolENorm φ z (2 * R) τ) ∞ with h'φ | h'φ
  · apply le_top.trans_eq
    rw [eq_comm]
    simp only [defaultτ] at h'φ
    simp [h'φ, ht]
  rw [← ENNReal.coe_toNNReal h'φ]
  apply iLipENorm_holderApprox' ht h't
  · apply continuous_of_iHolENorm_ne_top' (τ_pos X) hφ h'φ
  · exact hφ
  · apply fun x ↦ norm_le_iHolNNNorm_of_subset h'φ (hφ.trans ?_)
    intro y hy
    simp only [mem_ball] at hy ⊢
    have : 0 < R := dist_nonneg.trans_lt hy
    linarith

/-- The constant occurring in Proposition 2.0.5.
Has value `2 ^ (7 * a)` in the blueprint. -/
def C2_0_5 (a : ℝ) : ℝ≥0 := 2 ^ (7 * a)

--NOTE (MI) : there was a missing minus sign in the exponent.
/-- Proposition 2.0.5. -/
theorem holder_van_der_corput {z : X} {R : ℝ} {φ : X → ℂ}
    (φ_supp : support φ ⊆ ball z R) {f g : Θ X} :
    ‖∫ x, exp (I * (f x - g x)) * φ x‖ₑ ≤
    (C2_0_5 a : ℝ≥0∞) * volume (ball z R) * iHolENorm φ z (2 * R) τ *
      (1 + edist_{z, R} f g) ^ (- (2 * a^2 + a^3 : ℝ)⁻¹) := by
  have : 4 ≤ a := four_le_a X
  have : (4 : ℝ) ≤ a := mod_cast four_le_a X
  rcases le_or_gt R 0 with hR | hR
  · simp [ball_eq_empty.2 hR, subset_empty_iff, support_eq_empty_iff] at φ_supp
    simp [φ_supp]
  rcases eq_or_ne (iHolENorm φ z (2 * R) τ) ∞ with h2φ | h2φ
  · apply le_top.trans_eq
    symm
    simp only [defaultτ] at h2φ
    have : (0 : ℝ) < 2 * a ^ 2 + a ^ 3 := by positivity
    simp [h2φ, C2_0_5, (measure_ball_pos volume z hR).ne', this, edist_ne_top]
  let t : ℝ := (1 + nndist_{z, R} f g) ^ (- (τ / (2 + a)))
  have t_pos : 0 < t := Real.rpow_pos_of_pos (by positivity) _
  have t_one : t ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · simp only [le_add_iff_nonneg_right,  NNReal.zero_le_coe]
    · simp only [defaultτ, Left.neg_nonpos_iff]
      positivity
  have φ_cont : Continuous φ := continuous_of_iHolENorm_ne_top' (τ_pos X) φ_supp h2φ
  have φ_comp : HasCompactSupport φ := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall z R)
    exact φ_supp.trans ball_subset_closedBall
  let φ' := holderApprox R t φ
  have φ'_supp : support φ' ⊆ ball z (2 * R) := support_holderApprox_subset hR φ_supp ⟨t_pos, t_one⟩
  have φ'_cont : Continuous φ' := by
    apply LipschitzWith.continuous
    apply lipschitzWith_holderApprox hR t_pos t_one φ_cont φ_supp
    exact fun x ↦ norm_le_iHolNNNorm_of_subset h2φ (φ_supp.trans (ball_subset_ball (by linarith)))
  have φ'_comp : HasCompactSupport φ' := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall z (2 * R))
    exact φ'_supp.trans ball_subset_closedBall
  have : volume (ball z (2 * R)) ≤ 2 ^ a * volume (ball z R) := by
    convert measure_ball_two_le_same z R (μ := volume)
    simp [defaultA]
  /- First step: control `‖∫ x, exp (I * (f x - g x)) * φ' x‖ₑ`, using that this function is
  Lipschitz and the cancellativity assumption for the integral against Lipschitz functions. -/
  have : (ENNReal.ofReal t) ^ (-1 - a : ℝ) * (1 + edist_{z, R} f g) ^ (- τ) ≤
      (1 + edist_{z, R} f g) ^ (- τ ^ 2 / (2 + a)) := by
    simp only [coe_nndist, defaultτ, t]
    rw [← ENNReal.ofReal_rpow_of_pos (by positivity),
      ENNReal.ofReal_add zero_le_one (by positivity), ← edist_dist, ENNReal.ofReal_one]
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_add]; rotate_left
    · apply ne_of_gt
      apply zero_lt_one.trans_le (by simp)
    · simp [edist_ne_top]
    gcongr
    · simp
    · field_simp
      nlinarith
  have : ‖∫ x, exp (I * (f x - g x)) * φ' x‖ₑ ≤ 2 ^ (6 * a) * volume (ball z R)
        * iHolENorm φ z (2 * R) τ * (1 + edist_{z, R} f g) ^ (- τ ^ 2 / (2 + a)) := calc
      ‖∫ x, exp (I * (f x - g x)) * φ' x‖ₑ
    _ ≤ 2 ^ a * volume (ball z (2 * R))
      * iLipENorm φ' z (2 * R) * (1 + edist_{z, 2 * R} f g) ^ (- τ) := by
      simpa only [defaultA, Nat.cast_pow, Nat.cast_ofNat, t] using
        enorm_integral_exp_le (x := z) (r := 2 * R) (φ := φ') φ'_supp (f := f) (g := g)
    _ ≤ 2 ^ a * (2 ^ a * volume (ball z R))
        * (2 ^ (4 * a) * (ENNReal.ofReal t) ^ (-1 - a : ℝ) * iHolENorm φ z (2 * R) τ)
        * (1 + edist_{z, R} f g) ^ (- τ) := by
      gcongr 2 ^ a * ?_ * ?_ * ?_
      · exact iLipENorm_holderApprox_le t_pos t_one φ_supp
      · apply ENNReal.rpow_le_rpow_of_nonpos
        · simp
        apply add_le_add_right
        simp only [edist_dist]
        apply ENNReal.ofReal_le_ofReal
        apply CompatibleFunctions.cdist_mono
        apply ball_subset_ball (by linarith)
    _ = 2 ^ (6 * a) * volume (ball z R) * iHolENorm φ z (2 * R) τ *
        ((ENNReal.ofReal t) ^ (-1 - a : ℝ) * (1 + edist_{z, R} f g) ^ (- τ)) := by
      rw [show 6 * a = 4 * a + a + a by ring, pow_add, pow_add]
      ring
    _ ≤ 2 ^ (6 * a) * volume (ball z R) * iHolENorm φ z (2 * R) τ *
        (1 + edist_{z, R} f g) ^ (- τ ^ 2 / (2 + a)) := by gcongr;
  /- Second step: control `‖∫ x, exp (I * (f x - g x)) * (φ x - φ' x)‖ₑ` using that `‖φ x - φ' x‖`
  is controlled pointwise, and vanishes outside of `B (z, 2R)`. -/
  have : ENNReal.ofReal (t/2) ^ τ ≤ (1 + edist_{z, R} f g) ^ (- τ ^ 2 / (2 + a)) := by
    have : 0 < τ := τ_pos X
    have : ENNReal.ofReal (t/2) ^ τ ≤ ENNReal.ofReal t ^ τ := by gcongr; linarith
    apply this.trans_eq
    rw [show - τ ^ 2 / (2 + a) = (-τ / (2 + a)) * τ by ring, ENNReal.rpow_mul]
    congr 1
    simp only [coe_nndist, defaultτ, t]
    rw [← ENNReal.ofReal_rpow_of_pos (by positivity),
      ENNReal.ofReal_add zero_le_one (by positivity), ← edist_dist, ENNReal.ofReal_one]
    congr
    ring
  have : ‖∫ x, exp (I * (f x - g x)) * (φ x - φ' x)‖ₑ
    ≤ 2 ^ (6 * a) * volume (ball z R) * iHolENorm φ z (2 * R) τ *
        (1 + edist_{z, R} f g) ^ (- τ ^ 2 / (2 + a)) := calc
      ‖∫ x, exp (I * (f x - g x)) * (φ x - φ' x)‖ₑ
    _ = ‖∫ x in ball z (2 * R), exp (I * (f x - g x)) * (φ x - φ' x)‖ₑ := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro x hx
      have A : φ x = 0 := by
        apply notMem_support.1
        contrapose! hx
        apply (φ_supp.trans (ball_subset_ball (by linarith))) hx
      have A' : φ' x = 0 := by
        apply notMem_support.1
        contrapose! hx
        apply φ'_supp hx
      simp [A, A']
    _ ≤ ∫⁻ x in ball z (2 * R), ‖exp (I * (f x - g x)) * (φ x - φ' x)‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ x in ball z (2 * R), ‖φ x - φ' x‖ₑ := by
      simp only [enorm_mul, ← ofReal_sub, enorm_exp_I_mul_ofReal, one_mul]
    _ ≤ ∫⁻ x in ball z (2 * R), ENNReal.ofReal (t/2) ^ τ * iHolENorm φ z (2 * R) τ :=
      lintegral_mono (fun x ↦ enorm_holderApprox_sub_le hR t_pos t_one φ_supp x)
    _ = volume (ball z (2 * R)) * ENNReal.ofReal (t/2) ^ τ * iHolENorm φ z (2 * R) τ := by
      simp; ring
    _ ≤ (2 ^ a * volume (ball z R)) * ENNReal.ofReal (t/2) ^ τ * iHolENorm φ z (2 * R) τ := by
      gcongr
    _ = 2 ^ a * volume (ball z R) * iHolENorm φ z (2 * R) τ * ENNReal.ofReal (t/2) ^ τ := by ring
    _ ≤ 2 ^ (6 * a) * volume (ball z R) * iHolENorm φ z (2 * R) τ *
        (1 + edist_{z, R} f g) ^ (- τ ^ 2 / (2 + a)) := by
      gcongr
      · exact one_le_two
      · linarith
  /- Final step: control `‖∫ x, exp (I * (f x - g x)) * φ x‖ₑ` by adding up the estimates of the
  two previous steps. -/
  calc
      ‖∫ x, exp (I * (f x - g x)) * φ x‖ₑ
  _ = ‖∫ x, exp (I * (f x - g x)) * (φ x - φ' x) + exp (I * (f x - g x)) * φ' x‖ₑ := by
    congr with x
    ring
  _ = ‖(∫ x, exp (I * (f x - g x)) * (φ x - φ' x)) + ∫ x, exp (I * (f x - g x)) * φ' x‖ₑ := by
    rw [integral_add]
    · apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
      exact (φ_comp.sub φ'_comp).mul_left
    · apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
      exact φ'_comp.mul_left
  _ ≤ ‖∫ x, exp (I * (f x - g x)) * (φ x - φ' x)‖ₑ + ‖∫ x, exp (I * (f x - g x)) * φ' x‖ₑ :=
    enorm_add_le _ _
  _ ≤ 2 ^ (6 * a) * volume (ball z R) * iHolENorm φ z (2 * R) τ *
        (1 + edist_{z, R} f g) ^ (- τ ^ 2 / (2 + a)) +
      2 ^ (6 * a) * volume (ball z R) * iHolENorm φ z (2 * R) τ *
        (1 + edist_{z, R} f g) ^ (- τ ^ 2 / (2 + a)) := by gcongr;
  _ = 2 ^ (1 + 6 * a) * volume (ball z R) * iHolENorm φ z (2 * R) τ *
        (1 + edist_{z, R} f g) ^ (- τ ^ 2 / (2 + a)) := by rw [pow_add, pow_one]; ring
  _ ≤ 2 ^ (7 * a) * volume (ball z R) * iHolENorm φ z (2 * R) τ *
        (1 + edist_{z, R} f g) ^ (- τ ^ 2 / (2 + a)) := by
    gcongr
    · exact one_le_two
    · linarith
  _ = (C2_0_5 a : ℝ≥0∞) * volume (ball z R) * iHolENorm φ z (2 * R) τ *
      (1 + edist_{z, R} f g) ^ (- (2 * a^2 + a^3 : ℝ)⁻¹) := by
    congr
    · simp only [C2_0_5]
      rw [ENNReal.coe_rpow_of_nonneg]
      · simp [← ENNReal.rpow_natCast]
      · linarith
    · simp [defaultτ]
      field_simp
