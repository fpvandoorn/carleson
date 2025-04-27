import Carleson.TwoSidedCarleson.WeakCalderonZygmund
import Carleson.ToMathlib.Analysis.Convex.SpecificFunctions.Basic


open MeasureTheory Set Bornology Function ENNReal Metric
open scoped NNReal

noncomputable section

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {τ C r R : ℝ} {q q' : ℝ≥0}
variable {F G : Set X}
variable {K : X → X → ℂ} {x x' : X} [IsTwoSidedKernel a K]
variable [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)]

/-! ## Section 10.1 and Lemma 10.0.2 -/

variable (K) in
/-- The operator `T_*^r g(x)`, defined in (10.1.31), as part of Lemma 10.1.6. -/
def simpleNontangentialOperator (r : ℝ) (g : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (R > r) (x' ∈ ball x R), ‖czOperator K R g x'‖ₑ

theorem Real.two_mul_lt_two_pow (x : ℝ) (hx : 2 ≤ x) :
    (2 : ℝ) * x ≤ 2 ^ x := by
  calc
    _ ≤ (1 + (x - 1) * 1) * 2 := by linarith
    _ ≤ (1 + 1 : ℝ) ^ (x - 1) * 2 := by
      gcongr
      apply one_add_mul_self_le_rpow_one_add (by norm_num) (by linarith)
    _ ≤ (2 : ℝ) ^ (x - 1) * (2 : ℝ) ^ (1 : ℝ) := by norm_num
    _ ≤ _ := by
      rw [← rpow_add (by positivity)]
      norm_num

lemma geom_estimate_constant_le_two :
    (4 * (1 - 2 ^ (-1 / 4 : ℝ)))⁻¹ ≤ (2 : ℝ) := by
  have : (2 : ℝ) ^ (-1 / 4 : ℝ) ≤ 7 / 8 := by
    rw [neg_div, one_div, neg_eq_neg_one_mul, mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_neg_one, inv_le_comm₀ (by positivity) (by norm_num)]
    apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity)
    conv_rhs => rw [← Real.rpow_natCast (n := 4), ← Real.rpow_mul (by norm_num)]
    norm_num
  calc
    _ ≤ ((4 : ℝ) * (1 - 7 / 8))⁻¹ := by gcongr
    _ ≤ _ := by norm_num

theorem real_geometric_series_estimate {x : ℝ} (hx : 4 ≤ x) :
    tsum (fun (n : ℕ) ↦ (2 : ℝ) ^ (-n / x)) ≤ 2 ^ x := by

  have two_pow_neg_inv_lt_one : (2 : ℝ) ^ (-1 / x) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · simp
    · rw [neg_div]
      simp only [one_div, Left.neg_neg_iff, inv_pos]
      positivity

  have zero_le_one_sub_four_div_x : 0 ≤ 1 - 4 / x := by
    simp only [sub_nonneg]
    rw [div_le_iff₀]
    · simp only [one_mul]
      exact hx
    · positivity

  have one_sub_two_pow_neg_one_div_four_pos : 0 < 1 - (2 : ℝ) ^ (-1 / 4 : ℝ) := by
    norm_num
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · simp
    · norm_num

  -- By convexity, for all 0 ≤ λ ≤ 1, we have ...
  have two_pow_convex := (ConvexOn_rpow_left (2 : ℝ) (by linarith only)).2
  have two_pow_neg_one_div_bound := two_pow_convex
               (x := (-1/4 : ℝ)) (by simp)
               (y := 0) (by simp)
               (a := 4/x)
               (b := 1 - 4/x)
               (by positivity)
               (zero_le_one_sub_four_div_x)
               (by ring)
  simp only [smul_eq_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_mul_div_cancel₀',
    mul_zero, add_zero, Real.rpow_zero, mul_one] at two_pow_neg_one_div_bound

  calc
    _ = ∑' (n : ℕ), ((2 : ℝ) ^ (-1 / x)) ^ n := by
      congr
      ext n
      rw [<- Real.rpow_mul_natCast (by norm_num)]
      congr
      ring
    _ ≤ (1 - 2 ^ (-1 / x))⁻¹ := by
      rw [tsum_geometric_of_lt_one (by positivity) (two_pow_neg_inv_lt_one)]
    _ ≤ (4 / x * (1 - 2 ^ (-1 / 4 : ℝ)))⁻¹ := by
      rw [inv_le_inv₀]
      · linarith only [two_pow_neg_one_div_bound]
      · linarith only [two_pow_neg_inv_lt_one]
      · apply @_root_.mul_pos
        · positivity
        · exact one_sub_two_pow_neg_one_div_four_pos
    _ ≤ (4 * (1 - 2 ^ (-1 / 4 : ℝ)))⁻¹ * x := by field_simp
    _ ≤ 2 * x := mul_le_mul_of_nonneg_right geom_estimate_constant_le_two (by linarith only [hx])
    _ ≤ 2 ^ x := by
      apply Real.two_mul_lt_two_pow
      linarith only [hx]

/-- Lemma 10.1.1 -/
theorem geometric_series_estimate {x : ℝ} (hx : 4 ≤ x) :
    tsum (fun (n : ℕ) ↦ (2 : ℝ≥0) ^ (-n / x)) ≤ 2 ^ x := by
  suffices this : ((tsum (fun (n : ℕ) ↦ (2 : ℝ≥0) ^ (-n / x)) : ℝ≥0) : ℝ) ≤ (((2 ^ x) : ℝ≥0) : ℝ) by
    exact this
  push_cast
  exact real_geometric_series_estimate hx

/-- The constant used in `estimate_x_shift`. -/
irreducible_def C10_1_2 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 2 * a + 1)

/-- Lemma 10.1.2 -/
theorem estimate_x_shift (ha : 4 ≤ a)
    {g : X → ℂ} (hg : BoundedFiniteSupport g) (hr : 0 < r) (hx : dist x x' ≤ r) :
    nndist (czOperator K r g x) (czOperator K r g x') ≤
    C10_1_2 a * globalMaximalFunction volume 1 g x := by
  sorry

/-- The constant used in `cotlar_control`. -/
irreducible_def C10_1_3 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 4 * a + 1)

--TODO: to mathlib
lemma Set.indicator_eq_indicator' {α : Type*} {M : Type*} [Zero M] {s : Set α} {f g : α → M} (h : ∀ x ∈ s, f x = g x) :
    s.indicator f = s.indicator g := by
  ext x
  unfold indicator
  split
  . rename_i hxs
    exact h x hxs
  . rfl

lemma MeasureTheory.lintegral_set_mono_fn {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) ⦃f g : α → ℝ≥0∞⦄ (hfg : ∀ x ∈ s, f x ≤ g x) :
    ∫⁻ (a : α) in s, f a ∂μ ≤ ∫⁻ (a : α) in s, g a ∂μ := by
  rw [← lintegral_indicator hs, ← lintegral_indicator hs]
  apply lintegral_mono_fn
  intro x
  unfold indicator
  split
  . rename_i hxs
    exact hfg x hxs
  . rfl


/-- Stolen from PR for Lemma 10.1.2 -/
lemma czoperator_welldefined {g : X → ℂ} (hg : BoundedFiniteSupport g) (hr : 0 < r) (x : X):
    IntegrableOn (fun y => K x y * g y) (ball x r)ᶜ volume := sorry

--set_option maxHeartbeats 300000 in

lemma radius_change (ha : 4 ≤ a) {g : X → ℂ} (hg : BoundedFiniteSupport g volume)
  (hr : r ∈ Ioc 0 R) (hx : dist x x' ≤ R / 4) :
    ‖czOperator K r ((ball x (R / 2))ᶜ.indicator g) x' - czOperator K R ((ball x (R / 2))ᶜ.indicator g) x'‖ₑ ≤
      2 ^ (a ^ 3 + 4 * a) * globalMaximalFunction volume 1 g x := by
  have R_pos : 0 < R := by
    rw [mem_Ioc] at hr
    linarith
  unfold czOperator
  --rw [MeasureTheory.setIntegral_diff]
  rw [← integral_indicator, ← integral_indicator, ← integral_sub]
  --rw [eLpNorm_indicator_sub_indicator]
  calc _
    _ = ‖∫ (y : X), ((ball x' R) \ (ball x' r ∪ ball x (R / 2))).indicator (fun y ↦ K x' y * g y) y‖ₑ := by
      congr
      ext y
      unfold indicator
      split <;> split <;> split <;> rename_i yx'r yx'R hy
      . exfalso
        exact yx'R hy.1
      . simp
      . simp
        intro h
        exfalso
        simp at yx'r yx'R hy
        linarith
      . simp
        intro h
        exfalso
        simp at yx'r yx'R hy
        linarith [hy yx'R yx'r]
      . --simp
        simp at yx'r yx'R hy
        linarith
      . simp
        intro h
        exfalso
        simp at yx'r yx'R hy hr
        linarith
      . simp at yx'r yx'R hy
        linarith
      . ring
    _ ≤ ∫⁻ (y : X), ‖((ball x' R) \ (ball x' r ∪ ball x (R / 2))).indicator (fun y ↦ K x' y * g y) y‖ₑ := by
      apply enorm_integral_le_lintegral_enorm
    --_ = ∫⁻ (y : X) in ((ball x' R) \ (ball x' r ∪ ball x (R / 2))), ‖K x' y * g y‖ₑ := by
    _ = ∫⁻ (y : X) in ((ball x' R) \ (ball x' r ∪ ball x (R / 2))), ‖K x' y‖ₑ * ‖g y‖ₑ := by
      rw [← lintegral_indicator]
      . congr with y
        rw[enorm_indicator_eq_indicator_enorm]
        congr with y
        apply enorm_mul
      measurability
    _ ≤ ∫⁻ (y : X) in ((ball x (2 * R)) \ (ball x' (R / 4))), ‖K x' y‖ₑ * ‖g y‖ₑ := by
      apply lintegral_mono_set
      intro y
      simp
      intro h1 h2 h3
      simp at hr
      constructor <;>
      . rw [dist_comm] at hx
        linarith [dist_triangle y x' x]
    _ ≤ ∫⁻ (y : X) in ((ball x (2 * R)) \ (ball x' (R / 4))), (C_K a : ℝ≥0∞) / vol x' y * ‖g y‖ₑ := by
      gcongr with y
      apply enorm_K_le_vol_inv
      --norm_K_le_vol_inv
    _ ≤ ∫⁻ (y : X) in ((ball x (2 * R)) \ (ball x' (R / 4))), (C_K a : ℝ≥0∞) / (volume (ball x' (R / 4))) * ‖g y‖ₑ := by
      apply lintegral_set_mono_fn (by measurability)
      intro y hy
      gcongr
      unfold vol
      apply measure_mono
      intro z hz
      simp at *
      rw [dist_comm x' y]
      linarith
    _ = (C_K a : ℝ≥0∞) / (volume (ball x' (R / 4))) * ∫⁻ (y : X) in ((ball x (2 * R)) \ (ball x' (R / 4))), ‖g y‖ₑ := by
      apply lintegral_const_mul
      -- maybe use different version of lintegral_const_mul
      apply Measurable.enorm
      exact BoundedFiniteSupport.measurable hg
    _ ≤ (C_K a : ℝ≥0∞) / (volume (ball x' (R / 4))) * ∫⁻ (y : X) in (ball x (2 * R)), ‖g y‖ₑ := by
      gcongr
      apply lintegral_mono_set
      exact diff_subset
    _ ≤ (C_K a : ℝ≥0∞) / (volume (ball x' (R / 4))) * (volume (ball x (2 * R)) * globalMaximalFunction volume 1 g x) := by
      gcongr
      apply lintegral_ball_le_volume_globalMaximalFunction
      simpa

  rw [← mul_assoc]
  gcongr

  calc _
    _ ≤ (C_K a : ℝ≥0∞) / (volume (ball x (2 * R)) / 2 ^ (4 * a)) * (volume (ball x (2 * R))) := by
      gcongr
      rw [ENNReal.div_le_iff' (by simp) (by simp)]
      calc _
        _ = volume (ball x (2 ^ 3 * (R / 4))) := by
          congr
          ring_nf
        _ ≤ (defaultA a) ^ 3 * volume (ball x (R / 4)) := by
          apply measure_ball_two_le_same_iterate
        _ ≤ (defaultA a) ^ 3 * volume (ball x' (R / 2)) := by
          gcongr
          refine ball_subset ?_
          linarith
        _ = (defaultA a) ^ 3 * volume (ball x' (2 * (R / 4))) := by congr; ring_nf
        _ ≤ (defaultA a) ^ 3 * ((defaultA a) * volume (ball x' (R / 4))) := by
          gcongr
          apply measure_ball_two_le_same
        _ = 2 ^ (4 * a) * volume (ball x' (R / 4)) := by
          unfold defaultA
          push_cast
          ring_nf
    --TODO: calculate with volumes
    _= 2 ^ (a ^ 3 + 4 * a) := by
      unfold C_K
      --push_cast
      rw [← ENNReal.div_mul, mul_assoc, mul_comm (2 ^ (4 * a)), ← mul_assoc, ENNReal.div_mul_cancel]
      . norm_cast
        ring
      . apply (measure_ball_pos volume x (by linarith)).ne.symm
      . apply measure_ball_ne_top
      . simp
      . simp
  . rw [integrable_indicator_iff (by measurability)]
    apply czoperator_welldefined
    . sorry
    . rw [mem_Ioc] at hr; exact hr.1
  . rw [integrable_indicator_iff (by measurability)]
    apply czoperator_welldefined _ R_pos
    . sorry
  . measurability
  . measurability
  --calc _
  --  _ = ‖czOperator K r ((ball x (R / 2))ᶜ.indicator g) x' - czOperator K R ((ball x (R / 2))ᶜ.indicator g) x'‖ₑ


lemma cut_out_ball {g : X → ℂ}
  (hr : r ∈ Ioc 0 R) (hx : dist x x' ≤ R / 4) :
    czOperator K R g x' = czOperator K R ((ball x (R / 2))ᶜ.indicator g) x' := by
  have R_pos : 0 < R := by
    rw [mem_Ioc] at hr
    linarith
  unfold czOperator
  rw [← integral_indicator, ← integral_indicator]
  . congr
    apply indicator_eq_indicator'
    intro y hy
    rw [indicator_apply_eq_self.mpr]
    intro hy'
    exfalso
    simp at hy hy'
    have : dist y x' ≤ dist y x + dist x x' := by
      apply dist_triangle
    linarith
  . measurability
  . measurability

/-- Lemma 10.1.3 -/
theorem cotlar_control (ha : 4 ≤ a)
    {g : X → ℂ} (hg : BoundedFiniteSupport g) (hr : r ∈ Ioc 0 R) (hx : dist x x' ≤ R / 4) :
    ‖czOperator K R g x‖ₑ ≤ ‖czOperator K r ((ball x (R / 2))ᶜ.indicator g) x'‖ₑ +
    C10_1_3 a * globalMaximalFunction volume 1 g x := by
  have R_pos : 0 < R := by
    rw [mem_Ioc] at hr
    linarith

  calc ‖czOperator K R g x‖ₑ
    _ = ‖(czOperator K R g x - czOperator K R g x') + czOperator K R g x'‖ₑ := by
      congr
      ring
    _ ≤ ‖czOperator K R g x - czOperator K R g x'‖ₑ + ‖czOperator K R g x'‖ₑ := by
      apply enorm_add_le
    _ = nndist (czOperator K R g x) (czOperator K R g x') + ‖czOperator K R ((ball x (R / 2))ᶜ.indicator g) x'‖ₑ := by congr 2; exact cut_out_ball hr hx
    _ ≤ C10_1_2 a * globalMaximalFunction volume 1 g x + (‖czOperator K r ((ball x (R / 2))ᶜ.indicator g) x' - czOperator K R ((ball x (R / 2))ᶜ.indicator g) x'‖ₑ + ‖czOperator K r ((ball x (R / 2))ᶜ.indicator g) x'‖ₑ) := by
      gcongr
      . apply estimate_x_shift ha hg R_pos
        linarith
      . --triangle inequality as above
        rw [← edist_eq_enorm_sub, edist_comm, edist_eq_enorm_sub]
        apply le_trans _ (enorm_add_le _ _)
        apply le_of_eq
        congr
        ring
    _ ≤ C10_1_2 a * globalMaximalFunction volume 1 g x + 2 ^ (a ^ 3 + 4 * a) * globalMaximalFunction volume 1 g x + ‖czOperator K r ((ball x (R / 2))ᶜ.indicator g) x'‖ₑ := by
      rw [add_assoc]
      gcongr
      exact radius_change ha hg hr hx
    _ ≤ ‖czOperator K r ((ball x (R / 2))ᶜ.indicator g) x'‖ₑ + C10_1_3 a * globalMaximalFunction volume 1 g x := by
      rw [add_comm]
      gcongr
      rw [← add_mul]
      gcongr
      rw [C10_1_2_def, C10_1_3_def]
      norm_num
      calc (2 : ℝ≥0∞) ^ (a ^ 3 + 2 * a + 1) + 2 ^ (a ^ 3 + 4 * a)
        _ = (2 : ℝ≥0∞) ^ (a ^ 3 + (2 * a + 1)) + 2 ^ (a ^ 3 + 4 * a) := by
          congr 1
        _ ≤ 2 ^ (a ^ 3 + 4 * a) + 2 ^ (a ^ 3 + 4 * a) := by
          gcongr
          . exact one_le_two
          . linarith
        _ = 2 * 2 ^ (a ^ 3 + 4 * a) := (two_mul (2 ^ (a ^ 3 + 4 * a))).symm
        _ = 2 ^ (a ^ 3 + 4 * a + 1) := (pow_succ' 2 (a ^ 3 + 4 * a)).symm


/-- The constant used in `cotlar_set_F₂`. -/
irreducible_def C10_1_4 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 20 * a + 2)

/-- Part 1 of Lemma 10.1.4 about `F₁`. -/
theorem cotlar_set_F₁ (ha : 4 ≤ a)
    (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a))
    {g : X → ℂ} (hg : BoundedFiniteSupport g) :
    volume {x' ∈ ball x (R / 4) |
      4 * globalMaximalFunction volume 1 (czOperator K r g) x < ‖czOperator K r g x'‖ₑ } ≤
    volume (ball x (R / 4)) / 4 := by
  sorry

/-- Part 2 of Lemma 10.1.4 about `F₂`. -/
theorem cotlar_set_F₂ (ha : 4 ≤ a)
    (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a))
    {g : X → ℂ} (hg : BoundedFiniteSupport g) :
    volume {x' ∈ ball x (R / 4) |
      C10_1_4 a * globalMaximalFunction volume 1 g x <
      ‖czOperator K r ((ball x (R / 2)).indicator g) x'‖ₑ } ≤
    volume (ball x (R / 4)) / 4 := by
  sorry

/-- The constant used in `cotlar_estimate`. -/
irreducible_def C10_1_5 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 20 * a + 2)

/-- Lemma 10.1.5 -/
theorem cotlar_estimate (ha : 4 ≤ a)
    (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a))
    {g : X → ℂ} (hg : BoundedFiniteSupport g) (hr : r ∈ Ioc 0 R) :
    ‖czOperator K R g x‖ₑ ≤ 4 * globalMaximalFunction volume 1 (czOperator K r g) x +
      C10_1_5 a * globalMaximalFunction volume 1 g x := by
  sorry

/-- The constant used in `simple_nontangential_operator`. -/
irreducible_def C10_1_6 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 24 * a + 6)

/-- Lemma 10.1.6. The formal statement includes the measurability of the operator.
See also `simple_nontangential_operator_le` -/
theorem simple_nontangential_operator (ha : 4 ≤ a)
    (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a))
    {g : X → ℂ} (hg : BoundedFiniteSupport g) (hr : 0 < r) :
    HasStrongType (simpleNontangentialOperator K r) 2 2 volume volume (C10_1_6 a) := by
  sorry

/-- This is the first step of the proof of Lemma 10.0.2, and should follow from 10.1.6 +
monotone convergence theorem. (measurability should be proven without any restriction on `r`.) -/
theorem simple_nontangential_operator_le (ha : 4 ≤ a)
    (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a))
    {g : X → ℂ} (hg : BoundedFiniteSupport g) (hr : 0 ≤ r) :
    HasStrongType (simpleNontangentialOperator K r) 2 2 volume volume (C10_1_6 a) := by
  sorry

/-- Part of Lemma 10.1.7, reformulated. -/
theorem small_annulus_right (ha : 4 ≤ a)
    (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a))
    {f : X → ℂ} (hf : BoundedFiniteSupport f) {R₁ : ℝ} :
    Continuous (fun R₂ ↦ ∫ y in {y | dist x' y ∈ Ioo R₁ R₂}, K x' y * f y) := by
  sorry

/-- Part of Lemma 10.1.7, reformulated -/
theorem small_annulus_left (ha : 4 ≤ a)
    (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a))
    {f : X → ℂ} (hf : BoundedFiniteSupport f) {R₂ : ℝ} :
    Continuous (fun R₁ ↦ ∫ y in {y | dist x' y ∈ Ioo R₁ R₂}, K x' y * f y) := by
  sorry

/-- Lemma 10.1.8. -/
theorem nontangential_operator_boundary (ha : 4 ≤ a)
    {f : X → ℂ} (hf : BoundedFiniteSupport f) :
    nontangentialOperator K f x =
    ⨆ (R₁ : ℝ) (R₂ : ℝ) (_ : R₁ < R₂) (x' : X) (_ : dist x x' ≤ R₁),
    ‖∫ y in ball x' R₂ \ ball x' R₁, K x' y * f y‖ₑ := by
  sorry

/-- The constant used in `nontangential_from_simple`. -/
irreducible_def C10_0_2 (a : ℕ) : ℝ≥0 := 2 ^ (3 * a ^ 3)

/-- Lemma 10.0.2. The formal statement includes the measurability of the operator. -/
theorem nontangential_from_simple (ha : 4 ≤ a)
    (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a))
    {g : X → ℂ} (hg : BoundedFiniteSupport g) :
    HasStrongType (nontangentialOperator K) 2 2 volume volume (C10_0_2 a) := by
  have := simple_nontangential_operator_le ha hT hg le_rfl
  sorry


end
