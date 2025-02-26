import Carleson.TwoSidedCarleson.WeakCalderonZygmund
import Carleson.ToMathlib.Analysis.Convex.SpecificFunctions.Basic
import Carleson.ToMathlib.ENorm

open MeasureTheory Set Bornology Function ENNReal Metric Complex
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
irreducible_def C10_1_2 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 2 * a + 2)

-- Couldn't find this. Probably suboptimal formulation and location. Help appreciated.
lemma czoperator_welldefined {g : X → ℂ} (hmg : Measurable g) (hg : eLpNorm g ∞ < ∞)
    (h2g : volume (support g) < ∞) (hr : 0 < r) (x : X):
    IntegrableOn (fun y => K x y * g y) (ball x r)ᶜ volume := by
  sorry

/- This should go somewhere else

But this version of setIntegral_union is easier to apply as it starts from the overall integral which
is to be estimated.
-/
variable {α β E F : Type*} [MeasurableSpace α]
variable {f : α → ℂ } {s t : Set α} {μ : Measure α}

theorem MeasureTheory.setIntegral_union_2 (hst : Disjoint s t) (ht : MeasurableSet t) (hfst : IntegrableOn f (s ∪ t) μ) :
    ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ + ∫ x in t, f x ∂μ := by
  let hfs : IntegrableOn f s μ := IntegrableOn.mono_set hfst subset_union_left
  let hft : IntegrableOn f t μ := IntegrableOn.mono_set hfst subset_union_right
  exact setIntegral_union hst ht hfs hft
/- End of somewhere else -/

/-- Lemma 10.1.2 -/
theorem estimate_x_shift (ha : 4 ≤ a)
    {g : X → ℂ} (hg : BoundedFiniteSupport g) (hr : 0 < r) (hx : dist x x' ≤ r) :
    nndist (czOperator K r g x) (czOperator K r g x') ≤
    C10_1_2 a * globalMaximalFunction volume 1 g x := by
  let bxrc := (ball x r)ᶜ
  let bx2r := ball x (2*r)

  -- Domain split x integral
  have dom_x : bxrc =  (bxrc ∩ bx2r) ∪ bx2rᶜ := by
    have tmp1 : bx2rᶜ = bxrc ∩ bx2rᶜ := by
      suffices bx2rᶜ ⊆ bxrc by
        rw [Set.right_eq_inter]
        exact this
      suffices ball x r ⊆ bx2r by
        rw [Set.compl_subset_compl]
        exact this
      apply Metric.ball_subset_ball
      linarith

    calc bxrc
      _ = bxrc ∩ univ                  := by rw[Set.inter_univ bxrc]
      _ = bxrc ∩ (bx2r ∪ bx2rᶜ)        := by rw[Set.union_compl_self bx2r]
      _ = (bxrc ∩ bx2r) ∪ bxrc ∩ bx2rᶜ := by rw[Set.inter_union_distrib_left bxrc bx2r bx2rᶜ]
      _ = (bxrc ∩ bx2r) ∪ bx2rᶜ        := by rw[← tmp1]

  set bxprc := (ball x' r)ᶜ
  have tmp2 : bx2rᶜ ⊆ bxprc := by
    rw [Set.compl_subset_compl]
    apply ball_subset
    calc dist x' x
    _ = dist x x' := by apply dist_comm
    _ ≤ r := hx
    _ = 2 * r - r := by ring

  -- Domain split x' integral
  have dom_x_prime : bxprc = (bxprc ∩ bx2r) ∪ bx2rᶜ := by
    have tmp3 : bx2rᶜ = bxprc ∩ bx2rᶜ := by
      rw [Set.right_eq_inter]
      exact tmp2

    rw [tmp3]
    exact Eq.symm (inter_union_compl bxprc bx2r)

  -- Integral split x
  have integral_x : CZOperator K r g x = (∫ y in (bxrc ∩ bx2r), K x y * g y) + (∫ y in bx2rᶜ, K x y * g y) := by
    calc CZOperator K r g x
      _ = (∫ y in bxrc, K x y * g y) := by rfl
      _ = (∫ y in (bxrc ∩ bx2r) ∪ bx2rᶜ , K x y * g y) := by nth_rw 1 [dom_x]

    apply MeasureTheory.setIntegral_union_2
    . rw [disjoint_compl_right_iff_subset]
      exact inter_subset_right
    . apply MeasurableSet.compl
      apply measurableSet_ball
    . rw [← dom_x]
      unfold bxrc
      apply czoperator_welldefined hmg hg h2g hr

  -- Integral split x'
  have integral_x_prime : CZOperator K r g x' = (∫ y in (bxprc ∩ bx2r), K x' y * g y) + (∫ y in bx2rᶜ, K x' y * g y) := by
    calc CZOperator K r g x'
      _ = (∫ y in bxprc, K x' y * g y) := by rfl
      _ = (∫ y in (bxprc ∩ bx2r) ∪ bx2rᶜ , K x' y * g y) := by nth_rw 1 [dom_x_prime]

    apply MeasureTheory.setIntegral_union_2
    . rw [disjoint_compl_right_iff_subset]
      exact inter_subset_right
    . apply MeasurableSet.compl
      apply measurableSet_ball
    . rw [← dom_x_prime]
      unfold bxprc
      apply czoperator_welldefined hmg hg h2g hr

  let int10_1_2 := 0
  let int10_1_3 := 0
  let int10_1_4 := 0

  rw [← edist_nndist, edist_eq_enorm_sub, integral_x, integral_x_prime]

  -- Rewrite lhs according to 10.1.234 split
  conv =>
    arg 1; arg 1
    calc _
      _ = (∫ (y : X) in bxrc ∩ bx2r, K x y * g y)
                + ((∫ (y : X) in bx2rᶜ, K x y * g y) - (∫ (y : X) in bx2rᶜ, K x' y * g y))
                - (∫ (y : X) in bxprc ∩ bx2r, K x' y * g y) := by ring
      _ = (∫ (y : X) in bxrc ∩ bx2r, K x y * g y)
                + (∫ (y : X) in bx2rᶜ, K x y * g y - K x' y * g y)
                - (∫ (y : X) in bxprc ∩ bx2r, K x' y * g y) := by
          rw[← integral_sub]
          apply czoperator_welldefined hmg hg h2g (by simp; exact hr)
          apply IntegrableOn.mono_set
          swap; exact tmp2
          apply czoperator_welldefined hmg hg h2g hr

  trans ‖(∫ (y : X) in bxrc ∩ bx2r, K x y * g y) + ∫ (y : X) in bx2rᶜ, K x y * g y - K x' y * g y‖ₑ +
      ‖∫ (y : X) in bxprc ∩ bx2r, K x' y * g y‖ₑ
  . apply enorm_sub_le

  trans ‖∫ (y : X) in bxrc ∩ bx2r, K x y * g y‖ₑ + ‖ ∫ (y : X) in bx2rᶜ, K x y * g y - K x' y * g y‖ₑ +
      ‖∫ (y : X) in bxprc ∩ bx2r, K x' y * g y‖ₑ
  . refine add_le_add ?_ ?_
    . apply @_root_.enorm_add_le
    . rfl

  trans (∫⁻ (y : X) in bxrc ∩ bx2r, ‖ K x y * g y‖ₑ) + ‖ ∫ (y : X) in bx2rᶜ, K x y * g y - K x' y * g y‖ₑ +
      ‖∫ (y : X) in bxprc ∩ bx2r, K x' y * g y‖ₑ
  . refine add_le_add_three ?_ ?_ ?_
    . apply enorm_integral_le_lintegral_enorm
    . rfl
    . rfl

  trans (∫⁻ (y : X) in bxrc ∩ bx2r, ‖ K x y * g y‖ₑ) + ‖ ∫ (y : X) in bx2rᶜ, K x y * g y - K x' y * g y‖ₑ +
      ∫⁻ (y : X) in bxprc ∩ bx2r, ‖ K x' y * g y‖ₑ
  . refine add_le_add_three ?_ ?_ ?_
    . rfl
    . rfl
    . apply enorm_integral_le_lintegral_enorm

  -- LHS is now 10.1.234

  have y_est {x₀: X}: ∀(y : X), y ∈ (ball x₀ r)ᶜ → r ≤ dist x₀ y := by
    intro y h
    unfold ball at h
    rw [compl_setOf, mem_setOf_eq] at h
    simp only [not_lt] at h
    rw [dist_comm] at h
    exact h

  have pointwise_1 {x₀ : X}: ∀(y : X), y ∈ (ball x₀ r)ᶜ  → ‖K x₀ y‖ₑ * ‖g y‖ₑ ≤
      ENNReal.ofReal (C_K a) / volume (ball x₀ r) * ‖g y‖ₑ := by
    intro y h
    refine mul_le_mul' ?_ ?_
    swap
    . rfl
    rw [← ofReal_norm_eq_enorm]

    trans ENNReal.ofReal (C_K a / Real.vol x₀ y)
    rw [ofReal_le_ofReal_iff]
    apply IsOneSidedKernel.norm_K_le_vol_inv -- Applying this is a pain, should it be reformulated?
    refine div_nonneg ?_ ?_
    . refine LT.lt.le ?_
      exact C_K_pos a
    . unfold Real.vol
      simp

    rw [ENNReal.ofReal_div_of_pos]
    apply ENNReal.div_le_div_left
    unfold Real.vol Measure.real
    refine (le_ofReal_iff_toReal_le ?_ ?_).mpr ?_
    . rw [← lt_top_iff_ne_top]
      exact measure_ball_lt_top
    . simp

    refine toReal_mono ?_ ?_
    . rw [← lt_top_iff_ne_top]
      exact measure_ball_lt_top
    refine measure_mono ?_
    refine ball_subset_ball ?_
    . apply y_est
      exact h

    unfold Real.vol Measure.real
    apply toReal_pos
    . have p : volume (ball x₀ (dist x₀ y)) > 0 := by
        apply measure_ball_pos
        calc 0
          _ < r := hr
          _ ≤ dist x₀ y := by apply y_est; exact h
      exact Ne.symm (ne_of_lt p)
    . rw [← lt_top_iff_ne_top]
      exact measure_ball_lt_top

  have tmp5 {x₀ : X} {n : ℝ} : ∫⁻ (a : X) in ball x₀ (n * r), ‖g a‖ₑ = (⨍⁻ (a : X) in ball x₀ (n * r), ‖g a‖ₑ ∂volume)  * volume (ball x₀ (n * r)) := by
    have h_meas_finite : IsFiniteMeasure (volume.restrict (ball x₀ (n * r))) := by
      refine isFiniteMeasure_restrict.mpr ?_
      exact ne_of_lt measure_ball_lt_top
    rw [← measure_mul_laverage]
    simp only [defaultA, MeasurableSet.univ, Measure.restrict_apply, univ_inter, mul_comm]

  have estimate_10_1_2 : (∫⁻ (y : X) in bxrc ∩ bx2r, ‖ K x y * g y‖ₑ)
      ≤ 2 ^ (a ^ 3 + a) * globalMaximalFunction volume 1 g x := by
    simp only [enorm_mul]

    trans ∫⁻ (y : X) in bxrc ∩ bx2r, ENNReal.ofReal (C_K ↑a) / volume (ball x r) * ‖g y‖ₑ
    . apply lintegral_mono_fn
      -- I think a general lemma is missing to make this work on bxrc ∩ bx2r instead of X
      -- Then pointwise_1 with x₀ = x proves it
      sorry

    rw [lintegral_const_mul] -- LHS = 10.1.5
    case hf => apply Measurable.enorm; exact hmg

    trans ENNReal.ofReal (C_K ↑a) / volume (ball x r) * (globalMaximalFunction volume 1 g x * volume (ball x (2 * r)))
    . apply mul_le_mul
      case h₁ => rfl
      case c0 | b0 => simp only [zero_le]

      trans ∫⁻ (a : X) in bx2r, ‖g a‖ₑ
      . apply lintegral_mono_set
        exact inter_subset_right

      rw [tmp5]
      apply mul_le_mul
      case h₂ => rfl
      case c0 =>
        apply le_of_lt
        apply measure_ball_pos
        exact mul_pos zero_lt_two hr
      case b0 => simp only [zero_le]

      conv in ‖ _ ‖ₑ =>
        rw [enorm_eq_nnnorm]
      apply laverage_le_globalMaximalFunction -- Should this be rewritten to ‖ ‖ₑ instead?
      rw [dist_self]
      exact mul_pos zero_lt_two hr

    calc _
      _ = ENNReal.ofReal (C_K ↑a) / volume (ball x r) * volume (ball x (2 * r)) * globalMaximalFunction volume 1 g x := by rw [mul_assoc]; nth_rw 2 [mul_comm]

    apply mul_le_mul
    case h₂ => rfl
    case c0 | b0 => simp only [zero_le]

    trans ENNReal.ofReal (C_K ↑a) / volume (ball x r) * (defaultA a * volume (ball x r))
    . apply mul_le_mul
      case h₁ => rfl
      case h₂ => apply measure_ball_two_le_same
      case c0 | b0 => simp only [zero_le]

    -- Somehow simp doesn't do it
    nth_rw 2 [mul_comm]
    rw [← mul_assoc, div_eq_mul_inv]
    nth_rw 2 [mul_assoc]
    conv =>
      lhs; arg 1; arg 2
      rw [mul_comm]
      apply ENNReal.mul_inv_cancel
      . apply ne_of_gt
        apply measure_ball_pos
        exact hr
      . apply ne_of_lt
        apply measure_ball_lt_top

    simp only [mul_one, C_K, defaultA]
    norm_cast
    rw [pow_add]

  have estimate_10_1_3 : ‖ ∫ (y : X) in bx2rᶜ, K x y * g y - K x' y * g y‖ₑ
      ≤ 2 ^ (a ^ 3 + 2 * a) * globalMaximalFunction volume 1 g x := by
    sorry

  have estimate_10_1_4 : (∫⁻ (y : X) in bxprc ∩ bx2r, ‖ K x' y * g y‖ₑ)
      ≤ 2 ^ (a ^ 3 + 2 * a) * globalMaximalFunction volume 1 g x := by
    simp only [enorm_mul]

    trans ∫⁻ (y : X) in bxprc ∩ bx2r, ENNReal.ofReal (C_K ↑a) / volume (ball x' r) * ‖g y‖ₑ
    . apply lintegral_mono_fn
      -- I think a general lemma is missing to make this work on bxrc ∩ bx2r instead of X
      -- Then pointwise_1 with x₀ = x' proves it
      sorry

    rw [lintegral_const_mul] -- LHS = 10.1.5 but for x'
    case hf => apply Measurable.enorm; exact hmg

    trans ENNReal.ofReal (C_K ↑a) / volume (ball x' r) * (globalMaximalFunction volume 1 g x * volume (ball x' (4 * r)))
    . apply mul_le_mul
      case h₁ => rfl
      case c0 | b0 => simp only [zero_le]

      trans ∫⁻ (a : X) in ball x' (4 * r), ‖g a‖ₑ
      . apply lintegral_mono_set
        trans bx2r
        . exact inter_subset_right
        . apply ball_subset
          linarith

      rw [tmp5]
      apply mul_le_mul
      case h₂ => rfl
      case c0 =>
        apply le_of_lt
        apply measure_ball_pos
        exact mul_pos zero_lt_four hr
      case b0 => simp only [zero_le]

      conv in ‖ _ ‖ₑ =>
        rw [enorm_eq_nnnorm]
      apply laverage_le_globalMaximalFunction -- Should this be rewritten to ‖ ‖ₑ instead?
      linarith

    calc _
      _ = ENNReal.ofReal (C_K ↑a) / volume (ball x' r) * volume (ball x' (4 * r)) * globalMaximalFunction volume 1 g x := by rw [mul_assoc]; nth_rw 2 [mul_comm]

    apply mul_le_mul
    case h₂ => rfl
    case c0 | b0 => simp only [zero_le]

    trans ENNReal.ofReal (C_K ↑a) / volume (ball x' r) * ((defaultA a) ^ 2 * volume (ball x' r))
    . apply mul_le_mul
      case h₁ => rfl
      case h₂ => apply measure_ball_four_le_same'
      case c0 | b0 => simp only [zero_le]

    -- Somehow simp doesn't do it
    nth_rw 2 [mul_comm]
    rw [← mul_assoc, div_eq_mul_inv]
    nth_rw 2 [mul_assoc]
    conv =>
      lhs; arg 1; arg 2
      rw [mul_comm]
      apply ENNReal.mul_inv_cancel
      . apply ne_of_gt
        apply measure_ball_pos
        exact hr
      . apply ne_of_lt
        apply measure_ball_lt_top

    simp only [mul_one, C_K, defaultA]
    norm_cast
    apply le_of_eq
    ring

  trans (2 ^ (a ^ 3 + a) * globalMaximalFunction volume 1 g x) + (2 ^ (a ^ 3 + 2 * a) * globalMaximalFunction volume 1 g x) +
      (2 ^ (a ^ 3 + 2 * a) * globalMaximalFunction volume 1 g x)
  . refine add_le_add_three ?_ ?_ ?_
    . exact estimate_10_1_2
    . exact estimate_10_1_3
    . exact estimate_10_1_4

  conv =>
    lhs
    calc _
      -- I can't seem to figure out how to do this in ENNReal...
      _ = (2 ^ (a ^ 3 + a) + 2 ^ (a ^ 3 + 2 * a) + 2 ^ (a ^ 3 + 2 * a)) * globalMaximalFunction volume 1 g x := by sorry

  refine mul_le_mul' ?_ ?_
  swap
  . unfold globalMaximalFunction
    unfold defaultA
    norm_cast

  -- Now it is unavoidable to unfold C10_1_2
  with_unfolding_all simp only [C10_1_2]
  norm_cast

  -- Note: It is unclear to me which tactic can avoid this manual computation
  have tmp4 : 2 ^ (a ^ 3 + a) ≤ 2 ^ (a ^ 3 + 2 * a + 1) := by
    rw [Nat.pow_le_pow_iff_right]
    rw [Nat.add_assoc]
    rw [Nat.add_le_add_iff_left]
    refine Nat.le_add_right_of_le ?_
    refine Nat.le_mul_of_pos_left a ?_
    exact Nat.zero_lt_two
    exact Nat.one_lt_two

  trans 2 ^ (a ^ 3 + 2 * a + 1) + 2 ^ (a ^ 3 + 2 * a) + 2 ^ (a ^ 3 + 2 * a)
  . apply Nat.add_le_add_iff_right.mpr
    apply Nat.add_le_add_iff_right.mpr
    apply tmp4

  ring_nf
  rfl

/- Breakdown from PDF
  Expand def
x Split first domain in parts > set work
    part 1 r < d x y < 2r
    part 2 2r < d x y
x Split 2nd domain in parts > set work
    part 1 r < d x' y and r < d x y < 2r
    part 2 r < d x' y and 2r < d x y which is 2r < d x y by triangle ineq
x Split integrals accordingly (sum of disjoint) obtain 10.1.234

x 10.1.2 estimate
    Use def CZ kernel 1.0.14, def V, estimate 1/V by 1/B(x,r) 10.1.5
    Doubling measure, larger domain pos function 10.1.6, Mg + def of integral of unit 10.1.7

  10.1.4 estimate
    Use def CZ kernel 10.0.14, def V, estimate 1/V by 1/B(x',r)
    Doubling measure twice, larger domain pos function, Mg + def integral of unit 10.1.8

  10.1.3 estimate
    Use def CZ kernel 10.0.1 (check hyp) 10.1.9
    Split domain in infinite parts > set work 10.1.10
    Estimate term 1/V by 1/B(x,2^j r), d xx'/d xy by 1/2^j 10.1.11
    Doubling measure, larger domain pos function 10.1.12
    Mg + def integral of unit + sum factor 10.1.13
    Lemma 10.1.1 > 10.1.14

x Total = sum of estimates ? 2(a3 + a) + 2(a3+2a) + 2(a3+2a) le 2(a3+2a+2)
-/

/-- The constant used in `cotlar_control`. -/
irreducible_def C10_1_3 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 4 * a + 1)

/-- Lemma 10.1.3 -/
theorem cotlar_control (ha : 4 ≤ a)
    {g : X → ℂ} (hg : BoundedFiniteSupport g) (hr : r ∈ Ioc 0 R) (hx : dist x x' ≤ R / 4) :
    ‖czOperator K R g x‖ₑ ≤ ‖czOperator K r ((ball x (R / 2))ᶜ.indicator g) x'‖ₑ +
    C10_1_3 a * globalMaximalFunction volume 1 g x := by
  sorry

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
