import Carleson.ToMathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Carleson.ToMathlib.MeasureTheory.Integral.Lebesgue
import Carleson.TwoSidedCarleson.WeakCalderonZygmund

open MeasureTheory Set Bornology Function ENNReal Metric
open scoped NNReal

noncomputable section

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {τ C r R : ℝ} {q q' : ℝ≥0}
variable {F G : Set X}
variable {K : X → X → ℂ} {x x' : X} [IsTwoSidedKernel a K]

/-! ## Section 10.1 and Lemma 10.0.2 -/

variable (K) in
/-- The operator `T_*^r g(x)`, defined in (10.1.31), above Lemma 10.1.6. -/
def simpleNontangentialOperator (r : ℝ) (g : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (R > r) (x' ∈ ball x R), ‖czOperator K R g x'‖ₑ

/-- The constant used in `estimate_x_shift`. -/
irreducible_def C10_1_2 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 2 * a + 2)
-- exact estimate from proof: C_K * (defaultA + 2 * defaultA²) ≤ C10_1_2

lemma _laverage_mul_measure_ball {g : X → ℂ} {x₀ : X} {n : ℝ} :
    ∫⁻ (a : X) in ball x₀ (n * r), ‖g a‖ₑ = (⨍⁻ (a : X) in ball x₀ (n * r), ‖g a‖ₑ ∂volume) * volume (ball x₀ (n * r)) := by
  have : IsFiniteMeasure (volume.restrict (ball x₀ (n * r))) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  rw [← measure_mul_laverage]
  simp only [MeasurableSet.univ, Measure.restrict_apply, univ_inter, mul_comm]

lemma estimate_10_1_2 {g : X → ℂ} (hg : BoundedFiniteSupport g) (hr : 0 < r) :
    (∫⁻ (y : X) in (ball x r)ᶜ ∩ ball x (2*r), ‖K x y * g y‖ₑ) ≤
    2 ^ (a ^ 3 + a) * globalMaximalFunction volume 1 g x := by
  simp only [enorm_mul]

  trans ∫⁻ (y : X) in (ball x r)ᶜ ∩ ball x (2*r), C_K ↑a / volume (ball x r) * ‖g y‖ₑ
  · apply setLIntegral_mono_ae (by fun_prop) (.of_forall _)
    intro y
    trans y ∈ (ball x r)ᶜ
    · exact fun a ↦ mem_of_mem_inter_left a
    exact fun h ↦ mul_le_mul' (enorm_K_le_ball_complement h) (by rfl)

  rw [lintegral_const_mul'' _ hg.aemeasurable.restrict.enorm] -- LHS = 10.1.5

  trans C_K a / volume (ball x r) * (globalMaximalFunction volume 1 g x * volume (ball x (2 * r)))
  · gcongr
    trans ∫⁻ (a : X) in ball x (2*r), ‖g a‖ₑ
    · exact lintegral_mono_set inter_subset_right
    rw [_laverage_mul_measure_ball]
    gcongr
    apply laverage_le_globalMaximalFunction
    rw [dist_self]
    exact mul_pos zero_lt_two hr

  nth_rw 2 [mul_comm]
  rw [← mul_assoc]
  gcongr

  trans C_K a / volume (ball x r) * (defaultA a * volume (ball x r))
  · gcongr
    apply measure_ball_two_le_same
  -- Somehow simp doesn't do it
  apply le_of_eq
  nth_rw 2 [mul_comm]
  rw [← mul_assoc, div_eq_mul_inv]
  nth_rw 2 [mul_assoc]
  simp_rw [mul_comm, ENNReal.mul_inv_cancel (measure_ball_pos volume x hr).ne.symm measure_ball_lt_top.ne, C_K]
  norm_cast
  ring

lemma estimate_10_1_3 (ha : 4 ≤ a) {g : X → ℂ} (hg : BoundedFiniteSupport g) (hr : 0 < r) (hx : dist x x' ≤ r) :
    ‖∫ (y : X) in (ball x (2*r))ᶜ, K x y * g y - K x' y * g y‖ₑ ≤
    2 ^ (a ^ 3 + 2 * a) * globalMaximalFunction volume 1 g x := by
  simp_rw [← mul_sub_right_distrib]

  trans ∫⁻ (y : X) in (ball x (2*r))ᶜ, ‖(K x y - K x' y) * g y‖ₑ
  · apply enorm_integral_le_lintegral_enorm
  simp only [enorm_mul]

  trans ∫⁻ (y : X) in (ball x (2*r))ᶜ, ((edist x x' / edist x y) ^ (a : ℝ)⁻¹ * (C_K a / vol x y)) * ‖g y‖ₑ
  · apply setLIntegral_mono_ae (by fun_prop) (.of_forall _)
    intro y h
    refine mul_le_mul' (enorm_K_sub_le' ?_) (by rfl)
    trans 2 * r
    · gcongr
    rw [mem_compl_iff, mem_ball, dist_comm] at h
    exact le_of_not_gt h

  let dom_i (i : ℕ) := Annulus.co x (2 ^ (i + 1) * r) (2 ^ (i + 2) * r)
  have rw_dom : (ball x (2*r))ᶜ = ⋃ (i : ℕ) , dom_i i:= by
    rw [Annulus.iUnion_co_eq_ci]
    · have : 2 * r = 2 ^ (0 + 1) * r := by ring
      rw [this, Annulus.ci_eq]
    · intro n
      gcongr <;> simp
    · apply Filter.not_bddAbove_of_tendsto_atTop (l := Filter.atTop)
      apply Filter.tendsto_atTop_atTop_of_monotone
      · exact (pow_right_mono₀ Nat.one_le_ofNat).comp Order.succ_mono|>.mul_const (le_of_lt hr)
      intro b
      use Nat.ceil (b / r)
      rw [← div_le_iff₀ hr]
      trans (Nat.ceil (b / r) : ℝ)
      · apply Nat.le_ceil
      · norm_cast
        trans Nat.ceil (b / r) + 1
        · exact Nat.le_add_right ⌈b / r⌉₊ 1
        · exact le_of_lt (Nat.lt_pow_self (le_refl 2))

  trans ∑' (i : ℕ), ∫⁻ (y : X) in dom_i i, ((edist x x' / edist x y) ^ (a : ℝ)⁻¹ * (C_K a / vol x y)) * ‖g y‖ₑ
  · rw [rw_dom]
    apply lintegral_iUnion_le

  -- Writing negative powers as positive powers of 1/2 to enable working with i : ℕ instead of -i : ℤ
  trans ∑' (i : ℕ), 2 ^ (a ^ 3 + a) * (1 / (2 : ℝ≥0) ) ^ ((i + 1) * (a : ℝ)⁻¹) * globalMaximalFunction volume 1 g x
  · apply Summable.tsum_le_tsum
    case hf | hg => apply ENNReal.summable

    intro i
    have est_edist : ∀y ∈ dom_i i, (edist x x' / edist x y) ≤ (1 / (2 : ℝ≥0)) ^ (i + 1) := by
      unfold dom_i Annulus.co
      simp_rw [← Ico_def, mem_setOf]
      intro y hdist
      trans edist x x' / (2 ^ (i + 1) * r.toNNReal)
      · gcongr
        rw [edist_dist, ENNReal.le_ofReal_iff_toReal_le]
        case ha => norm_cast; apply coe_ne_top
        case hb => exact dist_nonneg
        simp_rw [toReal_mul, toReal_pow, toReal_ofNat, coe_toReal, Real.coe_toNNReal', max_eq_left hr.le, hdist.left]
      rw [ENNReal.div_le_iff_le_mul]
      case hb0 => right; apply pow_ne_top; simp
      case hbt => left; exact (mul_ne_top (pow_ne_top ofNat_ne_top) coe_ne_top)
      rw [← mul_assoc, pow_mul_pow_eq_one]
      case a =>
        simp only [coe_ofNat, one_div]
        apply ENNReal.inv_mul_cancel <;> simp
      simp only [one_mul, edist_le_coe, nndist_dist]
      exact Real.toNNReal_le_toNNReal hx

    have est_vol : ∀y ∈ dom_i i, vol x y ≥ volume (ball x (2 ^ (i + 1) * r)) := by
      unfold dom_i Annulus.co
      simp_rw [← Ico_def, mem_setOf]
      apply fun y h ↦ measure_mono (ball_subset_ball h.left)

    trans ∫⁻ (y : X) in dom_i i, (1 / (2 : ℝ≥0)) ^ ((i + 1) * (a : ℝ)⁻¹) * (C_K a / volume (ball x (2 ^ (i + 1) * r))) * ‖g y‖ₑ
    · apply setLIntegral_mono_ae (by fun_prop) (.of_forall _)
      intro y hy
      gcongr
      · rw [rpow_mul]
        apply rpow_le_rpow _ (by positivity)
        · norm_cast
          exact est_edist y hy
      · exact est_vol y hy

    rw [lintegral_const_mul'' _ hg.aemeasurable.restrict.enorm]

    trans (1 / (2 : ℝ≥0)) ^ ((i + 1) * (a : ℝ)⁻¹) * (C_K ↑a / volume (ball x (2 ^ (i + 1) * r))) *
        ∫⁻ (y : X) in ball x (2 ^ (i + 2) * r), ‖g y‖ₑ
    · gcongr
      apply lintegral_mono_set
      unfold dom_i
      rw [Annulus.co_eq]
      exact inter_subset_left

    rw [_laverage_mul_measure_ball]
    nth_rw 5 [mul_comm]
    rw [← mul_assoc]
    trans (1 / (2 : ℝ≥0)) ^ ((i + 1) * (a : ℝ)⁻¹) * (C_K ↑a / volume (ball x (2 ^ (i + 1) * r))) *
        volume (ball x (2 ^ (i + 2) * r)) * globalMaximalFunction volume 1 g x
    · apply mul_le_mul'
      case h₁ => rfl
      apply laverage_le_globalMaximalFunction
      simp only [dist_self, Nat.ofNat_pos, pow_pos, mul_pos_iff_of_pos_left, hr]

    apply mul_le_mul' _ (by rfl)
    rw [mul_assoc, mul_comm]
    apply mul_le_mul' _ (by rfl)

    trans C_K a / volume (ball x (2 ^ (i + 1) * r)) * (defaultA a * volume (ball x (2 ^ (i + 1) * r)))
    · gcongr
      rw [pow_succ]
      nth_rw 2 [mul_comm]
      rw [mul_assoc]
      apply measure_ball_two_le_same

    apply le_of_eq
    rw [div_eq_mul_inv]
    nth_rw 4 [mul_comm]
    rw [mul_assoc]
    nth_rw 2 [← mul_assoc]
    nth_rw 3 [mul_comm]
    rw [ENNReal.mul_inv_cancel (measure_ball_pos volume x (by positivity)).ne.symm measure_ball_lt_top.ne]
    simp_rw [C_K, defaultA, one_mul, pow_add]
    norm_cast

  have : (2 : ℝ≥0∞) ^ (a ^ 3 + 2 * a) = 2 ^ (a ^ 3 + a) * 2 ^ a := by ring
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, this]
  gcongr
  simp_rw [coe_ofNat, one_div, inv_rpow, ← rpow_neg, ← div_eq_mul_inv]

  trans ∑' (i : ℕ), 2 ^ (-i / (a : ℝ))
  · apply Summable.tsum_le_tsum
    case hf | hg => apply ENNReal.summable
    intro i
    apply rpow_le_rpow_of_exponent_le Nat.one_le_ofNat
    rw [neg_div, neg_le_neg_iff, div_le_div_iff_of_pos_right (by positivity)]
    simp only [le_add_iff_nonneg_right, zero_le_one]
  rw [← rpow_natCast]
  exact geometric_series_estimate (by norm_cast; omega)

lemma estimate_10_1_4 {g : X → ℂ} (hg : BoundedFiniteSupport g) (hr : 0 < r) (hx : dist x x' ≤ r) :
    (∫⁻ (y : X) in (ball x' r)ᶜ ∩ ball x (2*r), ‖K x' y * g y‖ₑ) ≤
    2 ^ (a ^ 3 + 2 * a) * globalMaximalFunction volume 1 g x := by
  simp only [enorm_mul]

  trans ∫⁻ (y : X) in (ball x' r)ᶜ ∩ ball x (2 * r), C_K a / volume (ball x' r) * ‖g y‖ₑ
  · apply setLIntegral_mono_ae (by fun_prop) (.of_forall _)
    intro x
    trans x ∈ (ball x' r)ᶜ
    · exact fun a ↦ mem_of_mem_inter_left a
    exact fun h ↦ mul_le_mul' (enorm_K_le_ball_complement h) (by rfl)

  rw [lintegral_const_mul'' _ hg.aemeasurable.restrict.enorm] -- LHS = 10.1.5 but for x'

  trans C_K ↑a / volume (ball x' r) * (globalMaximalFunction volume 1 g x * volume (ball x' (4 * r)))
  · apply mul_le_mul' le_rfl
    trans ∫⁻ (a : X) in ball x' (4 * r), ‖g a‖ₑ
    · apply lintegral_mono_set
      trans ball x (2 * r)
      · exact inter_subset_right
      · exact ball_subset (by linarith)
    rw [_laverage_mul_measure_ball]
    apply mul_le_mul' ?_ le_rfl
    exact laverage_le_globalMaximalFunction (by linarith)

  nth_rw 2 [mul_comm]
  rw [← mul_assoc]

  apply mul_le_mul' ?_ le_rfl
  trans C_K ↑a / volume (ball x' r) * ((defaultA a) ^ 2 * volume (ball x' r))
  · exact mul_le_mul' le_rfl (measure_ball_four_le_same _ _)

  -- Somehow simp doesn't do it
  apply le_of_eq
  nth_rw 2 [mul_comm]
  rw [← mul_assoc, div_eq_mul_inv]
  nth_rw 2 [mul_assoc]
  simp_rw [mul_comm, ENNReal.mul_inv_cancel (measure_ball_pos volume x' hr).ne.symm measure_ball_lt_top.ne, C_K]
  norm_cast
  ring

/-- Lemma 10.1.2 -/
theorem estimate_x_shift (ha : 4 ≤ a)
    {g : X → ℂ} (hg : BoundedFiniteSupport g) (hr : 0 < r) (hx : dist x x' ≤ r) :
    edist (czOperator K r g x) (czOperator K r g x') ≤
    C10_1_2 a * globalMaximalFunction volume 1 g x := by
  let bxrc := (ball x r)ᶜ
  let bx2r := ball x (2*r)
  let bxprc := (ball x' r)ᶜ

  -- Domain split x integral
  have dom_x : bxrc = (bxrc ∩ bx2r) ∪ bx2rᶜ := by
    conv_lhs =>
      rw [← inter_univ bxrc, ← union_compl_self bx2r, inter_union_distrib_left]
    congr
    symm
    rw [right_eq_inter, compl_subset_compl]
    exact ball_subset_ball (by linarith)

  have ball2_sub_ballprime : bx2rᶜ ⊆ bxprc := by
    rw [compl_subset_compl]
    apply ball_subset
    rw [dist_comm]
    apply hx.trans
    linarith

  -- Domain split x' integral
  have dom_x_prime : bxprc = (bxprc ∩ bx2r) ∪ bx2rᶜ := by
    rw [right_eq_inter.mpr ball2_sub_ballprime]
    exact (inter_union_compl bxprc bx2r).symm

  -- Integral split x
  have integral_x : czOperator K r g x = (∫ y in (bxrc ∩ bx2r), K x y * g y) + (∫ y in bx2rᶜ, K x y * g y) := by
    calc czOperator K r g x
      _ = (∫ y in bxrc, K x y * g y) := by rfl
      _ = (∫ y in (bxrc ∩ bx2r) ∪ bx2rᶜ , K x y * g y) := by nth_rw 1 [dom_x]

    apply setIntegral_union_2
    · rw [disjoint_compl_right_iff_subset]
      exact inter_subset_right
    · exact measurableSet_ball.compl
    · rw [← dom_x]
      apply czoperator_welldefined hg hr

  -- Integral split x'
  have integral_x_prime : czOperator K r g x' = (∫ y in (bxprc ∩ bx2r), K x' y * g y) + (∫ y in bx2rᶜ, K x' y * g y) := by
    calc czOperator K r g x'
      _ = (∫ y in bxprc, K x' y * g y) := by rfl
      _ = (∫ y in (bxprc ∩ bx2r) ∪ bx2rᶜ , K x' y * g y) := by nth_rw 1 [dom_x_prime]

    refine setIntegral_union_2 ?_ measurableSet_ball.compl ?_
    · rw [disjoint_compl_right_iff_subset]
      exact inter_subset_right
    · rw [← dom_x_prime]
      exact czoperator_welldefined hg hr ..

  rw [edist_eq_enorm_sub, integral_x, integral_x_prime]

  -- Rewrite lhs according to 10.1.234 split
  conv =>
    lhs; arg 1
    calc _
      _ = (∫ (y : X) in bxrc ∩ bx2r, K x y * g y)
                + ((∫ (y : X) in bx2rᶜ, K x y * g y) - (∫ (y : X) in bx2rᶜ, K x' y * g y))
                - (∫ (y : X) in bxprc ∩ bx2r, K x' y * g y) := by ring
      _ = (∫ (y : X) in bxrc ∩ bx2r, K x y * g y)
                + (∫ (y : X) in bx2rᶜ, K x y * g y - K x' y * g y)
                - (∫ (y : X) in bxprc ∩ bx2r, K x' y * g y) := by
          rw[← integral_sub]
          · apply czoperator_welldefined hg (mul_pos zero_lt_two hr)
          · apply IntegrableOn.mono_set (hst := ball2_sub_ballprime)
            apply czoperator_welldefined hg hr

  apply enorm_sub_le.trans
  trans ‖∫ (y : X) in bxrc ∩ bx2r, K x y * g y‖ₑ + ‖∫ (y : X) in bx2rᶜ, K x y * g y - K x' y * g y‖ₑ +
      ‖∫ (y : X) in bxprc ∩ bx2r, K x' y * g y‖ₑ
  · gcongr
    apply enorm_add_le
  trans (∫⁻ (y : X) in bxrc ∩ bx2r, ‖K x y * g y‖ₑ) + ‖∫ (y : X) in bx2rᶜ, K x y * g y - K x' y * g y‖ₑ +
      ∫⁻ (y : X) in bxprc ∩ bx2r, ‖K x' y * g y‖ₑ
  · refine add_le_add_three ?_ (by rfl) ?_ <;> apply enorm_integral_le_lintegral_enorm
  -- LHS is now 10.1.234, apply respective estimates
  trans (2 ^ (a ^ 3 + a) * globalMaximalFunction volume 1 g x) + (2 ^ (a ^ 3 + 2 * a) * globalMaximalFunction volume 1 g x) +
      (2 ^ (a ^ 3 + 2 * a) * globalMaximalFunction volume 1 g x)
  · exact add_le_add_three (estimate_10_1_2 hg hr) (estimate_10_1_3 ha hg hr hx)
      (estimate_10_1_4 hg hr hx)
  rw [← distrib_three_right]
  gcongr
  -- Now it is unavoidable to unfold C10_1_2
  with_unfolding_all simp only [C10_1_2]
  norm_cast
  trans 2 ^ (a ^ 3 + 2 * a + 1) + 2 ^ (a ^ 3 + 2 * a) + 2 ^ (a ^ 3 + 2 * a)
  · apply Nat.add_le_add_iff_right.mpr
    apply Nat.add_le_add_iff_right.mpr
    rw [Nat.pow_le_pow_iff_right (h := Nat.one_lt_two)]
    linarith
  apply le_of_eq
  ring

/-- The constant used in `cotlar_control`. -/
irreducible_def C10_1_3 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 4 * a + 1)

lemma radius_change {g : X → ℂ} (hg : BoundedFiniteSupport g volume)
  (hr : r ∈ Ioc 0 R) (hx : dist x x' ≤ R / 4) :
    ‖czOperator K r ((ball x (R / 2))ᶜ.indicator g) x' - czOperator K R ((ball x (R / 2))ᶜ.indicator g) x'‖ₑ ≤
      2 ^ (a ^ 3 + 4 * a) * globalMaximalFunction volume 1 g x := by
  have R_pos : 0 < R := by
    rw [mem_Ioc] at hr
    linarith
  unfold czOperator
  rw [← integral_indicator (by measurability), ← integral_indicator (by measurability), ← integral_sub]
  rotate_left
  · rw [integrable_indicator_iff (by measurability)]
    apply czoperator_welldefined
    · apply BoundedFiniteSupport.indicator hg (by measurability)
    · rw [mem_Ioc] at hr; exact hr.1
  · rw [integrable_indicator_iff (by measurability)]
    apply czoperator_welldefined _ R_pos
    apply BoundedFiniteSupport.indicator hg (by measurability)
  calc _
    _ = ‖∫ (y : X), ((ball x' R) \ (ball x' r ∪ ball x (R / 2))).indicator (fun y ↦ K x' y * g y) y‖ₑ := by
      congr
      ext y
      unfold indicator
      split <;> split <;> split <;> rename_i yx'r yx'R hy
      · exfalso
        exact yx'R hy.1
      · simp
      · simp only [mem_compl_iff, mem_ball, not_lt, mul_ite, mul_zero, sub_zero, ite_eq_left_iff,
        not_le, zero_eq_mul]
        intro h
        exfalso
        simp at yx'r yx'R hy
        linarith
      · simp only [mem_compl_iff, mem_ball, not_lt, mul_ite, mul_zero, sub_zero, ite_eq_right_iff,
        mul_eq_zero]
        intro h
        exfalso
        simp only [mem_compl_iff, mem_ball, not_lt, not_le, mem_diff, mem_union, not_or,
          not_and] at yx'r yx'R hy
        linarith [hy yx'R yx'r]
      · simp only [mem_compl_iff, mem_ball, not_lt, not_le, mem_diff, mem_union,
        not_or] at yx'r yx'R hy
        linarith
      · simp only [mem_compl_iff, mem_ball, not_lt, mul_ite, mul_zero, zero_sub, neg_eq_zero,
        ite_eq_right_iff, mul_eq_zero]
        intro h
        exfalso
        simp at yx'r yx'R hy hr
        linarith
      · simp at yx'r yx'R hy
        linarith
      · ring
    _ ≤ ∫⁻ (y : X), ‖((ball x' R) \ (ball x' r ∪ ball x (R / 2))).indicator (fun y ↦ K x' y * g y) y‖ₑ := by
      apply enorm_integral_le_lintegral_enorm
    _ = ∫⁻ (y : X) in ((ball x' R) \ (ball x' r ∪ ball x (R / 2))), ‖K x' y‖ₑ * ‖g y‖ₑ := by
      rw [← lintegral_indicator]
      · congr with y
        rw[enorm_indicator_eq_indicator_enorm]
        congr with y
        apply enorm_mul
      measurability
    _ ≤ ∫⁻ (y : X) in ((ball x (2 * R)) \ (ball x' (R / 4))), ‖K x' y‖ₑ * ‖g y‖ₑ := by
      apply lintegral_mono_set
      intro y
      simp only [mem_diff, mem_ball, mem_union, not_or, not_lt, and_imp]
      intro h1 h2 h3
      simp at hr
      constructor <;>
      · rw [dist_comm] at hx
        linarith [dist_triangle y x' x]
    _ ≤ ∫⁻ (y : X) in ((ball x (2 * R)) \ (ball x' (R / 4))), (C_K a : ℝ≥0∞) / vol x' y * ‖g y‖ₑ := by
      gcongr with y
      apply enorm_K_le_vol_inv
    _ ≤ ∫⁻ (y : X) in ((ball x (2 * R)) \ (ball x' (R / 4))), (C_K a : ℝ≥0∞) / (volume (ball x' (R / 4))) * ‖g y‖ₑ := by
      apply lintegral_set_mono_fn (by measurability)
      intro y hy
      gcongr
      unfold vol
      apply measure_mono
      intro z hz
      simp only [mem_Ioc, mem_diff, mem_ball, not_lt] at *
      rw [dist_comm x' y]
      linarith
    _ = (C_K a : ℝ≥0∞) / (volume (ball x' (R / 4))) * ∫⁻ (y : X) in ((ball x (2 * R)) \ (ball x' (R / 4))), ‖g y‖ₑ := by
      apply lintegral_const_mul''
      apply AEMeasurable.enorm
      exact hg.aemeasurable.restrict
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
    _= 2 ^ (a ^ 3 + 4 * a) := by
      unfold C_K
      rw [← ENNReal.div_mul, mul_assoc, mul_comm (2 ^ (4 * a)), ← mul_assoc, ENNReal.div_mul_cancel]
      · norm_cast
        ring
      · apply (measure_ball_pos volume x (by linarith)).ne.symm
      · apply measure_ball_ne_top
      · simp
      · simp

omit [IsTwoSidedKernel a K] in
lemma cut_out_ball {g : X → ℂ}
  (hr : r ∈ Ioc 0 R) (hx : dist x x' ≤ R / 4) :
    czOperator K R g x' = czOperator K R ((ball x (R / 2))ᶜ.indicator g) x' := by
  have R_pos : 0 < R := by
    rw [mem_Ioc] at hr
    linarith
  unfold czOperator
  rw [← integral_indicator, ← integral_indicator]
  · congr
    apply indicator_eq_indicator'
    intro y hy
    rw [indicator_apply_eq_self.mpr]
    intro hy'
    exfalso
    simp at hy hy'
    have : dist y x' ≤ dist y x + dist x x' := by
      apply dist_triangle
    linarith
  · measurability
  · measurability

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
      · apply estimate_x_shift ha hg R_pos
        linarith
      · --triangle inequality as above
        rw [← edist_eq_enorm_sub, edist_comm, edist_eq_enorm_sub]
        apply le_trans _ (enorm_add_le _ _)
        apply le_of_eq
        congr
        ring
    _ ≤ C10_1_2 a * globalMaximalFunction volume 1 g x + 2 ^ (a ^ 3 + 4 * a) * globalMaximalFunction volume 1 g x + ‖czOperator K r ((ball x (R / 2))ᶜ.indicator g) x'‖ₑ := by
      rw [add_assoc]
      gcongr
      exact radius_change hg hr hx
    _ ≤ ‖czOperator K r ((ball x (R / 2))ᶜ.indicator g) x'‖ₑ + C10_1_3 a * globalMaximalFunction volume 1 g x := by
      rw [add_comm]
      gcongr
      rw [← add_mul]
      gcongr
      rw [C10_1_2_def, C10_1_3_def]
      norm_num
      calc (2 : ℝ≥0∞) ^ (a ^ 3 + 2 * a + 2) + 2 ^ (a ^ 3 + 4 * a)
        _ = (2 : ℝ≥0∞) ^ (a ^ 3 + (2 * a + 2)) + 2 ^ (a ^ 3 + 4 * a) := by
          congr 1
        _ ≤ 2 ^ (a ^ 3 + 4 * a) + 2 ^ (a ^ 3 + 4 * a) := by
          gcongr
          · exact one_le_two
          · linarith
        _ = 2 * 2 ^ (a ^ 3 + 4 * a) := (two_mul (2 ^ (a ^ 3 + 4 * a))).symm
        _ = 2 ^ (a ^ 3 + 4 * a + 1) := (pow_succ' 2 (a ^ 3 + 4 * a)).symm

/-- The constant used in `cotlar_set_F₂`. -/
irreducible_def C10_1_4 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 22 * a + 2)

lemma globalMaximalFunction_zero_enorm_ae_zero (hR : 0 < R) {f : X → ℂ} (hf : AEStronglyMeasurable f)
    (hMzero : globalMaximalFunction volume 1 f x = 0) :
    ∀ᵐ x' ∂(volume.restrict (ball x R)), ‖f x'‖ₑ = 0 := by
  change (fun x' ↦ ‖f x'‖ₑ) =ᶠ[ae (volume.restrict (ball x R))] 0
  rw [← lintegral_eq_zero_iff' (by fun_prop)]
  rw [← bot_eq_zero, ← le_bot_iff, bot_eq_zero]
  apply le_of_le_of_eq (lintegral_ball_le_volume_globalMaximalFunction _)
  · rw [hMzero]
    simp
  · simp [hR]

/-- Part 1 of Lemma 10.1.4 about `F₁`. -/
theorem cotlar_set_F₁ (hr : 0 < r) (hR : r ≤ R) {g : X → ℂ} (hg : BoundedFiniteSupport g) :
    volume.restrict (ball x (R / 4))
      {x' | 4 * globalMaximalFunction volume 1 (czOperator K r g) x < ‖czOperator K r g x'‖ₑ } ≤
    volume (ball x (R / 4)) / 4 := by
  let MTrgx := globalMaximalFunction volume 1 (czOperator K r g) x
  by_cases hMzero : MTrgx = 0
  · apply le_of_eq_of_le _ (zero_le _)
    rw [measure_zero_iff_ae_notMem]
    have czzero := globalMaximalFunction_zero_enorm_ae_zero (R := R / 4) (by simp [lt_of_lt_of_le hr hR]) (by fun_prop) hMzero
    filter_upwards [czzero] with x' hx'
    simp [hx']
  rw [← lintegral_indicator_one₀ (nullMeasurableSet_lt (by fun_prop) (by fun_prop))]
  by_cases hMinfty : MTrgx = ∞
  · unfold MTrgx at hMinfty
    simp_rw [hMinfty]
    simp
  rw [← ENNReal.mul_le_mul_right (by simp [hMzero]) (by finiteness) (c := 4 * MTrgx)]
  rw [← lintegral_mul_const' _ _ (by finiteness)]
  simp_rw [← indicator_mul_const, Pi.one_apply, one_mul]
  trans ∫⁻ (y : X) in ball x (R / 4),
      {x' | 4 * MTrgx < ‖czOperator K r g x'‖ₑ}.indicator (fun x_1 ↦ ‖czOperator K r g y‖ₑ ) y
  · apply lintegral_mono_fn
    intro y
    apply indicator_le_indicator'
    rw [mem_setOf_eq]
    exact le_of_lt
  trans ∫⁻ (y : X) in ball x (R / 4), ‖czOperator K r g y‖ₑ
  · apply lintegral_mono_fn
    intro y
    apply indicator_le_self
  nth_rw 2 [div_eq_mul_inv]
  rw [mul_assoc]
  nth_rw 2 [← mul_assoc]
  rw [ENNReal.inv_mul_cancel (by simp) (by simp)]
  simp only [one_mul, MTrgx]
  apply lintegral_ball_le_volume_globalMaximalFunction
  simp [(lt_of_lt_of_le hr hR)]

/-- Part 2 of Lemma 10.1.4 about `F₂`. -/
theorem cotlar_set_F₂ (ha : 4 ≤ a) (hr : 0 < r) (hR : r ≤ R)
    (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a))
    {g : X → ℂ} (hg : BoundedFiniteSupport g) :
    volume.restrict (ball x (R / 4))
      {x' | C10_1_4 a * globalMaximalFunction volume 1 g x <
      ‖czOperator K r ((ball x (R / 2)).indicator g) x'‖ₑ } ≤
    volume (ball x (R / 4)) / 4 := by
  by_cases hMzero : globalMaximalFunction volume 1 g x = 0
  · apply le_of_eq_of_le _ (zero_le _)
    rw [measure_zero_iff_ae_notMem]
    have gzero := globalMaximalFunction_zero_enorm_ae_zero (R := R / 2)
        (by simp [lt_of_lt_of_le hr hR]) hg.aestronglyMeasurable hMzero
    have czzero : ∀ᵐ x' ∂(volume.restrict (ball x (R / 4))), ‖czOperator K r ((ball x (R / 2)).indicator g) x'‖ₑ = 0 := by
      simp_rw [← bot_eq_zero, ← le_bot_iff]
      apply Filter.Eventually.mono (.of_forall _) (fun x ↦ (enorm_integral_le_lintegral_enorm _).trans)
      intro x'
      rw [le_bot_iff, bot_eq_zero, lintegral_eq_zero_iff' ?hf_ae]
      case hf_ae =>
        apply (AEMeasurable.enorm _).restrict
        apply AEMeasurable.mul (measurable_K_right x').aemeasurable
        exact AEMeasurable.indicator (hg.aemeasurable) measurableSet_ball
      simp_rw [← indicator_mul_right, enorm_indicator_eq_indicator_enorm]
      rw [indicator_ae_eq_zero, inter_comm, ← Measure.restrict_apply' measurableSet_ball,
        Measure.restrict_restrict measurableSet_ball, ← bot_eq_zero, ← le_bot_iff]
      apply le_trans (Measure.restrict_mono_set (t := ball x (R / 2)) volume inter_subset_left _)
      rw [le_bot_iff, bot_eq_zero, ← compl_compl (support _), ← mem_ae_iff]
      filter_upwards [gzero] with y hy
      simp [hy]
    filter_upwards [czzero] with x' hx'
    simp [hx']
  by_cases hMinfty : globalMaximalFunction volume 1 g x = ∞
  · simp_rw [hMinfty, C10_1_4_def]
    simp
  apply (Measure.restrict_le_self _).trans
  let g1 := (ball x (R / 2)).indicator g
  have bfs_g1 : BoundedFiniteSupport g1 := hg.indicator measurableSet_ball
  have czw11 := czoperator_weak_1_1 ha hr (hT r hr)
  unfold HasBoundedWeakType at czw11
  have := (czw11 (f := g1) bfs_g1).2
  unfold wnorm wnorm' distribution at this
  simp_rw [one_ne_top, reduceIte, toReal_one, inv_one, rpow_one,
    iSup_le_iff] at this
  have := this (C10_1_4 a * (globalMaximalFunction volume 1 g x).toNNReal)
  have constants : C10_1_4 a = C10_0_3 a * (2 ^ (a + 2)) := by rw [C10_1_4_def, C10_0_3_def]; ring
  nth_rw 1 [constants] at this
  rw [coe_mul, coe_mul, coe_mul] at this --push_cast unfolds defaultA which is cumbersome
  rw [mul_assoc, mul_assoc, ENNReal.mul_le_mul_left (by rw [C10_0_3_def]; positivity) coe_ne_top,
    ← mul_assoc, mul_comm, ENNReal.coe_toNNReal hMinfty,
    ← ENNReal.le_div_iff_mul_le ?ne_z ?ne_t] at this
  case ne_z => left; exact mul_ne_zero (by simp) hMzero --again due to defaultA behaviour
  case ne_t => left; exact mul_ne_top coe_ne_top hMinfty
  apply this.trans
  rw [ENNReal.div_le_iff_le_mul ?ne_z ?ne_t]
  case ne_z => left; exact mul_ne_zero (by simp) hMzero --defaultA behaviour
  case ne_t => left; exact mul_ne_top coe_ne_top hMinfty
  unfold g1
  simp_rw [eLpNorm_one_eq_lintegral_enorm, enorm_indicator_eq_indicator_enorm,
    lintegral_indicator measurableSet_ball]
  apply (lintegral_ball_le_volume_globalMaximalFunction (z := x) (x := x) (by simp [lt_of_lt_of_le hr hR])).trans
  rw [← mul_assoc]
  gcongr
  have : volume (ball x (R / 2)) ≤ defaultA a * volume (ball x (R / 4)) := by
    let tmp : R / 2 = 2 * (R / 4) := by ring
    rw [tmp]
    apply measure_ball_two_le_same
  apply this.trans (le_of_eq _)
  push_cast
  nth_rw 2 [div_eq_mul_inv]
  rw [mul_assoc, mul_comm]
  congr
  ring_nf
  rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

/-- The constant used in `cotlar_estimate`. -/
irreducible_def C10_1_5 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 22 * a + 3)

/-- Lemma 10.1.5 -/
theorem cotlar_estimate (ha : 4 ≤ a)
    (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a))
    {g : X → ℂ} (hg : BoundedFiniteSupport g) (hr : r ∈ Ioc 0 R) :
    ‖czOperator K R g x‖ₑ ≤ 4 * globalMaximalFunction volume 1 (czOperator K r g) x +
      C10_1_5 a * globalMaximalFunction volume 1 g x := by
  let F1 : Set X := {x' | 4 * globalMaximalFunction volume 1 (czOperator K r g) x < ‖czOperator K r g x'‖ₑ}
  let F2 : Set X := {x' | ↑(C10_1_4 a) * globalMaximalFunction volume 1 g x < ‖czOperator K r ((ball x (R / 2)).indicator g) x'‖ₑ}
  let noF : Set X := (F1 ∪ F2)ᶜ ∩ ball x (R / 4)
  have vF1F2 : volume.restrict (ball x (R / 4)) (F1 ∪ F2) ≤ volume (ball x (R / 4)) / 2 := by
    apply le_trans (measure_union_le F1 F2)
    have vF1 := cotlar_set_F₁ (K := K) (x := x) hr.1 hr.2 hg
    have vF2 := cotlar_set_F₂ (K := K) (x := x) ha hr.1 hr.2 hT hg
    unfold F1 F2
    apply le_of_le_of_eq (add_le_add vF1 vF2)
    rw [← mul_two, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
    congr
    apply ENNReal.eq_inv_of_mul_eq_one_left
    have : (2 : ℝ≥0∞) * 2 = 4 := by ring
    rw [mul_assoc, this, ENNReal.inv_mul_cancel (by simp) (by simp)]
  have : noF.Nonempty := by
    apply nonempty_of_measure_ne_zero (μ := volume)
    intro hnoF
    have : (2 : ℝ≥0∞) ≤ 1 := by
      rw [← ENNReal.mul_le_mul_left (a := volume (ball x (R / 4))) ?ne_z (by finiteness), mul_one]
      case ne_z => apply ne_of_gt; apply measure_ball_pos; linarith [lt_of_lt_of_le hr.1 hr.2]
      have := measure_univ_le_add_compl (μ := volume.restrict (ball x (R / 4))) (s := F1 ∪ F2)
      nth_rw 3 [Measure.restrict_apply' measurableSet_ball] at this
      rw [hnoF, add_zero, Measure.restrict_apply_univ] at this
      exact (ENNReal.le_div_iff_mul_le (by simp) (by simp)).mp (this.trans vF1F2)
    exact Nat.not_ofNat_le_one this
  obtain ⟨x', hx'⟩ := this
  have hxx' := mem_ball.mp hx'.2
  rw [dist_comm] at hxx'
  apply cotlar_control ha hg hr hxx'.le |> le_trans
  rw [indicator_compl, czoperator_sub hg (hg.indicator measurableSet_ball) hr.1, Pi.sub_apply]
  have h1x' : ‖czOperator K r g x'‖ₑ ≤ 4 * globalMaximalFunction volume 1 (czOperator K r g) x := by
    suffices x' ∉ F1 by
      rw [notMem_setOf_iff, not_lt] at this
      exact this
    exact notMem_subset subset_union_left ((mem_compl_iff _ _).mp hx'.1)
  have h2x' : ‖czOperator K r ((ball x (R / 2)).indicator g) x'‖ₑ ≤ C10_1_4 a * globalMaximalFunction volume 1 g x := by
    suffices x' ∉ F2 by
      rw [notMem_setOf_iff, not_lt] at this
      exact this
    exact notMem_subset subset_union_right ((mem_compl_iff _ _).mp hx'.1)
  apply add_le_add (add_le_add h1x' h2x' |> enorm_sub_le.trans) (by rfl) |> le_trans
  rw [add_assoc, C10_1_3_def, C10_1_4_def, C10_1_5_def, ← add_mul]
  conv_rhs => rw [pow_succ, mul_two]
  push_cast
  gcongr <;> simp


omit [IsTwoSidedKernel a K] in
/-- Part of Lemma 10.1.6. -/
lemma lowerSemicontinuous_simpleNontangentialOperator {g : X → ℂ} :
    LowerSemicontinuous (simpleNontangentialOperator K r g) := by
  unfold simpleNontangentialOperator
  simp_rw [lowerSemicontinuous_iff_isOpen_preimage, preimage, mem_Ioi, lt_iSup_iff, ← iUnion_setOf,
    mem_ball_comm, exists_prop]
  intro y
  apply isOpen_iUnion; intro R
  apply isOpen_iUnion; intro hR
  apply isOpen_iUnion; intro x'
  by_cases hx' : y < ‖czOperator K R g x'‖ₑ
  · simp_rw [hx', and_true, setOf_mem_eq, isOpen_ball]
  · simp [hx']

omit [IsTwoSidedKernel a K] in
lemma aestronglyMeasurable_simpleNontangentialOperator {g : X → ℂ} :
    AEStronglyMeasurable (simpleNontangentialOperator K r g) volume :=
  lowerSemicontinuous_simpleNontangentialOperator |>.measurable.aestronglyMeasurable

/-- The constant used in `simple_nontangential_operator`.
It is not tight and can be improved by some `a` + `constant`. -/
irreducible_def C10_1_6 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 26 * a + 6)

/-- Lemma 10.1.6. The formal statement includes the measurability of the operator.
See also `simple_nontangential_operator_le` -/
theorem simple_nontangential_operator (ha : 4 ≤ a)
    (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a)) (hr : 0 < r) :
    HasBoundedStrongType (simpleNontangentialOperator K r) 2 2 volume volume (C10_1_6 a) := by
  intro g hg
  constructor
  · exact aestronglyMeasurable_simpleNontangentialOperator
  let pointwise : X → ℝ≥0∞ :=
    4 * globalMaximalFunction volume 1 (czOperator K r g) + C10_1_5 a • globalMaximalFunction volume 1 g +
    C10_1_2 a • globalMaximalFunction volume 1 g
  trans eLpNorm pointwise 2 volume
  · apply eLpNorm_mono_enorm
    simp_rw [enorm_eq_self, simpleNontangentialOperator, iSup_le_iff]
    intro x R hR x' hx'
    rw [mem_ball, dist_comm] at hx'
    trans ‖czOperator K R g x‖ₑ + C10_1_2 a * globalMaximalFunction volume 1 g x
    · calc ‖czOperator K R g x'‖ₑ
        _ = ‖czOperator K R g x + (czOperator K R g x' - czOperator K R g x)‖ₑ := by congr; ring
      apply le_trans <| enorm_add_le _ _
      gcongr
      rw [← edist_eq_enorm_sub, edist_comm]
      exact estimate_x_shift ha hg (hr.trans hR.lt) hx'.le
    apply add_le_add (cotlar_estimate ha hT hg ?hrR) (by rfl)
    case hrR => rw [mem_Ioc]; exact ⟨hr, hR.le⟩
  unfold pointwise

  have hst_gmf := hasStrongType_globalMaximalFunction (p₁ := 1) (p₂ := 2) (X := X) (E := ℂ) (μ := volume) zero_lt_one one_lt_two
  norm_cast at hst_gmf
  have hst_gmf_g := hst_gmf g (hg.memLp 2)
  have aesm_gmf_g := hst_gmf_g.1 -- for fun_prop
  have hst_gmf_czg := hst_gmf (czOperator K r g) ((hT r hr).memLp hg)
  have aesm_gmf_czg := hst_gmf_czg.1 -- for fun_prop
  rw [show 4 * globalMaximalFunction volume 1 (czOperator K r g) =
      (4 : ℝ≥0) • globalMaximalFunction volume 1 (czOperator K r g) by rfl]
  apply le_trans <| eLpNorm_add_le (by fun_prop) (by fun_prop) one_le_two
  apply le_trans <| add_le_add (eLpNorm_add_le (by fun_prop) (by fun_prop) one_le_two) (by rfl)
  simp_rw [eLpNorm_const_smul' (f := globalMaximalFunction volume 1 g),
      eLpNorm_const_smul' (f := globalMaximalFunction volume 1 (czOperator K r g)),
      enorm_NNReal, add_assoc, ← add_mul]
  apply le_trans <| add_le_add
    (mul_le_mul_left' (hst_gmf_czg.2.trans <| mul_le_mul_left' (hT r hr g hg).2 _) _)
    (mul_le_mul_left' hst_gmf_g.2 _)
  nth_rw 3 [← mul_assoc]; nth_rw 2 [← mul_assoc]; rw [← mul_assoc, ← add_mul]
  gcongr
  -- what remains is constant manipulation
  nth_rw 2 [mul_comm]; rw [← mul_assoc, ← add_mul]
  norm_cast
  have : C2_0_6' (defaultA a) 1 2 ≤ 2 ^ (4 * a + 1) := by
    rw [C2_0_6'_defaultA_one_two_eq, ← NNReal.rpow_natCast]
    apply NNReal.rpow_le_rpow_of_exponent_le one_le_two
    trans 3 * a + 2
    · linarith
    norm_cast
    linarith [ha]
  apply le_trans <| mul_le_mul_left' this _
  rw [C10_1_6_def, C_Ts, C10_1_5, C10_1_2]
  norm_cast
  rw [show a ^ 3 + 26 * a + 6 = (a ^ 3 + 22 * a + 5) + (4 * a + 1) by ring]; nth_rw 4 [pow_add]
  gcongr
  nth_rw 6 [pow_succ]; rw [mul_two]
  apply add_le_add
  · ring_nf; gcongr <;> simp [Nat.one_le_pow]
  nth_rw 5 [pow_succ]; rw [mul_two]
  gcongr <;> simp

-- TODO: this helper lemma may be useful in other places to, for instance in `HardyLittlewood.lean`
lemma iSup_rpow {f : ℕ → ℝ≥0∞} {p : ℝ} (hp : 0 < p) :
    (⨆ n, f n) ^ p = ⨆ n, f n ^ p := by
  apply le_antisymm
  · rw [← rpow_le_rpow_iff (z := p⁻¹) (by positivity), rpow_rpow_inv (by positivity)]
    refine iSup_le fun i ↦ ?_
    rw [← rpow_le_rpow_iff (z := p) (by positivity), rpow_inv_rpow (by positivity)]
    apply le_iSup _ i
  · apply iSup_le; intro i; gcongr; apply le_iSup _ i

theorem eLpNormEssSup_iSup {α : Type*} {ι : Type*} [Countable ι] [MeasurableSpace α]
    {μ : Measure α} (f : ι → α → ℝ≥0∞) :
    ⨆ n, eLpNormEssSup (f n) μ = eLpNormEssSup (⨆ n, f n) μ := by
  simp_rw [eLpNormEssSup, essSup_eq_sInf, enorm_eq_self]
  apply le_antisymm
  · refine iSup_le fun i ↦ le_sInf fun b hb ↦ sInf_le ?_
    simp only [iSup_apply, mem_setOf_eq] at hb ⊢
    exact nonpos_iff_eq_zero.mp <|le_of_le_of_eq
        (measure_mono fun ⦃x⦄ h ↦ lt_of_lt_of_le h (le_iSup (fun i ↦ f i x) i)) hb
  · apply sInf_le
    simp only [iSup_apply, mem_setOf_eq]
    apply nonpos_iff_eq_zero.mp
    calc
    _ ≤ μ (⋃ i, {x | ⨆ n, sInf {a | μ {x | a < f n x} = 0} < f i x}) := by
      refine measure_mono fun x hx ↦ mem_iUnion.mpr ?_
      simp only [mem_setOf_eq] at hx
      exact lt_iSup_iff.mp hx
    _ ≤ _ := measure_iUnion_le _
    _ ≤ ∑' i, μ {x | sInf {a | μ {x | a < f i x} = 0} < f i x} := by
      gcongr with i; apply le_iSup _ i
    _ ≤ ∑' i, μ {x | eLpNormEssSup (f i) μ < ‖f i x‖ₑ} := by
      gcongr with i; rw [eLpNormEssSup, essSup_eq_sInf]; rfl
    _ = ∑' i, 0 := by congr with i; exact meas_eLpNormEssSup_lt
    _ = 0 := by simp

/-- Monotone convergence applied to eLpNorms. AEMeasurable variant.
  Possibly imperfect hypotheses, particularly on `p`. Note that for `p = ∞` the stronger
  statement in `eLpNormEssSup_iSup` holds. -/
theorem eLpNorm_iSup' {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, AEMeasurable (f n) μ) (h_mono : ∀ᵐ x ∂μ, Monotone fun n => f n x) :
    ⨆ n, eLpNorm (f n) p μ = eLpNorm (⨆ n, f n) p μ := by
  unfold eLpNorm
  split_ifs with hp hp'
  · simp
  · apply eLpNormEssSup_iSup
  · unfold eLpNorm'
    have := toReal_pos hp hp'
    rw [← iSup_rpow (by positivity), ← lintegral_iSup']
    · congr 2 with a; rw [← iSup_rpow (by positivity)]; simp
    · fun_prop
    · filter_upwards [h_mono] with a ha m n hmn
      beta_reduce; gcongr; simp only [enorm_eq_self]; apply ha hmn

/-- This is the first step of the proof of Lemma 10.0.2, and should follow from 10.1.6 +
monotone convergence theorem. (measurability should be proven without any restriction on `r`.) -/
theorem simple_nontangential_operator_le (ha : 4 ≤ a)
    (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a)) (hr : 0 ≤ r) :
    HasBoundedStrongType (simpleNontangentialOperator K r) 2 2 volume volume (C10_1_6 a) := by
  by_cases h : 0 < r
  · exact simple_nontangential_operator ha hT h
  have : r = 0 := by linarith
  rw [this]
  intro g hg
  constructor
  · exact aestronglyMeasurable_simpleNontangentialOperator
  let f (n : ℕ) := simpleNontangentialOperator K (n + 1 : ℝ)⁻¹ g
  have f_mon (x : X): Monotone fun n ↦ f n x := by
    intro m n hmn; simp only
    unfold f simpleNontangentialOperator
    gcongr with R
    simp_rw [gt_iff_lt]
    apply iSup_const_mono (lt_of_le_of_lt _)
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    simp [hmn]
  have snt0 : ⨆ (n : ℕ), f n = simpleNontangentialOperator K 0 g := by
    ext x
    unfold f simpleNontangentialOperator
    simp_rw [gt_iff_lt, iSup_apply]; rw [iSup_comm]
    congr with R
    apply le_antisymm (iSup_le <| fun n ↦ iSup_const_mono (lt_trans (by positivity))) (iSup_le _)
    intro hR
    let n := Nat.ceil R⁻¹
    have hn : (n + 1 : ℝ)⁻¹ < R := inv_lt_of_inv_lt₀ hR <| Nat.le_ceil R⁻¹ |>.trans_lt (by linarith)
    let seq (n : ℕ) := ⨆ (_ : (n + 1 : ℝ)⁻¹ < R), ⨆ x' ∈ ball x R, ‖czOperator K R g x'‖ₑ
    have : ⨆ x' ∈ ball x R, ‖czOperator K R g x'‖ₑ = seq n := by unfold seq; rw [iSup_pos hn]
    nth_rw 1 [this]
    exact le_iSup seq n
  have mct := eLpNorm_iSup' (p := 2) (f := f) (μ := volume)
    (fun n ↦ aestronglyMeasurable_simpleNontangentialOperator.aemeasurable)
    (by filter_upwards; exact f_mon)
  rw [← snt0, ← mct]
  apply iSup_le
  intro n; unfold f
  apply simple_nontangential_operator ha hT (by positivity) g hg |>.2

/-- Part of Lemma 10.1.7, reformulated. -/
theorem small_annulus_right {g : X → ℂ} (hg : BoundedFiniteSupport g) {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) :
    ContinuousWithinAt (fun R₂ ↦ ∫ y in Annulus.oo x R₁ R₂, K x y * g y) (Ioo R₁ R₂) R₁ := by
  by_cases hR1R2 : R₁ < R₂
  case neg => rw [Ioo_eq_empty hR1R2, ContinuousWithinAt, nhdsWithin_empty]; exact Filter.tendsto_bot
  conv => arg 1; intro R; rw [← integral_indicator (by measurability)]
  obtain ⟨B, hB⟩ := czoperator_bound (K := K) (r := R₁) hg hR₁ x
  rw [ae_restrict_iff' (by measurability), ← Annulus.ci_eq] at hB
  let bound (y : X) : ℝ := (Annulus.oo x R₁ R₂).indicator (fun y ↦ B) y
  apply continuousWithinAt_of_dominated (bound := bound)
  · filter_upwards with R
    have : Measurable (K x) := measurable_K_right x
    fun_prop (disch := measurability)
  · unfold bound
    simp_rw [norm_indicator_eq_indicator_norm]
    have : nhdsWithin R₁ (Ioo R₁ R₂) |>.Eventually (fun r ↦ r < R₂) := by
      apply eventually_nhdsWithin_of_eventually_nhds
      apply eventually_nhds_iff_ball.mpr
      use R₂ - R₁
      constructor
      · simp [hR1R2]
      · intro r hr
        rw [mem_ball] at hr
        linarith [Real.sub_le_dist r R₁]
    filter_upwards [this] with r hr
    filter_upwards [hB] with y hy
    refine indicator_le_indicator_of_subset (Annulus.oo_subset_oo (by rfl) hr.le)
      (fun a ↦ by positivity) _ |>.trans <| indicator_le_indicator' ?_
    exact fun h2y ↦ hy <| Annulus.oo_subset_ci (by rfl) h2y
  · unfold bound
    rw [integrable_indicator_iff (by measurability), Annulus.oo_eq]
    apply integrableOn_const (measure_ne_top_of_subset inter_subset_left (by finiteness)) (by simp)
  · -- This is painful because we have to show continuity of the indicator
    -- which is needed to apply `dominated` because `R` is variable in the domain of the integral.
    -- This in turn meant proving continuity at `R₁`, which actually aligns with the blueprint.
    filter_upwards with y
    unfold ContinuousWithinAt
    have : nhdsWithin R₁ (Ioo R₁ R₂) |>.Eventually (fun r ↦ y ∉ Annulus.oo x R₁ r) := by
      by_cases hy : R₁ < dist x y
      · have : nhdsWithin R₁ (Ioo R₁ R₂) |>.Eventually (fun r ↦ r < dist x y) := by
          apply eventually_nhdsWithin_of_eventually_nhds
          apply eventually_nhds_iff_ball.mpr
          use (dist x y - R₁)
          constructor
          · simp [hy]
          · intro r hr
            rw [mem_ball] at hr
            linarith [Real.sub_le_dist r R₁]
        filter_upwards [this] with r hr
        exact fun hy ↦ hr.not_gt hy.2
      · filter_upwards with r; unfold Annulus.oo; rw [notMem_setOf_iff]; exact fun hy2 ↦ hy hy2.1
    rw [Filter.tendsto_iff_forall_eventually_mem]
    intro s hs
    filter_upwards [this] with r hr
    apply mem_of_mem_nhds
    simpa [indicator_of_notMem hr] using hs

/-- Part of Lemma 10.1.7, reformulated -/
theorem small_annulus_left {g : X → ℂ} (hg : BoundedFiniteSupport g) {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁):
    ContinuousWithinAt (fun R ↦ ∫ y in Annulus.oo x R R₂, K x y * g y) (Ioo R₁ R₂) R₂ := by
  by_cases hR1R2 : R₁ < R₂
  case neg => rw [Ioo_eq_empty hR1R2, ContinuousWithinAt, nhdsWithin_empty]; exact Filter.tendsto_bot
  conv => arg 1; intro R; rw [← integral_indicator (by measurability)]
  obtain ⟨B, hB⟩ := czoperator_bound (K := K) (r := R₂ / 2) hg (by linarith [hR₁.trans_lt hR1R2]) x
  rw [ae_restrict_iff' (by measurability), ← Annulus.ci_eq] at hB
  let bound (y : X) : ℝ := (Annulus.oo x (R₂ / 2) R₂).indicator (fun y ↦ B) y
  apply continuousWithinAt_of_dominated (bound := bound)
  · filter_upwards with R
    have : Measurable (K x) := measurable_K_right x
    fun_prop (disch := measurability)
  · unfold bound
    simp_rw [norm_indicator_eq_indicator_norm]
    have : nhdsWithin R₂ (Ioo R₁ R₂) |>.Eventually (fun r ↦ R₂ / 2 < r) := by
      apply eventually_nhdsWithin_of_eventually_nhds
      apply eventually_nhds_iff_ball.mpr
      use R₂ / 2
      constructor
      · simp [hR₁.trans_lt hR1R2]
      · intro r hr
        rw [mem_ball, dist_comm] at hr
        linarith [Real.sub_le_dist R₂ r]
    filter_upwards [this] with r hr
    filter_upwards [hB] with y hy
    refine indicator_le_indicator_of_subset (Annulus.oo_subset_oo hr.le (by rfl))
      (fun a ↦ by positivity) _ |>.trans <| indicator_le_indicator' ?_
    exact fun h2y ↦ hy <| Annulus.oo_subset_ci (by rfl) h2y
  · unfold bound
    rw [integrable_indicator_iff (by measurability), Annulus.oo_eq]
    apply integrableOn_const (measure_ne_top_of_subset inter_subset_left (by finiteness)) (by simp)
  · -- This is painful because we have to show continuity of the indicator
    -- which is needed to apply `dominated` because `R` is variable in the domain of the integral.
    -- This in turn meant proving continuity at `R₂`, which actually aligns with the blueprint.
    filter_upwards with y
    unfold ContinuousWithinAt
    have : nhdsWithin R₂ (Ioo R₁ R₂) |>.Eventually (fun r ↦ y ∉ Annulus.oo x r R₂) := by
      by_cases hy : dist x y < R₂
      · have : nhdsWithin R₂ (Ioo R₁ R₂) |>.Eventually (fun r ↦ dist x y < r) := by
          apply eventually_nhdsWithin_of_eventually_nhds
          apply eventually_nhds_iff_ball.mpr
          use (R₂ - dist x y)
          constructor
          · simp [hy]
          · intro r hr
            rw [mem_ball, dist_comm] at hr
            linarith [Real.sub_le_dist R₂ r]
        filter_upwards [this] with r hr
        exact fun hy ↦ hr.not_gt hy.1
      · filter_upwards with r; unfold Annulus.oo; rw [notMem_setOf_iff]; exact fun hy2 ↦ hy hy2.2
    rw [Filter.tendsto_iff_forall_eventually_mem]
    intro s hs
    filter_upwards [this] with r hr
    apply mem_of_mem_nhds
    simpa [indicator_of_notMem hr] using hs

/-- Lemma 10.1.8. -/
theorem nontangential_operator_boundary {f : X → ℂ} (hf : BoundedFiniteSupport f) :
    nontangentialOperator K f x =
    ⨆ (R₂ : ℝ) (R₁ ∈ Ioo 0 R₂) (x' ∈ ball x R₁),
    ‖∫ y in ball x' R₂ \ ball x' R₁, K x' y * f y‖ₑ := by
  let sup : ℝ≥0∞ := ⨆ (R₂ : ℝ) (R₁ ∈ Ioo 0 R₂) (x' ∈ ball x R₁),
    ‖∫ y in ball x' R₂ \ ball x' R₁, K x' y * f y‖ₑ
  unfold nontangentialOperator
  apply le_antisymm
  all_goals (
    rw [iSup_le_iff]; intro R₂
    rw [iSup₂_le_iff]; intro R₁ hR₁
    rw [iSup₂_le_iff]; intro x' hx'
  )
  · have (R' : ℝ) (hR' : R' ∈ Ioo R₁ R₂) : ‖∫ (y : X) in Annulus.oo x' R₁ R₂, K x' y * f y‖ₑ ≤
        ‖∫ (y : X) in Annulus.oo x' R₁ R', K x' y * f y‖ₑ + sup := by
      have : Annulus.oo x' R₁ R₂ = Annulus.oo x' R₁ R' ∪ Annulus.co x' R' R₂ :=
        Annulus.oo_union_co hR'.1 hR'.2.le |>.symm
      rw [this, setIntegral_union_2 (disjoint_left.mpr <| fun x hx hx2 ↦ not_lt.mpr hx2.1 hx.2)
        (by measurability)]; swap
      · simp_rw [← this]
        apply IntegrableOn.mono_set <| czoperator_welldefined hf hR₁.1 x'
        rw [← Annulus.ci_eq]
        exact Annulus.oo_subset_ci (by rfl)
      apply le_trans <| enorm_add_le _ _
      gcongr
      rw [Annulus.co_eq, inter_comm, ← diff_eq_compl_inter]
      refine le_iSup_of_le ?_ (i := R₂)
      refine le_iSup₂_of_le ?_ (i := R') (j := ⟨hR₁.1.trans hR'.1, hR'.2⟩)
      refine le_iSup₂_of_le ?_  (i := x') (j := hx'.trans hR'.1)
      rfl
    -- apply continuity
    have le_R1 : ‖∫ (y : X) in Annulus.oo x' R₁ R₂, K x' y * f y‖ₑ ≤
        ‖∫ (y : X) in Annulus.oo x' R₁ R₁, K x' y * f y‖ₑ + sup := by
      refine ContinuousWithinAt.closure_le ?_ ?_ ?_ this
      · simp [closure_Ioo hR₁.2.ne, hR₁.2.le]
      · apply continuousWithinAt_const
      · apply ContinuousWithinAt.add ?_ continuousWithinAt_const
        exact small_annulus_right hf hR₁.1 |>.enorm
    simpa using le_R1
  · have (R' : ℝ) (hR' : R' ∈ Ioo (dist x' x) R₁) : ‖∫ (y : X) in ball x' R₂ \ ball x' R₁, K x' y * f y‖ₑ ≤
        ‖∫ (y : X) in Annulus.oo x' R' R₁, K x' y * f y‖ₑ + nontangentialOperator K f x := by
      have hR'pos : 0 < R' := by linarith [dist_nonneg (x := x') (y := x), hR'.1]
      have : ∫ (y : X) in Annulus.co x' R₁ R₂, K x' y * f y = (∫ (y : X) in Annulus.oo x' R' R₁, K x' y * f y) +
          (∫ (y : X) in Annulus.co x' R₁ R₂, K x' y * f y) - ∫ (y : X) in Annulus.oo x' R' R₁, K x' y * f y := by
        simp
      rw [diff_eq_compl_inter, inter_comm, ← Annulus.co_eq, this]
      have : Annulus.oo x' R' R₂ = Annulus.oo x' R' R₁ ∪ Annulus.co x' R₁ R₂ :=
        Annulus.oo_union_co hR'.2 hR₁.2.le |>.symm
      rw [← setIntegral_union_2 (disjoint_left.mpr <| fun x hx hx2 ↦ not_lt.mpr hx2.1 hx.2) (by measurability), ← this]; swap
      · simp_rw [← this]
        apply IntegrableOn.mono_set <| czoperator_welldefined hf hR'pos x'
        rw [← Annulus.ci_eq]
        exact Annulus.oo_subset_ci (by rfl)
      apply le_trans enorm_sub_le
      rw [add_comm]
      gcongr
      refine le_iSup₂_of_le ?_ (i := R₂) (j := R')
      refine le_iSup₂_of_le ?_ (i := ⟨hR'pos, hR'.2.trans hR₁.2⟩) (j := x')
      refine le_iSup_of_le ?_ (i := hR'.1)
      rfl
    -- apply continuity
    have le_R1 : ‖∫ (y : X) in ball x' R₂ \ ball x' R₁, K x' y * f y‖ₑ ≤
        ‖∫ (y : X) in Annulus.oo x' R₁ R₁, K x' y * f y‖ₑ + nontangentialOperator K f x := by
      refine ContinuousWithinAt.closure_le ?_ ?_ ?_ this
      · simp [closure_Ioo (mem_ball.mp hx').ne, (mem_ball.mp hx').le]
      · apply continuousWithinAt_const
      · apply ContinuousWithinAt.add ?_ continuousWithinAt_const
        exact small_annulus_left hf (dist_nonneg) |>.enorm
    simpa using le_R1

omit [IsTwoSidedKernel a K] in
/-- Part of Lemma 10.1.6. -/
lemma lowerSemicontinuous_nontangentialOperator {g : X → ℂ} :
    LowerSemicontinuous (nontangentialOperator K g) := by
  unfold nontangentialOperator
  simp_rw [lowerSemicontinuous_iff_isOpen_preimage, preimage, mem_Ioi, lt_iSup_iff, ← iUnion_setOf,
    exists_prop]
  intro M
  apply isOpen_iUnion; intro R₂
  apply isOpen_biUnion; intro R₁ hR₁
  apply isOpen_iUnion; intro x'
  by_cases hx' : M < ‖∫ (y : X) in Annulus.oo x' R₁ R₂, K x' y * g y‖ₑ
  · simp_rw [hx', and_true, mem_ball_comm, setOf_mem_eq, isOpen_ball]
  · simp [hx']

omit [IsTwoSidedKernel a K] in
lemma aestronglyMeasurable_nontangentialOperator {g : X → ℂ} :
    AEStronglyMeasurable (nontangentialOperator K g) volume :=
  lowerSemicontinuous_nontangentialOperator |>.measurable.aestronglyMeasurable

/-- The constant used in `nontangential_from_simple`. -/
irreducible_def C10_0_2 (a : ℕ) : ℝ≥0 := 2 ^ (3 * a ^ 3)

/-- Lemma 10.0.2. The formal statement includes the measurability of the operator. -/
theorem nontangential_from_simple (ha : 4 ≤ a)
    (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a)) :
    HasBoundedStrongType (nontangentialOperator K) 2 2 volume volume (C10_0_2 a) := by
  intro g hg
  have eLpNorm_sno_le := simple_nontangential_operator_le ha hT le_rfl g hg |>.2
  constructor
  · exact aestronglyMeasurable_nontangentialOperator
  trans ENNReal.ofNNReal (2 * C10_1_6 a) * eLpNorm g 2 volume
  · push_cast; rw [two_mul, add_mul]
    apply le_trans _ <| add_le_add eLpNorm_sno_le eLpNorm_sno_le
    rw [← two_mul]
    apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
    simp_rw [nontangential_operator_boundary hg, enorm_eq_self]
    filter_upwards with x
    have {R₁ R₂ : ℝ} (hR1 : 0 < R₁) (hR1R2 : R₁ < R₂) {x' : X} : ‖∫ (y : X) in ball x' R₂ \ ball x' R₁, K x' y * g y‖ₑ ≤
        ‖∫ (y : X) in (ball x' R₁)ᶜ, K x' y * g y‖ₑ +
        ‖∫ (y : X) in (ball x' R₂)ᶜ, K x' y * g y‖ₑ := by
      apply le_trans _ enorm_sub_le
      have : (ball x' R₁)ᶜ = (ball x' R₂)ᶜ ∪ (ball x' R₂ \ ball x' R₁) := by
        rw [compl_eq_univ_diff, ← union_compl_self <| ball x' R₂, union_diff_distrib, union_comm]
        congr
        rw [diff_eq_compl_inter, inter_eq_right, compl_subset_compl]
        exact ball_subset_ball hR1R2.le
      rw [this, setIntegral_union_2 (disjoint_compl_left_iff_subset.mpr diff_subset) (by measurability)
        (by rw [← this]; exact czoperator_welldefined (K := K) hg hR1 x')]
      simp
    trans ⨆ (R₂ : ℝ) (R₁ ∈ Ioo 0 R₂) (x' ∈ ball x R₁),
        ‖∫ (y : X) in (ball x' R₁)ᶜ, K x' y * g y‖ₑ + ‖∫ (y : X) in (ball x' R₂)ᶜ, K x' y * g y‖ₑ
    · gcongr with R₂ R₁ hR₁
      exact this hR₁.1 hR₁.2
    have {R : ℝ} (hR : 0 < R) {x' : X} (hx' : dist x' x <  R) :
        ‖∫ (y : X) in (ball x' R)ᶜ, K x' y * g y‖ₑ ≤ simpleNontangentialOperator K 0 g x := by
      unfold simpleNontangentialOperator czOperator
      apply le_trans _ <| le_iSup _ R; rw [iSup_pos hR]
      apply le_trans _ <| le_iSup _ x'; rw [← mem_ball] at hx'; rw [iSup_pos hx']
    rw [iSup_le_iff]; intro R₂
    rw [iSup₂_le_iff]; intro R₁ hR₁
    rw [iSup₂_le_iff]; intro x' hx'
    norm_cast; rw [two_mul]
    exact add_le_add (this hR₁.1 hx') (this (hR₁.1.trans hR₁.2) (hx'.trans hR₁.2))
  · rw [C10_1_6, C10_0_2, ← pow_succ']; gcongr; · exact one_le_two
    calc
      _ ≤ a ^ 3 + 2 * 4 * 4 * a := by omega
      _ ≤ a ^ 3 + 2 * a * a * a := by gcongr
      _ = _ := by ring

omit [IsTwoSidedKernel a K] in
lemma nontangentialOperator_const_smul (z : ℂ) :
    nontangentialOperator (z • K) = ‖z‖ₑ • nontangentialOperator K := by
  unfold nontangentialOperator
  simp_rw [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul, enorm_mul, ← ENNReal.mul_iSup]
  rfl

end
