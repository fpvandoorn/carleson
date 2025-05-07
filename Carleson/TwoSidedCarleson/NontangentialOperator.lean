import Carleson.ToMathlib.Analysis.Convex.SpecificFunctions.Basic
import Carleson.ToMathlib.Annulus
import Carleson.ToMathlib.HardyLittlewood
import Carleson.ToMathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Carleson.ToMathlib.MeasureTheory.Integral.Lebesgue
import Carleson.TwoSidedCarleson.Basic

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

lemma hasSum_geometric_series {x : ℝ} (hx : 4 ≤ x) :
    HasSum (fun (n : ℕ) ↦ (2 : ℝ≥0) ^ (-n / x)) (1 - 2 ^ (-x⁻¹))⁻¹ := by
  have h2x : (2 : ℝ≥0) ^ (-x⁻¹) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · norm_num
    · simp_rw [Left.neg_neg_iff]
      positivity

  -- Bring it to the form of hasSum_geometric_of_lt_one
  simp_rw [← NNReal.hasSum_coe, NNReal.coe_rpow, NNReal.coe_ofNat, neg_div,
    div_eq_inv_mul (b := x), ← neg_mul, Real.rpow_mul_natCast zero_le_two]
  push_cast [h2x.le]
  exact hasSum_geometric_of_lt_one (by positivity) h2x

/-- Lemma 10.1.1 -/
theorem geometric_series_estimate {x : ℝ} (hx : 4 ≤ x) :
    tsum (fun (n : ℕ) ↦ (2 : ℝ≥0∞) ^ (-n / x)) ≤ 2 ^ x := by
  simp_rw [← ENNReal.coe_ofNat, ← ENNReal.coe_rpow_of_ne_zero two_ne_zero,
    ← ENNReal.coe_tsum (hasSum_geometric_series hx).summable, coe_le_coe,
    (hasSum_geometric_series hx).tsum_eq]

  -- TODO the rest of this proof can surely be optimized
  -- Floris suggests using `trans 2`
  suffices (1 - (2 : ℝ) ^ (-x⁻¹))⁻¹ ≤ 2 ^ x by
    rw [← NNReal.coe_le_coe, NNReal.coe_inv, NNReal.coe_rpow, NNReal.coe_ofNat, NNReal.coe_sub]
    swap
    · apply NNReal.rpow_le_one_of_one_le_of_nonpos
      · exact Nat.one_le_ofNat
      · simp_rw [Left.neg_nonpos_iff]
        positivity
    apply this

  have zero_le_one_sub_four_div_x : 0 ≤ 1 - 4 / x := by
    simp only [sub_nonneg]
    rw [div_le_iff₀]
    · simp only [one_mul]
      exact hx
    · positivity

  have one_sub_two_pow_neg_one_div_four_pos : 0 < 1 - (2 : ℝ) ^ (-1 / 4 : ℝ) := by
    norm_num
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact one_lt_two
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
    _ ≤ (4 / x * (1 - 2 ^ (-1 / 4 : ℝ)))⁻¹ := by
      rw [inv_le_inv₀]
      · simp_rw [inv_eq_one_div, ← neg_div]
        linarith only [two_pow_neg_one_div_bound]
      · rw [sub_pos]
        apply Real.rpow_lt_one_of_one_lt_of_neg
        · simp only [NNReal.coe_ofNat, Nat.one_lt_ofNat]
        · simp only [Left.neg_neg_iff, inv_pos]
          positivity
      · apply _root_.mul_pos
        · positivity
        · exact one_sub_two_pow_neg_one_div_four_pos
    _ ≤ (4 * (1 - 2 ^ (-1 / 4 : ℝ)))⁻¹ * x := by field_simp
    _ ≤ 2 * x := mul_le_mul_of_nonneg_right geom_estimate_constant_le_two (by linarith only [hx])
    _ ≤ 2 ^ x := by
      apply Real.two_mul_lt_two_pow
      linarith only [hx]

/-- The constant used in `estimate_x_shift`. -/
irreducible_def C10_1_2 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 2 * a + 2)
-- exact estimate from proof: C_K * (defaultA + 2 * defaultA²) ≤ C10_1_2

omit [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)] in
lemma _laverage_mul_measure_ball {g : X → ℂ} {x₀ : X} {n : ℝ} :
    ∫⁻ (a : X) in ball x₀ (n * r), ‖g a‖ₑ = (⨍⁻ (a : X) in ball x₀ (n * r), ‖g a‖ₑ ∂volume) * volume (ball x₀ (n * r)) := by
  have : IsFiniteMeasure (volume.restrict (ball x₀ (n * r))) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  rw [← measure_mul_laverage]
  simp only [MeasurableSet.univ, Measure.restrict_apply, univ_inter, mul_comm]

omit [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)] in
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

omit [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)] in
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
  apply geometric_series_estimate
  · simp only [Nat.ofNat_le_cast, ha]

omit [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)] in
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
  · exact mul_le_mul' le_rfl (measure_ball_four_le_same' _ _)

  -- Somehow simp doesn't do it
  apply le_of_eq
  nth_rw 2 [mul_comm]
  rw [← mul_assoc, div_eq_mul_inv]
  nth_rw 2 [mul_assoc]
  simp_rw [mul_comm, ENNReal.mul_inv_cancel (measure_ball_pos volume x' hr).ne.symm measure_ball_lt_top.ne, C_K]
  norm_cast
  ring

omit [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)] in
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

omit [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)] in
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
        simp at yx'r yx'R hy
        linarith [hy yx'R yx'r]
      · simp at yx'r yx'R hy
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

omit [IsTwoSidedKernel a K] [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)] in

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

omit [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)] in
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
irreducible_def C10_1_4 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 20 * a + 2)

@[fun_prop]
lemma czOperator_aemeasurable {g : X → ℂ} (hg : BoundedFiniteSupport g) :
    AEMeasurable (fun x ↦ czOperator K r g x) := by
  sorry

lemma globalMaximalFunction_zero_enorm_czoperator_ae_zero (hR : 0 < R) {g : X → ℂ} (hg : BoundedFiniteSupport g)
    (hMzero : globalMaximalFunction volume 1 (czOperator K r g) x = 0) :
    ∀ᵐ x' ∂(volume.restrict (ball x (R / 4))), ‖czOperator K r g x'‖ₑ = 0 := by
  change (fun x' ↦ ‖czOperator K r g x'‖ₑ) =ᶠ[ae (volume.restrict (ball x (R / 4)))] 0
  rw [← lintegral_eq_zero_iff' ?hf]
  case hf => exact AEMeasurable.restrict (by fun_prop) -- TODO tag with `fun_prop`?
  rw [← bot_eq_zero, ← le_bot_iff, bot_eq_zero]
  apply le_of_le_of_eq (lintegral_ball_le_volume_globalMaximalFunction _)
  · rw [hMzero]
    simp
  · simp [hR]

/-- Part 1 of Lemma 10.1.4 about `F₁`. -/
theorem cotlar_set_F₁ (ha : 4 ≤ a) (hr : 0 < r) (hR : r ≤ R)
    (hT : ∀ r > 0, HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a))
    {g : X → ℂ} (hg : BoundedFiniteSupport g) :
    volume.restrict (ball x (R / 4))
      {x' | 4 * globalMaximalFunction volume 1 (czOperator K r g) x < ‖czOperator K r g x'‖ₑ } ≤
    volume (ball x (R / 4)) / 4 := by
  let MTrgx := globalMaximalFunction volume 1 (czOperator K r g) x
  by_cases hMzero : MTrgx = 0
  · apply le_of_eq_of_le _ (zero_le _)
    rw [measure_zero_iff_ae_nmem]
    have czzero := globalMaximalFunction_zero_enorm_czoperator_ae_zero (lt_of_lt_of_le hr hR) hg hMzero
    filter_upwards [czzero]
    intro x' hx'
    simp [hx']
  rw [← lintegral_indicator_one₀ (nullMeasurableSet_lt (by fun_prop) (by fun_prop))]
  rw [← ENNReal.mul_le_mul_right (by simp [hMzero]) ?ne_t (c := 4 * MTrgx)]
  case ne_t => apply mul_ne_top (by simp); sorry --globalMaximalFunction_lt_top
  rw [← lintegral_mul_const' _ _ ?hr]
  case hr => apply mul_ne_top (by simp); sorry --globalMaximalFunction_lt_top
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
    intro y -- otherwise runs into deterministic timeout, don't ask me why
    apply indicator_le_self
  nth_rw 2 [div_eq_mul_inv]
  rw [mul_assoc]
  nth_rw 2 [← mul_assoc]
  rw [ENNReal.inv_mul_cancel (by simp) (by simp)]
  simp only [one_mul, MTrgx]
  apply lintegral_ball_le_volume_globalMaximalFunction
  simp [(lt_of_lt_of_le hr hR)]

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
