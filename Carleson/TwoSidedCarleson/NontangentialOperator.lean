import Carleson.TwoSidedCarleson.WeakCalderonZygmund
import Carleson.ToMathlib.Analysis.Convex.SpecificFunctions.Basic
import Carleson.ToMathlib.ENorm
import Carleson.ToMathlib.Annulus

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
    HasSum (fun (n : ℕ) ↦ (2 : ℝ≥0) ^ (-n / x)) (1 - 2 ^ (-1 / x))⁻¹ := by

  have two_pow_neg_inv_lt_one {x : ℝ} (hx : 4 ≤ x) :
      (2 : ℝ≥0) ^ (-1 / x) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · simp only [NNReal.coe_ofNat, Nat.one_lt_ofNat]
    · rw [neg_div]
      simp only [one_div, Left.neg_neg_iff, inv_pos]
      positivity

  -- Bring it to the form of hasSum_geometric_of_lt_one
  rw [← NNReal.hasSum_coe]
  conv =>
    arg 1; intro n;
    rw [NNReal.coe_rpow, NNReal.coe_ofNat, div_eq_mul_inv, neg_mul, mul_comm, ← neg_mul, Real.rpow_mul_natCast, inv_eq_one_div, ← neg_div]
    case h.hx => exact zero_le_two
  rw [NNReal.coe_inv, NNReal.coe_sub, NNReal.coe_rpow, NNReal.coe_one, NNReal.coe_ofNat]
  swap
  . exact le_of_lt (two_pow_neg_inv_lt_one hx)

  apply hasSum_geometric_of_lt_one
  . positivity
  . exact two_pow_neg_inv_lt_one hx

/-- Lemma 10.1.1 -/
theorem geometric_series_estimate {x : ℝ} (hx : 4 ≤ x) :
    tsum (fun (n : ℕ) ↦ (2 : ℝ≥0∞) ^ (-n / x)) ≤ 2 ^ x := by
  rw [← ENNReal.coe_ofNat]
  conv_lhs =>
    arg 1; intro n
    rw [← ENNReal.coe_rpow_of_ne_zero]
    case h.h => apply OfNat.ofNat_ne_zero
  rw [← ENNReal.coe_tsum, ← ENNReal.coe_rpow_of_ne_zero, coe_le_coe]
  case h => apply OfNat.ofNat_ne_zero
  swap --Summable from coe_tsum first
  . exact HasSum.summable (hasSum_geometric_series hx)

  rw [HasSum.tsum_eq (hasSum_geometric_series hx)]

  -- TODO the rest of this proof can surely be optimized
  suffices (1 - (2 : ℝ) ^ (-1 / x))⁻¹ ≤ 2 ^ x by
    rw [← NNReal.coe_le_coe, NNReal.coe_inv, NNReal.coe_rpow, NNReal.coe_ofNat, NNReal.coe_sub]
    swap
    . apply NNReal.rpow_le_one_of_one_le_of_nonpos
      . exact Nat.one_le_ofNat
      . apply div_nonpos_of_nonpos_of_nonneg
        . simp only [Left.neg_nonpos_iff, zero_le_one]
        . positivity
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
    _ ≤ (4 / x * (1 - 2 ^ (-1 / 4 : ℝ)))⁻¹ := by
      rw [inv_le_inv₀]
      · linarith only [two_pow_neg_one_div_bound]
      · rw [sub_pos]
        apply Real.rpow_lt_one_of_one_lt_of_neg
        · simp only [NNReal.coe_ofNat, Nat.one_lt_ofNat]
        · rw [neg_div]
          simp only [one_div, Left.neg_neg_iff, inv_pos]
          positivity
      · apply _root_.mul_pos
        · positivity
        · exact one_sub_two_pow_neg_one_div_four_pos
    _ ≤ (4 * (1 - 2 ^ (-1 / 4 : ℝ)))⁻¹ * x := by field_simp
    _ ≤ 2 * x := mul_le_mul_of_nonneg_right geom_estimate_constant_le_two (by linarith only [hx])
    _ ≤ 2 ^ x := by
      apply Real.two_mul_lt_two_pow
      linarith only [hx]

-- TODO move to ToMathlib, properly generalise
theorem integrableOn_of_integrableOn_inter_support {f : X → ℂ} {μ : Measure X} {s : Set X}
    (hs : MeasurableSet s) (hf : IntegrableOn f (s ∩ support f) μ) :
    IntegrableOn f s μ := by
  apply IntegrableOn.of_forall_diff_eq_zero hf hs
  simp

-- TODO move to sensible place
lemma czoperator_welldefined {g : X → ℂ} (hg : BoundedFiniteSupport g) (hr : 0 < r) (x : X):
    IntegrableOn (fun y => K x y * g y) (ball x r)ᶜ volume := by
  let Kxg := fun y ↦ K x y * g y
  have mKxg : Measurable Kxg := by
    have : Measurable (K x) := measurable_K_right x
    have : Measurable g := hg.measurable
    fun_prop

  have bdd_Kxg : ∃ (M : ℝ), ∀ y ∈ (ball x r)ᶜ ∩ support Kxg, ‖Kxg y‖ ≤ M := by
    use (C_K a / volume (ball x r) * eLpNorm g ∞).toNNReal
    intro y hy
    rw [toNNReal_mul, norm_mul]
    apply mul_le_mul
    case b0 => apply NNReal.zero_le_coe
    case c0 => simp only [norm_nonneg]
    . suffices ‖K x y‖ₑ ≤ (C_K a : ℝ≥0) / volume (ball x r) by
        rw [enorm_eq_nnnorm] at this
        sorry
      sorry
    sorry

  obtain ⟨M, hM⟩ := bdd_Kxg

  apply integrableOn_of_integrableOn_inter_support
  . exact MeasurableSet.compl measurableSet_ball
  apply Measure.integrableOn_of_bounded
  . apply ne_top_of_le_ne_top
    . sorry --exact ne_of_lt hg.finiteSupport
    . apply measure_mono
      trans support Kxg
      . exact inter_subset_right
      . exact support_mul_subset_right (K x) g
  . exact mKxg.aestronglyMeasurable
  . rw [MeasureTheory.ae_iff, Measure.restrict_apply']
    . trans (volume (∅ : Set X))
      . congr
        rw [← disjoint_iff_inter_eq_empty, disjoint_right]
        . intro y hy
          rw [mem_setOf, not_not]
          exact hM y hy
      . exact measure_empty
    . apply MeasurableSet.inter --somehow not used by simp despite the tag
      . simp [MeasurableSet.compl_iff, measurableSet_ball] --should measurableSet_ball have @[simp]?
      . exact measurableSet_support mKxg --should measureSet_support have @[simp]?

/- This should go somewhere else

But this version of setIntegral_union is easier to apply as it starts from the overall integral which
is to be estimated.
-/
variable {α : Type*} [MeasurableSpace α]
variable {f : α → ℂ } {s t : Set α} {μ : Measure α}

theorem MeasureTheory.setIntegral_union_2 (hst : Disjoint s t) (ht : MeasurableSet t) (hfst : IntegrableOn f (s ∪ t) μ) :
    ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ + ∫ x in t, f x ∂μ := by
  let hfs : IntegrableOn f s μ := IntegrableOn.left_of_union hfst
  let hft : IntegrableOn f t μ := IntegrableOn.right_of_union hfst
  exact setIntegral_union hst ht hfs hft
/- End of somewhere else -/

/-- The constant used in `estimate_x_shift`. -/
irreducible_def C10_1_2 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 2 * a + 2)
-- exact estimate from proof: C_K * (defaultA + 2 * defaultA²) ≤ C10_1_2

/-- Lemma 10.1.2 -/
theorem estimate_x_shift (ha : 4 ≤ a)
    {g : X → ℂ} (hg : BoundedFiniteSupport g) (hr : 0 < r) (hx : dist x x' ≤ r) :
    edist (czOperator K r g x) (czOperator K r g x') ≤
    C10_1_2 a * globalMaximalFunction volume 1 g x := by
  let bxrc := (ball x r)ᶜ
  let bx2r := ball x (2*r)
  let bxprc := (ball x' r)ᶜ

  have hmg : Measurable g := hg.measurable -- for fun_prop

  -- Domain split x integral
  have dom_x : bxrc =  (bxrc ∩ bx2r) ∪ bx2rᶜ := by
    have tmp1 : bx2rᶜ = bxrc ∩ bx2rᶜ := by
      rw [right_eq_inter, compl_subset_compl]
      apply ball_subset_ball
      linarith

    calc bxrc
      _ = bxrc ∩ univ                  := by rw[inter_univ]
      _ = bxrc ∩ (bx2r ∪ bx2rᶜ)        := by rw[union_compl_self]
      _ = (bxrc ∩ bx2r) ∪ bxrc ∩ bx2rᶜ := by rw[inter_union_distrib_left]
      _ = (bxrc ∩ bx2r) ∪ bx2rᶜ        := by rw[← tmp1]

  have tmp2 : bx2rᶜ ⊆ bxprc := by
    rw [compl_subset_compl]
    apply ball_subset
    calc dist x' x
    _ = dist x x' := dist_comm x' x
    _ ≤ r         := hx
    _ = 2 * r - r := by linarith

  -- Domain split x' integral
  have dom_x_prime : bxprc = (bxprc ∩ bx2r) ∪ bx2rᶜ := by
    have : bx2rᶜ = bxprc ∩ bx2rᶜ := right_eq_inter.mpr tmp2
    rw [this]
    exact Eq.symm (inter_union_compl bxprc bx2r)

  -- Integral split x
  have integral_x : czOperator K r g x = (∫ y in (bxrc ∩ bx2r), K x y * g y) + (∫ y in bx2rᶜ, K x y * g y) := by
    calc czOperator K r g x
      _ = (∫ y in bxrc, K x y * g y) := by rfl
      _ = (∫ y in (bxrc ∩ bx2r) ∪ bx2rᶜ , K x y * g y) := by nth_rw 1 [dom_x]

    apply MeasureTheory.setIntegral_union_2
    . rw [disjoint_compl_right_iff_subset]
      exact inter_subset_right
    . apply MeasurableSet.compl
      apply measurableSet_ball
    . rw [← dom_x]
      apply czoperator_welldefined hg hr

  -- Integral split x'
  have integral_x_prime : czOperator K r g x' = (∫ y in (bxprc ∩ bx2r), K x' y * g y) + (∫ y in bx2rᶜ, K x' y * g y) := by
    calc czOperator K r g x'
      _ = (∫ y in bxprc, K x' y * g y) := by rfl
      _ = (∫ y in (bxprc ∩ bx2r) ∪ bx2rᶜ , K x' y * g y) := by nth_rw 1 [dom_x_prime]

    apply MeasureTheory.setIntegral_union_2
    . rw [disjoint_compl_right_iff_subset]
      exact inter_subset_right
    . apply MeasurableSet.compl
      apply measurableSet_ball
    . rw [← dom_x_prime]
      apply czoperator_welldefined hg hr

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
          . apply czoperator_welldefined hg (mul_pos zero_lt_two hr)
          . apply IntegrableOn.mono_set
            case hg.hst => exact tmp2
            apply czoperator_welldefined hg hr

  trans ‖(∫ (y : X) in bxrc ∩ bx2r, K x y * g y) + ∫ (y : X) in bx2rᶜ, K x y * g y - K x' y * g y‖ₑ +
      ‖∫ (y : X) in bxprc ∩ bx2r, K x' y * g y‖ₑ
  . apply enorm_sub_le

  trans ‖∫ (y : X) in bxrc ∩ bx2r, K x y * g y‖ₑ + ‖∫ (y : X) in bx2rᶜ, K x y * g y - K x' y * g y‖ₑ +
      ‖∫ (y : X) in bxprc ∩ bx2r, K x' y * g y‖ₑ
  . refine add_le_add ?_ ?_
    . apply enorm_add_le
    . rfl

  trans (∫⁻ (y : X) in bxrc ∩ bx2r, ‖K x y * g y‖ₑ) + ‖∫ (y : X) in bx2rᶜ, K x y * g y - K x' y * g y‖ₑ +
      ∫⁻ (y : X) in bxprc ∩ bx2r, ‖K x' y * g y‖ₑ
  . refine add_le_add_three ?_ ?_ ?_
    . apply enorm_integral_le_lintegral_enorm
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

  have pointwise_1 {x₀ : X}: ∀(y : X), y ∈ (ball x₀ r)ᶜ → ‖K x₀ y‖ₑ * ‖g y‖ₑ ≤
      C_K a / volume (ball x₀ r) * ‖g y‖ₑ := by
    intro y h
    refine mul_le_mul' ?_ ?_
    case refine_2 => rfl

    trans C_K a / vol x₀ y
    . apply enorm_K_le_vol_inv

    apply ENNReal.div_le_div_left
    apply measure_mono
    exact ball_subset_ball (y_est y h)

  have pointwise_2 : ∀(y : X), y ∈ (ball x (2 * r))ᶜ → ‖K x y - K x' y‖ₑ * ‖g y‖ₑ ≤
      ((edist x x' / edist x y) ^ (a : ℝ)⁻¹ * (C_K a / vol x y)) * ‖g y‖ₑ := by
    intro y h
    apply mul_le_mul'
    case h₂ => rfl

    apply enorm_K_sub_le'

    trans 2 * r
    . apply mul_le_mul
      case h₁ => rfl
      case c0 | b0 => simp only [Nat.ofNat_nonneg, dist_nonneg]
      exact hx

    rw [mem_compl_iff, mem_ball, dist_comm] at h
    exact le_of_not_gt h

  have tmp5 {x₀ : X} {n : ℝ} : ∫⁻ (a : X) in ball x₀ (n * r), ‖g a‖ₑ = (⨍⁻ (a : X) in ball x₀ (n * r), ‖g a‖ₑ ∂volume) * volume (ball x₀ (n * r)) := by
    have : IsFiniteMeasure (volume.restrict (ball x₀ (n * r))) := by
      refine isFiniteMeasure_restrict.mpr ?_
      exact ne_of_lt measure_ball_lt_top
    rw [← measure_mul_laverage]
    simp only [MeasurableSet.univ, Measure.restrict_apply, univ_inter, mul_comm]

  have estimate_10_1_2 : (∫⁻ (y : X) in bxrc ∩ bx2r, ‖K x y * g y‖ₑ)
      ≤ 2 ^ (a ^ 3 + a) * globalMaximalFunction volume 1 g x := by
    simp only [enorm_mul]

    trans ∫⁻ (y : X) in bxrc ∩ bx2r, C_K ↑a / volume (ball x r) * ‖g y‖ₑ
    . apply setLIntegral_mono
      . fun_prop
      intro x
      trans x ∈ bxrc
      . exact fun a ↦ mem_of_mem_inter_left a
      apply pointwise_1

    rw [lintegral_const_mul] -- LHS = 10.1.5
    case hf => exact Measurable.enorm hmg

    trans C_K ↑a / volume (ball x r) * (globalMaximalFunction volume 1 g x * volume (ball x (2 * r)))
    . apply mul_le_mul'
      case h₁ => rfl

      trans ∫⁻ (a : X) in bx2r, ‖g a‖ₑ
      . apply lintegral_mono_set
        exact inter_subset_right

      rw [tmp5]
      apply mul_le_mul'
      case h₂ => rfl

      apply laverage_le_globalMaximalFunction
      rw [dist_self]
      exact mul_pos zero_lt_two hr

    nth_rw 2 [mul_comm]
    rw [← mul_assoc]

    apply mul_le_mul'
    case h₂ => rfl

    trans C_K ↑a / volume (ball x r) * (defaultA a * volume (ball x r))
    . apply mul_le_mul'
      case h₁ => rfl
      case h₂ => apply measure_ball_two_le_same

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

  have estimate_10_1_3 : ‖∫ (y : X) in bx2rᶜ, K x y * g y - K x' y * g y‖ₑ
      ≤ 2 ^ (a ^ 3 + 2 * a) * globalMaximalFunction volume 1 g x := by
    conv =>
      arg 1; arg 1; arg 2
      intro y
      rw [← mul_sub_right_distrib]

    trans ∫⁻ (y : X) in bx2rᶜ, ‖(K x y - K x' y) * g y‖ₑ
    . apply enorm_integral_le_lintegral_enorm
    simp only [enorm_mul]

    trans ∫⁻ (y : X) in bx2rᶜ, ((edist x x' / edist x y) ^ (a : ℝ)⁻¹ * (C_K a / vol x y)) * ‖g y‖ₑ
    . apply setLIntegral_mono
      . have : Measurable fun y ↦ vol x y := by sorry
        fun_prop
      apply pointwise_2

    let dom_i (i : ℕ) := Annulus.co x (2^(i+1) * r) (2^(i+2) * r)
    have rw_dom : bx2rᶜ = ⋃ (i : ℕ) , dom_i i:= by
      sorry

    trans ∑' (i : ℕ), ∫⁻ (y : X) in dom_i i, ((edist x x' / edist x y) ^ (a : ℝ)⁻¹ * (C_K a / vol x y)) * ‖g y‖ₑ
    . rw [rw_dom]
      apply lintegral_iUnion_le

    -- Writing negative powers as positive powers of 1/2 to enable working with i : ℕ instead of -i : ℤ
    trans ∑' (i : ℕ), 2 ^ (a ^ 3 + a) * (1 / (2 : ℝ≥0) ) ^ ((i + 1) * (a : ℝ)⁻¹) * globalMaximalFunction volume 1 g x
    . apply tsum_le_tsum
      case hf | hg => apply ENNReal.summable

      intro i
      have est_edist : ∀y ∈ dom_i i, (edist x x' / edist x y) ≤ (1 / (2 : ℝ≥0)) ^ (i + 1) := by
        intro y
        unfold dom_i Annulus.co
        rw [mem_setOf, ← Ico_def, mem_setOf]
        intro hdist
        trans edist x x' / (2 ^ (i + 1) * r.toNNReal)
        . apply ENNReal.div_le_div_left
          rw [edist_dist, ENNReal.le_ofReal_iff_toReal_le]
          case ha => norm_cast; apply coe_ne_top
          case hb => exact dist_nonneg
          simp only [toReal_mul, toReal_pow, toReal_ofNat, coe_toReal, Real.coe_toNNReal']
          rw [(max_eq_left (le_of_lt hr))]
          exact hdist.left
        rw [ENNReal.div_le_iff_le_mul]
        case hb0 => right; apply pow_ne_top; simp
        case hbt => left; apply mul_ne_top; exact pow_ne_top ofNat_ne_top; exact coe_ne_top
        rw [← mul_assoc]
        rw [pow_mul_pow_eq_one]
        case a =>
          simp only [coe_ofNat, one_div]
          apply ENNReal.inv_mul_cancel
          . simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
          . simp only [ne_eq, ofNat_ne_top, not_false_eq_true]
        simp only [one_mul, edist_le_coe, nndist_dist]
        exact Real.toNNReal_le_toNNReal hx

      have est_vol : ∀y ∈ dom_i i, vol x y ≥ volume (ball x (2 ^ (i + 1) * r)) := by
        intro y
        unfold dom_i Annulus.co
        rw [mem_setOf, ← Ico_def, mem_setOf]
        intro hdist
        apply measure_mono
        refine ball_subset_ball ?_
        exact hdist.left

      trans ∫⁻ (y : X) in dom_i i, (1 / (2 : ℝ≥0)) ^ ((i + 1) * (a : ℝ)⁻¹) * (C_K a / volume (ball x (2 ^ (i + 1) * r))) * ‖g y‖ₑ
      . apply setLIntegral_mono
        . fun_prop
        intro y hy
        apply mul_le_mul'
        case h₂ => rfl
        apply mul_le_mul'
        . rw [rpow_mul]
          apply rpow_le_rpow
          . norm_cast
            exact est_edist y hy
          . simp only [inv_nonneg, Nat.cast_nonneg]
        . apply ENNReal.div_le_div_left
          apply est_vol
          exact hy

      rw [lintegral_const_mul]
      case hf => exact Measurable.enorm hmg

      trans (1 / (2 : ℝ≥0)) ^ ((i + 1) * (a : ℝ)⁻¹) * (C_K ↑a / volume (ball x (2 ^ (i + 1) * r))) *
          ∫⁻ (y : X) in ball x (2 ^ (i + 2) * r), ‖g y‖ₑ
      . apply mul_le_mul'
        case h₁ => rfl
        apply lintegral_mono_set
        unfold dom_i
        rw [Set.Annulus.co_eq]
        exact inter_subset_left

      rw [tmp5]

      nth_rw 5 [mul_comm]
      rw [← mul_assoc]
      trans (1 / (2 : ℝ≥0)) ^ ((i + 1) * (a : ℝ)⁻¹) * (C_K ↑a / volume (ball x (2 ^ (i + 1) * r))) *
          volume (ball x (2 ^ (i + 2) * r)) * globalMaximalFunction volume 1 g x
      . apply mul_le_mul'
        case h₁ => rfl
        apply laverage_le_globalMaximalFunction
        simp only [dist_self, Nat.ofNat_pos, pow_pos, mul_pos_iff_of_pos_left, hr]

      apply mul_le_mul'
      case h₂ => rfl

      rw [mul_assoc, mul_comm]
      apply mul_le_mul'
      case h₂ => rfl

      trans C_K ↑a / volume (ball x (2 ^ (i + 1) * r)) * (defaultA a * volume (ball x (2 ^ (i + 1) * r)))
      . apply mul_le_mul'
        case h₁ => rfl
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
      rw [ENNReal.mul_inv_cancel]
      case h0 =>
        apply ne_of_gt
        apply measure_ball_pos
        simp only [Nat.ofNat_pos, pow_pos, mul_pos_iff_of_pos_left, hr]
      case ht =>
        apply ne_of_lt
        apply measure_ball_lt_top
      simp only [C_K, defaultA, Nat.cast_pow, Nat.cast_ofNat, one_mul]
      norm_cast
      rw [pow_add]

    rw [ENNReal.tsum_mul_right]
    apply mul_le_mul'
    case h₂ => rfl

    rw [ENNReal.tsum_mul_left]

    have : (2 : ℝ≥0∞) ^ (a ^ 3 + 2 * a) = 2 ^ (a ^ 3 + a) * 2 ^ a := by ring
    rw [this]
    apply mul_le_mul'
    case h₁ => rfl

    conv =>
      lhs; arg 1; intro i
      rw [coe_ofNat, one_div, inv_rpow, ← rpow_neg, ← div_eq_mul_inv]

    trans ∑' (i : ℕ), 2 ^ (-i / (a : ℝ))
    . apply tsum_le_tsum
      case hf | hg => apply ENNReal.summable
      intro i
      apply rpow_le_rpow_of_exponent_le
      . simp only [Nat.one_le_ofNat]
      . rw [neg_div, neg_le_neg_iff, div_le_div_iff_of_pos_right]
        . simp only [le_add_iff_nonneg_right, zero_le_one]
        . positivity

    rw [← rpow_natCast]
    apply geometric_series_estimate
    . simp only [Nat.ofNat_le_cast, ha]


  have estimate_10_1_4 : (∫⁻ (y : X) in bxprc ∩ bx2r, ‖K x' y * g y‖ₑ)
      ≤ 2 ^ (a ^ 3 + 2 * a) * globalMaximalFunction volume 1 g x := by
    simp only [enorm_mul]

    trans ∫⁻ (y : X) in bxprc ∩ bx2r, C_K ↑a / volume (ball x' r) * ‖g y‖ₑ
    . apply setLIntegral_mono
      . fun_prop
      intro x
      trans x ∈ bxprc
      . exact fun a ↦ mem_of_mem_inter_left a
      apply pointwise_1

    rw [lintegral_const_mul] -- LHS = 10.1.5 but for x'
    case hf => exact Measurable.enorm hmg

    trans C_K ↑a / volume (ball x' r) * (globalMaximalFunction volume 1 g x * volume (ball x' (4 * r)))
    . apply mul_le_mul'
      case h₁ => rfl

      trans ∫⁻ (a : X) in ball x' (4 * r), ‖g a‖ₑ
      . apply lintegral_mono_set
        trans bx2r
        . exact inter_subset_right
        . apply ball_subset
          linarith

      rw [tmp5]
      apply mul_le_mul'
      case h₂ => rfl

      apply laverage_le_globalMaximalFunction
      linarith

    nth_rw 2 [mul_comm]
    rw [← mul_assoc]

    apply mul_le_mul'
    case h₂ => rfl

    trans C_K ↑a / volume (ball x' r) * ((defaultA a) ^ 2 * volume (ball x' r))
    . apply mul_le_mul'
      case h₁ => rfl
      case h₂ => apply measure_ball_four_le_same'

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

  rw [← distrib_three_right]

  refine mul_le_mul' ?_ ?_
  case refine_2 => rfl

  -- Now it is unavoidable to unfold C10_1_2
  with_unfolding_all simp only [C10_1_2]
  norm_cast

  trans 2 ^ (a ^ 3 + 2 * a + 1) + 2 ^ (a ^ 3 + 2 * a) + 2 ^ (a ^ 3 + 2 * a)
  . apply Nat.add_le_add_iff_right.mpr
    apply Nat.add_le_add_iff_right.mpr
    rw [Nat.pow_le_pow_iff_right (h := Nat.one_lt_two)]
    linarith

  apply le_of_eq
  ring

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
