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
  ⨆ (R > r) (x' ∈ ball x R), ‖CZOperator K R g x'‖ₑ

-- theorem Real.rpow_mul' {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (n : ℕ) :
--     x ^ (y * n) = (x ^ y) ^ n := by
--   exact rpow_mul_natCast hx y n

example (a b c : ℝ) (hc : 0 < c ) : a * c ≤ b * c ↔ a ≤ b := by
  exact mul_le_mul_iff_of_pos_right hc

example (a b : ℕ) (hc : a < b ) : (a : ℝ) < (b : ℝ) := by
  exact Nat.cast_lt.mpr hc

example (a b : ℕ) (hc : a < b ) : (a : ℝ) < (b : ℝ) := by
  exact Nat.cast_lt.mpr hc

theorem Real.two_mul_lt_two_pow (x : ℝ) (hx : 7 ≤ x) :
    (2 : ℝ) * x ≤ 2 ^ x := by

  calc
    _ ≤ (x - 6 : ℝ) * 2 ^ 5 := by
      norm_num
      linarith
    _ ≤ (⌊x - 5⌋₊ : ℕ) * 2 ^ 5 := by
      have := Nat.sub_one_lt_floor (x - 5 : ℝ)
      linarith
    _ ≤ (2 : ℝ) ^ (⌊x - 5⌋₊) * 2 ^ 5 := by
      rw [mul_le_mul_iff_of_pos_right (by linarith)]
      apply le_of_lt
      have := Nat.lt_two_pow_self (n := ⌊x - 5⌋₊)
      rw [<-Nat.cast_lt (α := ℝ)] at this
      push_cast at this
      exact this
    _ = 2 ^ (⌊x - 5⌋₊ + 5) := by
      rw [<-pow_add]
    _ = 2 ^ (((⌊x - 5⌋₊ + 5) : ℕ) : ℝ) := by
      exact Eq.symm (rpow_natCast 2 (⌊x - 5⌋₊ + 5))
    _ = 2 ^ (((⌊x - 5⌋₊ + 5)) : ℝ) := by
      push_cast
      congr
    _ ≤ 2 ^ (x - 5 + 5) := by
      have : (⌊x - 5⌋₊ + 5) ≤ (x - 5 + 5) := by
        simp only [sub_add_cancel]
        have h05 : 0 ≤ x - 5 := by linarith
        have := Nat.floor_le (α := ℝ) h05
        linarith
      have two_pos : 1 ≤ (2 : ℝ) := by linarith
      exact rpow_le_rpow_of_exponent_le two_pos this
    _ = 2 ^ x := by
      congr
      ring

lemma geom_estimate_constant_le_two :
    (4 * (1 - 2 ^ (-1 / 4 : ℝ)))⁻¹ ≤ (2 : ℝ) := by
  -- simp only [mul_inv_rev]
  -- rw [mul_inv_le_iff₀]
  -- norm_num
  -- rw [inv_le_comm₀]
  -- rw [le_sub_iff_add_le]
  -- rw [add_comm]
  -- rw [<-le_sub_iff_add_le]
  -- norm_num
  -- sorry
  -- sorry
  sorry

theorem real_geometric_series_estimate {x : ℝ} (hx : 4 ≤ x) :
    tsum (fun (n : ℕ) ↦ (2 : ℝ) ^ (-n / x)) ≤ 2 ^ x := by

  have : ∑' (n : ℕ), (2 : ℝ) ^ (-n / x) = ∑' (n : ℕ), ((2 : ℝ) ^ (-1 / x)) ^ n := by
    congr
    ext n
    -- simp only [NNReal.coe_rpow, NNReal.coe_ofNat, NNReal.coe_pow]
    rw [<- Real.rpow_mul_natCast (by linarith)]
    congr
    ring
  rw [this]

  have zero_le_two_pow_neg_inv : 0 ≤ (2 : ℝ) ^ (-1 / x) := by
    positivity

  have two_pow_neg_inv_lt_one : (2 : ℝ) ^ (-1 / x) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · simp
    · rw [neg_div]
      simp only [one_div, Left.neg_neg_iff, inv_pos]
      positivity

  rw [tsum_geometric_of_lt_one (by assumption) (by assumption)]


  -- By convexity, for all 0 ≤ λ ≤ 1, we have ...
  have two_pow_convex := ConvexOn_rpow_left (2 : ℝ) (by linarith)
  rcases two_pow_convex with ⟨_, two_pow_convex⟩
  have h := two_pow_convex
               (x := (-1/4 : ℝ)) (by simp)
               (y := 0) (by simp)
               (a := 4/x)
               (b := 1 - 4/x)
               (by positivity)
               (by
                 simp only [sub_nonneg]
                 rw [div_le_iff₀]
                 linarith
                 positivity
                )
               (by ring)
  simp only [smul_eq_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_mul_div_cancel₀',
    mul_zero, add_zero, Real.rpow_zero, mul_one] at h

  have : 4 / x * 2 ^ (-1 / 4 : ℝ) + (1 - 4 / x) = 1 - 4 / x * (1 - 2 ^ (-1 / 4 : ℝ)) := by
    ring
  rw [this] at h
  clear this
  have h2 : 4 / x * (1 - 2 ^ (-1 / 4 : ℝ)) ≤ 1 - 2 ^ (-1 / x) := by
    linarith
  have h3 : ((1 : ℝ) - 2 ^ (-1 / x))⁻¹ ≤ (4 / x * (1 - 2 ^ (-1 / 4 : ℝ)))⁻¹ := by
    rw [inv_le_inv₀]
    · exact h2
    · linarith
    · apply @_root_.mul_pos
      positivity
      norm_num
      apply Real.rpow_lt_one_of_one_lt_of_neg
      · simp
      · linarith
  simp only [ge_iff_le]
  apply le_trans h3 _
  have h4 : (4 / x * (1 - 2 ^ (-1 / 4 : ℝ)))⁻¹ = (4 * (1 - 2 ^ (-1 / 4 : ℝ)))⁻¹ * x := by
    field_simp
  rw [h4]

  have h5' : (4 * (1 - 2 ^ (-1 / 4 : ℝ)))⁻¹ ≤ (2 : ℝ) := by
    exact geom_estimate_constant_le_two

  have h5 : (4 * (1 - 2 ^ (-1 / 4 : ℝ)))⁻¹ * x ≤ 2 * x := by
    nlinarith

  apply le_trans h5 _

  by_cases h5_lt_x : 7 ≤ x
  · exact Real.two_mul_lt_two_pow x h5_lt_x
  ·
    calc
      _ ≤ (14 : ℝ) := by linarith
      _ ≤ (16 : ℝ) := by linarith
      _ = 2 ^ (4 : ℝ) := by norm_num
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le
        · linarith
        · linarith


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
    {g : X → ℂ} (hmg : Measurable g) (hg : eLpNorm g ∞ < ∞) (h2g : volume (support g) < ∞)
    (hr : 0 < r) (hx : dist x x' ≤ r) :
    nndist (CZOperator K r g x) (CZOperator K r g x') ≤
    C10_1_2 a * globalMaximalFunction volume 1 g x := by
  sorry

/-- The constant used in `cotlar_control`. -/
irreducible_def C10_1_3 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 4 * a + 1)

/-- Lemma 10.1.3 -/
theorem cotlar_control (ha : 4 ≤ a)
    {g : X → ℂ} (hmg : Measurable g) (hg : eLpNorm g ∞ < ∞) (h2g : volume (support g) < ∞)
    (hr : r ∈ Ioc 0 R) (hx : dist x x' ≤ R / 4) :
    ‖CZOperator K R g x‖ₑ ≤ ‖CZOperator K r ((ball x (R / 2))ᶜ.indicator g) x'‖ₑ +
    C10_1_3 a * globalMaximalFunction volume 1 g x := by
  sorry

/-- The constant used in `cotlar_set_F₂`. -/
irreducible_def C10_1_4 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 20 * a + 2)

/-- Part 1 of Lemma 10.1.4 about `F₁`. -/
theorem cotlar_set_F₁ (ha : 4 ≤ a)
    (hT : ∀ r > 0, HasBoundedStrongType (CZOperator K r) 2 2 volume volume (C_Ts a))
    {g : X → ℂ} (hmg : Measurable g) (hg : eLpNorm g ∞ < ∞) (h2g : volume (support g) < ∞) :
    volume {x' ∈ ball x (R / 4) |
      4 * globalMaximalFunction volume 1 (CZOperator K r g) x < ‖CZOperator K r g x'‖ₑ } ≤
    volume (ball x (R / 4)) / 4 := by
  sorry

/-- Part 2 of Lemma 10.1.4 about `F₂`. -/
theorem cotlar_set_F₂ (ha : 4 ≤ a)
    (hT : ∀ r > 0, HasBoundedStrongType (CZOperator K r) 2 2 volume volume (C_Ts a))
    {g : X → ℂ} (hmg : Measurable g) (hg : eLpNorm g ∞ < ∞) (h2g : volume (support g) < ∞) :
    volume {x' ∈ ball x (R / 4) |
      C10_1_4 a * globalMaximalFunction volume 1 g x <
      ‖CZOperator K r ((ball x (R / 2)).indicator g) x'‖ₑ } ≤
    volume (ball x (R / 4)) / 4 := by
  sorry

/-- The constant used in `cotlar_estimate`. -/
irreducible_def C10_1_5 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 20 * a + 2)

/-- Lemma 10.1.5 -/
theorem cotlar_estimate (ha : 4 ≤ a)
    (hT : ∀ r > 0, HasBoundedStrongType (CZOperator K r) 2 2 volume volume (C_Ts a))
    {g : X → ℂ} (hmg : Measurable g) (hg : eLpNorm g ∞ < ∞) (h2g : volume (support g) < ∞)
    (hr : r ∈ Ioc 0 R) :
    ‖CZOperator K R g x‖ₑ ≤ 4 * globalMaximalFunction volume 1 (CZOperator K r g) x +
      C10_1_5 a * globalMaximalFunction volume 1 g x := by
  sorry

/-- The constant used in `simple_nontangential_operator`. -/
irreducible_def C10_1_6 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 24 * a + 6)

/-- Lemma 10.1.6. The formal statement includes the measurability of the operator.
See also `simple_nontangential_operator_le` -/
theorem simple_nontangential_operator (ha : 4 ≤ a)
    (hT : ∀ r > 0, HasBoundedStrongType (CZOperator K r) 2 2 volume volume (C_Ts a))
    {g : X → ℂ} (hmg : Measurable g) (hg : eLpNorm g ∞ < ∞) (h2g : volume (support g) < ∞)
    (hr : 0 < r) :
    HasStrongType (simpleNontangentialOperator K r) 2 2 volume volume (C10_1_6 a) := by
  sorry

/-- This is the first step of the proof of Lemma 10.0.2, and should follow from 10.1.6 +
monotone convergence theorem. (measurability should be proven without any restriction on `r`.) -/
theorem simple_nontangential_operator_le (ha : 4 ≤ a)
    (hT : ∀ r > 0, HasBoundedStrongType (CZOperator K r) 2 2 volume volume (C_Ts a))
    {g : X → ℂ} (hmg : Measurable g) (hg : eLpNorm g ∞ < ∞) (h2g : volume (support g) < ∞)
    (hr : 0 ≤ r) :
    HasStrongType (simpleNontangentialOperator K r) 2 2 volume volume (C10_1_6 a) := by
  sorry

/-- Part of Lemma 10.1.7, reformulated -/
theorem small_annulus_right (ha : 4 ≤ a)
    (hT : ∀ r > 0, HasBoundedStrongType (CZOperator K r) 2 2 volume volume (C_Ts a))
    {f : X → ℂ} (hmf : Measurable f) (hf : eLpNorm f ∞ < ∞) (h2f : volume (support f) < ∞)
    {R₁ : ℝ} :
    Continuous (fun R₂ ↦ ∫ y in {y | dist x' y ∈ Ioo R₁ R₂}, K x' y * f y) := by
  sorry

/-- Part of Lemma 10.1.7, reformulated -/
theorem small_annulus_left (ha : 4 ≤ a)
    (hT : ∀ r > 0, HasBoundedStrongType (CZOperator K r) 2 2 volume volume (C_Ts a))
    {f : X → ℂ} (hmf : Measurable f) (hf : eLpNorm f ∞ < ∞) (h2f : volume (support f) < ∞)
    {R₂ : ℝ} :
    Continuous (fun R₁ ↦ ∫ y in {y | dist x' y ∈ Ioo R₁ R₂}, K x' y * f y) := by
  sorry

/-- Lemma 10.1.8. -/
theorem nontangential_operator_boundary (ha : 4 ≤ a)
    {f : X → ℂ} (hmf : Measurable f) (hf : eLpNorm f ∞ < ∞) (h2f : volume (support f) < ∞) :
    nontangentialOperator K f x =
    ⨆ (R₁ : ℝ) (R₂ : ℝ) (_ : R₁ < R₂) (x' : X) (_ : dist x x' ≤ R₁),
    ‖∫ y in ball x' R₂ \ ball x' R₁, K x' y * f y‖ₑ := by
  sorry

/-- The constant used in `nontangential_from_simple`. -/
irreducible_def C10_0_2 (a : ℕ) : ℝ≥0 := 2 ^ (3 * a ^ 3)

/-- Lemma 10.0.2. The formal statement includes the measurability of the operator. -/
theorem nontangential_from_simple (ha : 4 ≤ a)
    (hT : ∀ r > 0, HasBoundedStrongType (CZOperator K r) 2 2 volume volume (C_Ts a))
    {g : X → ℂ} (hmg : Measurable g) (hg : eLpNorm g ∞ < ∞) (h2g : volume (support g) < ∞) :
    HasStrongType (nontangentialOperator K) 2 2 volume volume (C10_0_2 a) := by
  have := simple_nontangential_operator_le ha hT hmg hg h2g le_rfl
  sorry


end
