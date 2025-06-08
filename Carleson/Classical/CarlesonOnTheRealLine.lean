/-
This file contains the proof of Lemma 11.1.4 (real Carleson), from section 11.7.
We need to verify the assumptions of the two-sided metric Carleson theorem.
All smaller ones are done but the estimate for the truncated Hilbert transform is still missing.
-/

import Carleson.TwoSidedCarleson.MainTheorem
import Carleson.Classical.CarlesonOperatorReal
import Carleson.Classical.VanDerCorput
import Carleson.Classical.HilbertStrongType

noncomputable section

open MeasureTheory Function Metric Bornology Real

lemma localOscillation_on_emptyset {X : Type} [PseudoMetricSpace X] {f g : C(X, ℝ)} :
    localOscillation ∅ f g = 0 := by simp [localOscillation]

lemma localOscillation_on_empty_ball {X : Type} [PseudoMetricSpace X] {x : X} {f g : C(X, ℝ)}
    {R : ℝ} (R_nonpos : R ≤ 0): localOscillation (Metric.ball x R) f g = 0 := by
  rw [Metric.ball_eq_empty.mpr R_nonpos, localOscillation_on_emptyset]


section

open ENNReal MeasureTheory

section

def integer_linear (n : ℤ) : C(ℝ, ℝ) := ⟨fun (x : ℝ) ↦ n * x, by fun_prop⟩

local notation "θ" => integer_linear

set_option quotPrecheck false in
local notation "Θ" => {(θ n) | n : ℤ}



/-
/-Stronger version of oscillation_control based on earlier version of the blueprint -/
lemma localOscillation_of_integer_linear {x R : ℝ} (R_nonneg : 0 ≤ R) : ∀ n m : ℤ, localOscillation (Metric.ball x R) (θ n) (θ m) = 2 * R * |(n : ℝ) - m| := by
  intro n m
  by_cases n_ne_m : n = m
  · simp [n_ne_m, sub_self, abs_zero, mul_zero, localOscillation_of_same]
  push_neg at n_ne_m
  have norm_n_sub_m_pos : 0 < |(n : ℝ) - m| := by
    simp only [abs_pos, ne_eq]
    rwa [sub_eq_zero, Int.cast_inj]
  /- Rewrite to a more convenient form for the following steps. -/
  have norm_integer_linear_eq {n m : ℤ} {z : ℝ × ℝ} : ‖(θ n) z.1 - (θ m) z.1 - (θ n) z.2 + (θ m) z.2‖ = ‖(↑n - ↑m) * (z.1 - x) - (↑n - ↑m) * (z.2 - x)‖ := by
    simp only [integer_linear, ContinuousMap.coe_mk, Real.norm_eq_abs]
    ring_nf
  have localOscillation_eq : localOscillation (Metric.ball x R) (θ n) (θ m) = ⨆ z ∈ (Metric.ball x R) ×ˢ (Metric.ball x R), ‖(n - m) * (z.1 - x) - (n - m) * (z.2 - x)‖ := by
      rw [localOscillation]
      congr with z
      rw [norm_integer_linear_eq]
  rw [localOscillation_eq]
  /- Show inequalities in both directions. -/
  apply le_antisymm
  · calc ⨆ z ∈ (Metric.ball x R) ×ˢ (Metric.ball x R), ‖(n - m) * (z.1 - x) - (n - m) * (z.2 - x)‖
      _ ≤ 2 * R * |↑n - ↑m| := by
        apply Real.iSup_le
        --TODO: investigate strange (delaborator) behavior - why is there still a sup?
        intro z
        apply Real.iSup_le
        · intro hz
          simp at hz
          rw [Real.dist_eq, Real.dist_eq] at hz
          rw [Real.norm_eq_abs]
          calc |(n - m) * (z.1 - x) - (n - m) * (z.2 - x)|
          _ ≤ |(n - m) * (z.1 - x)| + |(n - m) * (z.2 - x)| := abs_sub _ _
          _ = |↑n - ↑m| * |z.1 - x| + |↑n - ↑m| * |z.2 - x| := by congr <;> apply abs_mul
          _ ≤ |↑n - ↑m| * R + |↑n - ↑m| * R := by gcongr; linarith [hz.1]; linarith [hz.2]
          _ = 2 * R * |↑n - ↑m| := by ring
        repeat
          apply mul_nonneg
          linarith
          apply abs_nonneg
  · apply le_of_forall_lt
    intro c hc
    have := fact_isCompact_ball x R
    by_cases c_nonneg : 0 > c
    · calc c
        _ < 0 := c_nonneg
        _ ≤ @dist (withLocalOscillation ℝ (Metric.ball x R)) PseudoMetricSpace.toDist (θ n) (θ m) := dist_nonneg
        _ = localOscillation (Metric.ball x R) (θ n) (θ m) := rfl
        _ = ⨆ z ∈ Metric.ball x R ×ˢ Metric.ball x R, ‖(↑n - ↑m) * (z.1 - x) - (↑n - ↑m) * (z.2 - x)‖ := by
          rw [localOscillation]
          congr with z
          rw [norm_integer_linear_eq]
    push_neg at c_nonneg
    set R' := (c + 2 * R * |(n : ℝ) - m|) / (4 * |(n : ℝ) - m|) with R'def
    have hR' : 0 ≤ R' ∧ R' < R := by
      rw [R'def]
      constructor
      · positivity
      calc (c + 2 * R * |↑n - ↑m|) / (4 * |↑n - ↑m|)
        _ < (2 * R * |↑n - ↑m| + 2 * R * |↑n - ↑m|) / (4 * |↑n - ↑m|) := by gcongr
        _ = R := by
          ring_nf
          rw [mul_assoc, mul_inv_cancel norm_n_sub_m_pos.ne.symm, mul_one]
    let y := (x - R', x + R')
    calc c
      _ = c / 2 + c / 2 := by ring
      _ < c / 2 + (2 * R * |↑n - ↑m|) / 2 := by gcongr
      _ = 2 * R' * |↑n - ↑m| := by
        rw [R'def]
        ring_nf
        rw [pow_two, ←mul_assoc, mul_assoc c, mul_inv_cancel norm_n_sub_m_pos.ne.symm,
          mul_assoc (R * _), mul_inv_cancel norm_n_sub_m_pos.ne.symm]
        ring
      _ ≤ ‖(↑n - ↑m) * (y.1 - x) - (↑n - ↑m) * (y.2 - x)‖ := by
        simp only [mul_assoc, sub_sub_cancel_left, mul_neg, add_sub_cancel_left,
          sub_eq_add_neg (-((n - m) * R')), ← two_mul, norm_neg, norm_mul, RCLike.norm_ofNat,
          Real.norm_eq_abs, mul_comm |(n : ℝ) - m|, gt_iff_lt, Nat.ofNat_pos,
          _root_.mul_le_mul_left]
        gcongr
        exact le_abs_self _
      _ ≤ ⨆ z ∈ Metric.ball x R ×ˢ Metric.ball x R, ‖(↑n - ↑m) * (z.1 - x) - (↑n - ↑m) * (z.2 - x)‖ := by
        apply ConditionallyCompleteLattice.le_biSup
        · convert bddAbove_localOscillation (Metric.ball x R) (θ n) (θ m) using 2
          exact norm_integer_linear_eq.symm
        · use y
          simp [abs_of_nonneg, hR'.1, hR'.2]
-/

end

instance instFunctionDistancesReal : FunctionDistances ℝ ℝ where
  Θ := ℤ
  coeΘ := integer_linear
  coeΘ_injective {n m} hnm := by simpa [integer_linear] using hnm 1
  metric := fun _ R ↦ {
      dist := fun n m ↦ 2 * max R 0 * |n - m|
      dist_self := by simp
      dist_comm := by
        simp only [Int.cast_abs, Int.cast_sub, mul_eq_mul_left_iff]
        exact fun _ _ ↦  Or.inl (abs_sub_comm ..)
      dist_triangle := by
        simp only [Int.cast_abs, Int.cast_sub]
        intro x y z
        rw [← mul_add]
        gcongr
        apply abs_sub_le
      --next field will get default in mathlib and is left out here
      --TODO: remove when that is the case
      edist_dist := fun _ _ ↦ rfl
  }


lemma dist_integer_linear_eq {n m : Θ ℝ} {x R : ℝ} :
    dist_{x, R} n m = 2 * max R 0 * |(n : ℝ) - m| := by
  norm_cast

lemma coeΘ_R (n : Θ ℝ) (x : ℝ) : n x = n * x := rfl

lemma coeΘ_R_C (n : Θ ℝ) (x : ℝ) : (n x : ℂ) = n * x := by norm_cast

lemma oscillation_control {x : ℝ} {r : ℝ} {f g : Θ ℝ} :
    localOscillation (ball x r) (coeΘ f) (coeΘ g) ≤ ENNReal.ofReal (dist_{x, r} f g) := by
  by_cases r_pos : r ≤ 0
  · rw [ball_eq_empty.mpr r_pos]
    simp [localOscillation, norm_nonneg]
  push_neg at r_pos
  simp_rw [dist_integer_linear_eq]
  calc ⨆ z ∈ ball x r ×ˢ ball x r, ENNReal.ofReal ‖↑f * z.1 - ↑g * z.1 - ↑f * z.2 + ↑g * z.2‖
    _ = ⨆ z ∈ ball x r ×ˢ ball x r, ENNReal.ofReal |(f - g) * (z.1 - x) - (f - g) * (z.2 - x)| := by
      congr with z
      congr with h
      rw [Real.norm_eq_abs]
      ring_nf
    _ ≤ ENNReal.ofReal (2 * r * |↑f - ↑g|) := by
      refine iSup₂_le (fun z hz ↦ ?_)
      apply ENNReal.ofReal_le_of_le_toReal
      rw [ENNReal.toReal_ofReal (by positivity)]
      simp_rw [Set.mem_prod, mem_ball, Real.dist_eq] at hz
      calc |(f - g) * (z.1 - x) - (f - g) * (z.2 - x)|
        _ ≤ |(f - g) * (z.1 - x)| + |(f - g) * (z.2 - x)| := abs_sub ..
        _ = |↑f - ↑g| * |z.1 - x| + |↑f - ↑g| * |z.2 - x| := by congr <;> apply abs_mul
        _ ≤ |↑f - ↑g| * r + |↑f - ↑g| * r := by
          gcongr
          · linarith [hz.1]
          · linarith [hz.2]
        _ = 2 * r * |↑f - ↑g| := by ring
    _ ≤ ENNReal.ofReal (2 * max r 0 * |↑f - ↑g|) := by
      gcongr
      apply le_max_left

lemma frequency_monotone {x₁ x₂ r R : ℝ} {f g : Θ ℝ} (h : ball x₁ r ⊆ ball x₂ R) : dist_{x₁,r} f g ≤ dist_{x₂,R} f g := by
  rw [dist_integer_linear_eq, dist_integer_linear_eq]
  by_cases r_pos : r ≤ 0
  · rw [ball_eq_empty.mpr r_pos] at h
    rw [max_eq_right r_pos]
    gcongr
    apply le_max_right
  push_neg at r_pos
  gcongr
  rw [Real.ball_eq_Ioo, Real.ball_eq_Ioo, Set.Ioo_subset_Ioo_iff (by linarith)] at h
  linarith [h.1, h.2]

lemma frequency_ball_doubling {x₁ x₂ r : ℝ} {f g : Θ ℝ} :
    dist_{x₂, 2 * r} f g ≤ 2 * dist_{x₁, r} f g := by
  rw [dist_integer_linear_eq, dist_integer_linear_eq]
  by_cases r_nonneg : r ≥ 0
  · rw [max_eq_left, max_eq_left]
    · ring_nf; rfl
    all_goals linarith [r_nonneg]
  · rw [max_eq_right, max_eq_right]
    · simp
    all_goals linarith [r_nonneg]

  theorem frequency_ball_growth {x₁ x₂ r : ℝ} {f g : Θ ℝ} :
      2 * dist_{x₁, r} f g ≤ dist_{x₂, 2 * r} f g := by
    rw [dist_integer_linear_eq, dist_integer_linear_eq]
    by_cases r_nonneg : r ≥ 0
    · rw [max_eq_left, max_eq_left]
      · ring_nf; rfl
      all_goals linarith [r_nonneg]
    · rw [max_eq_right, max_eq_right]
      · simp
      all_goals linarith [r_nonneg]

lemma integer_ball_cover {x : ℝ} {R R' : ℝ} {f : WithFunctionDistance x R}:
    CoveredByBalls (ball f (2 * R')) 3 R' := by
  unfold WithFunctionDistance at f
  rw [coveredByBalls_iff]
  by_cases R'pos : 0 ≥ R'
  · --trivial case
    use {f}
    constructor
    · norm_num
    simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left]
    rw [Metric.ball_eq_empty.mpr R'pos, Set.subset_empty_iff, Metric.ball_eq_empty]
    linarith
  push_neg at R'pos
  by_cases Rpos : 0 ≥ R
  · --trivial case
    use {f}
    constructor
    · norm_num
    simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left]
    convert Set.subset_univ _
    ext g
    constructor
    · simp
    simp only [Set.mem_univ, mem_ball, true_implies]
    rw [dist_integer_linear_eq]
    convert R'pos
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, max_eq_right_iff, false_or, abs_eq_zero]
    left
    exact Rpos
  push_neg at Rpos
  set m₁ := Int.floor (f - R' / (2 * R)) with m₁def
  set! m₂ := f with m₂def
  set m₃ := Int.ceil (f + R' / (2 * R)) with m₃def

  /- classical is necessary to be able to build a Finset of WithFunctionDistance. -/
  classical
  set balls : Finset (WithFunctionDistance x R) := {m₁, m₂, m₃} with balls_def
  use balls
  constructor
  · rw [balls_def]
    apply Finset.card_le_three
  intro φ hφ
  unfold WithFunctionDistance at φ
  rw [mem_ball] at hφ
  rw [dist_comm] at hφ
  /- m₁, m₂, m₃ each correspond to one case. -/
  simp only [Set.mem_iUnion, mem_ball, exists_prop]
  by_cases h : φ ≤ f - R' / (2 * R)
  · use m₁
    constructor
    · rw [balls_def]
      simp
    rw [dist_integer_linear_eq]
    calc 2 * max R 0 * |↑φ - ↑m₁|
      _ = 2 * R * |↑φ - ↑m₁| := by
        congr
        rw [max_eq_left_iff]
        exact Rpos.le
      _ = 2 * R * (m₁ - ↑φ) := by
        rw [abs_of_nonpos]
        on_goal 1 => simp only [neg_sub]
        norm_cast
        simp only [tsub_le_iff_right, zero_add, Int.cast_le]
        rwa [m₁def, Int.le_floor]
      _ = 2 * R * (m₁ - f) + 2 * R * (f - φ) := by ring
      _ < - R' + 2 * R' := by
        apply add_lt_add_of_le_of_lt
        · rw [m₁def]
          calc 2 * R * (⌊f - R' / (2 * R)⌋ - f)
            _ ≤ 2 * R * (f - R' / (2 * R) - f) := by
              gcongr
              apply Int.floor_le
            _ = -R' := by
              ring_nf
              rw [mul_comm, ←mul_assoc, inv_mul_cancel₀ Rpos.ne.symm, one_mul]
        · calc 2 * R * (↑f - ↑φ)
            _ ≤ 2 * R * |↑f - ↑φ| := by
              gcongr
              apply le_abs_self
            _ < 2 * R' := by
              convert hφ
              rw [dist_integer_linear_eq]
              congr
              symm
              rw [max_eq_left_iff]
              exact Rpos.le
      _ = R' := by ring
  push_neg at h
  by_cases h' : φ < f + R' / (2 * R)
  · use m₂
    constructor
    · rw [balls_def]
      simp
    rw [m₂def, dist_comm]
    rw [dist_integer_linear_eq]
    calc 2 * max R 0 * |↑f - ↑φ|
      _ = 2 * R * |↑f - ↑φ| := by
        congr
        rw [max_eq_left_iff]
        exact Rpos.le
      _ < 2 * R * (R' / (2 * R)) := by
        gcongr
        rw [abs_sub_lt_iff]
        constructor <;> linarith
      _ = R' := by field_simp
  push_neg at h'
  use m₃
  constructor
  · simp [balls_def]
  rw [dist_integer_linear_eq]
  calc 2 * max R 0 * |↑φ - ↑m₃|
    _ = 2 * R * (↑φ - ↑m₃) := by
      rw [abs_of_nonneg]
      · congr
        rw [max_eq_left_iff]
        exact Rpos.le
      simp only [sub_nonneg, Int.cast_le]
      rwa [m₃def, Int.ceil_le]
    _ = 2 * R * (φ - f) + 2 * R * (f - m₃) := by ring
    _ < 2 * R' - R' := by
      apply add_lt_add_of_lt_of_le
      · calc 2 * R * (↑φ - ↑f)
          _ ≤ 2 * R * |↑φ - ↑f| := by
            gcongr
            exact le_abs_self _
          _ = 2 * R * |↑f - ↑φ| := by
            congr 1
            exact abs_sub_comm _ _
          _ < 2 * R' := by
            convert hφ
            rw [dist_integer_linear_eq]
            congr
            symm
            rw [max_eq_left_iff]
            exact Rpos.le
      · rw [m₃def]
        calc 2 * R * (f - ⌈f + R' / (2 * R)⌉)
          _ ≤ 2 * R * (f - (f + R' / (2 * R))) := by
            gcongr
            exact Int.le_ceil _
          _ = -R' := by
            ring_nf
            rw [mul_comm, ←mul_assoc, inv_mul_cancel₀ Rpos.ne.symm, one_mul]
    _ = R' := by ring


instance compatibleFunctions_R : CompatibleFunctions ℝ ℝ (2 ^ 4) where
  eq_zero := by
    use 0
    intro f
    change f 0 = 0
    rw [coeΘ_R, mul_zero]
  localOscillation_le_cdist := oscillation_control
  cdist_mono := frequency_monotone
  cdist_le := by
    intro x₁ x₂ r f g _
    apply le_trans frequency_ball_doubling
    gcongr; norm_num
  le_cdist := by
    intro x₁ x₂ r f g _
    apply le_trans (@frequency_ball_growth x₁ x₂ r _ _)
    rw [dist_integer_linear_eq, dist_integer_linear_eq]
    by_cases r_nonneg : 0 ≤ r
    · gcongr; norm_num
    · push_neg at r_nonneg
      rw [max_eq_right (by linarith), max_eq_right (by norm_num; linarith)]
  allBallsCoverBalls := by
    intro x R R' f
    exact integer_ball_cover.mono_nat (by norm_num)

open scoped NNReal

instance real_van_der_Corput : IsCancellative ℝ (defaultτ 4) := by
  apply isCancellative_of_norm_integral_exp_le
  intro x r ϕ r_pos hK hϕ f g
  rw [defaultτ, ← one_div, measureReal_def, Real.volume_ball,
    ENNReal.toReal_ofReal (by linarith [r_pos]), Real.ball_eq_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [r_pos]), dist_integer_linear_eq,
    max_eq_left r_pos.le]
  calc ‖∫ (x : ℝ) in x - r..x + r, (Complex.I * (↑(f x) - ↑(g x))).exp * ϕ x‖
    _ = ‖∫ (x : ℝ) in x - r..x + r, (Complex.I * ((↑f - ↑g) : ℤ) * x).exp * ϕ x‖ := by
      congr with x
      rw [mul_assoc]
      congr
      push_cast
      rw [_root_.sub_mul]
      norm_cast
    _ ≤ 2 * π * ((x + r) - (x - r)) * (iLipNNNorm ϕ x r +
          (iLipNNNorm ϕ x r / r.toNNReal : ℝ≥0) * ((x + r) - (x - r)) / 2) *
      (1 + |((↑f - ↑g) : ℤ)| * ((x + r) - (x - r)))⁻¹ := by
      apply van_der_Corput (by linarith)
      · rw [Ioo_eq_ball]
        simp only [sub_add_add_cancel, add_self_div_two, add_sub_sub_cancel]
        apply LipschitzOnWith.of_iLipENorm_ne_top hK
      · intro y hy
        apply norm_le_iLipNNNorm_of_mem hK
        rwa [Real.ball_eq_Ioo]
    _ = 2 * π * (2 * r) * (iLipNNNorm ϕ x r + r * (iLipNNNorm ϕ x r / r.toNNReal : ℝ≥0))
          * (1 + 2 * r * |((↑f - ↑g) : ℤ)|)⁻¹ := by
      ring
    _ = 2 * π * (2 * r) * (iLipNNNorm ϕ x r + iLipNNNorm ϕ x r)
          * (1 + 2 * r * |((↑f - ↑g) : ℤ)|)⁻¹ := by
      congr
      rw [NNReal.coe_div, Real.coe_toNNReal _ r_pos.le, mul_div_cancel₀ _ r_pos.ne']
    _ = 4 * π * (2 * r) * iLipNNNorm ϕ x r * (1 + 2 * r * ↑|(↑f - ↑g : ℤ)|)⁻¹ := by ring
    _ ≤ (2 ^ 4 : ℕ) * (2 * r) * iLipNNNorm ϕ x r *
      (1 + 2 * r * ↑|(↑f - ↑g : ℤ)|) ^ (- (1 / (4 : ℝ))) := by
      gcongr
      · norm_num
        linarith [pi_le_four]
      · rw [← Real.rpow_neg_one]
        apply Real.rpow_le_rpow_of_exponent_le _ (by norm_num)
        simp only [Int.cast_abs, Int.cast_sub, le_add_iff_nonneg_right]
        exact mul_nonneg (by linarith) (abs_nonneg _)
  norm_cast


-- remove?
lemma Real.vol_real_eq {x y : ℝ} : Real.vol x y = 2 * |x - y| := by
  rw [Real.vol, measureReal_def, Real.dist_eq, Real.volume_ball,
    ENNReal.toReal_ofReal (by linarith [abs_nonneg (x-y)])]

-- proof can be simplified with enorm lemma
lemma Real.vol_eq {x y : ℝ} : vol x y = 2 * ‖x - y‖ₑ := by
  rw [vol, Real.volume_ball, ofReal_mul (by positivity), ← edist_dist, edist_eq_enorm_sub,
    ofReal_ofNat]

-- remove?
lemma Real.vol_real_symm {x y : ℝ} : Real.vol x y = Real.vol y x := by
  rw [Real.vol_real_eq, Real.vol_real_eq, abs_sub_comm]

-- proof can be simplified with enorm lemma
lemma Real.vol_symm {x y : ℝ} : vol x y = vol y x := by
  simp_rw [Real.vol_eq, ← ofReal_norm, norm_sub_rev]

instance isOneSidedKernelHilbert : IsOneSidedKernel 4 K where
  /- uses Hilbert_kernel_bound -/
  norm_K_le_vol_inv := by
    intro x y
    rw [Real.vol, measureReal_def, Real.dist_eq, Real.volume_ball, ENNReal.toReal_ofReal (by linarith [abs_nonneg (x-y)])]
    calc ‖K x y‖
    _ ≤ 2 ^ (2 : ℝ) / (2 * |x - y|) := Hilbert_kernel_bound
    _ ≤ 2 ^ (4 : ℝ) ^ 3 / (2 * |x - y|) := by gcongr <;> norm_num
  /- uses Hilbert_kernel_regularity -/
  norm_K_sub_le := by
    intro x y y' h
    rw [Real.dist_eq, Real.dist_eq] at *
    calc ‖K x y - K x y'‖
    _ ≤ 2 ^ 8 * (1 / |x - y|) * (|y - y'| / |x - y|) := by
      apply Hilbert_kernel_regularity
      linarith [abs_nonneg (x-y)]
    _ ≤ (|y - y'| / |x - y|) ^ (4 : ℝ)⁻¹ * (2 ^ (4 : ℝ) ^ 3 / Real.vol x y) := by
      rw [Real.vol_real_eq]
      ring_nf
      rw [pow_two, mul_assoc |x - y|⁻¹]
      gcongr
      · conv =>
          lhs
          rw [← Real.rpow_one (|x - y|⁻¹ * |y - y'|)]
        apply Real.rpow_le_rpow_of_exponent_ge'
        · field_simp
          exact div_nonneg (abs_nonneg (y - y')) (abs_nonneg (x - y))
        · field_simp
          apply div_le_one_of_le₀ <;> linarith [abs_nonneg (x - y)]
        · norm_num
        · norm_num
      · norm_num
  measurable_K := Hilbert_kernel_measurable

instance isTwoSidedKernelHilbert : IsTwoSidedKernel 4 K where
  enorm_K_sub_le' := by
    intro x x' y h
    rw [dist_comm x y] at h
    rw [Hilbert_kernel_conj_symm, @Hilbert_kernel_conj_symm y x', ← map_sub, ← ofReal_norm,
      Complex.norm_conj, edist_comm x y, Real.vol_symm, ofReal_norm_eq_enorm]
    exact enorm_K_sub_le (K := K) h

local notation "T" => carlesonOperatorReal K

--TODO : change name to reflect that this only holds for a specific instance of CarlesonOperaterReal?
lemma carlesonOperatorReal_le_carlesonOperator : T ≤ carlesonOperator K := by
  intro f x
  rw [carlesonOperator, carlesonOperatorReal]
  apply iSup_le
  intro n
  apply iSup_le
  intro r
  apply iSup_le
  intro rpos
  apply iSup_le _
  intro rle1
  apply le_iSup_of_le n _
  apply le_iSup₂_of_le r 1 _
  apply (le_iSup₂_of_le rpos rle1 (le_of_eq _))
  congr with y
  rw [coeΘ_R_C]
  ring_nf

/- Version of Lemma 11.1.5 for general exponents -/
lemma rcarleson_general {q q' : ℝ≥0} (hq : q ∈ Set.Ioc 1 2) (hqq' : q.HolderConjugate q')
    {F G : Set ℝ} (hF : MeasurableSet F) (hG : MeasurableSet G)
    (f : ℝ → ℂ) (hmf : Measurable f) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    ∫⁻ x in G, T f x ≤ C10_0_1 4 q * (volume G) ^ (q' : ℝ)⁻¹ * (volume F) ^ (q : ℝ)⁻¹ := by
  calc ∫⁻ x in G, T f x
    _ ≤ ∫⁻ x in G, carlesonOperator K f x :=
      lintegral_mono (carlesonOperatorReal_le_carlesonOperator _)
    _ ≤ C10_0_1 4 q * (volume G) ^ (q' : ℝ)⁻¹ * (volume F) ^ (q : ℝ)⁻¹ :=
      two_sided_metric_carleson (a := 4) (by norm_num) hq hqq' hF hG
        Hilbert_strong_2_2 hmf hf


/- Lemma 11.1.5 -/
lemma rcarleson {F G : Set ℝ} (hF : MeasurableSet F) (hG : MeasurableSet G)
    (f : ℝ → ℂ) (hmf : Measurable f) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x) :
    ∫⁻ x in G, T f x ≤ C10_0_1 4 2 * (volume G) ^ (2 : ℝ)⁻¹ * (volume F) ^ (2 : ℝ)⁻¹ := by
  have conj_exponents : NNReal.HolderConjugate 2 2 := by
    rw [NNReal.holderConjugate_iff_eq_conjExponent]
    · ext; norm_num
    norm_num
  exact rcarleson_general (by simp) conj_exponents hF hG f hmf hf

end
