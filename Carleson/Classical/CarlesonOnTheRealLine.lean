/- This file contains the proof of Lemma 11.1.4, from section 11.7 -/

import Carleson.MetricCarleson
import Carleson.Classical.Basic
import Carleson.Classical.Helper
import Carleson.Classical.HilbertKernel
import Carleson.Classical.CarlesonOperatorReal
import Carleson.Classical.VanDerCorput

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals

noncomputable section

open MeasureTheory Function Metric Bornology

--#lint

section
@[reducible]
def DoublingMeasureR2 : DoublingMeasure ℝ 2 :=
  InnerProductSpace.DoublingMeasure.mono (by simp)

instance DoublingMeasureR4 : DoublingMeasure ℝ (2 ^ 4 : ℕ) :=
  DoublingMeasureR2.mono (by norm_num)
end

lemma localOscillation_on_emptyset {X : Type} [PseudoMetricSpace X] {f g : C(X, ℝ)} :
    localOscillation ∅ f g = 0 := by simp [localOscillation]

lemma localOscillation_on_empty_ball {X : Type} [PseudoMetricSpace X] {x : X} {f g : C(X, ℝ)} {R : ℝ} (R_nonpos : R ≤ 0):
    localOscillation (Metric.ball x R) f g = 0 := by
  rw [Metric.ball_eq_empty.mpr R_nonpos, localOscillation_on_emptyset]


section

open ENNReal

section

def integer_linear (n : ℤ) : C(ℝ, ℝ) := ⟨fun (x : ℝ) ↦ n * x, by fun_prop⟩


local notation "θ" => integer_linear

local notation "Θ" => {(θ n) | n : ℤ}


/-Stronger version of oscillation_control from the paper-/
/-Based on earlier version of the paper. -/
/-

theorem localOscillation_of_same  {X : Type} [PseudoMetricSpace X] {E : Set X} {f : C(X, ℝ)} :
    localOscillation E f f = 0 := by simp [localOscillation]

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
        simp only [Int.cast_abs, Int.cast_sub, mul_eq_mul_left_iff, mul_eq_zero,
          OfNat.ofNat_ne_zero, false_or]
        intro x y
        left
        norm_cast
        apply abs_sub_comm
      dist_triangle := by
        simp only [Int.cast_abs, Int.cast_sub]
        intro x y z
        rw [← mul_add]
        gcongr
        norm_cast
        apply abs_sub_le
      --next field will get default in mathlib and is left out here
      --TODO: remove when that is the case
      edist_dist := fun x y ↦ rfl
  }

--TODO: add lemma to avoid unfolds.
--lemma dist_eq_

lemma coeΘ_R (n : Θ ℝ) (x : ℝ) : n x = n * x := rfl
lemma coeΘ_R_C (n : Θ ℝ) (x : ℝ) : (n x : ℂ) = n * x := by norm_cast

lemma oscillation_control {x : ℝ} {r : ℝ} {f g : Θ ℝ} :
    localOscillation (ball x r) (coeΘ f) (coeΘ g) ≤ dist_{x, r} f g := by
  by_cases r_pos : r ≤ 0
  . rw [ball_eq_empty.mpr r_pos]
    unfold localOscillation
    simp [dist_nonneg]
  push_neg at r_pos
  unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric instFunctionDistancesReal
    localOscillation integer_linear
  dsimp
  calc ⨆ z ∈ ball x r ×ˢ ball x r, |↑f * z.1 - ↑g * z.1 - ↑f * z.2 + ↑g * z.2|
    _ = ⨆ z ∈ ball x r ×ˢ ball x r, ‖(f - g) * (z.1 - x) - (f - g) * (z.2 - x)‖ := by
      congr
      ext z
      congr
      ext h
      rw [Real.norm_eq_abs]
      congr 1
      ring
    _ ≤ 2 * r * |↑f - ↑g| := by
      apply Real.iSup_le
      --TODO: investigate strange (delaborator) behavior - why is there still a sup?
      intro z
      apply Real.iSup_le
      . intro hz
        simp at hz
        rw [Real.dist_eq, Real.dist_eq] at hz
        rw [Real.norm_eq_abs]
        calc |(f - g) * (z.1 - x) - (f - g) * (z.2 - x)|
        _ ≤ |(f - g) * (z.1 - x)| + |(f - g) * (z.2 - x)| := by apply abs_sub
        _ = |↑f - ↑g| * |z.1 - x| + |↑f - ↑g| * |z.2 - x| := by congr <;> apply abs_mul
        _ ≤ |↑f - ↑g| * r + |↑f - ↑g| * r := by gcongr; linarith [hz.1]; linarith [hz.2]
        _ = 2 * r * |↑f - ↑g| := by ring
      all_goals
      repeat
        apply mul_nonneg
        linarith
        apply abs_nonneg
    _ ≤ 2 * max r 0 * |↑f - ↑g| := by
      gcongr
      apply le_max_left
  norm_cast

lemma frequency_monotone {x₁ x₂ r R : ℝ} {f g : Θ ℝ} (h : ball x₁ r ⊆ ball x₂ R) : dist_{x₁,r} f g ≤ dist_{x₂,R} f g := by
  unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric instFunctionDistancesReal
  dsimp
  by_cases r_pos : r ≤ 0
  . rw [ball_eq_empty.mpr r_pos] at h
    rw [max_eq_right r_pos]
    gcongr
    apply le_max_right
  push_neg at r_pos
  gcongr
  rw [Real.ball_eq_Ioo, Real.ball_eq_Ioo, Set.Ioo_subset_Ioo_iff (by linarith)] at h
  linarith [h.1, h.2]

lemma frequency_ball_doubling {x₁ x₂ r : ℝ} {f g : Θ ℝ} : dist_{x₂, 2 * r} f g ≤ 2 * dist_{x₁, r} f g := by
  unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric instFunctionDistancesReal Real.pseudoMetricSpace
  dsimp
  by_cases r_nonneg : r ≥ 0
  . rw [max_eq_left, max_eq_left]
    ring_nf;rfl
    all_goals linarith [r_nonneg]
  . rw [max_eq_right, max_eq_right]
    simp
    all_goals linarith [r_nonneg]

  theorem frequency_ball_growth {x₁ x₂ r : ℝ} {f g : Θ ℝ} : 2 * dist_{x₁, r} f g ≤ dist_{x₂, 2 * r} f g := by
    unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric instFunctionDistancesReal
    dsimp
    by_cases r_nonneg : r ≥ 0
    . rw [max_eq_left, max_eq_left]
      ring_nf;rfl
      all_goals linarith [r_nonneg]
    . rw [max_eq_right, max_eq_right]
      simp
      all_goals linarith [r_nonneg]

lemma integer_ball_cover {x : ℝ} {R R' : ℝ} {f : WithFunctionDistance x R}:
    CoveredByBalls (ball f (2 * R')) 3 R' := by
  unfold WithFunctionDistance at f
  rw [coveredByBalls_iff]
  by_cases R'pos : 0 ≥ R'
  · --trivial case
    use {f}
    constructor
    . norm_num
    simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left]
    rw [Metric.ball_eq_empty.mpr R'pos, Set.subset_empty_iff, Metric.ball_eq_empty]
    linarith
  push_neg at R'pos
  by_cases Rpos : 0 ≥ R
  · --trivial case
    use {f}
    constructor
    . norm_num
    simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left]
    convert Set.subset_univ _
    ext g
    constructor
    . simp
    simp only [Set.mem_univ, mem_ball, true_implies]
    unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric instFunctionDistancesReal
    dsimp
    convert R'pos
    simp
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
  . use m₁
    constructor
    · rw [balls_def]
      simp
    unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric instFunctionDistancesReal
    dsimp
    calc 2 * max R 0 * |↑φ - m₁|
      _ = 2 * R * |↑φ - m₁| := by
        congr
        rw [max_eq_left_iff]
        exact Rpos.le
      _ = 2 * R * (m₁ - ↑φ) := by
        rw [abs_of_nonpos]
        simp only [neg_sub]
        norm_cast
        simp only [tsub_le_iff_right, zero_add, Int.cast_le]
        rwa [m₁def, Int.le_floor]
      _ = 2 * R * (m₁ - f) + 2 * R * (f - φ) := by ring
      _ < - R' + 2 * R' := by
        apply add_lt_add_of_le_of_lt
        . rw [m₁def]
          calc 2 * R * (⌊f - R' / (2 * R)⌋ - f)
            _ ≤ 2 * R * (f - R' / (2 * R) - f) := by
              gcongr
              apply Int.floor_le
            _ = -R' := by
              ring_nf
              rw [mul_comm, ←mul_assoc, inv_mul_cancel Rpos.ne.symm, one_mul]
        . calc 2 * R * (↑f - ↑φ)
            _ ≤ 2 * R * |↑f - ↑φ| := by
              gcongr
              apply le_abs_self
            _ < 2 * R' := by
              convert hφ
              unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric instFunctionDistancesReal
              dsimp
              norm_cast
              congr
              symm
              rw [max_eq_left_iff]
              exact Rpos.le
      _ = R' := by ring
  push_neg at h
  by_cases h' : φ < f + R' / (2 * R)
  . use m₂
    constructor
    · rw [balls_def]
      simp
    rw [m₂def, dist_comm]
    unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric instFunctionDistancesReal
    dsimp
    push_cast
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
  . simp [balls_def]
  unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric instFunctionDistancesReal
  dsimp
  push_cast
  calc 2 * max R 0 * |↑φ - ↑m₃|
    _ = 2 * R * (↑φ - ↑m₃) := by
      rw [abs_of_nonneg]
      congr
      rw [max_eq_left_iff]
      exact Rpos.le
      simp only [sub_nonneg, Int.cast_le]
      rwa [m₃def, Int.ceil_le]
    _ = 2 * R * (φ - f) + 2 * R * (f - m₃) := by ring
    _ < 2 * R' - R' := by
      apply add_lt_add_of_lt_of_le
      . calc 2 * R * (↑φ - ↑f)
          _ ≤ 2 * R * |↑φ - ↑f| := by
            gcongr
            exact le_abs_self _
          _ = 2 * R * |↑f - ↑φ| := by
            congr 1
            exact abs_sub_comm _ _
          _ < 2 * R' := by
            convert hφ
            unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric instFunctionDistancesReal
            dsimp
            norm_cast
            congr
            symm
            rw [max_eq_left_iff]
            exact Rpos.le
      . rw [m₃def]
        calc 2 * R * (f - ⌈f + R' / (2 * R)⌉)
          _ ≤ 2 * R * (f - (f + R' / (2 * R))) := by
            gcongr
            exact Int.le_ceil _
          _ = -R' := by
            ring_nf
            rw [mul_comm, ←mul_assoc, inv_mul_cancel Rpos.ne.symm, one_mul]
    _ = R' := by ring


--TODO: Some of the statements are stronger in the paper. Extract these
instance compatibleFunctions_R : CompatibleFunctions ℝ ℝ (2 ^ 4) where
  eq_zero := by
    use 0
    intro f
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
    unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric instFunctionDistancesReal
    dsimp
    by_cases r_nonneg : 0 ≤ r
    . gcongr; norm_num
    . push_neg at r_nonneg
      rw [max_eq_right (by linarith), max_eq_right (by linarith)]
  ballsCoverBalls := by
    intro x R R' f
    exact integer_ball_cover.mono_nat (by norm_num)

--TODO : What is Lemma 11.7.10 (frequency ball growth) needed for?

instance real_van_der_Corput : IsCancellative ℝ (defaultτ 4) where
  /- Lemma 11.7.12 (real van der Corput) from the paper. -/
  norm_integral_exp_le := by
    intro x r ϕ K hK _ f g
    by_cases r_pos : 0 ≥ r
    . rw [ball_eq_empty.mpr r_pos]
      simp
    push_neg at r_pos
    rw [defaultτ, ← one_div, measureReal_def, Real.volume_ball, ENNReal.toReal_ofReal (by linarith [r_pos]), Real.ball_eq_Ioo, ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [r_pos])]
    unfold dist PseudoMetricSpace.toDist instPseudoMetricSpaceWithFunctionDistance FunctionDistances.metric CompatibleFunctions.toFunctionDistances compatibleFunctions_R
    dsimp only
    unfold instFunctionDistancesReal
    dsimp only
    rw [max_eq_left r_pos.le]
    set L : NNReal :=
      ⟨⨆ (x : ℝ) (y : ℝ) (_ : x ≠ y), ‖ϕ x - ϕ y‖ / dist x y,
        Real.iSup_nonneg fun x ↦ Real.iSup_nonneg fun y ↦ Real.iSup_nonneg
        fun _ ↦ div_nonneg (norm_nonneg _) dist_nonneg⟩ with Ldef
    set B : NNReal :=
      ⟨⨆ y ∈ ball x r, ‖ϕ y‖, Real.iSup_nonneg fun i ↦ Real.iSup_nonneg
        fun _ ↦ norm_nonneg _⟩  with Bdef
    calc ‖∫ (x : ℝ) in x - r..x + r, (Complex.I * (↑(f x) - ↑(g x))).exp * ϕ x‖
      _ = ‖∫ (x : ℝ) in x - r..x + r, (Complex.I * ((↑f - ↑g) : ℤ) * x).exp * ϕ x‖ := by
        congr
        ext x
        rw [mul_assoc]
        congr
        push_cast
        rw [_root_.sub_mul]
        norm_cast
      _ ≤ 2 * Real.pi * ((x + r) - (x - r)) * (B + L * ((x + r) - (x - r)) / 2) * (1 + |((↑f - ↑g) : ℤ)| * ((x + r) - (x - r)))⁻¹ := by
        apply van_der_Corput (by linarith)
        . rw [lipschitzWith_iff_dist_le_mul]
          intro x y
          --TODO: The following could be externalised as a lemma.
          by_cases hxy : x = y
          . rw [hxy]
            simp
          rw [dist_eq_norm, ← div_le_iff (dist_pos.mpr hxy), Ldef, NNReal.coe_mk]
          apply le_ciSup_of_le _ x
          apply le_ciSup_of_le _ y
          apply le_ciSup_of_le _ hxy
          rfl
          . use K
            rw [upperBounds]
            simp only [ne_eq, Set.mem_range, exists_prop, and_imp,
              forall_apply_eq_imp_iff, Set.mem_setOf_eq]
            intro h
            rw [div_le_iff (dist_pos.mpr h), dist_eq_norm]
            exact LipschitzWith.norm_sub_le hK _ _
          . use K
            rw [upperBounds]
            simp only [ne_eq, Set.mem_range, forall_exists_index,
              forall_apply_eq_imp_iff, Set.mem_setOf_eq]
            intro y
            apply Real.iSup_le _ NNReal.zero_le_coe
            intro h
            rw [div_le_iff (dist_pos.mpr h), dist_eq_norm]
            exact LipschitzWith.norm_sub_le hK _ _
          . use K
            rw [upperBounds]
            simp only [ne_eq, Set.mem_range, forall_exists_index,
              forall_apply_eq_imp_iff, Set.mem_setOf_eq]
            intro x
            apply Real.iSup_le _ NNReal.zero_le_coe
            intro y
            apply Real.iSup_le _ NNReal.zero_le_coe
            intro h
            rw [div_le_iff (dist_pos.mpr h), dist_eq_norm]
            apply LipschitzWith.norm_sub_le hK
        . --prove main property of B
          intro y hy
          apply ConditionallyCompleteLattice.le_biSup
          . --TODO: externalize as lemma LipschitzWithOn.BddAbove or something like that?
            rw [Real.ball_eq_Ioo]
            exact BddAbove.mono (Set.image_mono Set.Ioo_subset_Icc_self)
              (isCompact_Icc.bddAbove_image (continuous_norm.comp hK.continuous).continuousOn)
          use y
          rw [Real.ball_eq_Ioo]
          use hy
      _ = 2 * Real.pi * (2 * r) * (B + r * L) * (1 + 2 * r * |((↑f - ↑g) : ℤ)|)⁻¹ := by
        ring
      _ ≤ (2 ^ 4 : ℕ) * (2 * r) * iLipNorm ϕ x r * (1 + 2 * r * ↑|(↑f - ↑g : ℤ)|) ^ (- (1 / (4 : ℝ))) := by
        gcongr
        . exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (iLipNorm_nonneg r_pos.le)
        . norm_num
          linarith [Real.pi_le_four]
        . unfold iLipNorm
          gcongr
          apply le_of_eq Bdef
          apply le_of_eq Ldef
        . rw [← Real.rpow_neg_one]
          apply Real.rpow_le_rpow_of_exponent_le _ (by norm_num)
          simp only [Int.cast_abs, Int.cast_sub, le_add_iff_nonneg_right]
          exact mul_nonneg (by linarith) (abs_nonneg _)


lemma Real.vol_real_eq {x y : ℝ} : Real.vol x y = 2 * |x - y| := by
  rw [Real.vol, MeasureTheory.measureReal_def, Real.dist_eq, Real.volume_ball, ENNReal.toReal_ofReal (by linarith [abs_nonneg (x-y)])]

lemma Real.vol_real_symm {x y : ℝ} : Real.vol x y = Real.vol y x := by
  rw [Real.vol_real_eq, Real.vol_real_eq, abs_sub_comm]

instance isOneSidedKernelHilbert : IsOneSidedKernel 4 K where
  /- uses Hilbert_kernel_bound -/
  norm_K_le_vol_inv := by
    intro x y
    rw [Complex.norm_eq_abs, Real.vol, MeasureTheory.measureReal_def, Real.dist_eq, Real.volume_ball, ENNReal.toReal_ofReal (by linarith [abs_nonneg (x-y)])]
    calc Complex.abs (K x y)
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
          apply div_le_one_of_le <;> linarith [abs_nonneg (x - y)]
        · norm_num
        · norm_num
      · norm_num
  /- Lemma ?-/
  measurable_K_left := fun y ↦ Hilbert_kernel_measurable.of_uncurry_right
  /- Lemma ?-/
  measurable_K_right := Hilbert_kernel_measurable

instance isTwoSidedKernelHilbert : IsTwoSidedKernel 4 K where
  norm_K_sub_le' := by
    intro x x' y h
    rw [Hilbert_kernel_conj_symm, @Hilbert_kernel_conj_symm y x', ← map_sub, Complex.norm_eq_abs, Complex.abs_conj, ← Complex.norm_eq_abs, dist_comm x y, Real.vol_real_symm]
    rw [dist_comm x y] at h
    exact isOneSidedKernelHilbert.norm_K_sub_le h

lemma Hilbert_strong_2_2 : ∀ r > 0, HasBoundedStrongType (CZOperator K r) 2 2 volume volume (C_Ts 4) := sorry


local notation "T" => CarlesonOperatorReal K

--TODO : change name to reflect that this only holds for a specific instance of CarlesonOperaterReal?
lemma CarlesonOperatorReal_le_CarlesonOperator : T ≤ CarlesonOperator K := by
  intro f x
  rw [CarlesonOperator, CarlesonOperatorReal]
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


/- Lemma 11.1.4 (ENNReal version) -/
lemma rcarleson {F G : Set ℝ}
    (hF : MeasurableSet F) (hG : MeasurableSet G)
    (f : ℝ → ℂ) (hf : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    :
    ∫⁻ x in G, T f x ≤
    ENNReal.ofReal (C10_1 4 2) * (MeasureTheory.volume G) ^ (2 : ℝ)⁻¹ * (MeasureTheory.volume F) ^ (2 : ℝ)⁻¹ := by
  have conj_exponents : Real.IsConjExponent 2 2 := by rw [Real.isConjExponent_iff_eq_conjExponent] <;> norm_num
  calc ∫⁻ x in G, T f x
    _ ≤ ∫⁻ x in G, CarlesonOperator K f x :=
      MeasureTheory.lintegral_mono (CarlesonOperatorReal_le_CarlesonOperator _)
    _ ≤ ENNReal.ofReal (C10_1 4 2) * (MeasureTheory.volume G) ^ (2 : ℝ)⁻¹ * (MeasureTheory.volume F) ^ (2 : ℝ)⁻¹ :=
      two_sided_metric_carleson (a := 4) K (by norm_num) (by simp) conj_exponents hF hG Hilbert_strong_2_2 f hf

end section
