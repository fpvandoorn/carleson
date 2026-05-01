import Carleson.Calculations
import Carleson.HolderVanDerCorput
import Carleson.Operators
import Carleson.ToMathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# 6.2. Proof of the Tile Correlation Lemma

This file contains the proofs of lemmas 6.2.1, 6.2.2, 6.2.3 and 6.1.5 from the blueprint.

## Main definitions
- `Tile.correlation` : the function `φ` defined in Lemma 6.2.1.

## Main results
- `Tile.mem_ball_of_correlation_ne_zero` and `Tile.correlation_kernel_bound`: Lemma 6.2.1.
- `Tile.range_support`: Lemma 6.2.2.
- `Tile.uncertainty` : Lemma 6.2.3.
- `Tile.correlation_le` and `Tile.correlation_zero_of_ne_subset`: Lemma 6.1.5.
-/

macro_rules | `(tactic |gcongr_discharger) => `(tactic | with_reducible assumption)

noncomputable section

open scoped ComplexConjugate ENNReal NNReal ShortVariables

open Complex Function MeasureTheory Measure Metric Set

namespace Tile

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X} [MetricSpace X]
  [ProofData a q K σ₁ σ₂ F G]

/-- Def 6.2.1 (from Lemma 6.2.1), denoted by `φ(y)` in the blueprint. -/
def correlation (s₁ s₂ : ℤ) (x₁ x₂ y : X) : ℂ := conj (Ks s₁ x₁ y) * Ks s₂ x₂ y

@[fun_prop]
lemma measurable_correlation : Measurable (correlation (X := X)) := by fun_prop

/-- First part of Lemma 6.2.1 (eq. 6.2.2). -/
lemma mem_ball_of_correlation_ne_zero {s₁ s₂ : ℤ} {x₁ x₂ y : X}
    (hy : correlation s₁ s₂ x₁ x₂ y ≠ 0) : y ∈ ball x₁ (D ^ s₁) := by
  have hKs : Ks s₁ x₁ y ≠ 0 := by
    simp only [correlation, ne_eq, mul_eq_zero, map_eq_zero, not_or] at hy
    exact hy.1
  rw [mem_ball, dist_comm]
  exact (dist_mem_Icc_of_Ks_ne_zero hKs).2.trans_lt (half_lt_self_iff.mpr (defaultD_pow_pos a s₁))

/-- The constant from lemma 6.2.1.
Has value `2 ^ (231 * a ^ 3)` in the blueprint. -/
def C6_2_1 (a : ℕ) : ℝ≥0 := 2 ^ ((2 * 𝕔 + 6 + 𝕔 / 4) * a ^ 3)

private lemma aux_6_2_3 (s₁ s₂ : ℤ) (x₁ x₂ y y' : X) :
    ‖Ks s₂ x₂ y‖ₑ * ‖Ks s₁ x₁ y - Ks s₁ x₁ y'‖ₑ ≤ C2_1_3 a / volume (ball x₂ (D ^ s₂)) *
    (D2_1_3 a / volume (ball x₁ (D ^ s₁)) * (edist y y' ^ τ / (D ^ s₁) ^ τ)) := by
  apply mul_le_mul' enorm_Ks_le
  convert enorm_Ks_sub_Ks_le
  rw [← ENNReal.div_rpow_of_nonneg _ _ (τ_nonneg X), defaultτ]

/-- Ineq. (6.2.5) ≤ (6.2.9) from the proof of Lemma 6.2.1. -/
private lemma e625 {s₁ s₂ : ℤ} {x₁ x₂ y y' : X} (hy' : y ≠ y') (hs : s₁ ≤ s₂) :
    (2 * D ^ s₁) ^ τ *
    (‖correlation s₁ s₂ x₁ x₂ y - correlation s₁ s₂ x₁ x₂ y'‖ₑ / edist y y' ^ τ) ≤
    2 ^ ((2 * 𝕔 + 5 + 𝕔 / 4) * a ^ 3) /
    (volume (ball x₁ (D ^ s₁)) * volume (ball x₂ (D ^ s₂))) := by
  rw [mul_comm]
  refine ENNReal.mul_le_of_le_div ?_
  rw [ENNReal.div_le_iff_le_mul (.inl _) (.inl _)]; rotate_left
  · rw [← ENNReal.inv_ne_top, ← ENNReal.rpow_neg]
    exact ENNReal.rpow_ne_top_of_nonneg' (edist_pos.mpr hy') (edist_ne_top y y')
  · exact ENNReal.rpow_ne_top_of_nonneg (τ_nonneg X) (edist_ne_top y y')
  calc
    _ = ‖conj (Ks s₁ x₁ y) * Ks s₂ x₂ y - conj (Ks s₁ x₁ y') * Ks s₂ x₂ y +
        (conj (Ks s₁ x₁ y') * Ks s₂ x₂ y - conj (Ks s₁ x₁ y') * Ks s₂ x₂ y')‖ₑ := by
      simp only [correlation, sub_add_sub_cancel]
    _ ≤ ‖conj (Ks s₁ x₁ y) * Ks s₂ x₂ y - conj (Ks s₁ x₁ y') * Ks s₂ x₂ y‖ₑ +
        ‖conj (Ks s₁ x₁ y') * Ks s₂ x₂ y - conj (Ks s₁ x₁ y') * Ks s₂ x₂ y'‖ₑ := enorm_add_le _ _
    _ = ‖Ks s₁ x₁ y - Ks s₁ x₁ y'‖ₑ * ‖Ks s₂ x₂ y‖ₑ +
        ‖Ks s₁ x₁ y'‖ₑ * ‖Ks s₂ x₂ y - Ks s₂ x₂ y'‖ₑ := by
      simp only [← sub_mul, ← mul_sub, enorm_mul, RCLike.enorm_conj, ← map_sub]
    _ ≤ 2 ^ ((2 * 𝕔 + 4 + 𝕔 / 4) * a ^ 3) / (volume (ball x₁ (D ^ s₁)) *
        volume (ball x₂ (D ^ s₂))) *
        (edist y y' ^ τ / (D ^ s₁) ^ τ + edist y y' ^ τ / (D ^ s₂) ^ τ) := by
      have h2 : (2 : ℝ≥0∞) ^ ((2 * 𝕔 + 4 + 𝕔 / 4) * a ^ 3) = C2_1_3 a * D2_1_3 a := by
        simp only [C2_1_3, D2_1_3]
        norm_cast
        ring
      rw [mul_comm, mul_add, h2, mul_comm (volume _)]
      rw [ENNReal.mul_div_mul_comm (.inr measure_ball_ne_top) (.inl measure_ball_ne_top), mul_assoc]
      apply add_le_add (aux_6_2_3 s₁ s₂ x₁ x₂ y y')
      rw [← neg_sub, enorm_neg]
      convert aux_6_2_3 s₂ s₁ x₂ x₁ y' y using 1
      simp only [← mul_assoc,
        ← ENNReal.mul_div_mul_comm (.inr measure_ball_ne_top) (.inl measure_ball_ne_top)]
      rw [mul_comm (volume _), edist_comm]
    _ ≤ 2 ^ ((2 * 𝕔 + 4 + 𝕔 / 4) * a ^ 3) / (volume (ball x₁ (D ^ s₁)) *
        volume (ball x₂ (D ^ s₂))) * (2 * (edist y y' ^ τ / (D ^ s₁) ^ τ)) := by
      simp only [two_mul, defaultD, Nat.cast_pow, Nat.cast_ofNat, defaultτ]
      gcongr
      exact_mod_cast one_le_realD _
    _ = 2 ^ ((2 * 𝕔 + 4 + 𝕔 / 4) * a ^ 3) * 2 / (volume (ball x₁ (D ^ s₁)) *
        volume (ball x₂ (D ^ s₂))) * (edist y y' ^ τ / (D ^ s₁) ^ τ) := by
      rw [← mul_assoc, mul_comm _ 2]
      congr 1
      rw [← mul_div_assoc, mul_comm]
    _ ≤ 2 ^ ((2 * 𝕔 + 5 + 𝕔 / 4) * a ^ 3) / (volume (ball x₁ (D ^ s₁)) *
        volume (ball x₂ (D ^ s₂))) * (edist y y' ^ τ / (2 * D ^ s₁) ^ τ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (τ_nonneg X)]
      nth_rw 4 [← neg_neg τ]; rw [ENNReal.rpow_neg, ← ENNReal.div_eq_inv_mul, ← ENNReal.div_mul]
      rotate_left
      · right; rw [← ENNReal.inv_ne_top, ENNReal.rpow_neg, inv_inv]
        exact ENNReal.rpow_ne_top_of_nonneg' zero_lt_two ENNReal.ofNat_ne_top
      · exact .inr (ENNReal.rpow_ne_top_of_nonneg' zero_lt_two ENNReal.ofNat_ne_top)
      rw [← mul_assoc, ← mul_rotate, ← mul_div_assoc (2 ^ (-τ))]; gcongr ?_ / _ * _
      rw [show (2 : ℝ≥0∞) ^ (-τ) * 2 ^ ((2 * 𝕔 + 5 + 𝕔 / 4) * a ^ 3) =
        2 ^ ((2 * 𝕔 + 4 + 𝕔 / 4) * a ^ 3) * (2 ^ (a ^ 3) * 2 ^ (-τ)) by ring]; gcongr
      nth_rw 1 [← ENNReal.rpow_one 2, ← ENNReal.rpow_natCast,
        ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
      refine ENNReal.rpow_le_rpow_of_exponent_le one_le_two ?_
      rw [← sub_eq_add_neg, le_sub_iff_add_le']
      calc
        _ ≤ (1 : ℝ) + 1 := by gcongr; exact τ_le_one (X := X)
        _ ≤ a := by norm_cast; linarith only [four_le_a X]
        _ ≤ _ := mod_cast Nat.le_self_pow three_ne_zero _
    _ = _ := by rw [← ENNReal.mul_comm_div]

/-- Second part of Lemma 6.2.1 (eq. 6.2.3). -/
lemma correlation_kernel_bound {s₁ s₂ : ℤ} {x₁ x₂ : X} (hs : s₁ ≤ s₂) :
    iHolENorm (correlation s₁ s₂ x₁ x₂) x₁ (2 * D ^ s₁) τ ≤
    C6_2_1 a / (volume (ball x₁ (D ^ s₁)) * volume (ball x₂ (D ^ s₂))) := by
  -- 6.2.4
  have hφ' (y : X) : ‖correlation s₁ s₂ x₁ x₂ y‖ₑ ≤
      (C2_1_3 a) ^ 2 / (volume (ball x₁ (D ^ s₁)) * volume (ball x₂ (D ^ s₂))):= by
    simp only [correlation, enorm_mul, RCLike.enorm_conj, pow_two,
      ENNReal.mul_div_mul_comm (.inr measure_ball_ne_top) (.inl measure_ball_ne_top)]
    exact mul_le_mul' enorm_Ks_le enorm_Ks_le
  -- Bound 6.2.6 + 6.2.7
  calc
    _ ≤ C2_1_3 a ^ 2 / (volume (ball x₁ (D ^ s₁)) * volume (ball x₂ (D ^ s₂))) +
        2 ^ ((2 * 𝕔 + 5 + 𝕔 / 4) * a ^ 3) /
        (volume (ball x₁ (D ^ s₁)) * volume (ball x₂ (D ^ s₂))) := by
      apply add_le_add (iSup₂_le fun x _ ↦ hφ' x)
      simp only [ENNReal.mul_iSup, iSup_le_iff]
      intro z hz z' hz' hzz'
      convert e625 hzz' hs
      rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, ← Real.rpow_intCast,
        ← ENNReal.ofReal_rpow_of_pos (realD_pos _), ENNReal.ofReal_natCast,
        ENNReal.rpow_intCast]
    _ ≤ _ := by
      rw [← ENNReal.add_div]
      refine ENNReal.div_le_div_right ?_ _
      rw [C2_1_3, C6_2_1]
      norm_cast
      rw [← pow_mul]
      apply add_le_pow_two ?_ le_rfl ?_
      · ring_nf
        lia
      · ring_nf
        suffices 1 ≤ a ^ 3 by lia
        exact one_le_pow₀ (by linarith [four_le_a X])

variable [TileStructure Q D κ S o]

/-- Lemma 6.2.2. -/
lemma range_support {p : 𝔓 X} {g : X → ℂ} {y : X} (hpy : adjointCarleson p g y ≠ 0) :
    y ∈ ball (𝔠 p) (5 * D ^ 𝔰 p) := by
  simp only [adjointCarleson] at hpy
  obtain ⟨x, hxE, hx0⟩ := exists_ne_zero_of_setIntegral_ne_zero hpy
  have hxp : dist x (𝔠 p) < 4 * D ^ 𝔰 p := -- 6.2.13
    Grid_subset_ball (mem_of_subset_of_mem (fun _ ha ↦ ha.1) hxE)
  have hyx : dist y x ≤ 1 / 2 * D ^ 𝔰 p := by -- 6.2.14
    have hK : Ks (𝔰 p) x y ≠ 0 := by
      by_contra h0
      simp only [h0, map_zero, zero_mul, ne_eq, not_true] at hx0
    rw [dist_comm]
    convert (dist_mem_Icc_of_Ks_ne_zero hK).2 using 1
    ring
  have hpos := defaultD_pow_pos a (𝔰 p)
  have hle : (9 : ℝ) / 2 < 5 := by norm_num
  calc
    _ ≤ dist y x + dist x (𝔠 p) := dist_triangle ..
    _ ≤ 1 / 2 * D ^ 𝔰 p + 4 * D ^ 𝔰 p := add_le_add hyx hxp.le
    _ < _ := by ring_nf; gcongr -- uses hpos, hle.

/-- The constant from lemma 6.2.3. -/
def C6_2_3 (a : ℕ) : ℝ≥0 := 2 ^ (8 * a)

private lemma ineq_6_2_16 {p : 𝔓 X} {x : X} (hx : x ∈ E p) : dist_(p) (Q x) (𝒬 p) < 1 :=
  subset_cball hx.2.1

/-- Lemma 6.2.3 (dist version). -/
lemma uncertainty' (ha : 1 ≤ a) {p₁ p₂ : 𝔓 X} (hle : 𝔰 p₁ ≤ 𝔰 p₂)
    (hinter : (ball (𝔠 p₁) (5 * D ^ 𝔰 p₁) ∩ ball (𝔠 p₂) (5 * D ^ 𝔰 p₂)).Nonempty) {x₁ x₂ : X}
    (hx₁ : x₁ ∈ E p₁) (hx₂ : x₂ ∈ E p₂) :
    1 + dist_(p₁) (𝒬 p₁) (𝒬 p₂) ≤ C6_2_3 a * (1 + dist_{x₁, D ^ 𝔰 p₁} (Q x₁) (Q x₂)) := by
  -- Inequalities 6.2.16.
  have hp₁ : dist_(p₁) (𝒬 p₁) (Q x₁) < 1 := by rw [dist_comm]; exact ineq_6_2_16 hx₁
  have hp₂ := ineq_6_2_16 hx₂
  --Needed for ineq. 6.2.17
  have hss : ↑(𝓘 p₁) ⊆ ball (𝔠 p₂) (14 * D^𝔰 p₂) := by
    have h1D : 1 ≤ (D : ℝ) := one_le_realD a
    have hdist : dist (𝔠 p₁) (𝔠 p₂) < 10 * D ^ 𝔰 p₂ := by
      have h5 : 10 * (D : ℝ) ^ 𝔰 p₂ = 5 * D ^ 𝔰 p₂ + 5 * D ^ 𝔰 p₂ := by ring
      obtain ⟨y, hy₁, hy₂⟩ := hinter
      rw [mem_ball, dist_comm] at hy₁
      apply (dist_triangle ..).trans_lt
      apply (add_lt_add hy₁ hy₂).trans_le
      rw [h5]
      gcongr -- uses h1D
    refine Grid_subset_ball.trans fun x hx ↦ ?_
    rw [mem_ball] at hx ⊢
    calc
      _ ≤ dist x (𝔠 p₁) + dist (𝔠 p₁) (𝔠 p₂) := dist_triangle ..
      _ < 4 * D ^ 𝔰 p₁ + 10 * D ^ 𝔰 p₂ := add_lt_add hx hdist
      _ ≤ 4 * D ^ 𝔰 p₂ + 10 * D ^ 𝔰 p₂ := by gcongr -- uses h1D, hle
      _ = _ := by ring
  -- Inequality 6.2.17.
  have hp₁p₂ : dist_(p₁) (Q x₂) (𝒬 p₂) ≤ 2 ^ (6 * a) := by
    calc
      _ ≤ 2 ^ (6 * a) * dist_(p₂) (Q x₂) (𝒬 p₂) := by
        set r := (D : ℝ) ^ 𝔰 p₂ / 4 with hr_def
        have hr : 0 < (D : ℝ) ^ 𝔰 p₂ / 4 := by
          rw [div_pos_iff_of_pos_right (by positivity)]
          exact defaultD_pow_pos a (𝔰 p₂)
        have haux : dist_{𝔠 p₂, 2 ^ 6 * r} (Q x₂) (𝒬 p₂) ≤
          2 ^ (6 * a) * dist_{𝔠 p₂, r} (Q x₂) (𝒬 p₂) := by
          have h6a : (2 : ℝ) ^ (6 * a) = defaultA a ^ 6 := by simp; ring
          convert cdist_le_iterate hr (Q x₂) (𝒬 p₂) 6
        exact (cdist_mono (ball_subset_Grid.trans
          (hss.trans (ball_subset_ball (by linarith))))).trans haux
      _ ≤ _ := by
        nth_rw 2 [← mul_one (2 ^ _)]
        exact mul_le_mul_of_nonneg_left hp₂.le (by positivity)
  -- Auxiliary ineq. for 6.2.18
  have haux : dist_(p₁) (𝒬 p₁) (𝒬 p₂) ≤ 1 + 2 ^ (6 * a) + dist_(p₁) (Q x₁) (Q x₂) :=
    calc
      _ ≤ dist_(p₁) (𝒬 p₁) (Q x₁) + dist_(p₁) (Q x₁) (Q x₂) + dist_(p₁) (Q x₂) (𝒬 p₂) :=
        dist_triangle4 ..
      _ ≤ 1 + dist_(p₁) (Q x₁) (Q x₂) + 2 ^ (6 * a) := add_le_add_three hp₁.le le_rfl hp₁p₂
      _ = _ := by ring
  calc
    -- 6.2.18
    _ ≤ 2 + 2 ^ (6 * a) + dist_(p₁) (Q x₁) (Q x₂) := by
      have h2 : (2 + 2 ^ (6 * a) : ℝ) = 1 + (1 + 2 ^ (6 * a)) := by ring
      rw [h2, add_assoc]
      exact add_le_add le_rfl haux
    -- 6.2.21
    _ ≤ 2 + 2 ^ (6 * a) + dist_{x₁, 8 * D ^ 𝔰 p₁} (Q x₁) (Q x₂) := by
      apply add_le_add le_rfl
      -- 6.2.19
      have h1 : dist (𝔠 p₁) x₁ < 4 * D ^ 𝔰 p₁ := by rw [dist_comm]; exact Grid_subset_ball hx₁.1
      -- 6.2.20
      have hI : ↑(𝓘 p₁) ⊆ ball x₁ (8 * D ^ 𝔰 p₁) := by
        refine Grid_subset_ball.trans fun x hx ↦ ?_
        calc
          _ ≤ dist x (𝔠 p₁) + dist (𝔠 p₁) x₁ := dist_triangle _ _ _
          _ < 4 * D ^ 𝔰 p₁ + 4 * D ^ 𝔰 p₁ := add_lt_add hx h1
          _ = _ := by ring
      exact cdist_mono (subset_trans ball_subset_Grid hI)
    -- 6.2.22
    _ ≤ 2 + 2 ^ (6 * a) + 2 ^ (3 * a) * dist_{x₁, D ^ 𝔰 p₁} (Q x₁) (Q x₂) := by
      gcongr
      have hr : 0 < (D : ℝ) ^ 𝔰 p₁ := defaultD_pow_pos a (𝔰 p₁)
      have h8 : (8 : ℝ) = 2 ^ 3 := by norm_num
      have h3a : (2 : ℝ) ^ (3 * a) = defaultA a ^ 3 := by simp; ring
      convert cdist_le_iterate hr (Q x₁) (Q x₂) 3 -- uses h8, h3a
    -- 6.2.15
    _ ≤ _ := by
      have hpow : (2 : ℝ) + 2 ^ (6 * a) ≤ 2 ^ (a * 8) :=
        calc
          _ ≤ (2 : ℝ) ^ (6 * a) + 2 ^ (6 * a) := by
            apply add_le_add_left
            norm_cast
            nth_rw 1 [← pow_one 2]
            exact Nat.pow_le_pow_right zero_lt_two (by lia)
          _ = 2 * (2 : ℝ) ^ (6 * a) := by ring
          _ ≤ _ := by
            nth_rw 1 [← pow_one 2, ← pow_add]
            norm_cast
            exact Nat.pow_le_pow_right zero_lt_two (by lia)
      have h38 : 3 ≤ 8 := by lia
      have h12 : (1 : ℝ) ≤ 2 := by norm_num
      rw [C6_2_3]
      conv_rhs => ring_nf
      push_cast
      rw [mul_comm 3]
      gcongr

/-- Lemma 6.2.3 (edist version). -/
lemma uncertainty (ha : 1 ≤ a) {p₁ p₂ : 𝔓 X} (hle : 𝔰 p₁ ≤ 𝔰 p₂)
    (hinter : (ball (𝔠 p₁) (5 * D ^ 𝔰 p₁) ∩ ball (𝔠 p₂) (5 * D ^ 𝔰 p₂)).Nonempty) {x₁ x₂ : X}
    (hx₁ : x₁ ∈ E p₁) (hx₂ : x₂ ∈ E p₂) :
    1 + edist_(p₁) (𝒬 p₁) (𝒬 p₂) ≤ C6_2_3 a * (1 + edist_{x₁, D ^ 𝔰 p₁} (Q x₁) (Q x₂)) := by
  have hC : C6_2_3 a = ENNReal.ofReal (C6_2_3 a) := by rw [ENNReal.ofReal_coe_nnreal]
  simp only [edist_dist, ← ENNReal.ofReal_one, hC, ← ENNReal.ofReal_add zero_le_one dist_nonneg,
    ← ENNReal.ofReal_mul NNReal.zero_le_coe]
  exact ENNReal.ofReal_le_ofReal (uncertainty' ha hle hinter hx₁ hx₂)

section lemma_6_1_5

/-- The constant from lemma 6.1.5.
Has value `2 ^ (232 * a ^ 3)` in the blueprint. -/
def C6_1_5 (a : ℕ) : ℝ≥0 := 2 ^ ((2 * 𝕔 + 7 + 𝕔 / 4) * a ^ 3)

lemma C6_1_5_bound (ha : 4 ≤ a) :
    2 ^ ((2 * 𝕔 + 6 + 𝕔 / 4) * a ^ 3 + 1) * 2 ^ (11 * a) ≤ C6_1_5 a := by
  have h142 : a ^ 3 = a ^ 2 * a := rfl
  rw [C6_1_5, ← pow_add]
  exact pow_le_pow le_rfl one_le_two (by nlinarith)

open GridStructure

set_option backward.isDefEq.respectTransparency false in
lemma complex_exp_lintegral {p : 𝔓 X} {g : X → ℂ} (y : X) :
    conj (∫ y1 in E p, conj (Ks (𝔰 p) y1 y) * exp (I * (Q y1 y1 - Q y1 y)) * g y1) =
    ∫ y1 in E p, Ks (𝔰 p) y1 y * exp (I * (-Q y1 y1 + Q y1 y)) * conj (g y1) := by
  simp only [← integral_conj, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  congr; ext x; rw [← exp_conj]; congr
  simp only [map_mul, conj_I, map_sub, conj_ofReal]
  ring

/-- Definition (6.2.27). -/
def I12 (p p' : 𝔓 X) (g : X → ℂ) (x1 x2 : X) : ℝ≥0∞ :=
  ‖(∫ y, exp (I * (-Q x1 y + Q x2 y)) * correlation (𝔰 p') (𝔰 p) x1 x2 y) * g x1 * g x2‖ₑ

/-- Inequality (6.2.28). -/
lemma I12_le' {p p' : 𝔓 X} (hle : 𝔰 p' ≤ 𝔰 p) {g : X → ℂ} (x1 : E p') (x2 : E p) :
    I12 p p' g x1 x2 ≤
    2 ^ ((2 * 𝕔 + 6 + 𝕔 / 4) * a ^ 3 + 8 * a) *
      ((1 + edist_{x1.1, D ^ 𝔰 p'} (Q x1) (Q x2)) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹)) /
    volume (ball x2.1 (D ^ 𝔰 p)) * ‖g x1‖ₑ * ‖g x2‖ₑ := by
  have hD' : 0 < (D : ℝ) ^ 𝔰 p' := defaultD_pow_pos a (𝔰 p')
  have hsupp : support (correlation (𝔰 p') (𝔰 p) x1.1 x2) ⊆ ball x1 (D ^ 𝔰 p') :=
    fun _ hx ↦ mem_ball_of_correlation_ne_zero hx
  -- For compatibility with holder_van_der_corput
  have heq : 2 ^ ((2 * 𝕔 + 6 + 𝕔 / 4) * a ^ 3 + 8 * a) *
      (1 + edist_{x1.1, D ^ 𝔰 p'} (Q x1) (Q x2)) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) /
      volume (ball x2.1 (D ^ 𝔰 p)) =
      (2 ^ ((2 * 𝕔 + 6 + 𝕔 / 4) * a ^ 3 + 8 * a)) / volume (ball x2.1 (D ^ 𝔰 p)) *
      (1 + edist_{x1.1, D ^ 𝔰 p'} (Q x1) (Q x2)) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) := by
    rw [ENNReal.mul_comm_div, mul_comm, mul_comm _ (2 ^ _), mul_div_assoc]
  simp only [I12, enorm_mul]
  gcongr
  simp_rw [← sub_eq_neg_add]
  apply (holder_van_der_corput hsupp).trans
  rw [heq, edist_comm]
  gcongr
  · have hbdd := correlation_kernel_bound (a := a) (X := X) hle (x₁ := x1) (x₂ := x2)
    have hle : C2_0_5 a * volume (ball x1.1 (D ^ 𝔰 p')) *
        iHolENorm (correlation (𝔰 p') (𝔰 p) x1.1 x2.1) x1 (2 * D ^ 𝔰 p') τ ≤
        C2_0_5 a * volume (ball x1.1 (D ^ 𝔰 p')) *
        (C6_2_1 a / (volume (ball x1.1 (D ^ 𝔰 p')) * volume (ball x2.1 (D ^ 𝔰 p)))) := by
      gcongr
    -- Note: simp, ring_nf, field_simp did not help (because we work with ℝ≥0∞).
    have heq : C2_0_5 a * volume (ball x1.1 (D ^ 𝔰 p')) *
        (C6_2_1 a / (volume (ball x1.1 (D ^ 𝔰 p')) * volume (ball x2.1 (D ^ 𝔰 p)))) =
        C2_0_5 a * (C6_2_1 a / volume (ball x2.1 (D ^ 𝔰 p))) := by
      simp only [mul_assoc]
      congr 1
      rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (.inr measure_ball_ne_top)
        (.inl measure_ball_ne_top), ← mul_assoc, ← mul_assoc, ENNReal.mul_inv_cancel
        (measure_ball_pos volume _ hD').ne' measure_ball_ne_top, one_mul, ENNReal.div_eq_inv_mul]
    apply hle.trans
    rw [heq, mul_div]
    apply ENNReal.div_le_div _ le_rfl
    simp only [C2_0_5, C6_2_1, ENNReal.coe_pow, ENNReal.coe_ofNat]
    rw [pow_add, mul_comm]
    norm_cast
    gcongr
    · exact one_le_two
    · lia

private lemma exp_ineq (ha : 4 ≤ a) : 0 < (8 * a : ℕ) * -(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹ + 1 := by
  have hpos : 0 < (a : ℝ) ^ 2 * 2 + a ^ 3 := by positivity
  ring_nf
  rw [Nat.cast_mul, Nat.cast_ofNat, sub_pos, ← div_eq_mul_inv, div_lt_one hpos]
  norm_cast
  nlinarith

/-- Inequality (6.2.29). -/
lemma I12_le (ha : 4 ≤ a) {p p' : 𝔓 X} (hle : 𝔰 p' ≤ 𝔰 p) {g : X → ℂ}
    (hinter : (ball (𝔠 p') (5 * D ^ 𝔰 p') ∩ ball (𝔠 p) (5 * D ^ 𝔰 p)).Nonempty)
    (x1 : E p') (x2 : E p) :
    I12 p p' g x1 x2 ≤
    (2 ^ ((2 * 𝕔 + 6 + 𝕔 / 4) * a ^ 3 + 8 * a + 1) *
      ((1 + edist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹))) /
    volume (ball x2.1 (D ^ 𝔰 p)) * ‖g x1‖ₑ * ‖g x2‖ₑ := by
  apply (I12_le' hle x1 x2).trans
  gcongr ?_ * _ * _
  rw [pow_add 2 _ 1, pow_one, mul_comm _ 2, mul_assoc, mul_comm 2 (_ * _), mul_assoc]
  gcongr
  -- Now we need to use Lemma 6.2.3 to conclude this inequality.
  have h623 := uncertainty (by lia) hle hinter x1.2 x2.2
  rw [C6_2_3, ENNReal.coe_pow, ENNReal.coe_ofNat] at h623
  have hneg : -(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹ < 0 :=
    neg_neg_iff_pos.mpr (inv_pos.mpr (by norm_cast; nlinarith))
  rw [← ENNReal.rpow_le_rpow_iff_of_neg hneg] at h623
  have h0 : ((2 : ℝ≥0∞) ^ (8 * a)) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) ≠ 0 := by simp
  have h210 : (2 : ℝ≥0∞) ^ (1 : ℝ) ≠ 0 := by rw [ENNReal.rpow_one]; exact two_ne_zero
  rw [ENNReal.mul_rpow_of_ne_top (by finiteness) (by finiteness), mul_comm,
    ← ENNReal.le_div_iff_mul_le (.inl h0) (.inl (by finiteness))] at h623
  apply h623.trans
  rw [ENNReal.div_eq_inv_mul, mul_comm _ 2]
  gcongr
  conv_rhs => rw [← ENNReal.rpow_one (2 : ℝ≥0∞)]
  rw [ENNReal.inv_le_iff_le_mul (fun _ ↦ h0) (fun _ ↦ h210), ← ENNReal.rpow_natCast 2,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
  exact ENNReal.one_le_rpow one_le_two (exp_ineq ha)

/-- Inequality (6.2.32). -/
lemma volume_coeGrid_le {p : 𝔓 X} (x2 : E p) :
    volume (𝓘 p : Set X) ≤ 2 ^ (3 * a) * volume (ball x2.1 (D ^ 𝔰 p)) := by
  -- Inequality 6.2.30
  have hdist : dist (𝔠 p) x2 < 4 * D ^ 𝔰 p :=
    dist_comm (𝔠 p) x2 ▸ Grid_subset_ball (mem_of_subset_of_mem (fun _ ha ↦ ha.1) x2.prop)
  -- Inclusion 6.2.31
  have hsub : (𝓘 p : Set X) ⊆ ball x2 (8 * D ^ 𝔰 p) := by
    refine Grid_subset_ball.trans fun x hx ↦ ?_
    calc
      _ ≤ dist x (𝔠 p) + dist (𝔠 p) x2 := dist_triangle ..
      _ < 4 * D ^ 𝔰 p + 4 * D ^ 𝔰 p := add_lt_add hx hdist
      _ = _ := by ring
  apply (measure_mono hsub).trans
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num]
  convert measure_ball_two_le_same_iterate (μ := volume) x2.1 (D ^ 𝔰 p) 3 using 2
  rw [mul_comm 3, pow_mul]; simp

lemma bound_6_2_29 (ha : 4 ≤ a) {p p' : 𝔓 X} (x2 : E p) :
    2 ^ ((2 * 𝕔 + 6 + 𝕔 / 4) * a ^ 3 + 8 * a + 1) *
    (1 + edist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) / volume (ball x2.1 (D ^ 𝔰 p)) ≤
    C6_1_5 a *
    (1 + edist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) / volume (𝓘 p : Set X) := by
  rw [mul_comm, mul_div_assoc, mul_comm (C6_1_5 a : ℝ≥0∞), mul_div_assoc]
  refine mul_le_mul_right ?_ _
  calc
    _ = 2 ^ ((2 * 𝕔 + 6 + 𝕔 / 4) * a ^ 3 + 1) * 2 ^ (11 * a) * 2 ^ (-(3 : ℤ) * a) /
        volume (ball x2.1 (D ^ 𝔰 p)) := by
      simp_rw [← zpow_natCast, ← ENNReal.zpow_add two_ne_zero ENNReal.ofNat_ne_top]
      congr; push_cast; ring
    _ = 2 ^ ((2 * 𝕔 + 6 + 𝕔 / 4) * a ^ 3 + 1) * 2 ^ (11 * a) /
        (2 ^ (3 * a) * volume (ball x2.1 (D ^ 𝔰 p))) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (by left; positivity) (by left; simp),
        ← mul_assoc, ← zpow_natCast _ (3 * a), ← ENNReal.zpow_neg]
      congr
    _ ≤ C6_1_5 a / (2 ^ (3 * a) * volume (ball x2.1 (D ^ 𝔰 p))) := by
      gcongr; exact ENNReal.coe_le_coe.mpr (C6_1_5_bound ha)
    _ ≤ _ := by gcongr; exact volume_coeGrid_le _

omit [TileStructure Q D κ S o] in
lemma enorm_eq_zero_of_notMem_closedBall {g : X → ℂ} (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    {x : X} (hx : x ∉ closedBall o (D ^ S / 4)) : ‖g x‖ₑ = 0 := by
  rw [enorm_eq_zero, ← norm_eq_zero]
  refine le_antisymm ((hg1 _).trans ?_) (norm_nonneg _)
  rw [indicator_of_notMem (notMem_subset G_subset (notMem_subset ball_subset_closedBall hx))]

omit [TileStructure Q D κ S o] in
lemma eq_zero_of_notMem_closedBall {g : X → ℂ} (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    {x : X} (hx : x ∉ closedBall o (D ^ S / 4)) : g x = 0 := by
  simpa [coe_nnnorm, norm_eq_zero] using enorm_eq_zero_of_notMem_closedBall hg1 hx

lemma boundedCompactSupport_star_Ks_mul_g {p' : 𝔓 X} {g : X → ℂ}
    (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    BoundedCompactSupport fun x : X × X ↦ conj (Ks (𝔰 p') x.1 x.2) * g x.1 := by
  apply BoundedCompactSupport.mul_bdd_left' (bcs_of_measurable_of_le_indicator_g hg hg1)
    continuous_fst
  · exact quasiMeasurePreserving_fst
  · fun_prop
  · intros K hK
    obtain ⟨C, hC⟩ := isBounded_iff.1 hK.isBounded
    apply isCompact_of_isClosed_isBounded
      ((IsClosed.preimage continuous_fst hK.isClosed).inter (isClosed_tsupport _))
    rw [isBounded_iff]
    use D ^ 𝔰 p' + C
    intros x hx y hy
    rw [Prod.dist_eq, sup_le_iff]
    constructor
    · calc
        _ ≤ _ := hC hx.1 hy.1
        _ ≤ _ := le_add_of_nonneg_left (by positivity)
    · calc
        _ ≤ dist x.2 x.1 + dist x.1 y.1 + dist y.1 y.2 := dist_triangle4 ..
        _ ≤ D ^ 𝔰 p' / 2 + C + D ^ 𝔰 p' / 2 := by
          gcongr
          · rw [dist_comm]
            have hx' : x ∈ tsupport fun x ↦ Ks (𝔰 p') x.1 x.2 := by
              convert hx.2 using 1
              simp only [tsupport]
              apply congr_arg
              ext z
              simp only [mem_support, ne_eq, map_eq_zero]
            exact (dist_mem_Icc_of_mem_tsupport_Ks hx').2
          · exact hC hx.1 hy.1
          · have hy' : y ∈ tsupport fun x ↦ Ks (𝔰 p') x.1 x.2 := by
              convert hy.2 using 1
              simp only [tsupport]
              apply congr_arg
              ext z
              simp only [mem_support, ne_eq, map_eq_zero]
            exact (dist_mem_Icc_of_mem_tsupport_Ks hy').2
        _ = _ := by ring
  · intro A hA; rw [isBounded_image_iff]
    obtain ⟨C, hC0, hC⟩ := Bornology.IsBounded.exists_bound_of_norm_Ks hA (𝔰 p')
    use C + C; intro x hx y hy; rw [dist_conj_conj]
    calc
      _ ≤ _ := dist_le_norm_add_norm ..
      _ ≤ _ := add_le_add (hC x.1 x.2 hx) (hC y.1 y.2 hy)

lemma boundedCompactSupport_Ks_mul_star_g {p : 𝔓 X} {g : X → ℂ}
    (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    BoundedCompactSupport fun x : X × X ↦ Ks (𝔰 p) x.1 x.2 * (conj ∘ g) x.1 := by
  conv => enter [1, x]; rw [← conj_conj (_ * _), map_mul, comp_apply, conj_conj]
  exact (boundedCompactSupport_star_Ks_mul_g hg hg1).conj

lemma boundedCompactSupport_aux_6_2_26 {p p' : 𝔓 X} {g : X → ℂ}
    (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    BoundedCompactSupport fun (x, z1, z2) ↦
      conj (Ks (𝔰 p') z1 x) * exp (I * (Q z1 z1 - Q z1 x)) * g z1 *
      (Ks (𝔰 p) z2 x * exp (I * (-Q z2 z2 + Q z2 x)) * conj (g z2)) := by
  suffices BoundedCompactSupport fun (x, z1, z2) ↦
      conj (Ks (𝔰 p') z1 x) * g z1 * (Ks (𝔰 p) z2 x * conj (g z2)) by
    have heq : (fun (x, z1, z2) ↦ conj (Ks (𝔰 p') z1 x) *
        exp (I * (Q z1 z1 - Q z1 x)) * g z1 * (Ks (𝔰 p) z2 x *
          exp (I * (-Q z2 z2 + Q z2 x)) * conj (g z2))) =
        fun (x, z1, z2) ↦ conj (Ks (𝔰 p') z1 x) * g z1 *
          (Ks (𝔰 p) z2 x * conj (g z2)) * (exp (I * (Q z1 z1 - Q z1 x)) *
            exp (I * (-Q z2 z2 + Q z2 x))) := by ext; ring
    exact heq ▸ BoundedCompactSupport.mul_bdd_right this
      ⟨(Measurable.stronglyMeasurable (by fun_prop)).aestronglyMeasurable, lt_of_le_of_lt
        (eLpNorm_le_of_ae_bound (C := 1) (Filter.Eventually.of_forall
          (fun x ↦ by simp [← ofReal_sub, mul_comm I, ← ofReal_neg, ← ofReal_add]))) (by simp)⟩
  constructor
  · -- MemLp
    constructor
    · -- AEStronglyMeasurable
      exact (Measurable.stronglyMeasurable (by fun_prop)).aestronglyMeasurable
    · -- eLpNorm < ⊤
      simp only [eLpNorm_exponent_top, eLpNormEssSup_lt_top_iff_isBoundedUnder]
      have h1 : Filter.IsBoundedUnder (· ≤ ·) (ae volume) fun x : X × X ↦
          ‖conj (Ks (𝔰 p') x.1 x.2) * g x.1‖₊ := by
        rw [← eLpNormEssSup_lt_top_iff_isBoundedUnder, ← eLpNorm_exponent_top]
        exact (boundedCompactSupport_star_Ks_mul_g hg hg1).memLp_top.eLpNorm_lt_top
      have h2 : Filter.IsBoundedUnder (· ≤ ·) (ae volume) fun x : X × X ↦
          ‖Ks (𝔰 p) x.1 x.2 * conj (g x.1)‖₊ := by
        rw [← eLpNormEssSup_lt_top_iff_isBoundedUnder, ← eLpNorm_exponent_top]
        exact (boundedCompactSupport_Ks_mul_star_g hg hg1).memLp_top.eLpNorm_lt_top
      obtain ⟨B, hB⟩ := h1
      obtain ⟨C, hC⟩ := h2
      use B * C
      simp only [nnnorm_mul, RCLike.nnnorm_conj, Filter.eventually_map] at hB hC ⊢
      have hp1 : QuasiMeasurePreserving (fun z : X × X × X ↦ (z.2.1, z.1)) volume volume := by
        suffices QuasiMeasurePreserving (Prod.map (id (α := X)) (Prod.fst (α := X) (β := X)))
            volume volume from measurePreserving_swap.quasiMeasurePreserving.comp this
        fun_prop
      have hp2 : QuasiMeasurePreserving (fun z : X × X × X ↦ (z.2.2, z.1)) volume volume := by
        suffices QuasiMeasurePreserving (Prod.map (id (α := X)) (Prod.snd (α := X) (β := X)))
            volume volume from measurePreserving_swap.quasiMeasurePreserving.comp this
        fun_prop
      filter_upwards [hp1.ae hB, hp2.ae hC] with x h1x h2x
      exact mul_le_mul' h1x h2x
  · -- HasCompactSupport
    rw [← exists_compact_iff_hasCompactSupport]
    use closedBall o (D ^ S) ×ˢ closedBall o (D ^ S / 4) ×ˢ closedBall o (D ^ S / 4)
    refine ⟨(isCompact_closedBall _ _).prod
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)), fun x hx ↦ ?_⟩
    simp only [mem_prod, not_and_or] at hx
    simp only [mul_eq_zero, map_eq_zero]
    rcases hx with hx | hx | hx
    · left
      by_cases hx2 : x.2.1 ∈ closedBall o (D ^ S / 4)
      · left
        simp only [mem_closedBall, not_le] at hx hx2
        apply Ks_eq_zero_of_le_dist
        calc
          _ ≤ (D : ℝ) ^ S / 2 := by
            rw [← zpow_natCast]
            have : 1 ≤ (D : ℝ) := one_le_realD _
            have : 𝔰 p' ≤ S := (range_s_subset (X := X) (mem_range_self (𝓘 p'))).2
            gcongr
          _ ≤ D ^ S - D ^ S / 4 := by ring_nf; gcongr _ * ?_; norm_num
          _ ≤ dist x.1 o - D ^ S / 4 := by gcongr
          _ ≤ dist x.1 o - dist x.2.1 o := by gcongr
          _ ≤ _ := by rw [tsub_le_iff_right]; exact dist_triangle_left _ _ _
      · exact .inr (eq_zero_of_notMem_closedBall hg1 hx2)
    · exact .inl (.inr (eq_zero_of_notMem_closedBall hg1 hx))
    · exact .inr (.inr (eq_zero_of_notMem_closedBall hg1 hx))

set_option backward.isDefEq.respectTransparency false in
lemma bound_6_2_26_aux {p p' : 𝔓 X} {g : X → ℂ} :
    let f := fun (x, z1, z2) ↦
      conj (Ks (𝔰 p') z1 x) * exp (I * (Q z1 z1 - Q z1 x)) * g z1 *
      (Ks (𝔰 p) z2 x * exp (I * (-Q z2 z2 + Q z2 x)) * conj (g z2))
    ∫⁻ x in E p' ×ˢ E p, ‖∫ y, f (y, x)‖ₑ = ∫⁻ z in E p' ×ˢ E p, I12 p p' g z.1 z.2 := by
  congr; ext x
  -- We move `exp (I * Q x.1 x.1)`, `exp (I * -Q x.2 x.2)` and `g x.1` to the right
  -- so that we can take their product with `conj (g x.2)` out of the integral.
  have heq :
      ∫ y, conj (Ks (𝔰 p') x.1 y) * exp (I * (Q x.1 x.1 - Q x.1 y)) * g x.1 *
      (Ks (𝔰 p) x.2 y * exp (I * (-Q x.2 x.2 + Q x.2 y)) * conj (g x.2)) =
      ∫ y, conj (Ks (𝔰 p') x.1 y) * exp (I * -Q x.1 y) *
      (Ks (𝔰 p) x.2 y * exp (I * Q x.2 y)) * (exp (I * Q x.1 x.1) *
        exp (I * -Q x.2 x.2) * g x.1 * conj (g x.2)) := by
    congr; ext y
    simp_rw [mul_add I, mul_sub I, sub_eq_add_neg, exp_add]
    ring_nf
  simp only [I12, enorm_mul]
  rw [heq, integral_mul_const, enorm_mul, enorm_mul, enorm_mul, enorm_mul, enorm_exp_I_mul_ofReal,
    show ‖exp (_)‖ₑ = 1 from mod_cast enorm_exp_I_mul_ofReal _,
    RCLike.enorm_conj, one_mul, one_mul, ← mul_assoc]
  simp only [mul_neg, correlation]
  congr; ext y
  rw [mul_add I, exp_add]
  ring_nf

set_option backward.isDefEq.respectTransparency false in
lemma bound_6_2_26 {p p' : 𝔓 X} {g : X → ℂ}
    (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    ‖∫ y, adjointCarleson p' g y * conj (adjointCarleson p g y)‖ₑ ≤
    ∫⁻ z in E p' ×ˢ E p, I12 p p' g z.1 z.2 := by
  have haux : ∀ y,
      conj (∫ y1 in E p, conj (Ks (𝔰 p) y1 y) * exp (I * (Q y1 y1 - Q y1 y)) * g y1) =
      ∫ y1 in E p, Ks (𝔰 p) y1 y * exp (I * (-Q y1 y1 + Q y1 y)) * conj (g y1) :=
    complex_exp_lintegral
  simp_rw [adjointCarleson, haux, ← setIntegral_prod_mul]
  rw [← setIntegral_univ]
  let f := fun (x, z1, z2) ↦
    conj (Ks (𝔰 p') z1 x) * exp (I * (Q z1 z1 - Q z1 x)) * g z1 *
    (Ks (𝔰 p) z2 x * exp (I * (-Q z2 z2 + Q z2 x)) * conj (g z2))
  have hf : IntegrableOn f (univ ×ˢ E p' ×ˢ E p) (volume.prod (volume.prod volume)) :=
    (boundedCompactSupport_aux_6_2_26 hg hg1).integrable.integrableOn
  erw [← setIntegral_prod _ hf, ← setIntegral_prod_swap, setIntegral_prod _ (hf.swap), restrict_univ]
  simp_rw [← bound_6_2_26_aux]
  exact enorm_integral_le_lintegral_enorm _

-- We assume 6.2.23.
lemma correlation_le_of_nonempty_inter (ha : 4 ≤ a) {p p' : 𝔓 X} (hle : 𝔰 p' ≤ 𝔰 p) {g : X → ℂ}
    (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (hinter : (ball (𝔠 p') (5 * D ^ 𝔰 p') ∩ ball (𝔠 p) (5 * D ^ 𝔰 p)).Nonempty) :
    ‖∫ y, adjointCarleson p' g y * conj (adjointCarleson p g y)‖ₑ ≤
    C6_1_5 a * (1 + edist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) /
    volume (𝓘 p : Set X) * (∫⁻ y in E p', ‖g y‖ₑ) * ∫⁻ y in E p, ‖g y‖ₑ := by
  calc
    _ ≤ _ := bound_6_2_26 hg hg1
    _ ≤ ∫⁻ z in E p' ×ˢ E p,
        C6_1_5 a * (1 + edist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) /
        volume (𝓘 p : Set X) * ‖g z.1‖ₑ * ‖g z.2‖ₑ := by
      refine setLIntegral_mono' (measurableSet_E.prod measurableSet_E) fun z hz ↦ ?_
      apply (I12_le ha hle hinter ⟨_, hz.1⟩ ⟨_, hz.2⟩).trans
      gcongr ?_ * _ * _; exact bound_6_2_29 ha _
    _ = _ := by
      simp only [mul_assoc]
      rw [lintegral_const_mul _ (by fun_prop)]; congr 1
      rw [← lintegral_prod_mul (by fun_prop) (by fun_prop), prod_restrict]; rfl

/-- If (6.2.23) does not hold, the LHS is zero and the result follows trivially. -/
lemma correlation_le_of_empty_inter {p p' : 𝔓 X} {g : X → ℂ}
    (hinter : ¬(ball (𝔠 p') (5 * D ^ 𝔰 p') ∩ ball (𝔠 p) (5 * D ^ 𝔰 p)).Nonempty) :
    ‖∫ y, adjointCarleson p' g y * conj (adjointCarleson p g y)‖ₑ ≤
    C6_1_5 a * (1 + edist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) /
    volume (𝓘 p : Set X) * (∫⁻ y in E p', ‖g y‖ₑ) * ∫⁻ y in E p, ‖g y‖ₑ := by
  suffices ‖∫ y, adjointCarleson p' g y * conj (adjointCarleson p g y)‖ₑ = 0 by
    rw [this]; exact zero_le
  simp only [inter_nonempty, not_exists, not_and_or] at hinter
  rw [enorm_eq_zero]
  apply integral_eq_zero_of_ae (Eq.eventuallyEq _)
  ext y
  rcases hinter y with hp'y | hpy
  · have hp'0 : adjointCarleson p' g y = 0 := by
      by_contra hy
      exact hp'y (range_support hy)
    simp [hp'0, zero_mul]
  · have hp'0 : adjointCarleson p g y = 0 := by
      by_contra hy
      exact hpy (range_support hy)
    simp [hp'0, map_zero, mul_zero]

/-- Part 1 of Lemma 6.1.5 (eq. 6.1.43). -/
lemma correlation_le {p p' : 𝔓 X} (hle : 𝔰 p' ≤ 𝔰 p) {g : X → ℂ}
    (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    ‖∫ y, adjointCarleson p' g y * conj (adjointCarleson p g y)‖ₑ ≤
    C6_1_5 a * (1 + edist_(p') (𝒬 p') (𝒬 p)) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) /
    volume (𝓘 p : Set X) * (∫⁻ y in E p', ‖g y‖ₑ) * ∫⁻ y in E p, ‖g y‖ₑ := by
  by_cases hinter : (ball (𝔠 p') (5 * D ^ 𝔰 p') ∩ ball (𝔠 p) (5 * D ^ 𝔰 p)).Nonempty
  · exact correlation_le_of_nonempty_inter (four_le_a X) hle hg hg1 hinter
  · exact correlation_le_of_empty_inter hinter

/-- Part 2 of Lemma 6.1.5 (claim 6.1.44). -/
lemma correlation_zero_of_ne_subset {p p' : 𝔓 X} (hle : 𝔰 p' ≤ 𝔰 p) {g : X → ℂ}
    (hp : ¬(𝓘 p' : Set X) ⊆ ball (𝔠 p) (14 * D ^ 𝔰 p)) :
    ‖∫ y, adjointCarleson p' g y * conj (adjointCarleson p g y)‖ₑ = 0 := by
  contrapose! hp; rw [enorm_ne_zero] at hp
  obtain ⟨y, hy⟩ := exists_ne_zero_of_integral_ne_zero hp
  rw [mul_ne_zero_iff, map_ne_zero] at hy
  refine Grid_subset_ball.trans fun x (mx : x ∈ ball (𝔠 p') (4 * D ^ 𝔰 p')) ↦ ?_
  rw [mem_ball] at mx ⊢
  calc
    _ ≤ dist x (𝔠 p') + dist (𝔠 p') (𝔠 p) := dist_triangle ..
    _ < 4 * D ^ 𝔰 p' + (5 * D ^ 𝔰 p' + 5 * D ^ 𝔰 p) := by
      gcongr
      exact dist_lt_of_not_disjoint_ball
        (not_disjoint_iff.mpr ⟨_, range_support hy.1, range_support hy.2⟩)
    _ ≤ 4 * D ^ 𝔰 p + (5 * D ^ 𝔰 p + 5 * D ^ 𝔰 p) := by gcongr <;> exact one_le_realD a
    _ = _ := by ring

end lemma_6_1_5

end Tile
