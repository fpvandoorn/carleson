import Carleson.Carleson
import Carleson.HomogeneousType
import Carleson.Theorem1_1.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Convolution

open BigOperators
open Finset
open Complex

noncomputable section


def dirichletKernel (N : ℕ) : ℝ → ℂ := fun x ↦ ∑ n in Icc (-Int.ofNat ↑N) N, fourier n (x : AddCircle (2 * Real.pi))

def dirichletKernel' (N : ℕ) : ℝ → ℂ := fun x ↦ (exp (I * N * x) / (1 - exp (-I * x)) + exp (-I * N * x) / (1 - exp (I * x)))

lemma dirichletKernel_periodic {N : ℕ} : Function.Periodic (dirichletKernel N) (2 * Real.pi) := by
  sorry

lemma dirichletKernel'_periodic {N : ℕ} : Function.Periodic (dirichletKernel' N) (2 * Real.pi) := by
  sorry

@[measurability]
lemma dirichletKernel'_measurable {N : ℕ} : Measurable (dirichletKernel' N) := by
  apply Measurable.add
  . apply Measurable.div <;> measurability
  . apply Measurable.div <;> measurability

/-Second part of Lemma 10.10 (Dirichlet kernel) from the paper.-/
lemma dirichletKernel_eq {N : ℕ} {x : ℝ} (h : cexp (I * x) ≠ 1) : dirichletKernel N x = dirichletKernel' N x := by
  have : (cexp (1 / 2 * I * x) - cexp (-1 / 2 * I * x)) * dirichletKernel N x
      = cexp ((N + 1 / 2) * I * x) - cexp (-(N + 1 / 2) * I * x) := by
    calc (cexp (1 / 2 * I * x) - cexp (-1 / 2 * I * x)) * dirichletKernel N x
      _ = ∑ n in Icc (-Int.ofNat N) ↑N, (cexp ((n + 1 / 2) * I * ↑x) - cexp ((n - 1 / 2) * I * ↑x)) := by
        rw [dirichletKernel]
        rw [mul_sum]
        congr
        ext n
        simp
        rw [sub_mul, ←exp_add, ←exp_add]
        congr <;>
        . ring_nf
          congr 1
          rw [mul_assoc, mul_assoc]
          congr
          rw [←mul_assoc, mul_comm, ←mul_assoc, inv_mul_cancel, one_mul]
          norm_cast
          exact Real.pi_pos.ne.symm
      _ = ∑ n in Icc (-Int.ofNat N) ↑N, cexp ((n + 1 / 2) * I * ↑x) - ∑ n in Icc (-Int.ofNat N) ↑N, cexp ((n - 1 / 2) * I * ↑x) := by
        rw [sum_sub_distrib]
      _ = cexp ((N + 1 / 2) * I * x) - cexp (-(N + 1 / 2) * I * x) := by
        rw [←sum_Ico_add_eq_sum_Icc, ←sum_Ioc_add_eq_sum_Icc, add_sub_add_comm]
        symm
        rw [←zero_add (cexp ((↑N + 1 / 2) * I * ↑x) - cexp (-(↑N + 1 / 2) * I * ↑x))]
        congr
        symm
        rw [sub_eq_zero]
        conv => lhs; rw [←Int.add_sub_cancel (-Int.ofNat N) 1, sub_eq_add_neg, ←Int.add_sub_cancel (Nat.cast N) 1, sub_eq_add_neg, ←sum_Ico_add']
        congr
        . ext n
          rw [mem_Ico, mem_Ioc, Int.lt_iff_add_one_le, add_le_add_iff_right, ←mem_Icc, Int.lt_iff_add_one_le, ←mem_Icc]
        . ext n
          congr
          simp
          rw [add_assoc, sub_eq_add_neg]
          congr
          norm_num
        . rw [neg_add_rev, add_comm, Int.ofNat_eq_coe, Int.cast_neg, sub_eq_add_neg]
          norm_cast
        all_goals simp
  have h' : (cexp (1 / 2 * I * x) - cexp (-1 / 2 * I * x)) ≠ 0 := by
    contrapose! h
    rw [sub_eq_zero] at h
    calc cexp (I * ↑x)
      _ = cexp (1 / 2 * I * ↑x) * cexp (1 / 2 * I * ↑x) := by
        rw [←exp_add]
        congr
        rw [mul_assoc, ←mul_add]
        ring
      _ = cexp (1 / 2 * I * ↑x) * cexp (-1 / 2 * I * ↑x) := by
        congr
      _ = 1 := by
        rw [←exp_add]
        ring_nf
        exact exp_zero
  rw [dirichletKernel']
  apply mul_left_cancel₀ h'
  rw [this, mul_add, sub_eq_add_neg]
  congr
  . rw [mul_div]
    apply eq_div_of_mul_eq
    . contrapose! h
      rwa [sub_eq_zero, neg_mul, exp_neg, eq_comm, inv_eq_one] at h
    ring_nf
    rw [←exp_add, ←exp_add, ←exp_add]
    congr 2 <;> ring
  . rw [mul_div]
    apply eq_div_of_mul_eq
    . contrapose! h
      rwa [sub_eq_zero, eq_comm] at h
    ring_nf
    rw [←exp_add, ←exp_add, ←exp_add, neg_add_eq_sub]
    congr 2 <;> ring

lemma dirichletKernel'_eq_zero {N : ℕ} {x : ℝ} (h : cexp (I * x) = 1) : dirichletKernel' N x = 0 := by
  rw [dirichletKernel', neg_mul, exp_neg, h]
  simp

/- "a.e." version of previous lemma. -/
lemma dirichletKernel_eq_ae {N : ℕ} : ∀ᵐ (x : ℝ), dirichletKernel N x = dirichletKernel' N x := by
  rw [MeasureTheory.ae_iff]
  --aesop
  have : {x | ¬dirichletKernel N x = dirichletKernel' N x} = {x | ∃ n : ℤ, x = n * (2 * Real.pi)} := by
    ext x
    simp
    --rw [Set.uIoc_of_le Real.two_pi_pos.le]
    constructor
    . --apply Complex.exp_eq_one_iff
      sorry
    . sorry
  rw [this]
  sorry

lemma norm_dirichletKernel_le {N : ℕ} {x : ℝ} : ‖dirichletKernel N x‖ ≤ 2 * N + 1 := by
  rw [dirichletKernel]
  calc ‖∑ n ∈ Icc (-Int.ofNat N) ↑N, (fourier n) ↑x‖
    _ ≤ ∑ n ∈ Icc (-Int.ofNat N) ↑N, ‖(fourier n) ↑x‖ := by
      apply norm_sum_le
    _ ≤ ∑ n ∈ Icc (-Int.ofNat N) ↑N, 1 := by
      apply sum_le_sum
      intro n _
      have : Fact (0 < 2 * Real.pi) := by
        rw [fact_iff]
        exact Real.two_pi_pos
      apply le_trans (ContinuousMap.norm_coe_le_norm (fourier n) x) (fourier_norm n).le
    _ = 2 * N + 1 := by
      rw [sum_const]
      simp only [Int.ofNat_eq_coe, Int.card_Icc, sub_neg_eq_add, nsmul_eq_mul, mul_one]
      norm_cast
      rw [Int.toNat_ofNat]
      ring

lemma norm_dirichletKernel'_le {N : ℕ} {x : ℝ} : ‖dirichletKernel' N x‖ ≤ 2 * N + 1 := by
  by_cases h : cexp (I * x) ≠ 1
  . rw [← dirichletKernel_eq]
    apply norm_dirichletKernel_le
    exact h
  . push_neg at h
    rw [dirichletKernel'_eq_zero h, norm_zero]
    linarith

/-First part of lemma 10.10 (Dirichlet kernel) from the paper.-/
/-TODO (maybe): correct statement so that the integral is taken over the interval [-pi, pi] -/
lemma partialFourierSum_eq_conv_dirichletKernel {f : ℝ → ℂ} {N : ℕ} {x : ℝ} (h : IntervalIntegrable f MeasureTheory.volume 0 (2 * Real.pi)) :
    partialFourierSum f N x = (1 / (2 * Real.pi)) * ∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), f y * dirichletKernel N (x - y)  := by
  calc partialFourierSum f N x
    _ = ∑ n in Icc (-Int.ofNat N) ↑N, fourierCoeffOn Real.two_pi_pos f n * (fourier n) ↑x := by
      rw [partialFourierSum]
    _ = ∑ n in Icc (-Int.ofNat N) ↑N, (1 / (2 * Real.pi - 0)) • ((∫ (y : ℝ) in (0 : ℝ)..2 * Real.pi, (fourier (-n) ↑y • f y)) * (fourier n) ↑x) := by
      congr 1
      ext n
      rw [fourierCoeffOn_eq_integral, smul_mul_assoc]
    _ = (1 / (2 * Real.pi)) * ∑ n in Icc (-Int.ofNat N) ↑N, ((∫ (y : ℝ) in (0 : ℝ)..2 * Real.pi, (fourier (-n) ↑y • f y)) * (fourier n) ↑x) := by
      rw [←smul_sum, real_smul, sub_zero]
      norm_cast
    _ = (1 / (2 * Real.pi)) * ∑ n in Icc (-Int.ofNat N) ↑N, ((∫ (y : ℝ) in (0 : ℝ)..2 * Real.pi, (fourier (-n) ↑y • f y) * (fourier n) ↑x)) := by
      congr
      ext n
      symm
      apply intervalIntegral.integral_mul_const
    _ = (1 / (2 * Real.pi)) * ∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), ∑ n in Icc (-Int.ofNat N) ↑N, (fourier (-n)) y • f y * (fourier n) x := by
      rw [←intervalIntegral.integral_finset_sum]
      intro n _
      apply IntervalIntegrable.mul_const
      apply IntervalIntegrable.continuousOn_mul h fourier_uniformContinuous.continuous.continuousOn
    _ = (1 / (2 * Real.pi)) * ∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), f y * ∑ n in Icc (-Int.ofNat N) ↑N, (fourier (-n)) y * (fourier n) x := by
      congr
      ext y
      rw [mul_sum]
      congr
      ext n
      rw [smul_eq_mul]
      ring
    _ = (1 / (2 * Real.pi)) * ∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), f y * dirichletKernel N (x - y) := by
      congr
      ext y
      rw [dirichletKernel]
      congr
      ext n
      rw [fourier_coe_apply, fourier_coe_apply, fourier_coe_apply, ←exp_add]
      congr
      field_simp
      rw [mul_sub, sub_eq_neg_add]


lemma partialFourierSum_eq_conv_dirichletKernel' {f : ℝ → ℂ} {N : ℕ} {x : ℝ} (h : IntervalIntegrable f MeasureTheory.volume 0 (2 * Real.pi)) :
    partialFourierSum f N x = (1 / (2 * Real.pi)) * ∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), f y * dirichletKernel' N (x - y)  := by
  have : (1 / (2 * Real.pi)) * ∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), f y * dirichletKernel' N (x - y) = (1 / (2 * Real.pi)) * ∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), f y * dirichletKernel N (x - y) := by
    congr 1
    apply intervalIntegral.integral_congr_ae
    apply MeasureTheory.ae_imp_of_ae_restrict
    apply MeasureTheory.ae_restrict_of_ae
    sorry
    --apply MeasureTheory.ae_eq_comp
    --apply dirichletKernel_eq_ae
  rw [this]
  exact partialFourierSum_eq_conv_dirichletKernel h
