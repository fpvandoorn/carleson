/- This file contains definitions and lemmas regarding the Dirichlet kernel. -/

import Carleson.MetricCarleson
import Carleson.Classical.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Convolution

open BigOperators
open Finset
open Complex

noncomputable section

def dirichletKernel (N : ℕ) : ℝ → ℂ :=
  fun x ↦ ∑ n in Icc (-Int.ofNat N) N, fourier n (x : AddCircle (2 * Real.pi))

def dirichletKernel' (N : ℕ) : ℝ → ℂ :=
  fun x ↦ (exp (I * N * x) / (1 - exp (-I * x)) + exp (-I * N * x) / (1 - exp (I * x)))

lemma dirichletKernel_periodic {N : ℕ} : Function.Periodic (dirichletKernel N) (2 * Real.pi) := by
  intro x
  simp_rw [dirichletKernel]
  congr
  simp

lemma dirichletKernel'_periodic {N : ℕ} : Function.Periodic (dirichletKernel' N) (2 * Real.pi) := by
  intro x
  simp_rw [dirichletKernel']
  push_cast
  congr 2
  · rw [mul_add, exp_add]
    conv => rhs; rw [← mul_one (cexp _)]
    congr
    convert exp_int_mul_two_pi_mul_I N using 2
    norm_cast
    ring
  · congr 1
    rw [mul_add, exp_add]
    conv => rhs; rw [← mul_one (cexp _)]
    congr
    convert exp_int_mul_two_pi_mul_I (-1) using 2
    ring
  · rw [mul_add, exp_add]
    conv => rhs; rw [← mul_one (cexp _)]
    congr
    convert exp_int_mul_two_pi_mul_I (-(N : ℤ)) using 2
    simp
    ring
  · congr 1
    rw [mul_add, exp_add]
    conv => rhs; rw [← mul_one (cexp _)]
    congr
    convert exp_int_mul_two_pi_mul_I 1 using 2
    ring

@[measurability]
lemma dirichletKernel'_measurable {N : ℕ} : Measurable (dirichletKernel' N) :=
  by apply Measurable.add <;> apply Measurable.div <;> measurability

/-Second part of Lemma 11.1.8 (Dirichlet kernel) from the paper.-/
lemma dirichletKernel_eq {N : ℕ} {x : ℝ} (h : cexp (I * x) ≠ 1) :
    dirichletKernel N x = dirichletKernel' N x := by
  have : (cexp (1 / 2 * I * x) - cexp (-1 / 2 * I * x)) * dirichletKernel N x
      = cexp ((N + 1 / 2) * I * x) - cexp (-(N + 1 / 2) * I * x) := by
    calc (cexp (1 / 2 * I * x) - cexp (-1 / 2 * I * x)) * dirichletKernel N x
      _ = ∑ n in Icc (-(N : ℤ)) N, (cexp ((n + 1 / 2) * I * ↑x) - cexp ((n - 1 / 2) * I * ↑x)) := by
        rw [dirichletKernel, mul_sum]
        congr with n
        simp [sub_mul, ← exp_add, ← exp_add]
        congr <;>
        · ring_nf
          congr 1
          rw [mul_assoc, mul_assoc]
          congr
          rw_mod_cast [← mul_assoc, mul_comm, ← mul_assoc, inv_mul_cancel₀, one_mul]
          exact Real.pi_pos.ne.symm
      _ = ∑ n in Icc (-(N : ℤ)) N, cexp ((n + 1 / 2) * I * ↑x) - ∑ n in Icc (-(N : ℤ)) N, cexp ((n - 1 / 2) * I * ↑x) := by
        rw [sum_sub_distrib]
      _ = cexp ((N + 1 / 2) * I * x) - cexp (-(N + 1 / 2) * I * x) := by
        rw [← sum_Ico_add_eq_sum_Icc, ← sum_Ioc_add_eq_sum_Icc, add_sub_add_comm,
          ← zero_add (cexp ((N + 1 / 2) * I * ↑x) - cexp (-(N + 1 / 2) * I * ↑x))]
        congr
        rw [sub_eq_zero]
        conv => lhs; rw [← Int.add_sub_cancel (-(N : ℤ)) 1, sub_eq_add_neg, ← Int.add_sub_cancel (Nat.cast N) 1, sub_eq_add_neg, ← sum_Ico_add']
        congr with n
        · rw [mem_Ico, mem_Ioc, Int.lt_iff_add_one_le, add_le_add_iff_right,
            ← mem_Icc, Int.lt_iff_add_one_le, ← mem_Icc]
          simp
        · simp only [Int.reduceNeg, Int.cast_add, Int.cast_neg, Int.cast_one, one_div, add_assoc,
            sub_eq_add_neg]
          norm_num
        · rw [neg_add_rev, add_comm, Int.cast_neg, sub_eq_add_neg]
          norm_cast
        all_goals simp
  have h' : (cexp (1 / 2 * I * x) - cexp (-1 / 2 * I * x)) ≠ 0 := by
    contrapose! h
    rw [sub_eq_zero] at h
    calc cexp (I * ↑x)
      _ = cexp (1 / 2 * I * ↑x) * cexp (1 / 2 * I * ↑x) := by
        rw [← exp_add, mul_assoc, ← mul_add]
        ring_nf
      _ = cexp (1 / 2 * I * ↑x) * cexp (-1 / 2 * I * ↑x) := by congr
      _ = 1 := by
        rw [← exp_add]
        ring_nf
        exact exp_zero
  rw [dirichletKernel']
  apply mul_left_cancel₀ h'
  rw [this, mul_add, sub_eq_add_neg]
  congr
  · rw [mul_div]
    apply eq_div_of_mul_eq
    · contrapose! h
      rwa [sub_eq_zero, neg_mul, exp_neg, eq_comm, inv_eq_one] at h
    ring_nf
    rw [← exp_add, ← exp_add, ← exp_add]
    congr 2 <;> ring
  · rw [mul_div]
    apply eq_div_of_mul_eq
    · contrapose! h
      rwa [sub_eq_zero, eq_comm] at h
    ring_nf
    rw [← exp_add, ← exp_add, ← exp_add, neg_add_eq_sub]
    congr 2 <;> ring

lemma dirichletKernel'_eq_zero {N : ℕ} {x : ℝ} (h : cexp (I * x) = 1) : dirichletKernel' N x = 0 := by
  simp [dirichletKernel', exp_neg, h]

/- "a.e." version of previous lemma. -/
lemma dirichletKernel_eq_ae {N : ℕ} : ∀ᵐ (x : ℝ), dirichletKernel N x = dirichletKernel' N x := by
  have : {x | ¬dirichletKernel N x = dirichletKernel' N x} ⊆ {x | ∃ n : ℤ, n * (2 * Real.pi) = x} := by
    intro x hx
    simp at *
    by_contra h
    apply hx (dirichletKernel_eq _)
    rw [ne_eq, Complex.exp_eq_one_iff]
    push_neg at *
    ring_nf at *
    intro n
    rw [ne_eq, mul_assoc, mul_assoc, mul_eq_mul_left_iff]
    simp only [I_ne_zero, or_false]
    norm_cast
    exact (h n).symm
  rw [MeasureTheory.ae_iff]
  apply MeasureTheory.measure_mono_null this
  apply Set.Countable.measure_zero
  let f : ℤ → ℝ := fun n ↦ n * (2 * Real.pi)
  apply Set.countable_range f

lemma norm_dirichletKernel_le {N : ℕ} {x : ℝ} : ‖dirichletKernel N x‖ ≤ 2 * N + 1 := by
  rw [dirichletKernel]
  calc ‖∑ n ∈ Icc (-(N : ℤ)) N, (fourier n) ↑x‖
    _ ≤ ∑ n ∈ Icc (-(N : ℤ)) N, ‖(fourier n) ↑x‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc (-(N : ℤ)) N, 1 := by
      apply sum_le_sum
      have : Fact (0 < 2 * Real.pi) := by rw [fact_iff]; exact Real.two_pi_pos
      exact fun n _ ↦ le_trans (ContinuousMap.norm_coe_le_norm (fourier n) x) (fourier_norm n).le
    _ = 2 * N + 1 := by
      rw_mod_cast [sum_const, Int.card_Icc, sub_neg_eq_add, nsmul_eq_mul, mul_one,
        Int.toNat_ofNat]
      ring

lemma norm_dirichletKernel'_le {N : ℕ} {x : ℝ} : ‖dirichletKernel' N x‖ ≤ 2 * N + 1 := by
  by_cases h : cexp (I * x) ≠ 1
  · simp only [ne_eq, h, not_false_eq_true, ← dirichletKernel_eq, norm_eq_abs]
    exact norm_dirichletKernel_le
  · push_neg at h
    rw [dirichletKernel'_eq_zero h, norm_zero]
    linarith

/-First part of lemma 11.1.8 (Dirichlet kernel) from the blueprint.-/
lemma partialFourierSum_eq_conv_dirichletKernel {f : ℝ → ℂ} {N : ℕ} {x : ℝ} (h : IntervalIntegrable f MeasureTheory.volume 0 (2 * Real.pi)) :
    partialFourierSum N f x = (1 / (2 * Real.pi)) * ∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), f y * dirichletKernel N (x - y)  := by
  calc partialFourierSum N f x
    _ = ∑ n in Icc (-(N : ℤ)) N, fourierCoeffOn Real.two_pi_pos f n * (fourier n) ↑x := by
      rw [partialFourierSum]
    _ = ∑ n in Icc (-(N : ℤ)) N, (1 / (2 * Real.pi - 0)) • ((∫ (y : ℝ) in (0 : ℝ)..2 * Real.pi, (fourier (-n) ↑y • f y)) * (fourier n) ↑x) := by
      congr 1 with n
      rw [fourierCoeffOn_eq_integral, smul_mul_assoc]
    _ = (1 / (2 * Real.pi)) * ∑ n in Icc (-(N : ℤ)) N, ((∫ (y : ℝ) in (0 : ℝ)..2 * Real.pi, (fourier (-n) ↑y • f y)) * (fourier n) ↑x) := by
      rw_mod_cast [← smul_sum, real_smul, sub_zero]
    _ = (1 / (2 * Real.pi)) * ∑ n in Icc (-(N : ℤ)) N, ((∫ (y : ℝ) in (0 : ℝ)..2 * Real.pi, (fourier (-n) ↑y • f y) * (fourier n) ↑x)) := by
      congr with n
      exact (intervalIntegral.integral_mul_const _ _).symm
    _ = (1 / (2 * Real.pi)) * ∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), ∑ n in Icc (-(N : ℤ)) N, (fourier (-n)) y • f y * (fourier n) x := by
      rw [← intervalIntegral.integral_finset_sum]
      exact fun _ _ ↦ IntervalIntegrable.mul_const
        (h.continuousOn_mul fourier_uniformContinuous.continuous.continuousOn) _
    _ = (1 / (2 * Real.pi)) * ∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), f y * ∑ n in Icc (-(N : ℤ)) N, (fourier (-n)) y * (fourier n) x := by
      congr with y
      rw [mul_sum]
      congr with n
      rw [smul_eq_mul]
      ring
    _ = (1 / (2 * Real.pi)) * ∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), f y * dirichletKernel N (x - y) := by
      congr with y
      rw [dirichletKernel]
      congr with n
      rw [fourier_coe_apply, fourier_coe_apply, fourier_coe_apply, ←exp_add]
      congr
      field_simp
      rw [mul_sub, sub_eq_neg_add]

lemma partialFourierSum_eq_conv_dirichletKernel' {f : ℝ → ℂ} {N : ℕ} {x : ℝ} (h : IntervalIntegrable f MeasureTheory.volume 0 (2 * Real.pi)) :
    partialFourierSum N f x = (1 / (2 * Real.pi)) * ∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), f y * dirichletKernel' N (x - y)  := by
  rw [partialFourierSum_eq_conv_dirichletKernel h]
  calc _
    _ = (1 / (2 * Real.pi)) * ∫ (y : ℝ) in (x - 2 * Real.pi)..(x - 0), f (x - y) * dirichletKernel N y := by
      congr 1
      rw [← intervalIntegral.integral_comp_sub_left]
      simp
    _ = (1 / (2 * Real.pi)) * ∫ (y : ℝ) in (x - 2 * Real.pi)..(x - 0), f (x - y) * dirichletKernel' N y := by
      congr 1
      apply intervalIntegral.integral_congr_ae (MeasureTheory.ae_imp_of_ae_restrict
        (MeasureTheory.ae_restrict_of_ae _))
      have : {a | ¬f (x - a) * dirichletKernel N a = f (x - a) * dirichletKernel' N a} ⊆ {a | ¬dirichletKernel N a = dirichletKernel' N a} := by
        intro a ha
        contrapose! ha
        simp at *
        intro h
        exfalso
        exact h ha
      apply MeasureTheory.measure_mono_null this dirichletKernel_eq_ae
    _ = (1 / (2 * Real.pi)) * ∫ (y : ℝ) in (0 : ℝ)..(2 * Real.pi), f y * dirichletKernel' N (x - y) := by
      congr 1
      rw [← intervalIntegral.integral_comp_sub_left]
      simp
