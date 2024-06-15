import Carleson.Carleson
import Carleson.HomogeneousType
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Convolution

open BigOperators
open Finset
--open Complex

noncomputable section


--TODO : add reasonable notation
--local notation "S_" => partialFourierSum f

def partialFourierSum (f : ℝ → ℂ) (N : ℕ) : ℝ → ℂ := fun x ↦ ∑ n in Icc (-Int.ofNat ↑N) N, fourierCoeffOn Real.two_pi_pos f n * fourier n (x : AddCircle (2 * Real.pi))
--fun x ↦ ∑ n in Icc (-Int.ofNat ↑N) N, fourierCoeffOn Real.two_pi_pos f n * fourier n (x : AddCircle (2 * Real.pi))

@[simp]
lemma fourierCoeffOn_mul {a b : ℝ} {hab : a < b} {f: ℝ → ℂ} {c : ℂ} {n : ℤ} :
  fourierCoeffOn hab (fun x ↦ c * f x) n = c * (fourierCoeffOn hab f n):= by
  simp [fourierCoeffOn_eq_integral, intervalIntegral.integral_mul_const, mul_assoc, mul_comm]
  ring

@[simp]
lemma fourierCoeffOn_neg {a b : ℝ} {hab : a < b} {f: ℝ → ℂ} {n : ℤ} :
  fourierCoeffOn hab (-f) n = - (fourierCoeffOn hab f n):= by
  simp [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]

@[simp]
lemma fourierCoeffOn_add {a b : ℝ} {hab : a < b} {f g : ℝ → ℂ} {n : ℤ} (hf : IntervalIntegrable f MeasureTheory.volume a b) (hg : IntervalIntegrable g MeasureTheory.volume a b) :
    fourierCoeffOn hab (f + g) n = fourierCoeffOn hab f n + fourierCoeffOn hab g n:= by
  simp only [fourierCoeffOn_eq_integral, one_div, fourier_apply, neg_smul, fourier_neg',
    fourier_coe_apply', Complex.ofReal_sub, Pi.add_apply, smul_eq_mul, mul_add, Complex.real_smul,
    Complex.ofReal_inv]
  rw [← mul_add, ← intervalIntegral.integral_add]
  congr
  ring_nf
  . apply hf.continuousOn_mul
    apply Continuous.continuousOn
    continuity
  . apply hg.continuousOn_mul
    apply Continuous.continuousOn
    continuity

@[simp]
lemma fourierCoeffOn_sub {a b : ℝ} {hab : a < b} {f g : ℝ → ℂ} {n : ℤ} (hf : IntervalIntegrable f MeasureTheory.volume a b) (hg : IntervalIntegrable g MeasureTheory.volume a b) :
    fourierCoeffOn hab (f - g) n = fourierCoeffOn hab f n - fourierCoeffOn hab g n:= by
  rw [sub_eq_add_neg, fourierCoeffOn_add hf hg.neg, fourierCoeffOn_neg, ← sub_eq_add_neg]

@[simp]
lemma partialFourierSum_add {f g : ℝ → ℂ} {N : ℕ} (hf : IntervalIntegrable f MeasureTheory.volume 0 (2 * Real.pi)) (hg : IntervalIntegrable g MeasureTheory.volume 0 (2 * Real.pi)) :
  partialFourierSum (f + g) N = partialFourierSum f N + partialFourierSum g N := by
  ext x
  simp [partialFourierSum, sum_add_distrib, fourierCoeffOn_add hf hg, add_mul]

@[simp]
lemma partialFourierSum_sub {f g : ℝ → ℂ} {N : ℕ} (hf : IntervalIntegrable f MeasureTheory.volume 0 (2 * Real.pi)) (hg : IntervalIntegrable g MeasureTheory.volume 0 (2 * Real.pi)) :
  partialFourierSum (f - g) N = partialFourierSum f N - partialFourierSum g N := by
  ext x
  simp [partialFourierSum, sum_sub_distrib, fourierCoeffOn_sub hf hg, sub_mul]

@[simp]
lemma partialFourierSum_mul {f: ℝ → ℂ} {a : ℂ} {N : ℕ}:
  partialFourierSum (fun x ↦ a * f x) N = fun x ↦ a * partialFourierSum f N x := by
  ext x
  simp [partialFourierSum, mul_sum, fourierCoeffOn_mul, mul_assoc]

lemma fourier_periodic {n : ℤ} : Function.Periodic (fun (x : ℝ) ↦ fourier n (x : AddCircle (2 * Real.pi))) (2 * Real.pi) := by simp

lemma partialFourierSum_periodic {f : ℝ → ℂ} {N : ℕ} : Function.Periodic (partialFourierSum f N) (2 * Real.pi) := by
    simp [Function.Periodic, partialFourierSum, fourier_periodic]

/-TODO: Add lemma Periodic.uniformContinuous_of_continuous. -/
lemma fourier_uniformContinuous {n : ℤ} : UniformContinuous (fun (x : ℝ) ↦ fourier n (x : AddCircle (2 * Real.pi))) := by
  simp [fourier]
  --apply Complex.exp_mul_I_periodic.
  sorry

lemma partialFourierSum_uniformContinuous {f : ℝ → ℂ} {N : ℕ} : UniformContinuous (partialFourierSum f N) := by
  --apply continuous_finset_sum
  sorry


theorem strictConvexOn_cos_Icc : StrictConvexOn ℝ (Set.Icc (Real.pi / 2) (Real.pi + Real.pi / 2)) Real.cos := by
  apply strictConvexOn_of_deriv2_pos (convex_Icc _ _) Real.continuousOn_cos fun x hx => ?_
  rw [interior_Icc] at hx
  simp [Real.cos_neg_of_pi_div_two_lt_of_lt hx.1 hx.2]

/- Lemma 10.11 (lower secant bound) from the paper. -/
lemma lower_secant_bound' {η : ℝ}  {x : ℝ} (le_abs_x : η ≤ |x|) (abs_x_le : |x| ≤ 2 * Real.pi - η) :
    (2 / Real.pi) * η ≤ ‖1 - Complex.exp (Complex.I * x)‖ := by
  by_cases ηpos : η ≤ 0
  . calc (2 / Real.pi) * η
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (div_nonneg zero_le_two Real.pi_pos.le) ηpos
    _ ≤ ‖1 - Complex.exp (Complex.I * x)‖ := norm_nonneg _
  push_neg at ηpos
  wlog x_nonneg : 0 ≤ x generalizing x
  . convert (@this (-x) _ (by simpa) (by linarith)) using 1
    . rw [Complex.norm_eq_abs, ←Complex.abs_conj, map_sub, map_one, Complex.ofReal_neg, mul_neg, Complex.norm_eq_abs,
          ←Complex.exp_conj, map_mul, Complex.conj_I, neg_mul, Complex.conj_ofReal]
    . rwa [abs_neg]
  rw [abs_of_nonneg x_nonneg] at *
  wlog x_le_pi : x ≤ Real.pi generalizing x
  . convert (@this (2 * Real.pi - x) _ _ _ _) using 1
    . rw [Complex.norm_eq_abs, ← Complex.abs_conj]
      simp [← Complex.exp_conj, mul_sub, Complex.conj_ofReal, Complex.exp_sub,
        mul_comm Complex.I (2 * Real.pi), Complex.exp_two_pi_mul_I, ←inv_eq_one_div, ←Complex.exp_neg]
    all_goals linarith
  by_cases h : x ≤ Real.pi / 2
  . calc (2 / Real.pi) * η
    _ ≤ (2 / Real.pi) * x := by gcongr
    _ = (1 - (2 / Real.pi) * x) * Real.sin 0 + ((2 / Real.pi) * x) * Real.sin (Real.pi / 2) := by simp
    _ ≤ Real.sin ((1 - (2 / Real.pi) * x) * 0 + ((2 / Real.pi) * x) * (Real.pi / 2)) := by
      apply (strictConcaveOn_sin_Icc.concaveOn).2 (by simp [Real.pi_nonneg])
      . simp
        constructor <;> linarith [Real.pi_nonneg]
      . rw [sub_nonneg, mul_comm]
        exact mul_le_of_nonneg_of_le_div (by norm_num) (div_nonneg (by norm_num) Real.pi_nonneg) (by simpa)
      . exact mul_nonneg (div_nonneg (by norm_num) Real.pi_nonneg) x_nonneg
      . simp
    _ = Real.sin x := by field_simp
    _ ≤ Real.sqrt ((Real.sin x) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
      apply le_abs_self
    _ ≤ ‖1 - Complex.exp (Complex.I * ↑x)‖ := by
        rw [mul_comm, Complex.exp_mul_I, Complex.norm_eq_abs, Complex.abs_eq_sqrt_sq_add_sq]
        simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.cos_ofReal_re,
          Complex.mul_re, Complex.sin_ofReal_re, Complex.I_re, mul_zero, Complex.sin_ofReal_im,
          Complex.I_im, mul_one, sub_self, add_zero, Complex.sub_im, Complex.one_im, Complex.add_im,
          Complex.cos_ofReal_im, Complex.mul_im, zero_add, zero_sub, even_two, Even.neg_pow]
        apply (Real.sqrt_le_sqrt_iff _).mpr
        . simp [pow_two_nonneg]
        . linarith [pow_two_nonneg (1 - Real.cos x), pow_two_nonneg (Real.sin x)]
  . push_neg at h
    calc (2 / Real.pi) * η
    _ ≤ (2 / Real.pi) * x := by gcongr
    _ = 1 - ((1 - (2 / Real.pi) * (x - Real.pi / 2)) * Real.cos (Real.pi / 2) + ((2 / Real.pi) * (x - Real.pi / 2)) * Real.cos (Real.pi)) := by
      field_simp
      ring
    _ ≤ 1 - (Real.cos ((1 - (2 / Real.pi) * (x - Real.pi / 2)) * (Real.pi / 2) + (((2 / Real.pi) * (x - Real.pi / 2)) * (Real.pi)))) := by
      gcongr
      apply (strictConvexOn_cos_Icc.convexOn).2 (by simp [Real.pi_nonneg])
      . simp
        constructor <;> linarith [Real.pi_nonneg]
      . rw [sub_nonneg, mul_comm]
        apply mul_le_of_nonneg_of_le_div (by norm_num) (div_nonneg (by norm_num) Real.pi_nonneg) (by simpa)
      . exact mul_nonneg (div_nonneg (by norm_num) Real.pi_nonneg) (by linarith [h])
      . simp
    _ = 1 - Real.cos x := by
      congr
      field_simp
      ring
    _ ≤ Real.sqrt ((1 - Real.cos x) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
      apply le_abs_self
    _ ≤ ‖1 - Complex.exp (Complex.I * ↑x)‖ := by
        rw [mul_comm, Complex.exp_mul_I, Complex.norm_eq_abs, Complex.abs_eq_sqrt_sq_add_sq]
        simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.mul_re, Complex.I_re,
          mul_zero, Complex.sin_ofReal_im, Complex.I_im, mul_one, sub_self, add_zero,
          Complex.sub_im, Complex.one_im, Complex.add_im, Complex.cos_ofReal_im, Complex.mul_im,
          zero_add, zero_sub, even_two, Even.neg_pow]
        rw [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
        apply (Real.sqrt_le_sqrt_iff _).mpr
        . simp [pow_two_nonneg]
        . linarith [pow_two_nonneg (1 - Real.cos x), pow_two_nonneg (Real.sin x)]

/-Slightly weaker version of Lemma 10.11 (lower secant bound) with simplified constant. -/
lemma lower_secant_bound {η : ℝ} {x : ℝ} (xIcc : x ∈ Set.Icc (-2 * Real.pi + η) (2 * Real.pi - η)) (xAbs : η ≤ |x|) :
    η / 2 ≤ Complex.abs (1 - Complex.exp (Complex.I * x)) := by
  by_cases ηpos : η < 0
  . calc η / 2
    _ ≤ 0 := by linarith
    _ ≤ ‖1 - Complex.exp (Complex.I * x)‖ := by apply norm_nonneg
  push_neg at ηpos
  calc η / 2
  _ ≤ (2 / Real.pi) * η := by
    ring_nf
    rw [mul_assoc]
    gcongr
    field_simp
    rw [div_le_div_iff (by norm_num) Real.pi_pos]
    linarith [Real.pi_le_four]
  _ ≤ ‖1 - Complex.exp (Complex.I * x)‖ := by
    apply lower_secant_bound' xAbs
    rw [abs_le, neg_sub', sub_neg_eq_add, neg_mul_eq_neg_mul]
    exact xIcc

/-Further definitions-/
/-TODO : relocate this-/

--TODO : call constructor in a better way?
def integer_linear (n : ℤ) : C(ℝ, ℂ) := ⟨fun (x : ℝ) ↦ (n * x : ℂ), by continuity⟩

--local notation "θ" => integer_linear

--lemma θcont {n : ℤ} : Continuous (θ n) := sorry

--local notation "Θ" => {(θ n) | n : ℤ}
