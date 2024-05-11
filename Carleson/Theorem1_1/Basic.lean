import Mathlib.Analysis.Fourier.AddCircle

open BigOperators
open Finset

noncomputable section

def partialFourierSum (f : ℝ → ℂ) (N : ℕ) : ℝ → ℂ := fun x ↦ ∑ n in Icc (-Int.ofNat ↑N) N, fourierCoeffOn Real.two_pi_pos f n * fourier n (x : AddCircle (2 * Real.pi))
--fun x ↦ ∑ n in Icc (-Int.ofNat ↑N) N, fourierCoeffOn Real.two_pi_pos f n * fourier n (x : AddCircle (2 * Real.pi))

/-TODO: Add integrability assumptions. -/
@[simp]
lemma fourierCoeffOn_add {a b : ℝ} {hab : a < b} {f g : ℝ → ℂ} {n : ℤ} (hf : IntervalIntegrable f MeasureTheory.volume a b) (hg : IntervalIntegrable g MeasureTheory.volume a b) :
    fourierCoeffOn hab (f + g) n = fourierCoeffOn hab f n + fourierCoeffOn hab g n:= by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp
  rw [←mul_add, ←intervalIntegral.integral_add]
  congr
  ext x
  ring
  . apply IntervalIntegrable.continuousOn_mul hf
    apply Continuous.continuousOn
    continuity
  . apply IntervalIntegrable.continuousOn_mul hg
    apply Continuous.continuousOn
    continuity

@[simp]
lemma fourierCoeffOn_mul {a b : ℝ} {hab : a < b} {f: ℝ → ℂ} {a : ℂ} {n : ℤ} : fourierCoeffOn hab (fun x ↦ a * f x) n =
    a * (fourierCoeffOn hab f n):= by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp
  rw [←mul_assoc, mul_comm a, mul_assoc _ a, mul_comm a, ←intervalIntegral.integral_mul_const]
  congr
  ext x
  ring

@[simp]
lemma partialFourierSum_add {f g : ℝ → ℂ} {N : ℕ} (hf : IntervalIntegrable f MeasureTheory.volume 0 (2 * Real.pi)) (hg : IntervalIntegrable g MeasureTheory.volume 0 (2 * Real.pi)): partialFourierSum (f + g) N = partialFourierSum f N + partialFourierSum g N := by
  ext x
  simp
  rw [partialFourierSum, partialFourierSum, partialFourierSum, ←sum_add_distrib]
  congr
  ext n
  rw [fourierCoeffOn_add hf hg, add_mul]


@[simp]
lemma partialFourierSum_mul {f: ℝ → ℂ} {a : ℂ} {N : ℕ}: partialFourierSum (fun x ↦ a * f x) N = fun x ↦ a * partialFourierSum f N x := by
  ext x
  rw [partialFourierSum, partialFourierSum, mul_sum]
  congr
  ext n
  rw [fourierCoeffOn_mul, mul_assoc]

lemma fourier_periodic {n : ℤ} : Function.Periodic (fun (x : ℝ) ↦ fourier n (x : AddCircle (2 * Real.pi))) (2 * Real.pi) := by
  intro x
  simp

lemma partialFourierSum_periodic {f : ℝ → ℂ} {N : ℕ} : Function.Periodic (partialFourierSum f N) (2 * Real.pi) := by
  rw [Function.Periodic]
  intro x
  rw [partialFourierSum, partialFourierSum]
  congr
  ext n
  congr 1
  exact fourier_periodic x

variable {f : ℝ → ℂ} {N : ℕ}

--TODO : add reasonable notation
--local notation "S_" => partialFourierSum f
