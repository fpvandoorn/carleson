import Mathlib.Analysis.Fourier.AddCircle

open BigOperators
open Finset

noncomputable section

def partialFourierSum (f : ℝ → ℂ) (N : ℕ) : ℝ → ℂ := fun x ↦ ∑ n in Icc (-Int.ofNat ↑N) N, fourierCoeffOn Real.two_pi_pos f n * fourier n (x : AddCircle (2 * Real.pi))
--fun x ↦ ∑ n in Icc (-Int.ofNat ↑N) N, fourierCoeffOn Real.two_pi_pos f n * fourier n (x : AddCircle (2 * Real.pi))
#check partialFourierSum


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
