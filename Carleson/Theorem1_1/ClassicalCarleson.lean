import Carleson.Carleson
import Carleson.HomogeneousType

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.BigOperators.Basic


noncomputable section
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

#check theorem1_1C
/- Specialize this to get the usual version of Carleson's theorem,
by taking `X = ℝ`, `K x y := 1 / (x - y)` and `𝓠 = {linear functions}`.
-/

def K : ℝ → ℝ → ℂ := fun x y ↦ 1 / (x - y)

instance : IsSpaceOfHomogeneousType ℝ 2 := by
  have : IsSpaceOfHomogeneousType ℝ (2 ^ FiniteDimensional.finrank ℝ ℝ) := inferInstance
  simpa

#check theorem1_1C K (by norm_num)

#check Complex.abs

#check Finset.range

#check AddCircle (2 * Real.pi)

open BigOperators
open Finset


#check fourier
--def stdCircle : AddCircle (2 * Real.pi)

def partialFourierSum (f : ℝ → ℂ) (N : ℕ) : ℝ → ℂ := fun x ↦ ∑ n in range (2 * N + 1), fourierCoeffOn Real.two_pi_pos f (n - N) * fourier (n - N) (x : AddCircle (2 * Real.pi))

--#check partialFourierSum

variable [IsSpaceOfHomogeneousType ℝ 2] (μ : MeasureTheory.Measure ℝ)

--TODO : seems like theorem1_1 is actually Theorem 1.2 from the paper
--TODO : check and compare to version in mathlib has_pointwise_sum_fourier_series_of_summable and similar
theorem classical_carleson {f : ℝ → ℂ} (unicontf : UniformContinuous f)
  (periodicf : Function.Periodic f (2 * Real.pi)) (bdd_one : ∀ x, Complex.abs (f x) ≤ 1)
  {ε : ℝ} (hε : 0 < ε ∧ ε ≤ 2 * Real.pi) :
  ∃ E ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E ∧ MeasureTheory.volume.real E ≤ ε ∧
  ∃ N₀ > 0, ∀ x ∈ (Set.Icc 0 (2 * Real.pi)) \ E, ∀ N > N₀,
  Complex.abs (f x - partialFourierSum f N x) ≤ ε := sorry
