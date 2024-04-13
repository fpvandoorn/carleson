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

variable [IsSpaceOfHomogeneousType ℝ 2] (μ : MeasureTheory.Measure ℝ)

open BigOperators
open Finset

#check fourier
--def stdCircle : AddCircle (2 * Real.pi)

def partialFourierSum (f : ℝ → ℂ) (N : ℕ) : ℝ → ℂ := fun x ↦ ∑ n in range (2 * N + 1), fourierCoeffOn Real.two_pi_pos f (n - N) * fourier (n - N) (x : AddCircle (2 * Real.pi))
#check partialFourierSum

--section in which definitions depend on f
section f_variable
variable {f: ℝ → ℂ} (unicontf : UniformContinuous f)
variable {ε : ℝ} (εpos : ε > 0)


def δfromε : ℝ := by
  --TODO : use some scaled ε for the choose
  choose δ _ _ using Metric.uniformContinuous_iff.mp unicontf ε εpos
  exact δ

--define the approximation by a piecewise constant function (f₀) as in section 10.1
variable {δ : ℝ} (δdef : δ = δfromε unicontf εpos)

def Kfromδ : ℕ := Nat.floor ((2 * Real.pi) / δ) + 1
--TODO: tidy this up
variable {K : ℕ} (Kdef : K = Kfromδ)
-- note that K>2 ?

def piecewiseConstApprox : ℝ → ℂ := fun x ↦ f ((2 * Real.pi * Int.floor ((K * x) / (2 * δ))) / K)

/-
def piecewiseConstApprox : ℝ → ℂ := by
  --TODO : use some scaled ε for the choose
  choose δ δpos hδε using Metric.uniformContinuous_iff.mp unicontf ε εpos
  let K := Int.floor ((2 * Real.pi) / δ) + 1
  -- note that K>2 ?
  exact fun x ↦ f ((2 * Real.pi * Int.floor ((K * x) / (2 * δ))) / K)
-/

variable {f₀: ℝ → ℂ} (unicontf : UniformContinuous f) {ε : ℝ} (εpos : ε > 0) (f₀def : f₀ = piecewiseConstApprox)

def E₁fromK :=
  ⋃ (k : range (K + 1)), Set.Icc ((2 * Real.pi) / K * (k - ε / (16 * Real.pi))) ((2 * Real.pi) / K * (k + ε / (16 * Real.pi)))

variable {E₁ : Set ℝ} (E₁def : E₁ = E₁fromK)


--Lemma 10.2 from the paper
--TODO : correct size of N
lemma piecePartialFourierSumApprox {N : ℕ} (hN : N > (K^2 / ε^3)) :
  ∀ x ∈ Set.Ico 0 (2 * Real.pi) \ E₁, Complex.abs (partialFourierSum f₀ N x - f₀ x) ≤ ε / 4:= by
  sorry


--Lemma 10.3 from the paper
lemma diffPartialFourierSums : ∃ E₂, MeasureTheory.volume.real E₂ ≤ ε / 2 ∧ ∀ x ∈ (Set.Ico 0 1) \ E₂,
  sSup {Complex.abs (partialFourierSum f N x - partialFourierSum f₀ N x) | N : ℕ} ≤ ε / 4 := by
  sorry

--TODO : seems like theorem1_1 is actually Theorem 1.2 from the paper
--TODO : check and compare to version in mathlib has_pointwise_sum_fourier_series_of_summable and similar
theorem classical_carleson {f : ℝ → ℂ}
  (unicontf : UniformContinuous f) (periodicf : Function.Periodic f (2 * Real.pi)) (bdd_one : ∀ x, Complex.abs (f x) ≤ 1)
  {ε : ℝ} (hε : 0 < ε ∧ ε ≤ 2 * Real.pi) :
  ∃ E ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E ∧ MeasureTheory.volume.real E ≤ ε ∧
  ∃ N₀ > 0, ∀ x ∈ (Set.Icc 0 (2 * Real.pi)) \ E, ∀ N > N₀,
  Complex.abs (f x - partialFourierSum f N x) ≤ ε := by sorry
  --obtain ⟨E₂, E₂volume, _⟩ := diffPartialFourierSums



#check classical_carleson
