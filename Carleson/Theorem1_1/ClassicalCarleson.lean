import Carleson.Carleson
import Carleson.HomogeneousType
import Carleson.Theorem1_1.Basic
import Carleson.Theorem1_1.Approximation
import Carleson.Theorem1_1.Control_Approximation_Effect

import Mathlib.Analysis.Fourier.AddCircle


noncomputable section

/- Specialize this to get the usual version of Carleson's theorem,
by taking `X = ℝ`, `K x y := 1 / (x - y)` and `𝓠 = {linear functions}`.
-/

--def K : ℝ → ℝ → ℂ := fun x y ↦ 1 / (x - y)

theorem classical_carleson {f : ℝ → ℂ}
    (unicontf : UniformContinuous f) (periodicf : Function.Periodic f (2 * Real.pi)) (bdd_one : ∀ x, Complex.abs (f x) ≤ 1)
    {ε : ℝ} (hε : 0 < ε ∧ ε ≤ 2 * Real.pi) :
    --need condition E ⊆ Set.Icc 0 (2 * Real.pi) to ensure the E has finite volume
    ∃ E ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E ∧ MeasureTheory.volume.real E ≤ ε ∧
    ∃ N₀, ∀ x ∈ (Set.Icc 0 (2 * Real.pi)) \ E, ∀ N > N₀,
    Complex.abs (f x - partialFourierSum f N x) ≤ ε := by
  --TODO : use some scaled ε for the choose
  have ε2pos : (ε / 2) > 0 := by linarith [hε.1]
  obtain ⟨f₀, contDiff_f₀, periodic_f₀, hf₀⟩ := closeSmoothApproxPeriodic unicontf periodicf ε2pos

  --Lemma 10.2 from the paper
  --changed interval to Icc to match the interval in the theorem
  have ε4pos : ε / 4 > 0 := by linarith
  obtain ⟨N₀, hN₀⟩ := fourierConv_ofTwiceDifferentiable periodic_f₀ ((contDiff_top.mp (contDiff_f₀)) 2) ε4pos


  --Lemma 10.3 from the paper
  --TODO : review measurability assumption
  --added subset assumption
  --changed interval to match the interval in the theorem
  /-
  have diffPartialFourierSums : ∃ E₂ ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E₂ ∧ MeasureTheory.volume.real E₂ ≤ ε / 2 ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi) \ E₂,
    sSup {Complex.abs (partialFourierSum f₀ N x - partialFourierSum f N x) | N : ℕ} ≤ ε / 4 := by
    sorry
  -/
  --simplified statement so that we do not have to worry about a sSup
  have diffPartialFourierSums : ∃ E₂ ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E₂ ∧ MeasureTheory.volume.real E₂ ≤ ε ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi) \ E₂,
    ∀ N, Complex.abs (partialFourierSum f₀ N x - partialFourierSum f N x) ≤ ε / 4 := by
    sorry
  obtain ⟨E₂, E₂subset, E₂measurable, E₂volume, hE₂⟩ := diffPartialFourierSums

  --apply Set.mem_Ico_of_Ioo

  --Definition of E changed compared to the paper
  use E₂, E₂subset, E₂measurable, E₂volume, N₀
  intro x hx N NgtN₀
  --use "telescope" sum
  calc Complex.abs (f x - partialFourierSum f N x)
  _ = Complex.abs ((f x - f₀ x) + (f₀ x - partialFourierSum f₀ N x) + (partialFourierSum f₀ N x - partialFourierSum f N x)) := by congr; ring
  _ ≤ Complex.abs ((f x - f₀ x) + (f₀ x - partialFourierSum f₀ N x)) + Complex.abs (partialFourierSum f₀ N x - partialFourierSum f N x) := by
    apply AbsoluteValue.add_le
  _ ≤ Complex.abs (f x - f₀ x) + Complex.abs (f₀ x - partialFourierSum f₀ N x) + Complex.abs (partialFourierSum f₀ N x - partialFourierSum f N x) := by
    apply add_le_add_right
    apply AbsoluteValue.add_le
  _ ≤ (ε / 2) + (ε / 4) + (ε / 4) := by
    gcongr
    . exact hf₀ x
    . by_cases h : x = 2 * Real.pi
      . rw [h, ←zero_add (2 * Real.pi), periodic_f₀, partialFourierSum_periodic]
        apply hN₀ N NgtN₀ 0
        simp [Real.pi_pos]
      . have : x ∈ Set.Ico 0 (2 * Real.pi) := by
          simp
          simp at hx
          use hx.1.1
          apply lt_of_le_of_ne hx.1.2 h
        convert hN₀ N NgtN₀ x this
    . exact hE₂ x hx N
  _ ≤ ε := by linarith
