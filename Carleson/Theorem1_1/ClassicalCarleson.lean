import Carleson.MetricCarleson
import Carleson.Theorem1_1.Basic
import Carleson.Theorem1_1.Approximation
import Carleson.Theorem1_1.Control_Approximation_Effect

import Mathlib.Analysis.Fourier.AddCircle


noncomputable section

/- Theorem 1.1 (Classical Carleson) -/
theorem classical_carleson {f : ℝ → ℂ}
    (unicontf : UniformContinuous f) (periodicf : Function.Periodic f (2 * Real.pi)) --(bdd_one : ∀ x, Complex.abs (f x) ≤ 1)
    {ε : ℝ} (hε : ε ∈ Set.Ioc 0 (2 * Real.pi)) :
    ∃ E ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E ∧ MeasureTheory.volume.real E ≤ ε ∧
    ∃ N₀, ∀ x ∈ (Set.Icc 0 (2 * Real.pi)) \ E, ∀ N > N₀,
    Complex.abs (f x - partialFourierSum f N x) ≤ ε := by
  rcases hε with ⟨εpos, εle⟩
  set ε' := ε / 4 / C_control_approximation_effect ε with ε'def
  have ε'pos : ε' > 0 := div_pos (div_pos εpos (by norm_num)) (C_control_approximation_effect_pos εpos)

  -- Approximation
  obtain ⟨f₀, contDiff_f₀, periodic_f₀, hf₀⟩ := closeSmoothApproxPeriodic unicontf periodicf ε'pos
  have ε4pos : ε / 4 > 0 := by linarith
  obtain ⟨N₀, hN₀⟩ := fourierConv_ofTwiceDifferentiable periodic_f₀ ((contDiff_top.mp (contDiff_f₀)) 2) ε4pos

  set h := f₀ - f with hdef
  have h_measurable : Measurable h := Continuous.measurable (Continuous.sub contDiff_f₀.continuous unicontf.continuous)
  have h_periodic : Function.Periodic h (2 * Real.pi) := Function.Periodic.sub periodic_f₀ periodicf
  have h_bound : ∀ x, Complex.abs (h x) ≤ ε' := by
    intro x
    simp [hdef]
    rw [← Complex.dist_eq, dist_comm, Complex.dist_eq]
    exact hf₀ x

  -- Control approximation effect
  obtain ⟨E, Esubset, Emeasurable, Evolume, hE⟩ := control_approximation_effect ⟨εpos, εle⟩ ε'pos h_measurable h_periodic h_bound

  -- "epsilon third" argument
  use E, Esubset, Emeasurable, Evolume, N₀
  intro x hx N NgtN₀
  calc Complex.abs (f x - partialFourierSum f N x)
  _ = Complex.abs ((f x - f₀ x) + (f₀ x - partialFourierSum f₀ N x) + (partialFourierSum f₀ N x - partialFourierSum f N x)) := by congr; ring
  _ ≤ Complex.abs ((f x - f₀ x) + (f₀ x - partialFourierSum f₀ N x)) + Complex.abs (partialFourierSum f₀ N x - partialFourierSum f N x) := by
    apply AbsoluteValue.add_le
  _ ≤ Complex.abs (f x - f₀ x) + Complex.abs (f₀ x - partialFourierSum f₀ N x) + Complex.abs (partialFourierSum f₀ N x - partialFourierSum f N x) := by
    apply add_le_add_right
    apply AbsoluteValue.add_le
  _ ≤ ε' + (ε / 4) + (ε / 4) := by
    gcongr
    · exact hf₀ x
    · exact hN₀ N NgtN₀ x hx.1
    · have := hE x hx N
      rw [hdef, partialFourierSum_sub (contDiff_f₀.continuous.intervalIntegrable 0 (2 * Real.pi)) (unicontf.continuous.intervalIntegrable 0 (2 * Real.pi))] at this
      apply le_trans this
      rw [ε'def, mul_div_cancel₀ _ (C_control_approximation_effect_pos εpos).ne.symm]
  _ ≤ (ε / 2) + (ε / 4) + (ε / 4) := by
    gcongr
    rw [ε'def, div_div]
    apply div_le_div_of_nonneg_left εpos.le (by norm_num)
    rw [← div_le_iff' (by norm_num)]
    exact le_trans' (lt_C_control_approximation_effect εpos).le (by linarith [Real.two_le_pi])
  _ ≤ ε := by linarith
