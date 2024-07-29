/- This file contains the proof of the classical Carleson theorem from Section 11.1. -/

import Carleson.MetricCarleson
import Carleson.Classical.Basic
import Carleson.Classical.Approximation
import Carleson.Classical.ControlApproximationEffect

import Mathlib.Analysis.Fourier.AddCircle

open MeasureTheory

noncomputable section

local notation "S_" => partialFourierSum

/- Theorem 1.1 (Classical Carleson) -/
theorem classical_carleson {f : ℝ → ℂ}
    (cont_f : Continuous f) (periodic_f : f.Periodic (2 * Real.pi))
    {ε : ℝ} (εpos : 0 < ε) :
    ∃ E ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E ∧ volume.real E ≤ ε ∧
    ∃ N₀, ∀ x ∈ (Set.Icc 0 (2 * Real.pi)) \ E, ∀ N > N₀,
    ‖f x - S_ N f x‖ ≤ ε := by
  set ε' := ε / 4 / C_control_approximation_effect ε with ε'def
  have ε'pos : ε' > 0 := div_pos (div_pos εpos (by norm_num)) (C_control_approximation_effect_pos εpos)

  /- Approximate f by a smooth f₀. -/
  have unicont_f : UniformContinuous f := periodic_f.uniformContinuous_of_continuous Real.two_pi_pos cont_f.continuousOn
  obtain ⟨f₀, contDiff_f₀, periodic_f₀, hf₀⟩ := close_smooth_approx_periodic unicont_f periodic_f ε'pos
  have ε4pos : ε / 4 > 0 := by linarith
  obtain ⟨N₀, hN₀⟩ := fourierConv_ofTwiceDifferentiable periodic_f₀ ((contDiff_top.mp (contDiff_f₀)) 2) ε4pos

  set h := f₀ - f with hdef
  have h_measurable : Measurable h := (Continuous.sub contDiff_f₀.continuous cont_f).measurable
  have h_periodic : h.Periodic (2 * Real.pi) := periodic_f₀.sub periodic_f
  have h_bound : ∀ x, ‖h x‖ ≤ ε' := by
    intro x
    simp [hdef]
    rw [← Complex.dist_eq, dist_comm, Complex.dist_eq]
    exact hf₀ x

  /- Control approximation effect: Get a bound on the partial Fourier sums of h. -/
  obtain ⟨E, Esubset, Emeasurable, Evolume, hE⟩ := control_approximation_effect εpos ε'pos h_measurable h_periodic h_bound

  /- This is a classical "epsilon third" argument. -/
  use E, Esubset, Emeasurable, Evolume, N₀
  intro x hx N NgtN₀
  calc ‖f x - S_ N f x‖
  _ = ‖(f x - f₀ x) + (f₀ x - S_ N f₀ x) + (S_ N f₀ x - S_ N f x)‖ := by congr; ring
  _ ≤ ‖(f x - f₀ x) + (f₀ x - S_ N f₀ x)‖ + ‖S_ N f₀ x - S_ N f x‖ := by
    apply norm_add_le
  _ ≤ ‖f x - f₀ x‖ + ‖f₀ x - S_ N f₀ x‖ + ‖S_ N f₀ x - S_ N f x‖ := by
    apply add_le_add_right
    apply norm_add_le
  _ ≤ ε' + (ε / 4) + (ε / 4) := by
    gcongr
    · exact hf₀ x
    · exact hN₀ N NgtN₀ x hx.1
    · have := hE x hx N
      rw [hdef, partialFourierSum_sub (contDiff_f₀.continuous.intervalIntegrable 0 (2 * Real.pi)) (cont_f.intervalIntegrable 0 (2 * Real.pi))] at this
      apply le_trans this
      rw [ε'def, mul_div_cancel₀ _ (C_control_approximation_effect_pos εpos).ne.symm]
  _ ≤ (ε / 2) + (ε / 4) + (ε / 4) := by
    gcongr
    rw [ε'def, div_div]
    apply div_le_div_of_nonneg_left εpos.le (by norm_num)
    rw [← div_le_iff' (by norm_num)]
    exact le_trans' (lt_C_control_approximation_effect εpos).le (by linarith [Real.two_le_pi])
  _ ≤ ε := by linarith
