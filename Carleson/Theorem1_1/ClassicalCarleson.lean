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
  set ε' := (2 ^ (- (2 ^ 50 : ℝ))) * ε ^ 2 with ε'def
  have ε'pos : ε' > 0 := by
    rw [ε'def]
    apply mul_pos
    . apply Real.rpow_pos_of_pos zero_lt_two
    . rw [pow_two]
      apply mul_pos <;> exact hε.1
  obtain ⟨f₀, contDiff_f₀, periodic_f₀, hf₀⟩ := closeSmoothApproxPeriodic unicontf periodicf ε'pos

  --Lemma 10.2 from the paper
  --changed interval to Icc to match the interval in the theorem
  have ε4pos : ε / 4 > 0 := by linarith
  obtain ⟨N₀, hN₀⟩ := fourierConv_ofTwiceDifferentiable periodic_f₀ ((contDiff_top.mp (contDiff_f₀)) 2) ε4pos


  set h := f₀ - f with hdef
  have h_measurable : Measurable h := Continuous.measurable (Continuous.sub contDiff_f₀.continuous unicontf.continuous)
  have h_periodic : Function.Periodic h (2 * Real.pi) := Function.Periodic.sub periodic_f₀ periodicf
  have h_bound : ∀ x ∈ Set.Icc (-Real.pi) (3 * Real.pi), Complex.abs (h x) ≤ ε' := by
    intro x _
    rw [hdef]
    simp
    rw [←Complex.dist_eq, dist_comm, Complex.dist_eq]
    exact hf₀ x

  --TODO : replace E₂ by E
  obtain ⟨E₂, E₂subset, E₂measurable, E₂volume, hE₂⟩ := control_approximation_effect' hε ε'pos h_measurable h_periodic h_bound

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
  _ ≤ ε' + (ε / 4) + (ε / 4) := by
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
    . have := hE₂ x hx N
      rw [hdef, partialFourierSum_sub (contDiff_f₀.continuous.intervalIntegrable 0 (2 * Real.pi)) (unicontf.continuous.intervalIntegrable 0 (2 * Real.pi))] at this
      apply le_trans this
      rw [C_control_approximation_effect, ε'def]
      sorry
  _ ≤ (ε / 2) + (ε / 4) + (ε / 4) := by
    gcongr
    rw [ε'def, pow_two, ←mul_assoc, le_div_iff (by norm_num), mul_comm, ←mul_assoc, ←(le_div_iff hε.1), div_self hε.1.ne.symm, ←mul_assoc]
    calc 2 * 2 ^ (-2 ^ 50 : ℝ) * ε
      _ ≤ 2 ^ (1 - 2 ^ 50 : ℝ) * (2 * Real.pi) := by
        gcongr
        . exact hε.1.le
        . apply le_of_eq
          rw [sub_eq_neg_add, Real.rpow_add (by norm_num), Real.rpow_one, mul_comm]
        . exact hε.2
      _ ≤ 2 ^ (1 - 2 ^ 50 : ℝ) * (2 * 4) := by
        gcongr
        exact Real.pi_le_four
      _ = 2 ^ (1 - 2 ^ 50 : ℝ) * 2 ^ (3 : ℝ) := by
        congr
        norm_num
      _ = 2 ^ (1 - (2 ^ 50 : ℝ) + 3) := by
        rw [Real.rpow_add (by norm_num)]
      _ ≤ 1 := by
        apply Real.rpow_le_one_of_one_le_of_nonpos <;> norm_num
  _ ≤ ε := by linarith
