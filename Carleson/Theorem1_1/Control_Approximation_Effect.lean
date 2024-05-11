/- This file formalizes section 10.8 (The error bound) from the paper. -/
import Carleson.Carleson
import Carleson.HomogeneousType
import Carleson.Theorem1_1.Basic

import Mathlib.Analysis.Fourier.AddCircle


noncomputable section

/-Slightly more general version of Lemma 10.3 (control approximation effect).-/
lemma control_approximation_effect {ε : ℝ} (hε : 0 < ε ∧ ε ≤ 2 * Real.pi)
    {h : ℝ → ℂ} (hh: Measurable h ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi), Complex.abs (h x) ≤ 2 ^ (- (2 ^ 50 : Int))) :
    ∃ E₂ ⊆ Set.Icc 0 (2 * Real.pi), MeasurableSet E₂ ∧ MeasureTheory.volume.real E₂ ≤ ε ∧ ∀ x ∈ Set.Icc 0 (2 * Real.pi) \ E₂,
      ∀ N, Complex.abs (partialFourierSum h N x) ≤ ε / 4 := by
  sorry
