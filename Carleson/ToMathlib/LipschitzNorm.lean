import Mathlib.Analysis.RCLike.Basic

open Metric Function ENNReal
open scoped NNReal

/-!
# Inhomogeneous Lipschitz norm

This file defines the Lipschitz norm, which probably in some form should end up in Mathlib.
Lemmas about this norm that are proven in Carleson are collected here.

-/

noncomputable section

variable {𝕜 X : Type*} {A : ℕ} [_root_.RCLike 𝕜] [PseudoMetricSpace X]

/-- The inhomogeneous Lipschitz norm on a ball. -/
def iLipENorm {𝕜} [NormedField 𝕜] (ϕ : X → 𝕜) (x₀ : X) (R : ℝ) : ℝ≥0∞ :=
  (⨆ x ∈ ball x₀ R, ‖ϕ x‖ₑ) +
  ENNReal.ofReal R * ⨆ (x ∈ ball x₀ R) (y ∈ ball x₀ R) (_ : x ≠ y), ‖ϕ x - ϕ y‖ₑ / edist x y

/-- The `NNReal` version of the inhomogeneous Lipschitz norm on a ball, `iLipENorm`. -/
def iLipNNNorm {𝕜} [NormedField 𝕜] (ϕ : X → 𝕜) (x₀ : X) (R : ℝ) : ℝ≥0 :=
  (iLipENorm ϕ x₀ R).toNNReal
