import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.MetricSpace.Holder

open Metric Function ENNReal Complex
open scoped NNReal

/-!
# Inhomogeneous Hölder norm

This file defines the inhomogeneous Hölder norm, which probably in some form should end up in Mathlib.
Lemmas about this norm that are proven in Carleson are collected here.

-/

noncomputable section

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
variable [PseudoMetricSpace X]

/-- the L^∞-normalized τ-Hölder norm. Defined in ℝ≥0∞ to avoid sup-related issues. -/
def iHolENorm (ϕ : X → ℂ) (x₀ : X) (R : ℝ) (t : ℝ) : ℝ≥0∞ :=
  (⨆ (x ∈ ball x₀ R), ‖ϕ x‖ₑ) + (ENNReal.ofReal R) ^ t *
    ⨆ (x ∈ ball x₀ R) (y ∈ ball x₀ R) (_ : x ≠ y), (‖ϕ x - ϕ y‖ₑ / (edist x y) ^ t)

def iHolNNNorm (ϕ : X → ℂ) (x₀ : X) (R : ℝ) (t : ℝ) : ℝ≥0 :=
  (iHolENorm ϕ x₀ R t).toNNReal
