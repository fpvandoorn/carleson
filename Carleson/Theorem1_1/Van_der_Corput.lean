/- This file formalizes section 10.6 (The proof of the van der Corput Lemma) from the paper. -/
import Carleson.Theorem1_1.Basic

noncomputable section

/-Generalized and slightly changed definition. -/
def iLipNorm' {X : Type} [PseudoMetricSpace X] (ϕ : X → ℂ) (E : Set X) : ℝ :=
  (⨆ x ∈ E, ‖ϕ x‖) + Metric.diam E * ⨆ (x : X) (y : X), ‖ϕ x - ϕ y‖ / dist x y

open Complex

lemma van_der_Corput {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 2 * Real.pi) {n : ℤ} {ϕ : ℝ → ℂ} {K : NNReal} (h1 : LipschitzWith K ϕ) :
  ‖∫ (x : ℝ) in a..b, (-I * n).exp * ϕ x‖ ≤
    2 * Real.pi * (b - a) * iLipNorm' ϕ (Set.Icc a b) *
      (1 + |n| * (b - a))⁻¹ := sorry
