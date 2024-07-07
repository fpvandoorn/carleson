import Carleson.Forest

open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

noncomputable section

open Set MeasureTheory Metric Function Complex Bornology TileStructure
open scoped NNReal ENNReal ComplexConjugate

def C2_0_4 (a q : ℝ) (n : ℕ) : ℝ≥0 := 2 ^ (432 * a ^ 3 - (q - 1) / q * n)

theorem forest_operator {n : ℕ} (𝔉 : Forest X n) {f g : X → ℂ}
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hg : Measurable g)
    (h2g : IsBounded (support g)) :
    ‖∫ x, conj (g x) * ∑ u ∈ 𝔉.𝔘, ∑ p ∈ 𝔉.𝔗 u, T p f x‖₊ ≤
    C2_0_4 a q n * (dens₂ (X := X) (⋃ u ∈ 𝔉.𝔘, 𝔉.𝔗 u)) ^ (q⁻¹ - 2⁻¹) *
    snorm f 2 volume * snorm g 2 volume := by
  sorry
