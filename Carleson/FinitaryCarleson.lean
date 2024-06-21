import Carleson.DiscreteCarleson
import Carleson.TileExistence

open MeasureTheory Measure NNReal Metric Complex Set Function BigOperators Bornology
open scoped ENNReal
noncomputable section


open scoped ShortVariables
variable {X : Type*} {a q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [PseudoMetricSpace X]

theorem integrable_tile_sum_operator [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
    {G' : Set X} (hG' : Measurable G') (h2G' : 2 * volume G' ≤ volume G)
    {f : X → ℂ} (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    (hfg' : ‖∫ x in G \ G', ∑' p, T p f x‖₊ ≤
      C2_0_2 a q * (volume.real G) ^ (1 - 1 / q) * (volume.real F) ^ (1 / q)) {x : X}
    (hx : x ∈ G \ G') {s : ℤ} (hs : Icc (σ₁ x) (σ₂ x)) :
    Integrable fun y ↦ Ks s x y * f y * exp (I * (Q x y - Q x x)) := by
  sorry

theorem tile_sum_operator [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
    {G' : Set X} (hG' : Measurable G') (h2G' : 2 * volume G' ≤ volume G)
    {f : X → ℂ} (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    (hfg' : ‖∫ x in G \ G', ∑' p, T p f x‖₊ ≤
      C2_0_2 a q * (volume.real G) ^ (1 - 1 / q) * (volume.real F) ^ (1 / q)) {x : X}
    (hx : x ∈ G \ G') :
    ∑ p : 𝔓 X, T p f x =
    ∑ s in Icc (σ₁ x) (σ₂ x), ∫ y, Ks s x y * f y * exp (I * (Q x y - Q x x)) := by
  sorry

/- The constant used in Proposition 2.0.1 -/
def C2_0_1 (a : ℝ) (q : ℝ≥0) : ℝ≥0 := 2 ^ (440 * a ^ 3) / (q - 1) ^ 4

lemma C2_0_1_pos {a : ℝ} {q : ℝ≥0} : C2_0_1 a q > 0 := sorry

theorem finitary_carleson [ProofData a q K σ₁ σ₂ F G] :
    ∃ G', Measurable G' ∧ 2 * volume G' ≤ volume G ∧
    ∀ f : X → ℂ, Measurable f → (∀ x, ‖f x‖ ≤ F.indicator 1 x) →
    ∫⁻ x in G \ G', ‖∑ s in Icc (σ₁ x) (σ₂ x), ∫ y, Ks s x y * f y * exp (I * Q x y)‖₊ ≤
    C2_0_1 a nnq * (volume G) ^ (1 - 1 / q) * (volume F) ^ (1 / q) := by sorry
