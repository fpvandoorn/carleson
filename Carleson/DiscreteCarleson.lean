import Carleson.GridStructure
import Carleson.Psi
-- import Carleson.Proposition2
-- import Carleson.Proposition3

open MeasureTheory Measure NNReal Metric Complex Set Function BigOperators Bornology
open scoped ENNReal
noncomputable section


open scoped ShortVariables
variable {X : Type*} {a q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X]

/- The constant used in Proposition 2.0.2 -/
def C2_0_2 (a : ℝ) (q : ℝ) : ℝ := 2 ^ (440 * a ^ 3) / (q - 1) ^ 5

lemma C2_0_2_pos {a q : ℝ} : C2_0_2 a q > 0 := sorry

theorem discrete_carleson [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o] :
    ∃ G', Measurable G' ∧ 2 * volume G' ≤ volume G ∧
    ∀ f : X → ℂ, Measurable f → (∀ x, ‖f x‖ ≤ F.indicator 1 x) →
    ‖∫ x in G \ G', ∑' p, T p f x‖₊ ≤
    C2_0_2 a q * (volume.real G) ^ (1 - 1 / q) * (volume.real F) ^ (1 / q) := by sorry
