import Carleson.GridStructure
import Carleson.Psi
-- import Carleson.Proposition2
-- import Carleson.Proposition3

open MeasureTheory Measure NNReal Metric Complex Set Function BigOperators Bornology
open scoped ENNReal
noncomputable section

/- The constant used in Proposition 2.0.2 -/
def C2_2 (a : ℝ) (q : ℝ) : ℝ := 2 ^ (440 * a ^ 3) / (q - 1) ^ 4

lemma C2_2_pos (a q : ℝ) : C2_2 a q > 0 := sorry

open scoped ShortVariables
variable {X : Type*} {a q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}

-- variable {X : Type*} {a : ℝ} [MetricSpace X] [DoublingMeasure X (2 ^ a)] [Inhabited X]
-- variable {τ q q' D κ : ℝ} {C₀ C : ℝ}
-- variable [CompatibleFunctions ℝ X (2 ^ a)] [IsCancellative X τ]
-- variable {Q : X → Θ X} {S : ℤ} {o : X} [TileStructure Q D κ S o]
-- variable {F G : Set X} {σ₁ σ₂ : X → ℤ} {Q : X → Θ X}
-- variable (K : X → X → ℂ) [IsCZKernel τ K]

theorem discrete_carleson [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o] :
    ∃ G', 2 * volume G' ≤ volume G ∧ ∀ f : X → ℂ, (∀ x, ‖f x‖ ≤ F.indicator 1 x) →
    ‖∫ x in G \ G', ∑' p, T p f x‖₊ ≤
    C2_2 a q * (volume.real G) ^ (1 - 1 / q) * (volume.real F) ^ (1 / q) := by sorry
