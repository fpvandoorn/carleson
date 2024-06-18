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

def D2_2 (a : ℝ) : ℝ := 2 ^ (100 * a ^ 2)

lemma D2_2_pos (a : ℝ) : D2_2 a > 0 := sorry

def κ2_2 (A : ℝ) (τ q : ℝ) (C : ℝ) : ℝ := sorry

lemma κ2_2_pos (A : ℝ) (τ q : ℝ) (C : ℝ) : κ2_2 A τ q C > 0 := sorry

variable {X : Type*} {a : ℝ} [MetricSpace X] [DoublingMeasure X (2 ^ a)] [Inhabited X]
variable {τ q q' D κ : ℝ} {C₀ C : ℝ}
variable [CompatibleFunctions ℝ X (2 ^ a)] [IsCancellative X τ]
variable {Q : X → Θ X} {S : ℤ} {o : X} [TileStructure Q D κ C S o]
variable {F G : Set X} {σ₁ σ₂ : X → ℤ} {Q : X → Θ X}
variable (K : X → X → ℂ) [IsCZKernel τ K]

-- todo: add some conditions that σ and other functions have finite range?
-- todo: fix statement
theorem discrete_carleson
    (hA : 4 ≤ a) (hτ : τ ∈ Ioo 0 1) (hq : q ∈ Ioc 1 2) (hqq' : q.IsConjExponent q')
    -- (hC₀ : 0 < C₀) (hC : C2_2 A τ q C₀ < C) (hD : D2_2 A τ q C₀ < D)
    (hκ : κ ∈ Ioo 0 (κ2_2 (2 ^ a) τ q C₀))
    (hF : MeasurableSet F) (hG : MeasurableSet G)
    (h2F : IsBounded F) (h2G : IsBounded G)
    (m_σ₁ : Measurable σ₁) (m_σ₂ : Measurable σ₂)
    (hT : HasStrongType (ANCZOperator K) volume volume 2 2 1)
    :
    ∃ G', 2 * volume G' ≤ volume G ∧ ∀ f : X → ℂ, (∀ x, ‖f x‖ ≤ F.indicator 1 x) →
    ‖∫ x in G \ G', ∑' p, T K σ₁ σ₂ (ψ (D2_2 a)) p F 1 x‖₊ ≤
    C2_2 a q * (volume.real G) ^ (1 / q') * (volume.real F) ^ (1 / q) := by sorry
