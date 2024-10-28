import Carleson.ForestOperator.AlmostOrthogonality
import Carleson.HardyLittlewood
import Carleson.Psi
import Carleson.TileStructure


noncomputable section

open scoped ComplexConjugate ENNReal NNReal ShortVariables

open MeasureTheory Metric Set

namespace Tile

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X} [MetricSpace X]
  [ProofData a q K σ₁ σ₂ F G]

-- Def 6.2.1 (Lemma 6.2.1)
def correlation (s₁ s₂ : ℤ) (x₁ x₂ y : X) : ℂ := (conj (Ks s₁ x₁ y)) * (Ks s₂ x₂ y)

-- Eq. 6.2.2 (Lemma 6.2.1)
lemma mem_ball_of_correlation_ne_zero {s₁ s₂ : ℤ} {x₁ x₂ y : X}
    (hy : correlation s₁ s₂ x₁ x₂ y ≠ 0) : y ∈ (ball x₁ (↑D ^s₁)) := by
  have hKs : Ks s₁ x₁ y ≠ 0 := by
    simp only [correlation, ne_eq, mul_eq_zero, map_eq_zero, not_or] at hy
    exact hy.1
  rw [mem_ball, dist_comm]
  exact lt_of_le_of_lt (dist_mem_Icc_of_Ks_ne_zero hKs).2
    (half_lt_self_iff.mpr (defaultD_pow_pos a s₁))

def C_6_2_1 (a : ℕ) : ℝ≥0 := 2^(254 * a^3)

-- Eq. 6.2.3 (Lemma 6.2.1)
lemma correlation_kernel_bound {s₁ s₂ : ℤ} (hs₁ : s₁ ∈ Icc (- (S : ℤ)) s₂)
    (hs₂ : s₂ ∈ Icc s₁ S) {x₁ x₂ y : X} (hy : correlation s₁ s₂ x₁ x₂ y ≠ 0)/- Is hy needed?-/ :
    hnorm (a := a) (correlation s₁ s₂ x₁ x₂) x₁ ↑D ^s₁ ≤
    (C_6_2_1 a : ℝ≥0∞) / (volume (ball x₁ (↑D ^s₁)) * volume (ball x₂ (↑D ^s₂))) := by
  sorry

variable [TileStructure Q D κ S o]

def C_6_2_2 (a : ℕ) : ℝ≥0 := 2^(3 * a)

-- Lemma 6.2.2
lemma uncertainty {p₁ p₂ : 𝔓 X} (hle : 𝔰 p₁ ≤ 𝔰 p₂) {x₁ x₂ : X} (hx₁ : x₁ ∈ E p₁)
    (hx₂ : x₂ ∈ E p₂) :
    1  + dist_(p₁) (𝒬 p₁) (𝒬 p₂) ≤ (C_6_2_2 a) * (1 + dist_{x₁, D^𝔰 p₁} (Q x₁) (Q x₂)) :=
  sorry

open TileStructure.Forest

-- Lemma 6.2.3
lemma range_support {p : 𝔓 X} {g : X → ℂ} (hg : Measurable g)
    (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) {y : X} (hpy : adjointCarleson p g y ≠ 0) :
    y ∈ (ball (𝔠 p) (5 * ↑D ^𝔰 p)) :=
  sorry

def C_6_1_5 (a : ℕ) : ℝ≥0 := 2^(255 * a^3)

open GridStructure

-- Lemma 6.1.5 (part I)
lemma correlation_le {p p' : 𝔓 X} (hle : 𝔰 p' ≤ 𝔰 p) {g : X → ℂ} (hg : Measurable g)
    (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x) :
    ‖ ∫ y, (adjointCarleson p' g y) * conj (adjointCarleson p g y) ‖₊ ≤
      (C_6_1_5 a) * ((1 + dist_(p') (𝒬 p') (𝒬 p))^(-(1 : ℝ)/(2*a^2 + a^3))) /
        (volume.nnreal (coeGrid (𝓘 p))) * ∫ y in E p', ‖ g y‖ * ∫ y in E p, ‖ g y‖ := by
  sorry

-- Lemma 6.1.5 (part II)
lemma correlation_zero_of_ne_subset {p p' : 𝔓 X} (hle : 𝔰 p' ≤ 𝔰 p) {g : X → ℂ}
    (hg : Measurable g) (hg1 : ∀ x, ‖g x‖ ≤ G.indicator 1 x)
    (hpp' : ¬ coeGrid (𝓘 p) ⊆ ball (𝔠 p) (15 * ↑D ^𝔰 p) ) :
    ‖ ∫ y, (adjointCarleson p' g y) * conj (adjointCarleson p g y) ‖₊ = 0 := by
  by_contra h0
  apply hpp'
  have hy : ∃ y : X, (adjointCarleson p' g y) * conj (adjointCarleson p g y) ≠ 0 := sorry
  obtain ⟨y, hy⟩ := hy
  sorry

end Tile
