import Carleson.TileStructure
import Carleson.HardyLittlewood
import Carleson.Psi

noncomputable section

open scoped ComplexConjugate ENNReal ShortVariables

open MeasureTheory Metric Set

section

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X} [MetricSpace X]
  [ProofData a q K σ₁ σ₂ F G]

-- Def 6.2.1 (Lemma 6.2.1)
def correlation (s₁ s₂ : ℤ) (x₁ x₂ y : X) : ℂ := (conj (Ks s₁ x₁ y)) * (Ks s₂ x₂ y)

-- Eq. 6.2.2 (Lemma 6.2.1)
lemma mem_ball_of_correlation_ne_zero (s₁ s₂ : ℤ) {x₁ x₂ y : X}
    (hy : correlation s₁ s₂ x₁ x₂ y ≠ 0) : y ∈ (ball x₁ (↑D ^s₁)) := by
  have hKs : Ks s₁ x₁ y ≠ 0 := by
    simp only [correlation, ne_eq, mul_eq_zero, map_eq_zero, not_or] at hy
    exact hy.1
  rw [mem_ball, dist_comm]
  exact lt_of_le_of_lt (dist_mem_Icc_of_Ks_ne_zero hKs).2
    (half_lt_self_iff.mpr (defaultD_pow_pos a s₁))

def C_6_2_3 (a : ℕ) : ℝ≥0∞ := 2^(254 * a^3)

-- Eq. 6.2.3 (Lemma 6.2.1)
lemma correlation_kernel_bound {s₁ s₂ : ℤ} (hs₁ : s₁ ∈ Icc (- (S : ℤ)) s₂)
    (hs₂ : s₂ ∈ Icc s₁ S) {x₁ x₂ y : X} (hy : correlation s₁ s₂ x₁ x₂ y ≠ 0) :
    hnorm (a := a) (correlation s₁ s₂ x₁ x₂) x₁ ↑D ^s₁ ≤
    (C_6_2_3 a : ℝ≥0∞) / (volume (ball x₁ (↑D ^s₁)) * volume (ball x₂ (↑D ^s₂))) := by
  sorry

variable [TileStructure Q D κ S o]

-- Lemma 6.2.2
lemma two_tile_estimate {p₁ p₂ : 𝔓 X} (hle : 𝔰 p₁ ≤ 𝔰 p₂) {x₁ x₂ : X} (hx₁ : x₁ ∈ E p₁)
    (hx₂ : x₂ ∈ E p₂) :
    1  + dist_(p₁) (𝒬 p₁) (𝒬 p₂) ≤ 2^(3 * a) * (1 + dist_{x₁, D^𝔰 p₁} (Q x₁) (Q x₂)) :=
  sorry

-- TODO: ask about T*_p
-- Lemma 6.2.3
lemma tile_range_support {p : 𝔓 X} {y : X} (/- TODO -/hpy : y = y) :
    y ∈ (ball (𝔠 p) (5 * ↑D ^𝔰 p)) :=
  sorry

-- Lemma 6.1.5
