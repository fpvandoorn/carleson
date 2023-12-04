import Carleson.Defs

open MeasureTheory Measure NNReal Metric Complex Set TileStructure Function
open scoped ENNReal
noncomputable section
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

def C2_3 (A : ℝ) (τ q : ℝ) (C : ℝ) : ℝ := sorry

lemma C2_3_pos (A : ℝ) (τ q : ℝ) (C : ℝ) : C2_3 A τ q C > 0 := sorry

def κ2_3 (A : ℝ) (τ q : ℝ) (C : ℝ) : ℝ := sorry

lemma κ2_3_pos (A : ℝ) (τ q : ℝ) (C : ℝ) : κ2_3 A τ q C > 0 := sorry

def ε2_3 (A : ℝ) (τ q : ℝ) (C : ℝ) : ℝ := sorry

lemma ε2_3_pos (A : ℝ) (τ q : ℝ) (C : ℝ) : ε2_3 A τ q C > 0 := sorry

def δ2_3 (A : ℝ) (τ q : ℝ) (C : ℝ) : ℝ := sorry

lemma δ2_3_pos (A : ℝ) (τ : ℝ) (C : ℝ) : δ2_3 A τ C > 0 := sorry

def Cψ2_3 (A : ℝ) (τ q : ℝ) (C : ℝ) : ℝ≥0 := sorry

lemma Cψ2_3_pos (A : ℝ) (τ : ℝ) (C : ℝ) : Cψ2_3 A τ C > 0 := sorry

variable {X : Type*} {A : ℝ} (hA : 1 ≤ A) [IsSpaceOfHomogeneousType X A] [Inhabited X]
variable {τ q D κ ε δ : ℝ} {C₀ C t : ℝ}
variable {𝓠 : Set C(X, ℂ)} [IsCompatible 𝓠] [IsCancellative τ 𝓠] [TileStructure 𝓠 D κ C₀]
variable {F G : Set X} {σ σ' : X → ℤ} {Q' : X → C(X, ℂ)} /- Q-tilde in the pdf -/
variable (K : X → X → ℂ) [IsCZKernel τ K]
variable {ψ : ℝ → ℝ}
variable {n : ℕ} {𝔉 : Forest G Q' δ n}

theorem prop2_3
    (hA : 1 < A) (hτ : τ ∈ Ioo 0 1) (hq : q ∈ Ioc 1 2)
    (hC₀ : 0 < C₀) (hC : C2_3 A τ q C₀ < C)
    (hκ : κ ∈ Ioo 0 (κ2_3 A τ q C₀))
    (hε : ε ∈ Ioo 0 (ε2_3 A τ q C₀))
    (hδ : δ ∈ Ioo 0 (δ2_3 A τ q C₀))
    (hD : (2 * A) ^ 100 < D) -- or some other appropriate bound
    (hF : MeasurableSet F) (hG : MeasurableSet G)
    (h2F : volume F ∈ Ioo 0 ∞) (h2G : volume G ∈ Ioo 0 ∞)
    (Q'_mem : ∀ x, Q' x ∈ 𝓠) (m_Q' : Measurable Q')
    (m_σ : Measurable σ) (m_σ' : Measurable σ')
    (hT : NormBoundedBy (ANCZOperatorLp 2 K) 1)
    (hψ : LipschitzWith (Cψ2_3 A τ q C₀) ψ)
    (h2ψ : support ψ ⊆ Icc (4 * D)⁻¹ 2⁻¹) (h3ψ : ∀ x > 0, ∑ᶠ s : ℤ, ψ (D ^ s * x) = 1)
    (ht : t ∈ Ioc 0 1)
    (h𝔉 : 𝔉.carrier ⊆ boundedTiles F t)
    :
    ‖∑ᶠ p ∈ 𝔉.carrier, TL K Q' σ σ' ψ p F‖₊ ≤ C * (2 : ℝ) ^ (- ε * n) * t ^ (1 / q - 1 / 2) := by
  sorry
