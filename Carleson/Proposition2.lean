import Carleson.Defs

open MeasureTheory Measure NNReal Metric Complex Set Function
open scoped ENNReal
noncomputable section
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

def C2_2 (A : ℝ≥0) (τ q : ℝ) (C : ℝ≥0) : ℝ≥0 := sorry

lemma C2_2_pos (A : ℝ≥0) (τ q : ℝ) (C : ℝ≥0) : C2_2 A τ q C > 0 := sorry

def D2_2 (A : ℝ≥0) (τ q : ℝ) (C : ℝ≥0) : ℝ := sorry

lemma D2_2_pos (A : ℝ≥0) (τ q : ℝ) (C : ℝ≥0) : D2_2 A τ q C > 0 := sorry

def ε2_2 (A : ℝ≥0) (τ q : ℝ) (C : ℝ≥0) : ℝ := sorry

lemma ε2_2_pos (A : ℝ≥0) (τ q : ℝ) (C : ℝ≥0) : ε2_2 A τ q C > 0 := sorry

def κ2_2 (A : ℝ≥0) (τ q : ℝ) (C : ℝ≥0) : ℝ := sorry

lemma κ2_2_pos (A : ℝ≥0) (τ q : ℝ) (C : ℝ≥0) : κ2_2 A τ q C > 0 := sorry

-- this should be `10 * D` or something
def Cψ2_2 (A : ℝ≥0) (τ q : ℝ) (C : ℝ≥0) : ℝ≥0 := sorry

lemma Cψ2_2_pos (A : ℝ≥0) (τ : ℝ) (C : ℝ≥0) : Cψ2_2 A τ C > 0 := sorry

variable {X : Type*} {A : ℝ≥0} [fact : Fact (1 ≤ A)] [IsSpaceOfHomogeneousType X A] [Inhabited X]
variable [Metric.IsRegular X A]
variable {τ q D κ ε : ℝ} {C₀ C t : ℝ≥0}
variable {𝓠 : Set C(X, ℂ)} [IsCompatible 𝓠] [IsCancellative τ 𝓠] [TileStructure 𝓠 D κ C₀]
variable {F G : Set X} {σ σ' : X → ℤ} {Q' : X → C(X, ℂ)} /- Q-tilde in the pdf -/
variable (K : X → X → ℂ) [IsCZKernel τ K]
variable {ψ : ℝ → ℝ}
variable {𝔄 : Set (𝔓 X)}

theorem prop2_2
    (hA : 1 < A) (hτ : τ ∈ Ioo 0 1) (hq : q ∈ Ioc 1 2)
    (hC₀ : 0 < C₀) (hC : C2_2 A τ q C₀ < C) (hD : D2_2 A τ q C₀ < D)
    (hκ : κ ∈ Ioo 0 (κ2_2 A τ q C₀))
    (hε : ε ∈ Ioo 0 (ε2_2 A τ q C₀))
    (hF : MeasurableSet F) (hG : MeasurableSet G)
    (h2F : volume F ∈ Ioo 0 ∞) (h2G : volume G ∈ Ioo 0 ∞)
    (Q'_mem : ∀ x, Q' x ∈ 𝓠) (m_Q' : Measurable Q')
    (m_σ : Measurable σ) (m_σ' : Measurable σ')
    (hT : NormBoundedBy (ANCZOperatorLp 2 K) 1)
    (hψ : LipschitzWith (Cψ2_2 A τ q C₀) ψ)
    (h2ψ : support ψ ⊆ Icc (4 * D)⁻¹ 2⁻¹) (h3ψ : ∀ x > 0, ∑ᶠ s : ℤ, ψ (D ^ s * x) = 1)
    (ht : t ∈ Ioc 0 1)
    (h𝔄 : IsAntichain (·≤·) 𝔄)
    (h2𝔄 : 𝔄 ⊆ boundedTiles F t) (h3𝔄 : 𝔄.Finite)
    :
    ‖∑ᶠ p ∈ 𝔄, TL K Q' σ σ' ψ p F‖₊ ≤ C * (density G Q' 𝔄) ^ ε * t ^ (1 / q - 1 / 2) := by
  sorry
