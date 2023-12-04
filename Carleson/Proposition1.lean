import Carleson.Proposition2
import Carleson.Proposition3

open MeasureTheory Measure NNReal Metric Complex Set Function
open scoped ENNReal
noncomputable section
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

/- The constant used in proposition2_1 -/
def C2_1 (A : ℝ) (τ q : ℝ) (C : ℝ) : ℝ := sorry

lemma C2_1_pos (A : ℝ) (τ q : ℝ) (C : ℝ) : C2_1 A τ q C > 0 := sorry

def D2_1 (A : ℝ) (τ q : ℝ) (C : ℝ) : ℝ := sorry

lemma D2_1_pos (A : ℝ) (τ q : ℝ) (C : ℝ) : D2_1 A τ q C > 0 := sorry

def κ2_1 (A : ℝ) (τ q : ℝ) (C : ℝ) : ℝ := sorry

lemma κ2_1_pos (A : ℝ) (τ q : ℝ) (C : ℝ) : κ2_1 A τ q C > 0 := sorry

-- this should be `10 * D` or something
def Cψ2_1 (A : ℝ) (τ q : ℝ) (C : ℝ) : ℝ≥0 := sorry

lemma Cψ2_1_pos (A : ℝ) (τ : ℝ) (C : ℝ) : Cψ2_1 A τ C > 0 := sorry

variable {X : Type*} {A : ℝ} [MetricSpace X] [IsSpaceOfHomogeneousType X A] [Inhabited X]
variable {τ q q' D κ : ℝ} {C₀ C : ℝ}
variable {𝓠 : Set C(X, ℂ)} [IsCompatible 𝓠] [IsCancellative τ 𝓠] [TileStructure 𝓠 D κ C₀]
variable {F G : Set X} {σ σ' : X → ℤ} {Q' : X → C(X, ℂ)} /- Q-tilde in the pdf -/
variable (K : X → X → ℂ) [IsCZKernel τ K]
variable {ψ : ℝ → ℝ}

-- todo: add some conditions that σ and other functions have finite range?
theorem prop2_1
    (hA : 1 < A) (hτ : τ ∈ Ioo 0 1) (hq : q ∈ Ioc 1 2) (hqq' : q.IsConjugateExponent q')
    (hC₀ : 0 < C₀) (hC : C2_1 A τ q C₀ < C) (hD : D2_1 A τ q C₀ < D)
    (hκ : κ ∈ Ioo 0 (κ2_1 A τ q C₀))
    (hF : MeasurableSet F) (hG : MeasurableSet G)
    (h2F : volume F ∈ Ioo 0 ∞) (h2G : volume G ∈ Ioo 0 ∞)
    (Q'_mem : ∀ x, Q' x ∈ 𝓠) (m_Q' : Measurable Q')
    (m_σ : Measurable σ) (m_σ' : Measurable σ')
    (hT : NormBoundedBy (ANCZOperatorLp 2 K) 1)
    (hψ : LipschitzWith (Cψ2_1 A τ q C₀) ψ)
    (h2ψ : support ψ ⊆ Icc (4 * D)⁻¹ 2⁻¹) (h3ψ : ∀ x > 0, ∑ᶠ s : ℤ, ψ (D ^ s * x) = 1)
    :
    ∃ G', volume G' ≤ volume G / 4 ∧ ‖∫ x in G \ G', ∑' p, T K Q' σ σ' ψ p F 1 x‖₊ ≤
    C * (volume.real G) ^ (1 / q') * (volume.real F) ^ (1 / q) := by sorry
