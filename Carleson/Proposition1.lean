import Carleson.Proposition2
import Carleson.Proposition3
import Carleson.Proposition4

open MeasureTheory Measure NNReal Metric Complex Set
open scoped ENNReal
noncomputable section
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

/- The constant used in proposition2_1 -/
def C2_1 (A : ℝ≥0) (τ q : ℝ) (C : ℝ≥0) : ℝ≥0 := sorry

def C2_1_pos (A : ℝ≥0) (τ q : ℝ) (C : ℝ≥0) : C2_1 A τ q C > 0 := sorry

variable {X : Type*} {A : ℝ≥0} [fact : Fact (1 ≤ A)] [IsSpaceOfHomogeneousType X A] [Inhabited X]
variable [Metric.IsRegular X A]
variable {τ q q' D κ : ℝ} {C : ℝ≥0}
variable {𝓠 : Set C(X, ℂ)} [IsCompatible 𝓠] [IsCancellative τ 𝓠] [TileStructure 𝓠 D κ C]
variable {F G : Set X} {σ σ' : X → ℤ} {Q' : X → C(X, ℂ)} /- Q-tilde in the pdf -/
variable (K : X → X → ℂ) [IsCZKernel τ K]
variable {ψ : ℝ → ℝ} {Cψ : ℝ≥0} -- this should be `10 * D` or something

-- todo: add some conditions that σ and other functions have finite range?
theorem proposition2_1
    (hA : 1 < A) (hτ : τ ∈ Ioo 0 1) (hq : q ∈ Ioc 1 2) (hqq' : q.IsConjugateExponent q')
    (hC : 0 < C)
    (hD : (2 * A) ^ 100 < D) -- or some other appropriate bound
    (K : X → X → ℂ) [IsCZKernel τ K]
    (hF : Measurable F) (hG : Measurable G)
    (h2F : volume F ∈ Ioo 0 ∞) (h2G : volume G ∈ Ioo 0 ∞)
    (Q'_mem : ∀ x, Q' x ∈ 𝓠) (m_Q' : Measurable Q')
    (m_σ : Measurable σ) (m_σ' : Measurable σ')
    (hT : NormBoundedBy (ANCZOperatorLp 2 K) 1)
    (hψ : LipschitzWith Cψ ψ) (h2ψ : HasCompactSupport ψ)
    :
    ∃ G', volume G' ≤ volume G / 4 ∧ ‖∫ x in G \ G', ∑' p, T K Q' σ σ' ψ p F 1 x‖₊ ≤
    C2_1 A τ q C * (volume G) ^ (1 / q') * (volume F) ^ (1 / q) := by sorry
