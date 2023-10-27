import Carleson.Proposition1

open MeasureTheory Measure NNReal Metric Complex Set
open scoped ENNReal
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

/- The constant used in theorem1_1 -/
def C1_1 (A : ℝ≥0) (τ q : ℝ) : ℝ≥0 := sorry

def C1_1_pos (A : ℝ≥0) (τ q : ℝ) : C1_1 A τ q > 0 := sorry

variable {X : Type*} {A : ℝ≥0} [fact : Fact (1 ≤ A)] [IsSpaceOfHomogenousType X A]
  {τ q q' : ℝ} (hA : 1 < A) (h0τ : 0 < τ) (hτ1 : τ < 1)
  (h1q : 1 < q) (hq2 : q ≤ 2) (hqq' : q.IsConjugateExponent q')
  [Metric.IsRegular X A]
  (𝓠 : Set C(X, ℂ)) [IsCompatible 𝓠] [IsCancellative τ 𝓠]
  (K : X → X → ℂ) [IsCZKernel τ K]
  (hT : NormBoundedBy (ANCZOperatorLp 2 K) 1)
  {F G : Set X} (hF : Measurable F) (hG : Measurable G)

/- Theorem 1.1. -/
theorem theorem1_1 :
    ‖∫ x in G, CarlesonOperator K 𝓠 (indicator F 1) x‖₊ ≤
    C1_1 A τ q * (volume G) ^ (1 / q') * (volume F) ^ (1 / q) := by
  sorry
