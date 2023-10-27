import Carleson.Proposition1

open MeasureTheory Measure NNReal Metric Complex Set
open scoped ENNReal
noncomputable section
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

/- The constant used in theorem1_1 -/
def C1_1 (A : ℝ≥0) (τ q : ℝ) : ℝ≥0 := sorry

def C1_1_pos (A : ℝ≥0) (τ q : ℝ) : C1_1 A τ q > 0 := sorry

/- The constant used in equation2_2 -/
def Ce2_2 (A : ℝ≥0) (τ q : ℝ) : ℝ≥0 := sorry

def Ce2_2_pos (A : ℝ≥0) (τ q : ℝ) : C1_1 A τ q > 0 := sorry

section vars
variable {X : Type*} {A : ℝ≥0} [fact : Fact (1 ≤ A)] [IsSpaceOfHomogenousType X A]
  {τ q q' : ℝ} (hA : 1 < A) (hτ : τ ∈ Ioo 0 1) (hq : q ∈ Ioc 1 2) (hqq' : q.IsConjugateExponent q')
  [Metric.IsRegular X A]
  (𝓠 : Set C(X, ℂ)) [IsCompatible 𝓠] [IsCancellative τ 𝓠]
  (K : X → X → ℂ) [IsCZKernel τ K]
  (hT : NormBoundedBy (ANCZOperatorLp 2 K) 1)
  {F G : Set X} (hF : Measurable F) (hG : Measurable G)

theorem equation2_2 (h2F : volume F ∈ Ioo 0 ∞) (h2G : volume G ∈ Ioo 0 ∞) :
    ∃ G', volume G' ≤ volume G / 2 ∧ ‖∫ x in G \ G', CarlesonOperator K 𝓠 (indicator F 1) x‖₊ ≤
    Ce2_2 A τ q * (volume G) ^ (1 / q') * (volume F) ^ (1 / q) := by
  sorry


/- Theorem 1.1, written using constant C1_1 -/
theorem theorem1_1C :
    ‖∫ x in G, CarlesonOperator K 𝓠 (indicator F 1) x‖₊ ≤
    C1_1 A τ q * (volume G) ^ (1 / q') * (volume F) ^ (1 / q) := by
  sorry

/- Specialize this to get the usual version of Carleson's theorem,
by taking `X = ℝ`, `K x y := 1 / (x - y)` and `𝓠 = {linear functions}`.
-/

end vars

set_option linter.unusedVariables false in
 /- Theorem 1.1. -/
theorem theorem1_1 {A : ℝ≥0} [fact : Fact (1 ≤ A)] {τ q q' : ℝ}
    (hA : 1 < A) (h0τ : 0 < τ) (hτ1 : τ < 1)
    (h1q : 1 < q) (hq2 : q ≤ 2) (hqq' : q.IsConjugateExponent q') : ∃ (C : ℝ≥0), C > 0 ∧
    ∀ {X : Type*} [IsSpaceOfHomogenousType X A] [Metric.IsRegular X A]
    (𝓠 : Set C(X, ℂ)) [IsCompatible 𝓠] [IsCancellative τ 𝓠]
    (K : X → X → ℂ) [IsCZKernel τ K]
    (hT : NormBoundedBy (ANCZOperatorLp 2 K) 1)
    {F G : Set X} (hF : Measurable F) (hG : Measurable G),
    ‖∫ x in G, CarlesonOperator K 𝓠 (indicator F 1) x‖₊ ≤
    C * (volume G) ^ (1 / q') * (volume F) ^ (1 / q) := by
   use C1_1 A τ q, C1_1_pos A τ q
   intros
   apply theorem1_1C -- applied to arguments
