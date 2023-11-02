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
  {τ q q' : ℝ} (hA : 1 < A) (hτ : τ ∈ Ioo 0 1) (hq : q ∈ Ioc 1 2) (hqq' : q.IsConjugateExponent q')
  [Metric.IsRegular X A]
  {𝓠 : Set C(X, ℂ)} [IsCompatible 𝓠] [IsCancellative τ 𝓠]
  (K : X → X → ℂ) [IsCZKernel τ K]
  (hT : NormBoundedBy (ANCZOperatorLp 2 K) 1)
  {F G : Set X} (hF : Measurable F) (hG : Measurable G)
  (h2F : volume F ∈ Ioo 0 ∞) (h2G : volume G ∈ Ioo 0 ∞)
  {ι 𝔓 : Type*}
  {D : ℝ} (hD : (2 * A) ^ 100 < D) -- or some other appropriate bound
  {C : ℝ≥0} (hC : 0 < C)


variable (𝓠 ι 𝔓 D C) in
structure Proposition2_1_Data extends TileStructure 𝓠 ι 𝔓 D C where
  σ : X → ℤ
  σ' : X → ℤ
  Q' : X → C(X, ℂ)
  ψ : ℝ → ℝ
  Q'_mem : ∀ x, Q' x ∈ 𝓠
  measurable_σ : Measurable σ
  measurable_σ' : Measurable σ'
  measurable_Q' : Measurable Q'
  contDiff_ψ : ContDiff ℝ ⊤ ψ
  -- probably need some other conditions on `ψ`

-- #check Proposition2_1_Data
variable (t : Proposition2_1_Data 𝓠 ι 𝔓 D C)

namespace Proposition2_1_Data

def E (p : 𝔓) : Set X :=
  { x ∈ t.𝓓 (t.𝓘 p) | t.Q' x ∈ t.Ω p ∧ t.s (t.𝓘 p) ∈ Icc (t.σ x) (t.σ' x) }

-- todo: what is ?
def T (p : 𝔓) (f : X → ℂ) : X → ℂ :=
  indicator (t.E p)
    fun x ↦ ∫ y, exp (t.Q' x x - t.Q' x y) * K x y * t.ψ (D ^ (- t.s (t.𝓘 p)) * dist x y) * f y

end Proposition2_1_Data

theorem proposition2_1 :
    ∃ G', volume G' ≤ volume G / 4 ∧ ‖∫ x in G \ G', ∑' p, t.T p f (indicator F 1) x‖₊ ≤
    C2_1 A τ q C * (volume G) ^ (1 / q') * (volume F) ^ (1 / q) := by sorry
