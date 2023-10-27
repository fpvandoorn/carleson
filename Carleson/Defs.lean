import Carleson.HomogenousType

open MeasureTheory Measure NNReal Metric Complex Set
open scoped ENNReal
noncomputable section


/-! Miscellaneous definitions. We should move them to separate files once we start using them. -/

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

/-- A quasi metric space with regular/`A`-Lipschitz distance. -/
class Metric.IsRegular (X : Type*) (A : outParam ℝ≥0) [fact : Fact (1 ≤ A)] [QuasiMetricSpace X A]
  where abs_dist_sub_dist_le : ∀ x y y' : X, |dist x y - dist x y'| ≤ A * dist y y'

export Metric.IsRegular (abs_dist_sub_dist_le)

variable {X : Type*} {A : ℝ≥0} [fact : Fact (1 ≤ A)] [IsSpaceOfHomogenousType X A]

section localOscillation

/-- The local oscillation of two functions. -/
def localOscillation (E : Set X) (f g : C(X, ℂ)) : ℝ :=
  ⨆ z : E × E, ‖f z.1 - g z.1 - f z.2 + g z.2‖

variable {E : Set X} {f g : C(X, ℂ)}

def localOscillationBall (E : Set X) (f : C(X, ℂ)) (r : ℝ) : Set C(X, ℂ) :=
  { g : C(X, ℂ) | localOscillation E f g < r }

end localOscillation


/- mathlib is missing Hölder spaces.
Todo:
* Define Hölder spaces
* Define the norm in Hölder spaces
* Show that Hölder spaces are homogenous -/

/-- A set `𝓠` of (continuous) functions is compatible. -/
class IsCompatible (𝓠 : Set C(X, ℂ)) : Prop where
  localOscillation_two_mul_le {x₁ x₂ : X} {r : ℝ} {f g : C(X, ℂ)} (hf : f ∈ 𝓠) (hg : g ∈ 𝓠)
    (h : dist x₁ x₂ < 2 * r) :
    localOscillation (ball x₂ (2 * r)) f g ≤ A * localOscillation (ball x₁ r) f g
  localOscillation_le_of_subset {x₁ x₂ : X} {r : ℝ} {f g : C(X, ℂ)} (hf : f ∈ 𝓠) (hg : g ∈ 𝓠)
    (h1 : ball x₁ r ⊆ ball x₂ (A * r)) (h2 : A * r ≤ Metric.diam (univ : Set X)) :
    2 * localOscillation (ball x₁ r) f g ≤ localOscillation (ball x₂ (A * r)) f g
  ballsCoverBalls {x : X} {r R : ℝ} :
    BallsCoverBalls (localOscillation (ball x r)) (2 * R) R ⌊A⌋₊

export IsCompatible (localOscillation_two_mul_le localOscillation_le_of_subset ballsCoverBalls)

set_option linter.unusedVariables false in
/-- The inhomogeneous Lipschitz norm on a ball (I'm assuming `R` is the radius of the ball?). -/
def iLipNorm (ϕ : X → ℂ) (x₀ : X) (R : ℝ) : ℝ :=
  (⨆ x ∈ ball x₀ R, ‖ϕ x‖) + R * ⨆ (x : X) (y : X) (h : x ≠ y), ‖ϕ x - ϕ y‖ / nndist x y

/-- 𝓠 is τ-cancellative -/
class IsCancellative (τ : ℝ) (𝓠 : Set C(X, ℂ)) : Prop where
  norm_integral_exp_le {x : X} {r : ℝ} {ϕ : X → ℂ} {K : ℝ≥0} (h1 : LipschitzWith K ϕ)
    (h2 : tsupport ϕ ⊆ ball x r) {f g : C(X, ℂ)} (hf : f ∈ 𝓠) (hg : g ∈ 𝓠) :
    ‖∫ x in B, exp (i * (f x - g x)) * ϕ x‖ ≤
    A * (volume B).toReal * iLipNorm ϕ x r * (1 + localOscillation (ball x r) f g) ^ (- τ)

export IsCancellative (norm_integral_exp_le)

/-- The "volume function". Note that we will need to assume
`IsFiniteMeasureOnCompacts` and `ProperSpace` to actually know that this volume is finite. -/
def Real.vol {X : Type*} [QuasiMetricSpace X A] [MeasureSpace X] (x y : X) : ℝ :=
  ENNReal.toReal (volume (ball x (dist x y)))

open Real (vol)

/-- `K` is a one-sided `τ`-Calderon-Zygmund kernel -/
class IsCZKernel (τ : ℝ) (K : X → X → ℂ) : Prop where
  norm_le_vol_inv (x y : X) : ‖K x y‖ ≤ (vol x y)⁻¹
  norm_sub_le {x x' y y' : X} (h : A * dist x x' ≤ dist x y) :
    ‖K x y - K x y'‖ ≤ (dist y y' / dist x y) ^ τ * (vol x y)⁻¹

/-- In Mathlib we only have the operator norm for continuous linear maps,
and (I think that) `T_*` is not linear.
Here is the norm for an arbitary map `T` between normed spaces
(the infimum is defined to be 0 if the operator is not bounded). -/
def operatorNorm {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] (T : E → F) : ℝ :=
  sInf { c | 0 ≤ c ∧ ∀ x, ‖T x‖ ≤ c * ‖x‖ }

/-- Instead of the above `operatorNorm`, this might be more appropriate. -/
def NormBoundedBy {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] (T : E → F) (c : ℝ) :
    Prop :=
  ∀ x, ‖T x‖ ≤ c * ‖x‖

set_option linter.unusedVariables false in
/-- The associated nontangential Calderon Zygmund operator -/
def ANCZOperator (K : X → X → ℂ) (f : X → ℂ) (x : X) : ℝ :=
  ⨆ (R₁ : ℝ) (R₂ : ℝ) (h1 : R₁ < R₂) (x' : X) (h2 : dist x x' ≤ R₁),
  ‖∫ y in {y | R₁ < dist x' y ∧ dist x' y < R₂}, K x' y * f y‖

/-- The associated nontangential Calderon Zygmund operator, viewed as a map `L^p → L^p`.
Todo: is `T_*f` indeed in L^p if `f` is? -/
def ANCZOperatorLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (K : X → X → ℂ) (f : Lp ℂ p (volume : Measure X)) :
    Lp ℝ p (volume : Measure X) :=
  Memℒp.toLp (ANCZOperator K (f : X → ℂ)) sorry

set_option linter.unusedVariables false in
/-- The (maximally truncated) polynomial Carleson operator `T`. -/
def CarlesonOperator (K : X → X → ℂ) (𝓠 : Set C(X, ℂ)) (f : X → ℂ) (x : X) : ℝ :=
  ⨆ (Q ∈ 𝓠) (R₁ : ℝ) (R₂ : ℝ) (h1 : R₁ < R₂),
  ‖∫ y in {y | R₁ < dist x y ∧ dist x y < R₂}, K x y * f y * exp (I * Q y)‖

/- Specialize this to get the usual version of Carleson's theorem,
by taking `X = ℝ`, `K x y := 1 / (x - y)` and `𝓠 = {linear functions}`.
-/

set_option linter.unusedVariables false in
variable (X) in
class SmallBoundaryProperty (η : ℝ) : Prop where
  volume_diff_le : ∃ (C : ℝ≥0) (hC : C > 0), ∀ (x : X) r (δ : ℝ≥0), 0 < r → 0 < δ → δ < 1 →
    volume (ball x ((1 + δ) * r) \ ball x ((1 - δ) * r)) ≤ C * δ ^ η * volume (ball x r)
