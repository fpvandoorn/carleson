module

public import Mathlib.Analysis.Fourier.AddCircle

/-! # Key definitions and setup for the Carleson project

This file contains the statements of the main theorems from the Carleson formalization project:
Theorem 1.0.1 (classical Carleson), Theorem 1.1.1 (metric space Carleson) and Theorem 1.1.2
(linearised metric Carleson), as well as the definitions required to state these results.

These are intentionally put in a very low-level file to enable running the comparator tool.

## Main definitions and results

- `MeasureTheory.DoublingMeasure`: A metric space with a measure with some nice propreties,
including a doubling condition. This is called a "doubling metric measure space" in the blueprint.
- `FunctionDistances`: class stating that continuous functions have distances associated to
every ball.
- `IsOneSidedKernel K` states that `K` is a one-sided Calderon-Zygmund kernel.
- `KernelProofData`: Data common through most of chapters 2-7. These contain the minimal axioms
for `kernel-summand`'s proof.
- `MeasureTheory.DoublingMeasure`: A metric space with a measure with some nice propreties,
including a doubling condition. This is called a "doubling metric measure space" in the blueprint.
- `FunctionDistances`: class stating that continuous functions have distances associated to
every ball.
- `IsOneSidedKernel K` states that `K` is a one-sided Calderon-Zygmund kernel.
- `KernelProofData`: Data common through most of chapters 2-7. These contain the minimal axioms
for `kernel-summand`'s proof.
- `ClassicalCarleson`: statement of Carleson's theorem asserting a.e. convergence of the partial
Fourier sums for continous functions (Theorem 1.0.1 in the blueprint).
- `MetricSpaceCarleson`: statement of Theorem 1.1.1 from the blueprint.
- `LinearizedMetricCarleson`: statement of Theorem 1.1.2 from the blueprint.

-/

@[expose] public noncomputable section

open MeasureTheory Measure Metric Complex Set ENNReal
open scoped NNReal

open Real in
/-- The Nᵗʰ partial Fourier sum of `f : ℝ → ℂ` for `N : ℕ`. -/
def partialFourierSum (N : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
    fourierCoeffOn Real.two_pi_pos f n * fourier n (x : AddCircle (2 * π))

/- Basic definitions not specific to this project: they will be added to Mathlib soon -/
section BasicDefinitions

variable {X E : Type*}

/-- The "volume function" `V`. Preferably use `vol` instead. -/
protected def Real.vol [PseudoMetricSpace X] [MeasureSpace X] (x y : X) : ℝ :=
  volume.real (ball x (dist x y))

def Set.Annulus.oo [PseudoMetricSpace X] (x : X) (r R : ℝ) := {y | dist x y ∈ Ioo r R}

def Set.EAnnulus.oo [PseudoMetricSpace X] (x : X) (r R : ℝ≥0∞) := {y | edist x y ∈ Ioo r R}

/-- The inhomogeneous Lipschitz norm on a ball. -/
def iLipENorm {𝕜 X : Type*} [NormedField 𝕜] [PseudoMetricSpace X]
  (φ : X → 𝕜) (x₀ : X) (R : ℝ) : ℝ≥0∞ :=
  (⨆ x ∈ ball x₀ R, ‖φ x‖ₑ) +
  ENNReal.ofReal R * ⨆ (x ∈ ball x₀ R) (y ∈ ball x₀ R) (_ : x ≠ y), ‖φ x - φ y‖ₑ / edist x y

variable {𝕜 X : Type*} {A : ℕ} [_root_.RCLike 𝕜] [PseudoMetricSpace X] in
/-- The local oscillation of two functions w.r.t. a set `E`. This is `d_E` in the blueprint. -/
def localOscillation (E : Set X) (f g : C(X, 𝕜)) : ℝ≥0∞ :=
  ⨆ z ∈ E ×ˢ E, ENNReal.ofReal ‖f z.1 - g z.1 - f z.2 + g z.2‖

variable {X E : Type*} [MeasurableSpace X] {f g : X → E}
  {μ : Measure X} [TopologicalSpace E] [ENorm E] [Zero E] in
/-- Bounded measurable function $g$ on $X$ supported on a set of finite measure -/
@[fun_prop]
structure BoundedFiniteSupport (f : X → E) (μ : Measure X := by volume_tac) : Prop where
  memLp_top : MemLp f ∞ μ
  measure_support_lt : μ (Function.support f) < ∞

/-- A weaker version of `HasStrongType`. This is the same as `HasStrongType` if `T` is continuous
w.r.t. the L^2 norm, but weaker in general. -/
def MeasureTheory.HasBoundedStrongType
    {ε₁ ε₂ : Type*} [ENorm ε₁] [ENorm ε₂] [TopologicalSpace ε₁] [TopologicalSpace ε₂] [Zero ε₁]
    {α α' : Type*} {_x : MeasurableSpace α} {_x' : MeasurableSpace α'}
    (T : (α → ε₁) → (α' → ε₂))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, BoundedFiniteSupport f μ →
    AEStronglyMeasurable (T f) ν ∧ eLpNorm (T f) p' ν ≤ c * eLpNorm f p μ

/-- A doubling measure is a measure on a metric space with the condition that doubling
the radius of a ball only increases the volume by a constant factor, independent of the ball. -/
class MeasureTheory.Measure.IsDoubling {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) (A : outParam ℝ≥0) : Prop where
  measure_ball_two_le_same : ∀ (x : X) r, μ (ball x (2 * r)) ≤ A * μ (ball x r)
export IsDoubling (measure_ball_two_le_same)

/-- A metric space with a measure with some nice propreties, including a doubling condition.
This is called a "doubling metric measure space" in the blueprint.
`A` will usually be `2 ^ a`. -/
class MeasureTheory.DoublingMeasure (X : Type*) (A : outParam ℝ≥0) [PseudoMetricSpace X] extends
    CompleteSpace X, LocallyCompactSpace X,
    MeasureSpace X, BorelSpace X,
    IsLocallyFiniteMeasure (volume : Measure X),
    Measure.IsDoubling (volume : Measure X) A, NeZero (volume : Measure X) where

end BasicDefinitions

-- Definitions and set-up specific to Carleson's theorem
section setup

universe u

/-- A class stating that continuous functions have distances associated to every ball.
We use a separate type to conveniently index these functions. -/
class FunctionDistances (𝕜 : outParam Type*) (X : Type u) [NormedField 𝕜] [TopologicalSpace X] where
  /-- A type of continuous functions from `X` to `𝕜`. -/
  Θ : Type u
  /-- The coercion map from `Θ` to `C(X, 𝕜)`. -/
  coeΘ : Θ → C(X, 𝕜)
  /-- Injectivity of the coercion map from `Θ` to `C(X, 𝕜)`. -/
  coeΘ_injective {f g : Θ} (h : ∀ x, coeΘ f x = coeΘ g x) : f = g
  /-- For each `_x : X` and `_r : ℝ`, a `PseudoMetricSpace Θ`. -/
  metric : ∀ (_x : X) (_r : ℝ), PseudoMetricSpace Θ

export FunctionDistances (Θ coeΘ)

section FunctionDistances

variable {𝕜 X : Type*} {A : ℕ} [_root_.RCLike 𝕜] [PseudoMetricSpace X] [FunctionDistances 𝕜 X]

instance : Coe (Θ X) C(X, 𝕜) := ⟨FunctionDistances.coeΘ⟩
instance : FunLike (Θ X) X 𝕜 where
  coe := fun f ↦ (f : C(X, 𝕜))
  coe_injective' _ _ hfg := FunctionDistances.coeΘ_injective fun x ↦ congrFun hfg x

set_option linter.unusedVariables false in
/-- Class used to endow `Θ X` with a pseudometric space structure. -/
@[nolint unusedArguments]
def WithFunctionDistance (x : X) (r : ℝ) := Θ X

instance {x : X} {r : ℝ} [d : FunctionDistances 𝕜 X] :
    PseudoMetricSpace (WithFunctionDistance x r) := d.metric x r

end FunctionDistances

/-- The real-valued distance function on `WithFunctionDistance x r`. -/
notation3 "dist_{" x ", " r "}" => @dist (WithFunctionDistance x r) _
/-- The `ℝ≥0∞`-valued distance function on `WithFunctionDistance x r`. Preferred over `nndist`. -/
notation3 "edist_{" x ", " r "}" => @edist (WithFunctionDistance x r) _

variable {𝕜 X : Type*} {A : ℕ} [_root_.RCLike 𝕜] [PseudoMetricSpace X]

set_option linter.unusedVariables false in
/-- `s` can be covered by at most `N` balls with radius `r`. -/
@[mk_iff]
class inductive CoveredByBalls (s : Set X) (n : ℕ) (r : ℝ) : Prop where
  | mk (balls : Finset X)
    (card_balls : balls.card ≤ n)
    (union_balls : s ⊆ ⋃ x ∈ balls, ball x r) : CoveredByBalls s n r

variable (X) in
/-- Balls of radius `r` in `X` are covered by `n` balls of radius `r'` -/
def BallsCoverBalls (r r' : ℝ) (n : ℕ) : Prop := ∀ x : X, CoveredByBalls (ball x r) n r'

variable (X) in
/-- For all `r`, balls of radius `r` in `X` are covered by `n` balls of radius `a * r` -/
def AllBallsCoverBalls (a : ℝ) (n : ℕ) : Prop := ∀ r : ℝ, BallsCoverBalls X (a * r) r n

/-- A set `Θ` of (continuous) functions is compatible. `A` will usually be `2 ^ a`. -/
class CompatibleFunctions (𝕜 : outParam Type*) (X : Type u) (A : outParam ℕ)
  [RCLike 𝕜] [PseudoMetricSpace X] extends FunctionDistances 𝕜 X where
  eq_zero : ∃ o : X, ∀ f : Θ, coeΘ f o = 0
  /-- The distance is bounded below by the local oscillation. (1.1.4) -/
  localOscillation_le_cdist {x : X} {r : ℝ} {f g : Θ} :
    localOscillation (ball x r) (coeΘ f) (coeΘ g) ≤ ENNReal.ofReal (dist_{x, r} f g)
  /-- The distance is monotone in the ball. (1.1.6) -/
  cdist_mono {x₁ x₂ : X} {r₁ r₂ : ℝ} {f g : Θ}
    (h : ball x₁ r₁ ⊆ ball x₂ r₂) : dist_{x₁, r₁} f g ≤ dist_{x₂, r₂} f g
  /-- The distance of a ball with large radius is bounded above. (1.1.5) -/
  cdist_le {x₁ x₂ : X} {r : ℝ} {f g : Θ} (h : dist x₁ x₂ < 2 * r) :
    dist_{x₂, 2 * r} f g ≤ A * dist_{x₁, r} f g
  /-- The distance of a ball with large radius is bounded below. (1.1.7) -/
  le_cdist {x₁ x₂ : X} {r : ℝ} {f g : Θ} (h1 : ball x₁ r ⊆ ball x₂ (A * r)) :
    /-(h2 : A * r ≤ Metric.diam (univ : Set X))-/
    2 * dist_{x₁, r} f g ≤ dist_{x₂, A * r} f g
  /-- Every ball of radius `2R` can be covered by `A` balls of radius `R`. (1.1.8) -/
  allBallsCoverBalls {x : X} {r : ℝ} :
    AllBallsCoverBalls (WithFunctionDistance x r) 2 A

variable [DoublingMeasure X A]

variable (X) in
/-- Θ is τ-cancellative. `τ` will usually be `1 / a` -/
class IsCancellative (τ : ℝ) [CompatibleFunctions ℝ X A] : Prop where
  /- We register a definition with strong assumptions, which makes them easier to prove.
  However, `enorm_integral_exp_le` removes them for easier application. -/
  enorm_integral_exp_le' {x : X} {r : ℝ} {φ : X → ℂ} (hr : 0 < r) (h1 : iLipENorm φ x r ≠ ∞)
    (h2 : Function.support φ ⊆ ball x r) {f g : Θ X} :
    ‖∫ x, exp (I * (f x - g x)) * φ x‖ₑ ≤
    (A : ℝ≥0∞) * volume (ball x r) * iLipENorm φ x r * (1 + edist_{x, r} f g) ^ (- τ)

/-- `R_Q(θ, x)` defined in (1.1.17). -/
def upperRadius [FunctionDistances ℝ X] (Q : X → Θ X) (θ : Θ X) (x : X) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : dist_{x, r} θ (Q x) < 1), ENNReal.ofReal r

/-- The linearized maximally truncated nontangential Calderon–Zygmund operator `T_Q^θ`. -/
def linearizedNontangentialOperator [FunctionDistances ℝ X] (Q : X → Θ X) (θ : Θ X)
    (K : X → X → ℂ) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (R₂ : ℝ) (R₁ ∈ Ioo 0 R₂) (x' ∈ ball x R₁),
  ‖∫ y in EAnnulus.oo x' (ENNReal.ofReal R₁) (min (ENNReal.ofReal R₂) (upperRadius Q θ x')),
    K x' y * f y‖ₑ

/-- The maximally truncated nontangential Calderon–Zygmund operator `T_*`. -/
def nontangentialOperator (K : X → X → ℂ) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (R₂ : ℝ) (R₁ ∈ Ioo 0 R₂) (x' ∈ ball x R₁), ‖∫ y in Annulus.oo x' R₁ R₂, K x' y * f y‖ₑ

/-- The integrand in the (linearized) Carleson operator.
This is `G` in Lemma 3.0.1. -/
def carlesonOperatorIntegrand [FunctionDistances ℝ X] (K : X → X → ℂ)
    (θ : Θ X) (R₁ R₂ : ℝ) (f : X → ℂ) (x : X) : ℂ :=
  ∫ y in Annulus.oo x R₁ R₂, K x y * f y * exp (I * θ y)

/-- The linearized generalized Carleson operator `T_Q`, taking values in `ℝ≥0∞`.
Use `ENNReal.toReal` to get the corresponding real number. -/
def linearizedCarlesonOperator [FunctionDistances ℝ X] (Q : X → Θ X) (K : X → X → ℂ)
    (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (R₁ : ℝ) (R₂ : ℝ) (_ : 0 < R₁) (_ : R₁ < R₂), ‖carlesonOperatorIntegrand K (Q x) R₁ R₂ f x‖ₑ

/-- The generalized Carleson operator `T`, taking values in `ℝ≥0∞`.
Use `ENNReal.toReal` to get the corresponding real number. -/
def carlesonOperator [FunctionDistances ℝ X] (K : X → X → ℂ) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (θ : Θ X), linearizedCarlesonOperator (fun _ ↦ θ) K f x

end setup

/-- This is usually the value of the argument `A` in `DoublingMeasure`
and `CompatibleFunctions` -/
@[simp] abbrev defaultA (a : ℕ) : ℕ := 2 ^ a
/-- `defaultτ` is the inverse of `a`. -/
@[simp] def defaultτ (a : ℕ) : ℝ := a⁻¹

section Kernel

variable {X : Type*} {a : ℕ} {K : X → X → ℂ} [PseudoMetricSpace X] [MeasureSpace X]
open Function

/-- The constant used twice in the definition of the Calderon-Zygmund kernel. -/
@[simp] def C_K (a : ℝ) : ℝ≥0 := 2 ^ a ^ 3

/-- `K` is a one-sided Calderon-Zygmund kernel.
In the formalization `K x y` is defined everywhere, even for `x = y`. The assumptions on `K` show
that `K x x = 0`. -/
class IsOneSidedKernel (a : outParam ℕ) (K : X → X → ℂ) : Prop where
  measurable_K : Measurable (uncurry K)
  norm_K_le_vol_inv (x y : X) : ‖K x y‖ ≤ C_K a / Real.vol x y
  norm_K_sub_le {x y y' : X} (h : 2 * dist y y' ≤ dist x y) :
    ‖K x y - K x y'‖ ≤ (dist y y' / dist x y) ^ (a : ℝ)⁻¹ * (C_K a / Real.vol x y)

end Kernel

/-- Data common through most of chapters 2 through 7.
These contain the minimal axioms for `kernel-summand`'s proof.
This is used in Chapter 3 when we don't have all other fields from `ProofData`. -/
class KernelProofData {X : Type*} (a : outParam ℕ) (K : outParam (X → X → ℂ))
    [PseudoMetricSpace X] where
  d : DoublingMeasure X (defaultA a)
  four_le_a : 4 ≤ a
  cf : CompatibleFunctions ℝ X (defaultA a)
  hcz : IsOneSidedKernel a K

export KernelProofData (four_le_a)

attribute [implicit_reducible, instance] KernelProofData.d KernelProofData.cf

attribute [instance] KernelProofData.hcz

section Statements

/-- The main constant in the blueprint, driving all the construction, is `D = 2 ^ (100 * a ^ 2)`.
It turns out that the proof is robust, and works for other values of `100`, giving better constants
in the end. We will formalize it using a parameter `𝕔` (that we fix equal to `100` to follow
the blueprint) and having `D = 2 ^ (𝕔 * a ^ 2)`. We register two lemmas `seven_le_c` and
`c_le_100` and will never unfold `𝕔` from this point on. -/
irreducible_def 𝕔 : ℕ := 100

/-- The constant used in `MetricSpaceCarleson` and `LinearizedMetricCarleson`.
Has value `2 ^ (443 * a ^ 3) / (q - 1) ^ 6` in the blueprint. -/
def C1_0_2 (a : ℕ) (q : ℝ≥0) : ℝ≥0 := 2 ^ ((3 * 𝕔 + 18 + 5 * (𝕔 / 4)) * a ^ 3) / (q - 1) ^ 6

set_option linter.unusedVariables false

/-- A constant used on the boundedness of `T_Q^θ` and `T_*`. We generally assume
`HasBoundedStrongType (linearizedNontangentialOperator Q θ K · ·) 2 2 volume volume (C_Ts a)`
throughout this formalization. -/
def C_Ts (a : ℕ) : ℝ≥0 := 2 ^ a ^ 3

open Real in
/-- Theorem 1.0.1: Carleson's theorem asserting a.e. convergence of the partial Fourier sums for
continous functions.
For the proof, see `classical_carleson` in the file `Carleson.Classical.ClassicalCarleson`. -/
def ClassicalCarleson : Prop :=
  ∀ {f : ℝ → ℂ} (cont_f : Continuous f) (periodic_f : f.Periodic (2 * π)),
    ∀ᵐ x, Filter.Tendsto (partialFourierSum · f x) Filter.atTop (nhds (f x))

/-- Theorem 1.1.1.
For the proof, see `metric_carleson` in the file `Carleson.MetricCarleson.Main`. -/
def MetricSpaceCarleson : Prop :=
  ∀ {X : Type*} {a : ℕ} [MetricSpace X] {q q' : ℝ≥0} {F G : Set X} {K : X → X → ℂ}
    [KernelProofData a K] {f : X → ℂ} [IsCancellative X (defaultτ a)] (hq : q ∈ Ioc 1 2)
    (hqq' : q.HolderConjugate q') (mF : MeasurableSet F) (mG : MeasurableSet G)
    (mf : Measurable f) (nf : (‖f ·‖) ≤ F.indicator 1)
    (hT : HasBoundedStrongType (nontangentialOperator K · ·) 2 2 volume volume (C_Ts a)),
    ∫⁻ x in G, carlesonOperator K f x ≤ C1_0_2 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹

/-- Theorem 1.1.2.
For the proof, see `linearized_metric_carleson` in the file `Carleson.MetricCarleson.Linearized`. -/
def LinearizedMetricCarleson : Prop :=
  ∀ {X : Type*} {a : ℕ} [MetricSpace X] {q q' : ℝ≥0} {F G : Set X} {K : X → X → ℂ}
    [KernelProofData a K] {Q : SimpleFunc X (Θ X)} {f : X → ℂ} [IsCancellative X (defaultτ a)]
    (hq : q ∈ Ioc 1 2) (hqq' : q.HolderConjugate q') (mF : MeasurableSet F) (mG : MeasurableSet G)
    (mf : Measurable f) (nf : (‖f ·‖) ≤ F.indicator 1)
    (hT : ∀ θ : Θ X, HasBoundedStrongType (linearizedNontangentialOperator Q θ K · ·)
      2 2 volume volume (C_Ts a)),
    ∫⁻ x in G, linearizedCarlesonOperator Q K f x ≤
      C1_0_2 a q * volume G ^ (q' : ℝ)⁻¹ * volume F ^ (q : ℝ)⁻¹

end Statements
