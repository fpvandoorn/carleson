import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Topology.MetricSpace.Holder
open MeasureTheory Measure NNReal ENNReal Metric
noncomputable section

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

/- Mathlib is missing quasi metric spaces.
At some point we should generalize metric spaces to quasi metric spaces, but that takes some
refactoring in the mathematical library. -/

/-- A distance is regular, or `A`-Lipschitz. -/
class RegularDist (X : Type*) [MetricSpace X] (A : outParam ℝ≥0) : Prop where
  abs_dist_sub_dist_le : ∀ x y y' : X, |dist x y - dist x y'| ≤ A * dist y y'

/-- A space of homogenous type. -/
class IsSpaceOfHomogenousType (X : Type*) (A : outParam ℝ≥0) where
  metricSpace : MetricSpace X
  measureSpace : MeasureSpace X
  locallyCompactSpace : LocallyCompactSpace X
  completeSpace : LocallyCompactSpace X
  sigmaFinite : SigmaFinite (volume : Measure X) -- maybe?
  borelSpace : BorelSpace X
  volume_ball_le : ∀ (x : X) r, volume (ball x (2 * r)) ≤ A * volume (ball x r)

attribute [instance]
  IsSpaceOfHomogenousType.metricSpace
  IsSpaceOfHomogenousType.measureSpace
  IsSpaceOfHomogenousType.locallyCompactSpace
  IsSpaceOfHomogenousType.completeSpace
  IsSpaceOfHomogenousType.borelSpace
  IsSpaceOfHomogenousType.sigmaFinite

variable {X : Type*} {A : ℝ≥0} [IsSpaceOfHomogenousType X A]
export IsSpaceOfHomogenousType (volume_ball_le)


lemma test (x : X) (r : ℝ) : volume (ball x (4 * r)) ≤ A ^ 2 * volume (ball x r) := by
  calc volume (ball x (4 * r))
      = volume (ball x (2 * (2 * r))) := by ring_nf
    _ ≤ A * volume (ball x (2 * r)) := by apply volume_ball_le
    _ ≤ A * (A * volume (ball x r)) := by gcongr; apply volume_ball_le
    _ = A ^ 2 * volume (ball x r) := by ring_nf; norm_cast; ring_nf

example (x : X) (r : ℝ) : ∃ S : Finset X, ball x (2 * r) ⊆ ⋃ y ∈ S, ball y r :=
  sorry

section localOscillation

/-- The local oscillation of two functions. -/
def localOscillation (E : Set X) (f g : C(X, ℂ)) : ℝ :=
  ⨆ z : E × E, ‖f z.1 - g z.1 - f z.2 + g z.2‖

variable {E : Set X} {f g : C(X, ℂ)}

lemma localOscillation_nonneg : 0 ≤ localOscillation E f g := sorry

@[simps]
def nnlocalOscillation (E : Set X) (f g : C(X, ℂ)) : ℝ≥0 :=
  ⟨localOscillation E f g, localOscillation_nonneg⟩

def localOscillationBall (E : Set X) (f : C(X, ℂ)) (r : ℝ) : Set C(X, ℂ) :=
  { g : C(X, ℂ) | localOscillation E f g < r }

end localOscillation


/-- `s` can be covered by at most `N` balls with radius `r`. -/
class CoverByBalls {α : Type*} (d : α → α → ℝ) (s : Set α) (N : ℕ) (r : ℝ) : Type _ where
  balls : Set α
  balls_finite : Set.Finite balls
  card_balls : Nat.card balls ≤ N
  union_balls : ∀ x ∈ s, ∃ z ∈ balls, d x z < r

/- Good first project: state and prove basic properties about `CanBeCoveredByBalls` -/

/- mathlib is missing Hölder spaces.
Todo:
* Define Hölder spaces
* Define the norm in Hölder spaces
* Show that Hölder spaces are homogenous -/

/-- A set `𝓠` of (continuous) functions is `(N, M, ν, γ)`-moderate. -/
class IsModerate (𝓠 : Set C(X, ℂ)) (N M : ℝ) (ν : ℝ≥0) (γ : ℝ) : Prop where
  -- should `h` be strict subset?
  localOscillation_le_of_subset {x₁ x₂ : X} {r₁ r₂ : ℝ} {f g : C(X, ℂ)} (hf : f ∈ 𝓠) (hg : g ∈ 𝓠)
   (h1 : ball x₁ r₁ ⊆ ball x₂ r₂) (h2 : r ≤ EMetric.diam (univ : Set X)) :
    localOscillation (ball x₁ r₁) f g ≤ A * (r₁ / r₂) ^ (1 / N) * localOscillation (ball x₂ r₂) f g
  localOscillation_le_of_superset {x₁ x₂ : X} {r₁ r₂ : ℝ} {f g : C(X, ℂ)} (hf : f ∈ 𝓠) (hg : g ∈ 𝓠)
   (h1 : ball x₁ r₁ ⊆ ball x₂ r₂) (h2 : r ≤ EMetric.diam (univ : Set X)) :
    localOscillation (ball x₂ r₂) f g ≤ A * (r₂ / r₁) ^ N * localOscillation (ball x₁ r₁) f g
  coverByBalls {x : X} {r Λ : ℝ} (hΛ : Λ > 1) (f : C(X, ℂ)) :
    Nonempty <| CoverByBalls (localOscillation (ball x r)) (localOscillationBall (ball x r) f Λ)
      ⌊A * Λ ^ M⌋₊ 1
  norm_integral_le {x : X} {r : ℝ≥0} {C : ℝ≥0} {ψ : X → ℂ} (hψ : HolderWith C ν ψ)
    [Norm (X → ℂ)] -- todo: replace this with the actual Hölder norm
    (h2ψ : tsupport ψ ⊆ ball x r) {f g : C(X, ℂ)} (hf : f ∈ 𝓠) (hg : g ∈ 𝓠) :
    ‖∫ x in ball x r, Complex.exp (i * (f x - g x)) * ψ x‖ ≤
    A * (volume (ball x r)).toReal * ‖ψ‖ * (1 + localOscillation (ball x r) f g) ^ (-γ) * r ^ (ν : ℝ)


/-- The "volume function". Note that we will need to assume
`IsFiniteMeasureOnCompacts` and `ProperSpace` to actually know that this volume is finite. -/
def ENNReal.vol {X : Type*} [MetricSpace X] [MeasureSpace X] (x y : X) : ℝ :=
  ENNReal.toReal (volume (ball x (dist x y)))

/-- `K` is a `τ`-Calderon-Zygmund kernel -/
class IsCZKernel (τ : ℝ) (K : X → X → ℂ) : Prop where
  nnnorm_le_vol_inv (x y : X) : ‖K x y‖ ≤ (vol x y)⁻¹
  h {x x' y y' : X} (h : A * dist x x' ≤ dist x y) :
    ‖K x y - K x y'‖ ≤ (dist y y' / dist x y) ^ τ * (vol x y)⁻¹

set_option linter.unusedVariables false in
/-- The associated nontangential Calderon Zygmund operator -/
def ANCZOperator (K : X → X → ℂ) (C : ℝ) (f : X → ℂ) (x : X) : ℝ :=
  ⨆ (r : ℝ) (R : ℝ) (h1 : r < R) (x' : X) (h2 : dist x x' ≤ C * r),
  ‖∫ y in {y | r < dist x' y ∧ dist x' y < R}, K x' y * f y‖

/- TODO: state theorem 1.2. -/

set_option linter.unusedVariables false in
variable (X) in
class SmallBoundaryProperty (η : ℝ) : Prop where
  volume_diff_le : ∃ (C : ℝ≥0) (hC : C > 0), ∀ (x : X) r (δ : ℝ≥0), 0 < r → 0 < δ → δ < 1 →
    volume (ball x ((1 + δ) * r) \ ball x ((1 - δ) * r)) ≤ C * δ ^ η * volume (ball x r)


#print IsCZKernel

/- TODO: state theorem 1.3 and needed definitions. -/
/- TODO: state theorem 1.4 and needed definitions. -/
