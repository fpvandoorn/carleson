import Carleson.DoublingMeasure

open MeasureTheory Measure NNReal Metric Complex Set TopologicalSpace Bornology
open scoped ENNReal
noncomputable section

-- todo: rename and protect `Real.RCLike`

/-! Miscellaneous definitions.
These are mostly the definitions used to state the metric Carleson theorem.
We should move them to separate files once we start proving things about them. -/

variable {𝕜 X : Type*} {A : ℝ} [_root_.RCLike 𝕜] [PseudoMetricSpace X] [DoublingMeasure X A]

section localOscillation

/-- The local oscillation of two functions w.r.t. a set `E`. This is `d_E` in the blueprint. -/
def localOscillation (E : Set X) (f g : C(X, 𝕜)) : ℝ :=
  ⨆ z ∈ E ×ˢ E, ‖f z.1 - g z.1 - f z.2 + g z.2‖

example (E : Set X) (hE : IsBounded E) (f : C(X, ℝ)) :
    BddAbove (range fun z : E ↦ f z) := by
  have : IsCompact (closure E) := IsBounded.isCompact_closure hE
  sorry

lemma bddAbove_localOscillation (E : Set X) [Fact (IsBounded E)] (f g : C(X, 𝕜)) :
    BddAbove ((fun z : X × X ↦ ‖f z.1 - g z.1 - f z.2 + g z.2‖) '' E ×ˢ E) := sorry

--old
set_option linter.unusedVariables false in
variable (𝕜) in
/-- A type synonym of `C(X, 𝕜)` that uses the local oscillation w.r.t. `E` as the metric. -/
def withLocalOscillation (E : Set X) [Fact (IsBounded E)] : Type _ := C(X, 𝕜)

--old
instance withLocalOscillation.funLike (E : Set X) [Fact (IsBounded E)] :
    FunLike (withLocalOscillation 𝕜 E) X 𝕜 :=
  ContinuousMap.funLike

--old
instance withLocalOscillation.toContinuousMapClass (E : Set X) [Fact (IsBounded E)] :
    ContinuousMapClass (withLocalOscillation 𝕜 E) X 𝕜 :=
  ContinuousMap.toContinuousMapClass

--old
/-- The local oscillation on a set `E` gives rise to a pseudo-metric-space structure
  on the continuous functions `X → ℝ`. -/
instance homogeneousPseudoMetric (E : Set X) [Fact (IsBounded E)] :
    PseudoMetricSpace (withLocalOscillation 𝕜 E) where
  dist := localOscillation E
  dist_self := by simp [localOscillation]
  dist_comm f g := by simp only [localOscillation]; congr with z; rw [← norm_neg]; ring_nf
  dist_triangle f₁ f₂ f₃ := by
    rcases isEmpty_or_nonempty X with hX|hX
    · sorry
    apply ciSup_le (fun z ↦ ?_)
    trans ‖f₁ z.1 - f₂ z.1 - f₁ z.2 + f₂ z.2‖ + ‖f₂ z.1 - f₃ z.1 - f₂ z.2 + f₃ z.2‖
    · sorry
    · sorry --gcongr <;> apply le_ciSup (bddAbove_localOscillation _ _ _) z
  edist_dist := fun x y => by exact ENNReal.coe_nnreal_eq _

variable {E : Set X} {f g : C(X, 𝕜)}

--old
def localOscillationBall (E : Set X) (f : C(X, 𝕜)) (r : ℝ) :
    Set C(X, 𝕜) :=
  { g : C(X, 𝕜) | localOscillation E f g < r }

end localOscillation

lemma fact_isCompact_ball (x : X) (r : ℝ) : Fact (IsBounded (ball x r)) :=
  ⟨isBounded_ball⟩
attribute [local instance] fact_isCompact_ball

/-- A class stating that continuous functions have distances associated to every ball. -/
class FunctionDistances [DoublingMeasure X A] (Θ : Set C(X, 𝕜)) where
  /-- The distance of a compatible family. -/
  cdist (x : X) (r : ℝ) (f g : C(X, 𝕜)) : ℝ
  cdist_comm {x : X} {r : ℝ} {f g : C(X, 𝕜)} : cdist x r f g = cdist x r g f
  cdist_self {x : X} {r : ℝ} {f : C(X, 𝕜)} : cdist x r f f = 0
  cdist_triangle {x : X} {r : ℝ} {f g h : C(X, 𝕜)} : cdist x r f h ≤ cdist x r f g + cdist x r g h

set_option linter.unusedVariables false in
def WithFunctionDistance (Θ : Set C(X, 𝕜)) (x : X) (r : ℝ) := C(X, 𝕜)

variable [DoublingMeasure X A] {Θ : Set C(X, 𝕜)} {x : X} {r : ℝ}

def toWithFunctionDistance : C(X, 𝕜) ≃ WithFunctionDistance Θ x r :=
  .refl _

instance : FunLike (WithFunctionDistance Θ x r) X 𝕜 := ContinuousMap.funLike
instance : ContinuousMapClass (WithFunctionDistance Θ x r) X 𝕜 :=
  ContinuousMap.toContinuousMapClass

instance [FunctionDistances Θ] : PseudoMetricSpace (WithFunctionDistance Θ x r) where
  dist := FunctionDistances.cdist A Θ x r
  dist_self f := FunctionDistances.cdist_self
  dist_comm f g := FunctionDistances.cdist_comm
  dist_triangle f g h := FunctionDistances.cdist_triangle
  edist_dist f g := rfl

notation3 "dist_{" Θ "; " x " ," r "}" => @dist (WithFunctionDistance Θ x r) _
notation3 "ball_{" Θ "; " x " ," r "}" => @ball (WithFunctionDistance Θ x r) _

/-- A set `Θ` of (continuous) functions is compatible. `A` will usually be `2 ^ a`. -/
class IsCompatible [DoublingMeasure X A] (Θ : Set C(X, 𝕜)) extends FunctionDistances Θ where
  eq_zero : ∃ o : X, ∀ (f : C(X, 𝕜)) (_hf : f ∈ Θ), f o = 0
  /-- The distance is bounded below by the local oscillation. -/
  localOscillation_le_cdist {x : X} {r : ℝ} {f g : C(X, 𝕜)} (hf : f ∈ Θ) (hg : g ∈ Θ) :
    localOscillation (ball x r) f g ≤ cdist x r f g
  /-- The distance is monotone in the ball. -/
  cdist_mono {x₁ x₂ : X} {r₁ r₂ : ℝ} {f g : C(X, 𝕜)} (hf : f ∈ Θ) (hg : g ∈ Θ)
    (h : ball x₁ r₁ ⊆ ball x₂ r₂) : cdist x₁ r₁ f g ≤ cdist x₂ r₂ f g
  /-- The distance of a ball with large radius is bounded above. -/
  cdist_le {x₁ x₂ : X} {r : ℝ} {f g : C(X, 𝕜)} (hf : f ∈ Θ) (hg : g ∈ Θ)
    (h : dist x₁ x₂ < 2 * r) : cdist x₂ (2 * r) f g ≤ A * cdist x₁ r f g
  /-- The distance of a ball with large radius is bounded below. -/
  le_cdist {x₁ x₂ : X} {r : ℝ} {f g : C(X, 𝕜)} (hf : f ∈ Θ) (hg : g ∈ Θ)
    (h1 : ball x₁ r ⊆ ball x₂ (A * r)) /-(h2 : A * r ≤ Metric.diam (univ : Set X))-/ :
    2 * cdist x₁ r f g ≤ cdist x₂ (A * r) f g
  /-- The distance of a ball with large radius is bounded below. -/
  coveredByBalls {x : X} {r R : ℝ} {f : WithFunctionDistance Θ x r} (hf : f ∈ Θ) :
    CoveredByBalls (ball f (2 * R) ∩ Θ) ⌊A⌋₊ R

export IsCompatible (localOscillation_le_cdist cdist_mono cdist_le le_cdist)

variable (Θ) in
/-- The point `o` in the blueprint -/
def cancelPt [IsCompatible Θ] : X := IsCompatible.eq_zero A (Θ := Θ) |>.choose
def cancelPt_eq_zero [IsCompatible Θ] {f : C(X, 𝕜)} (hf : f ∈ Θ) : f (cancelPt Θ) = 0 :=
  IsCompatible.eq_zero A (Θ := Θ) |>.choose_spec f hf

lemma IsCompatible.IsSeparable [IsCompatible Θ] : IsSeparable Θ :=
  sorry

set_option linter.unusedVariables false in
/-- The inhomogeneous Lipschitz norm on a ball. -/
def iLipNorm {𝕜} [NormedField 𝕜] (ϕ : X → 𝕜) (x₀ : X) (R : ℝ) : ℝ :=
  (⨆ x ∈ ball x₀ R, ‖ϕ x‖) + R * ⨆ (x : X) (y : X) (h : x ≠ y), ‖ϕ x - ϕ y‖ / dist x y

/-- Θ is τ-cancellative. `τ` will usually be `1 / a` -/
class IsCancellative (τ : ℝ) (Θ : Set C(X, ℂ)) [FunctionDistances Θ] : Prop where
  norm_integral_exp_le {x : X} {r : ℝ} {ϕ : X → ℂ} {K : ℝ≥0} (h1 : LipschitzWith K ϕ)
    (h2 : tsupport ϕ ⊆ ball x r) {f g : C(X, ℂ)} (hf : f ∈ Θ) (hg : g ∈ Θ) :
    ‖∫ x in ball x r, exp (I * (f x - g x)) * ϕ x‖ ≤
    A * volume.real (ball x r) * iLipNorm ϕ x r * (1 + dist_{Θ; x, r} f g) ^ (- τ)

export IsCancellative (norm_integral_exp_le)

/-- The "volume function" `V`. Note that we will need to assume
`IsFiniteMeasureOnCompacts` and `ProperSpace` to actually know that this volume is finite. -/
def Real.vol {X : Type*} [PseudoMetricSpace X] [MeasureSpace X] (x y : X) : ℝ :=
  volume.real (ball x (dist x y))

open Real (vol)
open Function

/-- `K` is a one-sided Calderon-Zygmund kernel
In the formalization `K x y` is defined everywhere, even for `x = y`. The assumptions on `K` show
that `K x x = 0`. -/
class IsCZKernel (a : ℝ) (K : X → X → ℂ) : Prop where
  measurable : Measurable (uncurry K)
  norm_le_vol_inv (x y : X) : ‖K x y‖ ≤ 2 ^ a ^ 3 / vol x y
  norm_sub_le {x y y' : X} (h : 2 /-* A-/ * dist y y' ≤ dist x y) :
    ‖K x y - K x y'‖ ≤ (dist y y' / dist x y) ^ a⁻¹ * (2 ^ a ^ 3 / vol x y)
  measurable_right (y : X) : Measurable (K · y)

-- to show: K is locally bounded and hence integrable outside the diagonal

/-- In Mathlib we only have the operator norm for continuous linear maps,
and `T_*` is not linear.
Here is the norm for an arbitrary map `T` between normed spaces
(the infimum is defined to be 0 if the operator is not bounded). -/
def operatorNorm {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] (T : E → F) : ℝ :=
  sInf { c | 0 ≤ c ∧ ∀ x, ‖T x‖ ≤ c * ‖x‖ }

/- For sublinear maps: todo real interpolation.
Sublinear, L^1-bounded and L^2-bounded maps are also L^p bounded for p between 1 and 2.
This is a special case of the real interpolation spaces.
Reference: https://arxiv.org/abs/math/9910039
Lemma 3.6 - Lemma 3.9
-/

/-- This can be useful to say that `‖T‖ ≤ c`. -/
def NormBoundedBy {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] (T : E → F) (c : ℝ) :
    Prop :=
  ∀ x, ‖T x‖ ≤ c * ‖x‖

set_option linter.unusedVariables false in
/-- The associated nontangential Calderon Zygmund operator -/
def ANCZOperator (K : X → X → ℂ) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (R₁ : ℝ) (R₂ : ℝ) (h1 : R₁ < R₂) (x' : X) (h2 : dist x x' ≤ R₁),
  ‖∫ y in {y | dist x' y ∈ Ioo R₁ R₂}, K x' y * f y‖₊

/-- The associated nontangential Calderon Zygmund operator, viewed as a map `L^p → L^p`.
Todo: is `T_*f` indeed in L^p if `f` is? Needed at least for `p = 2`. -/
def ANCZOperatorLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (K : X → X → ℂ) (f : Lp ℂ p (volume : Measure X)) :
    Lp ℝ p (volume : Measure X) :=
  Memℒp.toLp (ANCZOperator K (f : X → ℂ) · |>.toReal) sorry

-- /-- The generalized Carleson operator `T`, using real suprema -/
-- def Real.CarlesonOperator (K : X → X → ℂ) (Θ : Set C(X, ℂ)) (f : X → ℂ) (x : X) : ℝ :=
--   ⨆ (Q ∈ Θ) (R₁ : ℝ) (R₂ : ℝ) (_ : 0 < R₁) (_ : R₁ < R₂),
--   ‖∫ y in {y | dist x y ∈ Ioo R₁ R₂}, K x y * f y * Complex.exp (I * Q y)‖

/-- The generalized Carleson operator `T`, ℝ≥0∞ version -/
--TODO: remove the last two suprema?
def CarlesonOperator (K : X → X → ℂ) (Θ : Set C(X, ℂ)) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (Q ∈ Θ) (R₁ : ℝ) (R₂ : ℝ) (_ : 0 < R₁) (_ : R₁ < R₂),
  ↑‖∫ y in {y | dist x y ∈ Ioo R₁ R₂}, K x y * f y * exp (I * Q y)‖₊
