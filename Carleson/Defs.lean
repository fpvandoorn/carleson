import Carleson.ToMathlib.DoublingMeasure
import Carleson.ToMathlib.WeakType
import Carleson.ToMathlib.Data.ENNReal
import Carleson.ToMathlib.Misc
import Carleson.ToMathlib.Annulus
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.Topology.Algebra.Support

open MeasureTheory Measure Metric Complex Set TopologicalSpace Bornology Function ENNReal
open scoped NNReal
noncomputable section

-- todo: rename and protect `Real.RCLike`

/-! Miscellaneous definitions.
These are mostly the definitions used to state the metric Carleson theorem.
We should move them to separate files once we start proving things about them. -/

section DoublingMeasure
universe u

variable {𝕜 X : Type*} {A : ℕ} [_root_.RCLike 𝕜] [PseudoMetricSpace X]

section localOscillation

/-- The local oscillation of two functions w.r.t. a set `E`. This is `d_E` in the blueprint. -/
def localOscillation (E : Set X) (f g : C(X, 𝕜)) : ℝ≥0∞ :=
  ⨆ z ∈ E ×ˢ E, ENNReal.ofReal ‖f z.1 - g z.1 - f z.2 + g z.2‖

-- example (E : Set X) (hE : IsBounded E) (f : C(X, ℝ)) :
--     BddAbove (range fun z : E ↦ f z) := by
--   have : IsCompact (closure E) := IsBounded.isCompact_closure hE
--   sorry

-- lemma bddAbove_localOscillation (E : Set X) [Fact (IsBounded E)] (f g : C(X, 𝕜)) :
--     BddAbove ((fun z : X × X ↦ ‖f z.1 - g z.1 - f z.2 + g z.2‖) '' E ×ˢ E) := sorry

variable {E : Set X} {f g : C(X, 𝕜)}

--old
/-- A ball w.r.t. the distance `localOscillation` -/
def localOscillationBall (E : Set X) (f : C(X, 𝕜)) (r : ℝ) :
    Set C(X, 𝕜) :=
  { g : C(X, 𝕜) | localOscillation E f g < ENNReal.ofReal r }

end localOscillation

lemma fact_isCompact_ball (x : X) (r : ℝ) : Fact (IsBounded (ball x r)) :=
  ⟨isBounded_ball⟩
attribute [local instance] fact_isCompact_ball

/-- A class stating that continuous functions have distances associated to every ball.
We use a separate type to conveniently index these functions. -/
class FunctionDistances (𝕜 : outParam Type*) (X : Type u)
    [NormedField 𝕜] [TopologicalSpace X] where
  Θ : Type u
  coeΘ : Θ → C(X, 𝕜)
  coeΘ_injective {f g : Θ} (h : ∀ x, coeΘ f x = coeΘ g x) : f = g
  metric : ∀ (_x : X) (_r : ℝ), PseudoMetricSpace Θ

export FunctionDistances (Θ coeΘ)

section FunctionDistances
variable [FunctionDistances 𝕜 X]

instance : Coe (Θ X) C(X, 𝕜) := ⟨FunctionDistances.coeΘ⟩
instance : FunLike (Θ X) X 𝕜 where
  coe := fun f ↦ (f : C(X, 𝕜))
  coe_injective' _ _ hfg := FunctionDistances.coeΘ_injective fun x ↦ congrFun hfg x
instance : ContinuousMapClass (Θ X) X 𝕜 := ⟨fun f ↦ (f : C(X, 𝕜)).2⟩

set_option linter.unusedVariables false in
@[nolint unusedArguments]
def WithFunctionDistance (x : X) (r : ℝ) := Θ X

variable {x : X} {r : ℝ}

def toWithFunctionDistance [FunctionDistances 𝕜 X] : Θ X ≃ WithFunctionDistance x r :=
  .refl _

-- instance : FunLike (WithFunctionDistance Θ x r) X 𝕜 := ContinuousMap.funLike
-- instance : ContinuousMapClass (WithFunctionDistance Θ x r) X 𝕜 :=
--   ContinuousMap.toContinuousMapClass

instance [d : FunctionDistances 𝕜 X] : PseudoMetricSpace (WithFunctionDistance x r) :=
  d.metric x r

end FunctionDistances

notation3 "dist_{" x " ," r "}" => @dist (WithFunctionDistance x r) _
/-- preferably use `edist` -/
notation3 "nndist_{" x " ," r "}" => @nndist (WithFunctionDistance x r) _
notation3 "edist_{" x " ," r "}" => @edist (WithFunctionDistance x r) _
notation3 "ball_{" x " ," r "}" => @ball (WithFunctionDistance x r) _ in

/-- A set `Θ` of (continuous) functions is compatible. `A` will usually be `2 ^ a`. -/
class CompatibleFunctions (𝕜 : outParam Type*) (X : Type u) (A : outParam ℕ)
  [RCLike 𝕜] [PseudoMetricSpace X] extends FunctionDistances 𝕜 X where
  eq_zero : ∃ o : X, ∀ f : Θ, coeΘ f o = 0
  /-- The distance is bounded below by the local oscillation. (1.0.7) -/
  localOscillation_le_cdist {x : X} {r : ℝ} {f g : Θ} :
    localOscillation (ball x r) (coeΘ f) (coeΘ g) ≤ ENNReal.ofReal (dist_{x, r} f g)
  /-- The distance is monotone in the ball. (1.0.9) -/
  cdist_mono {x₁ x₂ : X} {r₁ r₂ : ℝ} {f g : Θ}
    (h : ball x₁ r₁ ⊆ ball x₂ r₂) : dist_{x₁, r₁} f g ≤ dist_{x₂, r₂} f g
  /-- The distance of a ball with large radius is bounded above. (1.0.8) -/
  cdist_le {x₁ x₂ : X} {r : ℝ} {f g : Θ} (h : dist x₁ x₂ < 2 * r) :
    dist_{x₂, 2 * r} f g ≤ A * dist_{x₁, r} f g
  /-- The distance of a ball with large radius is bounded below. (1.0.10) -/
  le_cdist {x₁ x₂ : X} {r : ℝ} {f g : Θ} (h1 : ball x₁ r ⊆ ball x₂ (A * r)) :
    /-(h2 : A * r ≤ Metric.diam (univ : Set X))-/
    2 * dist_{x₁, r} f g ≤ dist_{x₂, A * r} f g
  /-- Every ball of radius `2R` can be covered by `A` balls of radius `R`. (1.0.11) -/
  allBallsCoverBalls {x : X} {r : ℝ} :
    AllBallsCoverBalls (WithFunctionDistance x r) 2 A

instance nonempty_Space [CompatibleFunctions 𝕜 X A] : Nonempty X := by
  obtain ⟨x,_⟩ := ‹CompatibleFunctions 𝕜 X A›.eq_zero
  use x

instance inhabited_Space [CompatibleFunctions 𝕜 X A] : Inhabited X :=
  ⟨nonempty_Space.some⟩

lemma le_localOscillation [CompatibleFunctions 𝕜 X A] (x : X) (r : ℝ) (f g : Θ X) {y z : X}
    (hy : y ∈ ball x r) (hz : z ∈ ball x r) : ‖coeΘ f y - coeΘ g y - coeΘ f z + coeΘ g z‖ ≤
    ENNReal.toReal (localOscillation (ball x r) (coeΘ f) (coeΘ g)) := by
  rw [(ENNReal.toReal_ofReal (norm_nonneg _)).symm]
  let f (z) := ⨆ (_ : z ∈ ball x r ×ˢ ball x r), ENNReal.ofReal ‖f z.1 - g z.1 - f z.2 + g z.2‖
  apply ENNReal.toReal_mono
  · exact lt_of_le_of_lt CompatibleFunctions.localOscillation_le_cdist ENNReal.ofReal_lt_top |>.ne
  · exact le_of_eq_of_le (Eq.symm (iSup_pos ⟨hy, hz⟩)) (le_iSup f ⟨y, z⟩)

lemma oscillation_le_cdist [CompatibleFunctions 𝕜 X A] (x : X) (r : ℝ) (f g : Θ X) {y z : X}
    (hy : y ∈ ball x r) (hz : z ∈ ball x r) :
    ‖coeΘ f y - coeΘ g y - coeΘ f z + coeΘ g z‖ ≤ dist_{x, r} f g := by
  apply le_trans <| le_localOscillation x r f g hy hz
  rw [← ENNReal.toReal_ofReal dist_nonneg]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top CompatibleFunctions.localOscillation_le_cdist

export CompatibleFunctions (localOscillation_le_cdist cdist_mono cdist_le le_cdist)

lemma dist_congr [FunctionDistances 𝕜 X] {x₁ x₂ : X} {r₁ r₂ : ℝ} {f g : Θ X}
    (e₁ : x₁ = x₂) (e₂ : r₁ = r₂) : dist_{x₁, r₁} f g = dist_{x₂, r₂} f g := by congr

variable (X) in
/-- The point `o` in the blueprint -/
def cancelPt [CompatibleFunctions 𝕜 X A] : X :=
  CompatibleFunctions.eq_zero (𝕜 := 𝕜) |>.choose
lemma cancelPt_eq_zero [CompatibleFunctions 𝕜 X A] {f : Θ X} : f (cancelPt X) = 0 :=
  CompatibleFunctions.eq_zero (𝕜 := 𝕜) |>.choose_spec f

-- not sure if needed
-- lemma CompatibleFunctions.IsSeparable [CompatibleFunctions 𝕜 X A] :
--   IsSeparable (range (coeΘ (X := X))) :=
--   sorry

/-- The inhomogeneous Lipschitz norm on a ball. -/
def iLipENorm {𝕜} [NormedField 𝕜] (ϕ : X → 𝕜) (x₀ : X) (R : ℝ) : ℝ≥0∞ :=
  (⨆ x ∈ ball x₀ R, ‖ϕ x‖ₑ) +
  ENNReal.ofReal R * ⨆ (x ∈ ball x₀ R) (y ∈ ball x₀ R) (_ : x ≠ y), ‖ϕ x - ϕ y‖ₑ / edist x y

def iLipNNNorm {𝕜} [NormedField 𝕜] (ϕ : X → 𝕜) (x₀ : X) (R : ℝ) : ℝ≥0 :=
  (iLipENorm ϕ x₀ R).toNNReal

variable [hXA : DoublingMeasure X A]

variable (X) in
/-- Θ is τ-cancellative. `τ` will usually be `1 / a` -/
class IsCancellative (τ : ℝ) [CompatibleFunctions ℝ X A] : Prop where
  /- We register a definition with strong assumptions, which makes them easier to prove.
  However, `enorm_integral_exp_le` removes them for easier application. -/
  enorm_integral_exp_le' {x : X} {r : ℝ} {ϕ : X → ℂ} (hr : 0 < r) (h1 : iLipENorm ϕ x r ≠ ∞)
    (h2 : support ϕ ⊆ ball x r) {f g : Θ X} :
    ‖∫ x, exp (I * (f x - g x)) * ϕ x‖ₑ ≤
    (A : ℝ≥0∞) * volume (ball x r) * iLipENorm ϕ x r * (1 + edist_{x, r} f g) ^ (- τ)

lemma enorm_integral_exp_le [CompatibleFunctions ℝ X A] {τ : ℝ} [IsCancellative X τ]
    {x : X} {r : ℝ} {ϕ : X → ℂ} (h2 : support ϕ ⊆ ball x r) {f g : Θ X} :
    ‖∫ x, exp (I * (f x - g x)) * ϕ x‖ₑ ≤
    (A : ℝ≥0∞) * volume (ball x r) * iLipENorm ϕ x r * (1 + edist_{x, r} f g) ^ (- τ) := by
  rcases le_or_gt r 0 with hr | hr
  · simp only [ball_eq_empty.2 hr, subset_empty_iff, support_eq_empty_iff] at h2
    simp [h2]
  rcases eq_or_ne A 0 with rfl | hA
  · have : (volume : Measure X) = 0 := by
      have := hXA.toIsDoubling
      simp at this
      apply eq_zero_of_isDoubling_zero
    simp [this]
  rcases eq_or_ne (iLipENorm ϕ x r) ∞ with h1 | h1
  · apply le_top.trans_eq
    symm
    simp [h1, ENNReal.mul_eq_top, edist_ne_top, hA, (measure_ball_pos volume x hr).ne']
  exact IsCancellative.enorm_integral_exp_le' hr h1 h2

/-- Constructor of `IsCancellative` in terms of real norms instead of extended reals. -/
lemma isCancellative_of_norm_integral_exp_le (τ : ℝ) [CompatibleFunctions ℝ X A]
    (h : ∀ {x : X} {r : ℝ} {ϕ : X → ℂ} (_hr : 0 < r) (_h1 : iLipENorm ϕ x r ≠ ∞)
    (_h2 : support ϕ ⊆ ball x r) {f g : Θ X},
      ‖∫ x in ball x r, exp (I * (f x - g x)) * ϕ x‖ ≤
      A * volume.real (ball x r) * iLipNNNorm ϕ x r * (1 + dist_{x, r} f g) ^ (- τ)) :
    IsCancellative X τ := by
  constructor
  intro x r ϕ hr h1 h2 f g
  convert ENNReal.ofReal_le_ofReal (h (x := x) (r := r) (ϕ := ϕ) hr h1 h2 (f := f) (g := g))
  · rw [ofReal_norm_eq_enorm]
    congr 1
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ ?_)]
    have : ϕ y = 0 := by
      apply notMem_support.1
      contrapose! hy
      exact h2 hy
    simp [this]
  · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity)]
    congr
    · simp
    · simp only [Measure.real, ofReal_toReal measure_ball_ne_top]
    · simp [iLipNNNorm, coe_toNNReal h1]
    · rw [← ENNReal.ofReal_rpow_of_pos (by positivity)]
      congr
      rw [ENNReal.ofReal_add zero_le_one dist_nonneg]
      simp [edist_dist]

/-- The "volume function" `V`. Preferably use `vol` instead. -/
protected def Real.vol {X : Type*} [PseudoMetricSpace X] [MeasureSpace X] (x y : X) : ℝ :=
  volume.real (ball x (dist x y))

/-- The "volume function" `V`. We will need to assume
`IsFiniteMeasureOnCompacts` and `ProperSpace` to actually know that this volume is finite. -/
def vol {X : Type*} [PseudoMetricSpace X] [MeasureSpace X] (x y : X) : ℝ≥0∞ :=
  volume (ball x (dist x y))

@[fun_prop]
lemma measurable_vol {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasureSpace X] [OpensMeasurableSpace X] [SFinite (volume : Measure X)] :
    Measurable (uncurry vol : X × X → ℝ≥0∞) := by
  let f : X × X → X × ℝ := fun (x, y) ↦ (x, dist x y)
  let g : X × ℝ → ℝ≥0∞ := fun (x, a) ↦ volume (ball x a)
  apply Measurable.comp (f := f) (g := g)
  · apply measurable_measure_ball
  · fun_prop

lemma Real.vol_def {X : Type*} [PseudoMetricSpace X] [MeasureSpace X] {x y : X} :
  Real.vol x y = (vol x y).toReal := rfl

lemma ofReal_vol {X : Type*} [PseudoMetricSpace X] [MeasureSpace X] [ProperSpace X]
  [IsFiniteMeasureOnCompacts (volume : Measure X)] {x y : X} :
    ENNReal.ofReal (Real.vol x y) = vol x y := by
  simp_rw [Real.vol_def, ENNReal.ofReal_toReal_eq_iff, vol]
  apply measure_ball_ne_top

-- /-- In Mathlib we only have the operator norm for continuous linear maps,
-- and `T_*` is not linear.
-- Here is the norm for an arbitrary map `T` between normed spaces
-- (the infimum is defined to be 0 if the operator is not bounded). -/
-- def operatorNorm {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] (T : E → F) : ℝ :=
--   sInf { c | 0 ≤ c ∧ ∀ x, ‖T x‖ ≤ c * ‖x‖ }

/-- The Calderon Zygmund operator `T_r` in chapter Two-sided Metric Space Carleson -/
def czOperator (K : X → X → ℂ) (r : ℝ) (f : X → ℂ) (x : X) : ℂ :=
  ∫ y in (ball x r)ᶜ, K x y * f y

/-- `R_Q(θ, x)` defined in (1.0.20). -/
def upperRadius [FunctionDistances ℝ X] (Q : X → Θ X) (θ : Θ X) (x : X) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : dist_{x, r} θ (Q x) < 1), ENNReal.ofReal r

lemma le_upperRadius [FunctionDistances ℝ X] {Q : X → Θ X} {θ : Θ X} {x : X} {r : ℝ}
    (hr : dist_{x, r} θ (Q x) < 1) : ENNReal.ofReal r ≤ upperRadius Q θ x := by
  apply le_iSup₂ (f := fun r _ ↦ ENNReal.ofReal r) r hr

/-- The linearized maximally truncated nontangential Calderon Zygmund operator `T_Q^θ` -/
def linearizedNontangentialOperator [FunctionDistances ℝ X] (Q : X → Θ X) (θ : Θ X)
    (K : X → X → ℂ) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (R₁ : ℝ) (x' : X) (_ : dist x x' ≤ R₁),
  ‖∫ y in {y | ENNReal.ofReal (dist x' y) ∈ Ioo (ENNReal.ofReal R₁) (upperRadius Q θ x')},
    K x' y * f y‖₊

/-- The maximally truncated nontangential Calderon Zygmund operator `T_*` -/
def nontangentialOperator (K : X → X → ℂ) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (R₁ : ℝ) (_ : 0 < R₁) (R₂ : ℝ) (_ : R₁ < R₂) (x' : X) (_ : dist x x' < R₁),
  ‖∫ y in Annulus.oo x' R₁ R₂, K x' y * f y‖ₑ

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


end DoublingMeasure

/-- This is usually the value of the argument `A` in `DoublingMeasure`
and `CompatibleFunctions` -/
@[simp] abbrev defaultA (a : ℕ) : ℕ := 2 ^ a
@[simp] def defaultD (a : ℕ) : ℕ := 2 ^ (100 * a ^ 2)
@[simp] def defaultκ (a : ℕ) : ℝ := 2 ^ (-10 * (a : ℝ))
@[simp] def defaultZ (a : ℕ) : ℕ := 2 ^ (12 * a)
@[simp] def defaultτ (a : ℕ) : ℝ := a⁻¹

lemma defaultD_pos (a : ℕ) : 0 < (defaultD a : ℝ) := by rw [defaultD]; positivity

lemma defaultD_pos' (a : ℕ) : 0 < defaultD a := by exact_mod_cast defaultD_pos a

lemma defaultD_pow_pos (a : ℕ) (z : ℤ) : 0 < (defaultD a : ℝ) ^ z :=
  zpow_pos (defaultD_pos _) _

lemma mul_defaultD_pow_pos (a : ℕ) {r : ℝ} (hr : 0 < r) (z : ℤ) : 0 < r * (defaultD a : ℝ) ^ z :=
  mul_pos hr (defaultD_pow_pos a z)

lemma one_le_defaultD (a : ℕ) : 1 ≤ (defaultD a : ℝ) := by
  rw [defaultD, Nat.cast_pow, Nat.cast_ofNat, ← pow_zero 2]
  exact pow_le_pow_right₀ (one_le_two) (by omega)

section Kernel

variable {X : Type*} {a : ℕ} {K : X → X → ℂ} [PseudoMetricSpace X] [MeasureSpace X]
open Function

/-- The constant used twice in the definition of the Calderon-Zygmund kernel. -/
@[simp] def C_K (a : ℝ) : ℝ≥0 := 2 ^ a ^ 3

lemma C_K_pos {a : ℝ} : 0 < C_K a := NNReal.rpow_pos (by norm_num)
lemma C_K_pos_real {a : ℝ} : 0 < (C_K a : ℝ) := C_K_pos

/-- `K` is a one-sided Calderon-Zygmund kernel
In the formalization `K x y` is defined everywhere, even for `x = y`. The assumptions on `K` show
that `K x x = 0`.

Todo: maybe make enorm_K_le_vol_inv + enorm_K_sub_le + K_eq_zero_of_dist_eq_zero the axioms. -/
class IsOneSidedKernel (a : outParam ℕ) (K : X → X → ℂ) : Prop where
  measurable_K : Measurable (uncurry K)
  norm_K_le_vol_inv (x y : X) : ‖K x y‖ ≤ C_K a / Real.vol x y
  norm_K_sub_le {x y y' : X} (h : 2 * dist y y' ≤ dist x y) :
    ‖K x y - K x y'‖ ≤ (dist y y' / dist x y) ^ (a : ℝ)⁻¹ * (C_K a / Real.vol x y)

export IsOneSidedKernel (measurable_K norm_K_le_vol_inv norm_K_sub_le)

lemma MeasureTheory.stronglyMeasurable_K [IsOneSidedKernel a K] :
    StronglyMeasurable (uncurry K) :=
  measurable_K.stronglyMeasurable

lemma MeasureTheory.aestronglyMeasurable_K [IsOneSidedKernel a K] :
    AEStronglyMeasurable (uncurry K) :=
  measurable_K.aestronglyMeasurable

lemma measurable_K_left [IsOneSidedKernel a K] (y : X) : Measurable (K · y) :=
  measurable_K.of_uncurry_right

lemma measurable_K_right [IsOneSidedKernel a K] (x : X) : Measurable (K x) :=
  measurable_K.of_uncurry_left

lemma enorm_K_le_vol_inv [ProperSpace X] [IsFiniteMeasureOnCompacts (volume : Measure X)]
    [IsOneSidedKernel a K] (x y : X) : ‖K x y‖ₑ ≤ (C_K a : ℝ≥0∞) / vol x y := by
  rw [← ofReal_norm, ← ofReal_vol, ← ofReal_coe_nnreal]
  refine le_trans ?_ (ofReal_div_le measureReal_nonneg)
  gcongr
  apply norm_K_le_vol_inv

--TODO good name
lemma enorm_K_le_ball_complement [ProperSpace X] [IsFiniteMeasureOnCompacts (volume : Measure X)]
    [IsOneSidedKernel a K] {r : ℝ} {x : X} {y : X} (hy : y ∈ (ball x r)ᶜ):
    ‖K x y‖ₑ ≤ C_K a / volume (ball x r) := by
  apply le_trans (enorm_K_le_vol_inv x y)
  apply ENNReal.div_le_div_left
  apply measure_mono
  apply ball_subset_ball
  rw [mem_compl_iff, ball, mem_setOf, not_lt, dist_comm] at hy
  exact hy

lemma enorm_K_le_ball_complement' [ProperSpace X] [IsFiniteMeasureOnCompacts (volume : Measure X)]
    [IsOpenPosMeasure (volume : Measure X)] [IsOneSidedKernel a K] {r : ℝ} (hr : 0 < r)
    {x : X} {y : X} (hy : y ∈ (ball x r)ᶜ):
    ‖K x y‖ₑ ≤ (C_K a / volume (ball x r)).toNNReal := by
  rw [ENNReal.coe_toNNReal ?ne_top]
  case ne_top =>
    rw [Ne, ENNReal.div_eq_top]
    push_neg
    simp [ne_of_gt (measure_ball_pos volume x hr)]
  exact enorm_K_le_ball_complement hy

lemma enorm_K_sub_le [ProperSpace X] [IsFiniteMeasureOnCompacts (volume : Measure X)]
    [IsOneSidedKernel a K] {x y y' : X} (h : 2 * dist y y' ≤ dist x y) :
    ‖K x y - K x y'‖ₑ ≤ (edist y y' / edist x y) ^ (a : ℝ)⁻¹ * (C_K a / vol x y) := by
  simp_rw [← ofReal_norm, ← ofReal_vol, ← ofReal_coe_nnreal, edist_dist]
  calc
    _ ≤ ENNReal.ofReal ((dist y y' / dist x y) ^ (a : ℝ)⁻¹ * (C_K a / Real.vol x y)) := by
      gcongr; apply norm_K_sub_le h
    _ ≤ _ := by
      rw [ENNReal.ofReal_mul']; swap
      · exact div_nonneg NNReal.zero_le_coe measureReal_nonneg
      gcongr
      · rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
        gcongr
        apply ofReal_div_le (by positivity)
      · exact ofReal_div_le measureReal_nonneg

lemma integrableOn_K_mul [IsOpenPosMeasure (volume : Measure X)]
    [IsFiniteMeasureOnCompacts (volume : Measure X)] [ProperSpace X]
    [IsOneSidedKernel a K] {f : X → ℂ} (hf : Integrable f) (x : X) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (K x * f) (ball x r)ᶜ := by
  use (measurable_K_right x).aestronglyMeasurable.mul hf.aestronglyMeasurable |>.restrict
  exact (hasFiniteIntegral_def _ _).mpr <| calc
    _ = ∫⁻ y in (ball x r)ᶜ, ‖K x y‖ₑ * ‖f y‖ₑ := by simp
    _ ≤ ∫⁻ y in (ball x r)ᶜ, C_K a / volume (ball x r) * ‖f y‖ₑ :=
      setLIntegral_mono_ae (hf.aemeasurable.enorm.const_mul _).restrict <|
        Filter.Eventually.of_forall fun y hy ↦ mul_le_mul_right' (enorm_K_le_ball_complement hy) _
    _ = _ * ∫⁻ y in (ball x r)ᶜ, ‖f y‖ₑ := lintegral_const_mul'' _ hf.aemeasurable.enorm.restrict
    _ ≤ _ * ∫⁻ y, ‖f y‖ₑ := mul_le_mul_left' (setLIntegral_le_lintegral _ _) _
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.div_lt_top coe_ne_top (measure_ball_pos _ x hr).ne') hf.2

lemma integrableOn_K_Icc [IsOpenPosMeasure (volume : Measure X)]
    [IsFiniteMeasureOnCompacts (volume : Measure X)] [ProperSpace X]
    [IsOneSidedKernel a K] {x : X} {r R : ℝ} (hr : r > 0) :
    IntegrableOn (K x) {y | dist x y ∈ Icc r R} volume := by
  use Measurable.aestronglyMeasurable (measurable_K_right x)
  rw [hasFiniteIntegral_def]
  calc ∫⁻ (y : X) in {y | dist x y ∈ Icc r R}, ‖K x y‖ₑ
    _ ≤ ∫⁻ (y : X) in {y | dist x y ∈ Icc r R}, C_K a / volume (ball x r) := by
      refine setLIntegral_mono measurable_const (fun y hy ↦ ?_)
      refine (enorm_K_le_vol_inv x y).trans ?_
      rw [vol]
      gcongr
      exact hy.1
    _ < _ := by
      rw [setLIntegral_const]
      apply ENNReal.mul_lt_top (ENNReal.div_lt_top ENNReal.coe_ne_top _); swap
      · simp_rw [← pos_iff_ne_zero, measure_ball_pos _ _ hr]
      refine (Ne.lt_top fun h ↦ ?_)
      have : {y | dist x y ∈ Icc r R} ⊆ closedBall x R := by
        intro y ⟨_, hy⟩
        exact mem_closedBall_comm.mp hy
      exact measure_closedBall_lt_top.ne (measure_mono_top this h)

/-- `K` is a two-sided Calderon-Zygmund kernel
In the formalization `K x y` is defined everywhere, even for `x = y`. The assumptions on `K` show
that `K x x = 0`. -/
class IsTwoSidedKernel (a : outParam ℕ) (K : X → X → ℂ) extends IsOneSidedKernel a K where
  enorm_K_sub_le' {x x' y : X} (h : 2 * dist x x' ≤ dist x y) :
    ‖K x y - K x' y‖ₑ ≤ (edist x x' / edist x y) ^ (a : ℝ)⁻¹ * (C_K a / vol x y)

export IsTwoSidedKernel (enorm_K_sub_le')

-- maybe show: `K` is a 2-sided kernel iff `K` and `fun x y ↦ K y x` are one-sided kernels.

end Kernel

-- to show: K is locally bounded and hence integrable outside the diagonal

/- A constant used on the boundedness of `T_*`. We generally assume
`HasBoundedStrongType (nontangentialOperator K) volume volume 2 2 (C_Ts a)`
throughout this formalization. -/
def C_Ts (a : ℝ) : ℝ≥0 := 2 ^ a ^ 3

/-- Data common through most of chapters 2-7.
These contain the minimal axioms for `kernel-summand`'s proof and `hasBoundedStrongType_Tstar`.
This is used in chapter 3 when we don't have all other fields from `ProofData`. -/
class KernelProofData {X : Type*} (a : outParam ℕ) (K : outParam (X → X → ℂ))
    [PseudoMetricSpace X] where
  d : DoublingMeasure X (defaultA a)
  four_le_a : 4 ≤ a
  cf : CompatibleFunctions ℝ X (defaultA a)
  hcz : IsOneSidedKernel a K
  hasBoundedStrongType_Tstar :
    HasBoundedStrongType (nontangentialOperator K · ·) 2 2 volume volume (C_Ts a)

/-- Data common through most of chapters 2-7 (except 3). -/
class ProofData {X : Type*} (a : outParam ℕ) (q : outParam ℝ) (K : outParam (X → X → ℂ))
  (σ₁ σ₂ : outParam (X → ℤ)) (F G : outParam (Set X)) [PseudoMetricSpace X] extends
    KernelProofData a K where
  c : IsCancellative X (defaultτ a)
  isBounded_F : IsBounded F
  isBounded_G : IsBounded G
  measurableSet_F : MeasurableSet F
  measurableSet_G : MeasurableSet G
  /-- `volume_F_pos` can probably be removed. -/
  volume_F_pos : 0 < volume F
  /-- `volume_G_pos` can probably be removed. -/
  volume_G_pos : 0 < volume G
  measurable_σ₁ : Measurable σ₁
  measurable_σ₂ : Measurable σ₂
  finite_range_σ₁ : Finite (range σ₁)
  finite_range_σ₂ : Finite (range σ₂)
  σ₁_le_σ₂ : σ₁ ≤ σ₂
  Q : SimpleFunc X (Θ X)
  q_mem_Ioc : q ∈ Ioc 1 2

export KernelProofData (four_le_a hasBoundedStrongType_Tstar)
export ProofData (isBounded_F isBounded_G measurableSet_F measurableSet_G
  measurable_σ₁ measurable_σ₂ finite_range_σ₁ finite_range_σ₂ σ₁_le_σ₂ Q q_mem_Ioc)
attribute [instance] KernelProofData.d KernelProofData.cf ProofData.c KernelProofData.hcz

section ProofData

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [PseudoMetricSpace X]

section Iterate
variable [CompatibleFunctions ℝ X (defaultA a)]

lemma le_cdist_iterate {x : X} {r : ℝ} (hr : 0 ≤ r) (f g : Θ X) (k : ℕ) :
    2 ^ k * dist_{x, r} f g ≤ dist_{x, (defaultA a) ^ k * r} f g := by
  induction k with
  | zero => rw [pow_zero, one_mul]; congr! <;> simp
  | succ k ih =>
    trans 2 * dist_{x, (defaultA a) ^ k * r} f g
    · rw [pow_succ', mul_assoc]
      exact (_root_.mul_le_mul_left zero_lt_two).mpr ih
    · convert le_cdist (ball_subset_ball _) using 1
      · exact dist_congr rfl (by rw [← mul_assoc, pow_succ'])
      · nth_rw 1 [← one_mul ((defaultA a) ^ k * r)]; gcongr
        rw [← Nat.cast_one, Nat.cast_le]; exact Nat.one_le_two_pow

lemma cdist_le_iterate {x : X} {r : ℝ} (hr : 0 < r) (f g : Θ X) (k : ℕ) :
    dist_{x, 2 ^ k * r} f g ≤ (defaultA a) ^ k * dist_{x, r} f g := by
  induction k with
  | zero => simp_rw [pow_zero, one_mul]; congr! <;> simp
  | succ k ih =>
    trans defaultA a * dist_{x, 2 ^ k * r} f g
    · convert cdist_le _ using 1
      · exact dist_congr rfl (by ring)
      · rw [dist_self]; positivity
    · replace ih := (mul_le_mul_left (show 0 < (defaultA a : ℝ) by positivity)).mpr ih
      rwa [← mul_assoc, ← pow_succ'] at ih

lemma cdist_le_mul_cdist {x x' : X} {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (f g : Θ X) :
    dist_{x', r'} f g ≤ As (defaultA a) ((r' + dist x' x) / r) * dist_{x, r} f g := by
  calc
    dist_{x', r'} f g ≤ dist_{x, 2 ^ _ * r} f g := ?e
    _ ≤ _ := cdist_le_iterate hr f g _
  case e =>
    apply cdist_mono
    apply ball_subset_ball'
    calc
      r' + dist x' x = (r' + dist x' x) / r * r := div_mul_cancel₀ _ hr.ne' |>.symm
      _ ≤ 2 ^ ⌈Real.logb 2 ((r' + dist x' x) / r)⌉₊ * r := by
        gcongr
        apply Real.le_pow_natCeil_logb (by norm_num) (by positivity)

lemma ballsCoverBalls_iterate_nat {x : X} {d r : ℝ} {n : ℕ} :
    BallsCoverBalls (WithFunctionDistance x d) (2 ^ n * r) r (defaultA a ^ n) :=
  CompatibleFunctions.allBallsCoverBalls.pow r

lemma ballsCoverBalls_iterate {x : X} {d R r : ℝ} (hr : 0 < r) :
    BallsCoverBalls (WithFunctionDistance x d) R r (defaultA a ^ ⌈Real.logb 2 (R / r)⌉₊) :=
  CompatibleFunctions.allBallsCoverBalls.ballsCoverBalls one_lt_two hr

end Iterate

section DBounds

variable (X)

-- used in 7.5.6 (`limited_scale_impact`)
lemma hundred_lt_realD [KernelProofData a K] : (100 : ℝ) < defaultD a := by
  simp only [defaultD]
  norm_cast
  calc 100
    _ < 128 := by
      linarith
    _ = 2 ^ 7 := by
      rfl
    _ < 2 ^ (100 * a ^ 2) := by
      have : 4 ≤ a := four_le_a X
      gcongr
      · linarith
      · nlinarith

-- used in 4.1.7 (`small_boundary`)
lemma twentyfive_le_realD [KernelProofData a K] : (25 : ℝ) ≤ defaultD a := by
  linarith [hundred_lt_realD X]

-- used in 4.1.3 (`I3_prop_3_1`)
lemma eight_le_realD [KernelProofData a K] : (8 : ℝ) ≤ defaultD a := by
  linarith [twentyfive_le_realD X]

-- used in 4.1.6 (`transitive_boundary`)
lemma five_le_realD [KernelProofData a K] : (5 : ℝ) ≤ defaultD a := by
  linarith [twentyfive_le_realD X]

-- used in various places in `Carleson.TileExistence`
lemma four_le_realD [KernelProofData a K] : (4 : ℝ) ≤ defaultD a := by
  linarith [twentyfive_le_realD X]

lemma one_le_realD [KernelProofData a K] : (1 : ℝ) ≤ defaultD a := by
  linarith [twentyfive_le_realD X]

lemma one_lt_realD [KernelProofData a K] : (1 : ℝ) < defaultD a := by
  linarith [twentyfive_le_realD X]

end DBounds

section MeasQ

variable [KernelProofData a K] {Q : SimpleFunc X (Θ X)}

@[fun_prop]
lemma measurable_Q₂ : Measurable fun p : X × X ↦ Q p.1 p.2 := fun s meass ↦ by
  have : (fun p : X × X ↦ (Q p.1) p.2) ⁻¹' s = ⋃ θ ∈ Q.range, (Q ⁻¹' {θ}) ×ˢ (θ ⁻¹' s) := by
    ext ⟨x, y⟩
    simp only [mem_preimage, SimpleFunc.mem_range, mem_range, iUnion_exists, iUnion_iUnion_eq',
      mem_iUnion, mem_prod, mem_singleton_iff]
    constructor <;> intro h
    · use x
    · obtain ⟨j, hj⟩ := h; exact congr($(hj.1) y).symm ▸ hj.2
  rw [this]
  exact Q.range.measurableSet_biUnion fun θ _ ↦
    (Q.measurableSet_fiber θ).prod (meass.preimage (map_continuous θ).measurable)

lemma stronglyMeasurable_Q₂ : StronglyMeasurable fun p : X × X ↦ Q p.1 p.2 :=
  measurable_Q₂.stronglyMeasurable

@[fun_prop]
lemma aestronglyMeasurable_Q₂ : AEStronglyMeasurable fun p : X × X ↦ Q p.1 p.2 :=
  measurable_Q₂.aestronglyMeasurable

@[fun_prop]
lemma measurable_Q₁ (x : X) : Measurable (Q x) :=
  let Q' : X → X → ℝ := fun x' y ↦ Q x' y
  have : (fun y ↦ Q' x y) = Q x := rfl
  this ▸ measurable_Q₂.of_uncurry_left

end MeasQ

variable [ProofData a q K σ₁ σ₂ F G]

include a q K σ₁ σ₂ F G

variable (X) in
lemma S_spec : ∃ n : ℕ, (∀ x, -n ≤ σ₁ x ∧ σ₂ x ≤ n) ∧
    F ⊆ ball (cancelPt X) (defaultD a ^ n / 4) ∧
    G ⊆ ball (cancelPt X) (defaultD a ^ n / 4) := by
  obtain ⟨l₁, hl₁⟩ := bddBelow_def.mp (Finite.bddBelow (finite_range_σ₁ (X := X)))
  obtain ⟨u₂, hu₂⟩ := bddAbove_def.mp (Finite.bddAbove (finite_range_σ₂ (X := X)))
  simp_rw [mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hl₁ hu₂
  have one_lt_D : (1 : ℝ) < defaultD a := by
    unfold defaultD; norm_cast; apply Nat.one_lt_two_pow
    have := four_le_a X; positivity
  obtain ⟨rF, rFpos, hrF⟩ : ∃ r > 0, F ⊆ ball (cancelPt X) r := by
    obtain ⟨r, hr⟩ := isBounded_F.subset_ball (cancelPt X)
    rcases lt_or_ge 0 r with lr | lr
    · use r
    · use 1, zero_lt_one, hr.trans (ball_subset_ball (lr.trans zero_le_one))
  let nF := ⌈Real.logb (defaultD a) (4 * rF)⌉
  obtain ⟨rG, rGpos, hrG⟩ : ∃ r > 0, G ⊆ ball (cancelPt X) r := by
    obtain ⟨r, hr⟩ := isBounded_G.subset_ball (cancelPt X)
    rcases lt_or_ge 0 r with lr | lr
    · use r
    · use 1, zero_lt_one, hr.trans (ball_subset_ball (lr.trans zero_le_one))
  let nG := ⌈Real.logb (defaultD a) (4 * rG)⌉
  refine ⟨(max (max (-l₁) u₂) (max nF nG)).toNat, ⟨fun x ↦ ?_, ?_, ?_⟩⟩
  · simp only [Int.ofNat_toNat, ← min_neg_neg, neg_neg, min_le_iff, le_max_iff]
    exact ⟨.inl (.inl (.inl (hl₁ x))), .inl (.inl (.inr (hu₂ x)))⟩
  · refine hrF.trans (ball_subset_ball ?_)
    calc
      _ ≤ (defaultD a : ℝ) ^ nF / 4 := by
        rw [le_div_iff₀' zero_lt_four, ← Real.rpow_intCast,
          ← Real.logb_le_iff_le_rpow one_lt_D (by positivity)]
        exact Int.le_ceil _
      _ ≤ (defaultD a : ℝ) ^ nF.toNat / 4 := by
        rw [← Real.rpow_natCast, ← Real.rpow_intCast]; gcongr
        · exact one_lt_D.le
        · exact_mod_cast Int.self_le_toNat nF
      _ ≤ _ := by
        gcongr
        · exact one_lt_D.le
        · exact Int.toNat_le_toNat ((le_max_left ..).trans (le_max_right ..))
  · refine hrG.trans (ball_subset_ball ?_)
    calc
      _ ≤ (defaultD a : ℝ) ^ nG / 4 := by
        rw [le_div_iff₀' zero_lt_four, ← Real.rpow_intCast,
          ← Real.logb_le_iff_le_rpow one_lt_D (by positivity)]
        exact Int.le_ceil _
      _ ≤ (defaultD a : ℝ) ^ nG.toNat / 4 := by
        rw [← Real.rpow_natCast, ← Real.rpow_intCast]; gcongr
        · exact one_lt_D.le
        · exact_mod_cast Int.self_le_toNat nG
      _ ≤ _ := by
        gcongr
        · exact one_lt_D.le
        · exact Int.toNat_le_toNat ((le_max_right ..).trans (le_max_right ..))

variable (X) in
open Classical in
def defaultS : ℕ := Nat.find (S_spec X)

lemma range_σ₁_subset : range σ₁ ⊆ Icc (-defaultS X) (defaultS X) := by
  classical
  rw [range_subset_iff]
  have := (Nat.find_spec (S_spec X)).1
  exact fun x ↦ ⟨(this x).1, (σ₁_le_σ₂ x).trans (this x).2⟩

lemma range_σ₂_subset : range σ₂ ⊆ Icc (-defaultS X) (defaultS X) := by
  classical
  rw [range_subset_iff]
  have := (Nat.find_spec (S_spec X)).1
  exact fun x ↦ ⟨(this x).1.trans (σ₁_le_σ₂ x), (this x).2⟩

lemma F_subset : F ⊆ ball (cancelPt X) (defaultD a ^ defaultS X / 4) := by
  classical exact (Nat.find_spec (S_spec X)).2.1

lemma G_subset : G ⊆ ball (cancelPt X) (defaultD a ^ defaultS X / 4) := by
  classical exact (Nat.find_spec (S_spec X)).2.2

lemma Icc_σ_subset_Icc_S {x : X} : Icc (σ₁ x) (σ₂ x) ⊆ Icc (-defaultS X) (defaultS X) :=
  fun _ h ↦ ⟨(range_σ₁_subset ⟨x, rfl⟩).1.trans h.1, h.2.trans (range_σ₂_subset ⟨x, rfl⟩).2⟩

/- unused
lemma neg_S_mem_or_S_mem [Nonempty X] :
    (- defaultS X : ℤ) ∈ range σ₁ ∨ (defaultS X : ℤ) ∈ range σ₂ := by
  by_cases h₀ : defaultS X = 0
  · right
    simp only [h₀, CharP.cast_eq_zero, mem_range]
    have : range σ₂ ⊆ Icc (- defaultS X) (defaultS X) := range_σ₂_subset
    simp only [h₀, CharP.cast_eq_zero, neg_zero, Icc_self, subset_singleton_iff, mem_range,
      forall_exists_index, forall_apply_eq_imp_iff] at this
    let x : X := Classical.choice inferInstance
    exact ⟨x, this x⟩
  by_contra! h
  let n := (defaultS X) - 1
  have h1 (x : X) : -n ≤ σ₁ x := by
    rw [Int.natCast_sub (Nat.one_le_iff_ne_zero.mpr h₀), neg_sub, sub_eq_add_neg, add_comm]
    exact lt_iff_le_and_ne.mpr ⟨(range_σ₁_subset (mem_range_self x)).1,
      fun h' ↦ h.1 <| mem_range.mpr ⟨x, h'.symm⟩⟩
  have h2 (x : X) : σ₂ x ≤ n :=
    Int.natCast_sub (Nat.one_le_iff_ne_zero.mpr h₀) ▸ le_sub_right_of_add_le (lt_iff_le_and_ne.mpr
      ⟨(range_σ₂_subset (mem_range_self x)).2, fun h' ↦ h.2 <| mem_range.mpr ⟨x, h'⟩⟩)
  have hn : n < defaultS X := by
    simp only [tsub_lt_self_iff, zero_lt_one, and_true, n]
    exact Nat.zero_lt_of_ne_zero h₀
  classical
  exact Nat.find_min (S_spec X) hn fun x ↦ ⟨h1 x, h2 x⟩ -/

variable (X)

lemma a_pos : 0 < a := by linarith [four_le_a X]
lemma cast_a_pos : 0 < (a : ℝ) := by norm_cast; exact a_pos X
lemma τ_pos : 0 < defaultτ a := inv_pos.mpr (cast_a_pos X)
lemma τ_nonneg : 0 ≤ defaultτ a := (τ_pos X).le
lemma τ_le_one : defaultτ a ≤ 1 := by
  rw [defaultτ, inv_le_one_iff₀]; right; norm_cast; linarith [four_le_a X]

/-- `τ` as an element of `ℝ≥0`. -/
def nnτ : ℝ≥0 := ⟨defaultτ a, τ_nonneg X⟩

lemma nnτ_pos : 0 < nnτ X := τ_pos X

lemma one_lt_q : 1 < q := (q_mem_Ioc X).1
lemma q_le_two : q ≤ 2 := (q_mem_Ioc X).2
lemma q_pos : 0 < q := zero_lt_one.trans (one_lt_q X)
lemma q_nonneg : 0 ≤ q := (q_pos X).le
lemma inv_q_sub_half_nonneg : 0 ≤ q⁻¹ - 2⁻¹ := by
  simp [inv_le_inv₀ zero_lt_two (q_pos X), q_le_two X]

/-- `q` as an element of `ℝ≥0`. -/
def nnq : ℝ≥0 := ⟨q, q_nonneg X⟩

lemma one_lt_nnq : 1 < nnq X := one_lt_q X
lemma nnq_le_two : nnq X ≤ 2 := q_le_two X
lemma nnq_pos : 0 < nnq X := q_pos X
lemma nnq_mem_Ioc : nnq X ∈ Ioc 1 2 :=
  ⟨NNReal.coe_lt_coe.mp (q_mem_Ioc X).1, NNReal.coe_le_coe.mp (q_mem_Ioc X).2⟩

end ProofData

namespace ShortVariables
-- open this section to get shorter 1-letter names for a bunch of variables

set_option hygiene false
scoped notation "D" => defaultD a
scoped notation "κ" => defaultκ a
scoped notation "Z" => defaultZ a
scoped notation "τ" => defaultτ a
scoped notation "o" => cancelPt X
scoped notation "S" => defaultS X
scoped notation "nnτ" => nnτ X
scoped notation "nnq" => nnq X

end ShortVariables

open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}

lemma one_lt_D [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] : 1 < (D : ℝ) := by
  exact_mod_cast one_lt_pow₀ Nat.one_lt_two (by nlinarith [four_le_a X])

lemma one_le_D : 1 ≤ (D : ℝ) := by
  rw [← Nat.cast_one, Nat.cast_le, defaultD, ← pow_zero 2]
  exact pow_le_pow_right' one_le_two (by positivity)

lemma D_nonneg : 0 ≤ (D : ℝ) := zero_le_one.trans one_le_D

lemma κ_nonneg : 0 ≤ κ :=
  Real.rpow_nonneg (by norm_num) _

lemma κ_le_one : κ ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by linarith)

/-- Used in `third_exception` (Lemma 5.2.10). -/
lemma two_le_κZ [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] : 2 ≤ κ * Z := by
  rw [defaultκ, defaultZ, Nat.cast_pow, show ((2 : ℕ) : ℝ) = 2 by rfl,
    show (2 : ℝ) ^ (12 * a) = 2 ^ (12 * a : ℝ) by norm_cast, ← Real.rpow_add zero_lt_two,
    show (-10 * a + 12 * a : ℝ) = 2 * a by ring]
  norm_cast; change 2 ^ 1 ≤ _
  exact Nat.pow_le_pow_of_le one_lt_two (by linarith [four_le_a X])

/-- Used in `third_exception` (Lemma 5.2.10). -/
lemma DκZ_le_two_rpow_100 [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] :
    (D : ℝ≥0∞) ^ (-κ * Z) ≤ 2 ^ (-100 : ℝ) := by
  rw [defaultD, Nat.cast_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    show ((2 : ℕ) : ℝ≥0∞) = 2 by rfl]
  apply ENNReal.rpow_le_rpow_of_exponent_le one_le_two
  rw [defaultκ, defaultZ, Nat.cast_pow, show ((2 : ℕ) : ℝ) = 2 by rfl, neg_mul,
    show (2 : ℝ) ^ (12 * a) = 2 ^ (12 * a : ℝ) by norm_cast, mul_neg,
    ← Real.rpow_add zero_lt_two, show (-10 * a + 12 * a : ℝ) = 2 * a by ring,
    neg_le_neg_iff]
  norm_cast
  calc
    _ ≤ 100 * a ^ 2 := by nlinarith [four_le_a X]
    _ ≤ _ := by
      nth_rw 1 [← mul_one (a ^ 2), ← mul_assoc]
      gcongr; exact Nat.one_le_two_pow

lemma four_le_Z [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G] : 4 ≤ Z := by
  rw [defaultZ, show 4 = 2 ^ 2 by rfl]
  exact Nat.pow_le_pow_right zero_lt_two (by linarith [four_le_a X])

variable (a) in
/-- `D` as an element of `ℝ≥0`. -/
def nnD : ℝ≥0 := ⟨D, by simp [D_nonneg]⟩

namespace ShortVariables

set_option hygiene false
scoped notation "nnD" => nnD a

end ShortVariables

section PseudoMetricSpace

variable [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]

lemma volume_F_lt_top : volume F < ⊤ := isBounded_F.measure_lt_top
lemma volume_F_ne_top : volume F ≠ ⊤ := volume_F_lt_top.ne
lemma volume_G_lt_top : volume G < ⊤ := isBounded_G.measure_lt_top
lemma volume_G_ne_top : volume G ≠ ⊤ := volume_G_lt_top.ne

/-- the L^∞-normalized τ-Hölder norm. Do we use this for other values of τ? Defined in ℝ≥0∞ to
avoid sup-related issues. -/
@[nolint unusedArguments]
def iHolENorm [ProofData a q K σ₁ σ₂ F G] (ϕ : X → ℂ) (x₀ : X) (R : ℝ) : ℝ≥0∞ :=
  (⨆ (x ∈ ball x₀ R), ‖ϕ x‖ₑ) + (ENNReal.ofReal R) ^ τ *
    ⨆ (x ∈ ball x₀ R) (y ∈ ball x₀ R) (_ : x ≠ y), (‖ϕ x - ϕ y‖ₑ / (edist x y) ^ τ)

def iHolNNNorm [ProofData a q K σ₁ σ₂ F G] (ϕ : X → ℂ) (x₀ : X) (R : ℝ) : ℝ≥0 :=
  (iHolENorm ϕ x₀ R).toNNReal

/-! Lemma 2.1.1 -/

def C2_1_1 (k : ℕ) (a : ℕ) : ℕ := 2 ^ (k * a)

lemma Θ.finite_and_mk_le_of_le_dist {x₀ : X} {r R : ℝ} {f : Θ X} {k : ℕ}
    {𝓩 : Set (Θ X)} (h𝓩 : 𝓩 ⊆ ball_{x₀, R} f (r * 2 ^ k))
    (h2𝓩 : 𝓩.PairwiseDisjoint (ball_{x₀, R} · r)) :
    𝓩.Finite ∧ Cardinal.mk 𝓩 ≤ C2_1_1 k a := by
  obtain ⟨𝓩', c𝓩', u𝓩'⟩ := ballsCoverBalls_iterate_nat (x := x₀) (n := k) (r := r) (d := R) f
  rw [mul_comm] at u𝓩'
  classical
    let g : Θ X → Finset (Θ X) := fun z ↦ 𝓩'.filter (z ∈ ball_{x₀, R} · r)
    have g_pd : 𝓩.PairwiseDisjoint g := fun z hz z' hz' hne ↦ by
      refine Finset.disjoint_filter.mpr fun c _ mz mz' ↦ ?_
      rw [mem_ball_comm (α := WithFunctionDistance x₀ R)] at mz mz'
      exact Set.disjoint_left.mp (h2𝓩 hz hz' hne) mz mz'
  have g_ne : ∀ z, z ∈ 𝓩 → (g z).Nonempty := fun z hz ↦ by
    obtain ⟨c, hc⟩ := mem_iUnion.mp <| mem_of_mem_of_subset hz (h𝓩.trans u𝓩')
    simp only [mem_iUnion, exists_prop] at hc
    use c; simpa only [g, Finset.mem_filter]
  have g_injOn : 𝓩.InjOn g := fun z hz z' hz' e ↦ by
    have : z ≠ z' → Disjoint (g z) (g z') := g_pd hz hz'
    rw [← e, Finset.disjoint_self_iff_empty] at this
    exact not_ne_iff.mp <| this.mt <| Finset.nonempty_iff_ne_empty.mp (g_ne z hz)
  have g_subset : g '' 𝓩 ⊆ 𝓩'.powerset.toSet := fun gz hgz ↦ by
    rw [mem_image] at hgz
    obtain ⟨z, hz⟩ := hgz
    simp_rw [Finset.coe_powerset, mem_preimage, mem_powerset_iff, Finset.coe_subset, ← hz.2, g,
      Finset.filter_subset]
  have f𝓩 : (g '' 𝓩).Finite := Finite.subset 𝓩'.powerset.finite_toSet g_subset
  rw [Set.finite_image_iff g_injOn] at f𝓩
  refine ⟨f𝓩, ?_⟩
  lift 𝓩 to Finset (Θ X) using f𝓩
  simp_rw [Cardinal.mk_fintype, Finset.coe_sort_coe, Fintype.card_coe]
  norm_cast
  classical calc
    _ = ∑ _ ∈ 𝓩, 1 := by simp
    _ ≤ ∑ u ∈ 𝓩, (g u).card := Finset.sum_le_sum fun z hz ↦ Finset.card_pos.mpr (g_ne z hz)
    _ = (𝓩.biUnion g).card := (Finset.card_biUnion (fun z hz z' hz' ↦ g_pd hz hz')).symm
    _ ≤ 𝓩'.card := by
      refine Finset.card_le_card fun _ h ↦ ?_
      rw [Finset.mem_biUnion] at h
      exact Finset.mem_of_subset (by simp [g]) h.choose_spec.2
    _ ≤ (2 ^ a) ^ k := c𝓩'
    _ ≤ _ := by rw [C2_1_1, mul_comm, pow_mul]

lemma Θ.card_le_of_le_dist {x₀ : X} {r R : ℝ} {f : Θ X} {k : ℕ}
    {𝓩 : Set (Θ X)} (h𝓩 : 𝓩 ⊆ ball_{x₀, R} f (r * 2 ^ k))
    (h2𝓩 : 𝓩.PairwiseDisjoint (ball_{x₀, R} · r)) :
    Nat.card 𝓩 ≤ C2_1_1 k a := by
  obtain ⟨f𝓩, c𝓩⟩ := finite_and_mk_le_of_le_dist h𝓩 h2𝓩
  lift 𝓩 to Finset (Θ X) using f𝓩
  simpa using c𝓩

end PseudoMetricSpace

section MetricSpace

variable [MetricSpace X] [ProofData a q K σ₁ σ₂ F G]

lemma iLipENorm_le_add {z : X} {R : ℝ} {C C' : ℝ≥0} {ϕ : X → ℂ}
    (h : ∀ x ∈ ball z R, ‖ϕ x‖ ≤ C)
    (h' : ∀ x ∈ ball z R, ∀ x' ∈ ball z R, x ≠ x' → ‖ϕ x - ϕ x'‖ ≤ C' * dist x x' / R) :
    iLipENorm ϕ z R ≤ C + C' := by
  apply add_le_add
  · simp only [iSup_le_iff, enorm_le_coe]
    exact h
  · apply ENNReal.mul_le_of_le_div'
    simp only [ne_eq, iSup_le_iff]
    intro x hx x' hx' hne
    have hR : 0 < R := pos_of_mem_ball hx
    have W := h' x hx x' hx' hne
    rw [ENNReal.div_le_iff (by simpa only [ne_eq, edist_eq_zero] using hne) (edist_ne_top x x')]
    convert ENNReal.ofReal_le_ofReal W
    · exact (ofReal_norm_eq_enorm (ϕ x - ϕ x')).symm
    · rw [ENNReal.ofReal_div_of_pos hR, ENNReal.ofReal_mul NNReal.zero_le_coe, edist_dist,
        ENNReal.mul_div_right_comm, ENNReal.ofReal_coe_nnreal]

lemma iLipENorm_le {z : X} {R : ℝ} {C : ℝ≥0} {ϕ : X → ℂ}
    (h : ∀ x ∈ ball z R, ‖ϕ x‖ ≤ 2⁻¹ * C)
    (h' : ∀ x ∈ ball z R, ∀ x' ∈ ball z R, x ≠ x' → ‖ϕ x - ϕ x'‖ ≤ 2⁻¹ * C * dist x x' / R) :
    iLipENorm ϕ z R ≤ C := by
  apply (iLipENorm_le_add (C := 2⁻¹ * C) (C' := 2⁻¹ * C) ?_ ?_).trans_eq
  · simp [← add_mul, ENNReal.inv_two_add_inv_two]
  · exact h
  · exact h'

lemma enorm_le_iLipENorm_of_mem {z : X} {R : ℝ} (ϕ : X → ℂ) {x : X} (hx : x ∈ ball z R) :
    ‖ϕ x‖ₑ ≤ iLipENorm ϕ z R := by
  apply le_trans _ le_self_add
  simp only [le_iSup_iff, iSup_le_iff]
  tauto

lemma norm_le_iLipNNNorm_of_mem {z : X} {R : ℝ} {ϕ : X → ℂ} (hϕ : iLipENorm ϕ z R ≠ ⊤)
    {x : X} (hx : x ∈ ball z R) :
    ‖ϕ x‖ ≤ iLipNNNorm ϕ z R :=
  (ENNReal.toReal_le_toReal (by simp) hϕ).2 (enorm_le_iLipENorm_of_mem ϕ hx)

lemma norm_le_iLipNNNorm_of_subset {z : X} {R : ℝ} {ϕ : X → ℂ} (hϕ : iLipENorm ϕ z R ≠ ⊤)
    {x : X} (h : support ϕ ⊆ ball z R) : ‖ϕ x‖ ≤ iLipNNNorm ϕ z R := by
  by_cases hx : x ∈ ball z R
  · apply norm_le_iLipNNNorm_of_mem hϕ hx
  · have : x ∉ support ϕ := fun a ↦ hx (h a)
    simp [notMem_support.mp this]

lemma LipschitzOnWith.of_iLipENorm_ne_top
    {z : X} {R : ℝ} {ϕ : X → ℂ} (hϕ : iLipENorm ϕ z R ≠ ⊤) :
    LipschitzOnWith (iLipNNNorm ϕ z R / R.toNNReal) ϕ (ball z R) := by
  intro x hx y hy
  have hR : 0 < R := by
    simp only [mem_ball] at hx
    apply dist_nonneg.trans_lt hx
  rcases eq_or_ne x y with rfl | hne
  · simp
  have : (ENNReal.ofReal R) * (‖ϕ x - ϕ y‖ₑ / edist x y) ≤ iLipENorm ϕ z R := calc
      (ENNReal.ofReal R) * (‖ϕ x - ϕ y‖ₑ / (edist x y))
    _ ≤ (ENNReal.ofReal R) *
        ⨆ (x ∈ ball z R) (y ∈ ball z R) (_ : x ≠ y), (‖ϕ x - ϕ y‖ₑ / edist x y) := by
      gcongr
      simp only [ne_eq, le_iSup_iff, iSup_le_iff]
      tauto
    _ ≤ _ := le_add_self
  rw [edist_eq_enorm_sub, ENNReal.coe_div (by simp [hR]), iLipNNNorm, coe_toNNReal hϕ]
  rw [← ENNReal.div_le_iff_le_mul]; rotate_left
  · have : edist x y ≠ 0 := by simp [hne]
    simp [this]
  · simp [edist_ne_top]
  rw [ENNReal.le_div_iff_mul_le]; rotate_left
  · simp [hR]
  · simp
  convert this using 1
  simp only [ENNReal.ofReal, mul_comm]

lemma continuous_of_iLipENorm_ne_top {z : X} {R : ℝ}
    {ϕ : X → ℂ} (hϕ : tsupport ϕ ⊆ ball z R) (h'ϕ : iLipENorm ϕ z R ≠ ⊤) :
    Continuous ϕ :=
  (LipschitzOnWith.of_iLipENorm_ne_top h'ϕ).continuousOn.continuous_of_tsupport_subset
    isOpen_ball hϕ

lemma enorm_le_iHolENorm_of_mem {z : X} {R : ℝ} (ϕ : X → ℂ) {x : X} (hx : x ∈ ball z R) :
    ‖ϕ x‖ₑ ≤ iHolENorm ϕ z R := by
  apply le_trans _ le_self_add
  simp only [le_iSup_iff, iSup_le_iff]
  tauto

lemma norm_le_iHolNNNorm_of_mem {z : X} {R : ℝ} {ϕ : X → ℂ} (hϕ : iHolENorm ϕ z R ≠ ⊤)
    {x : X} (hx : x ∈ ball z R) :
    ‖ϕ x‖ ≤ iHolNNNorm ϕ z R :=
  (ENNReal.toReal_le_toReal (by simp) hϕ).2 (enorm_le_iHolENorm_of_mem ϕ hx)

lemma norm_le_iHolNNNorm_of_subset {z : X} {R : ℝ} {ϕ : X → ℂ} (hϕ : iHolENorm ϕ z R ≠ ⊤)
    {x : X} (h : support ϕ ⊆ ball z R) : ‖ϕ x‖ ≤ iHolNNNorm ϕ z R := by
  by_cases hx : x ∈ ball z R
  · apply norm_le_iHolNNNorm_of_mem hϕ hx
  · have : x ∉ support ϕ := fun a ↦ hx (h a)
    simp [notMem_support.mp this]

lemma HolderOnWith.of_iHolENorm_ne_top
    {z : X} {R : ℝ} {ϕ : X → ℂ} (hϕ : iHolENorm ϕ z R ≠ ⊤) :
    HolderOnWith (iHolNNNorm ϕ z R / R.toNNReal ^ τ) nnτ ϕ (ball z R) := by
  intro x hx y hy
  have hR : 0 < R := by
    simp only [mem_ball] at hx
    apply dist_nonneg.trans_lt hx
  rcases eq_or_ne x y with rfl | hne
  · simp
  have : (ENNReal.ofReal R) ^ τ * (‖ϕ x - ϕ y‖ₑ / (edist x y) ^ τ) ≤ iHolENorm ϕ z R := calc
      (ENNReal.ofReal R) ^ τ * (‖ϕ x - ϕ y‖ₑ / (edist x y) ^ τ)
    _ ≤ (ENNReal.ofReal R) ^ τ *
        ⨆ (x ∈ ball z R) (y ∈ ball z R) (_ : x ≠ y), (‖ϕ x - ϕ y‖ₑ / (edist x y) ^ τ) := by
      gcongr
      simp only [ne_eq, le_iSup_iff, iSup_le_iff]
      tauto
    _ ≤ _ := le_add_self
  rw [edist_eq_enorm_sub, ENNReal.coe_div (by simp [hR]), iHolNNNorm, coe_toNNReal hϕ]
  rw [← ENNReal.div_le_iff_le_mul]; rotate_left
  · have : edist x y ≠ 0 := by simp [hne]
    simp [this]
  · simp [edist_ne_top]
  rw [ENNReal.le_div_iff_mul_le]; rotate_left
  · simp [hR]
  · simp
  convert this using 1
  rw [ENNReal.coe_rpow_of_ne_zero (by simp [hR])]
  simp only [ENNReal.ofReal, mul_comm]
  rfl

lemma continuous_of_iHolENorm_ne_top {z : X} {R : ℝ}
    {ϕ : X → ℂ} (hϕ : tsupport ϕ ⊆ ball z R) (h'ϕ : iHolENorm ϕ z R ≠ ∞) :
    Continuous ϕ :=
  ((HolderOnWith.of_iHolENorm_ne_top h'ϕ).continuousOn
    (nnτ_pos X)).continuous_of_tsupport_subset isOpen_ball hϕ

lemma continuous_of_iHolENorm_ne_top' {z : X} {R : ℝ}
    {ϕ : X → ℂ} (hϕ : support ϕ ⊆ ball z R) (h'ϕ : iHolENorm ϕ z (2 * R) ≠ ∞) :
    Continuous ϕ := by
  rcases le_or_gt R 0 with hR | hR
  · have : support ϕ ⊆ ∅ := by rwa [ball_eq_empty.2 hR] at hϕ
    simp only [subset_empty_iff, support_eq_empty_iff] at this
    simp only [this]
    exact continuous_const
  apply ((HolderOnWith.of_iHolENorm_ne_top h'ϕ).continuousOn
    (nnτ_pos X)).continuous_of_tsupport_subset isOpen_ball
  apply (closure_mono hϕ).trans (closure_ball_subset_closedBall.trans ?_)
  exact closedBall_subset_ball (by linarith)

end MetricSpace
