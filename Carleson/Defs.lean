import Carleson.DoublingMeasure

open MeasureTheory Measure NNReal Metric Complex Set TopologicalSpace Bornology
open scoped ENNReal
noncomputable section

-- todo: rename and protect `Real.RCLike`

/-! Miscellaneous definitions.
These are mostly the definitions used to state the metric Carleson theorem.
We should move them to separate files once we start proving things about them. -/

section DoublingMeasure
universe u
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
variable (𝕜) in
/-- A type synonym of `C(X, 𝕜)` that uses the local oscillation w.r.t. `E` as the metric. -/
@[nolint unusedArguments]
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
/-- A ball w.r.t. the distance `localOscillation` -/
def localOscillationBall (E : Set X) (f : C(X, 𝕜)) (r : ℝ) :
    Set C(X, 𝕜) :=
  { g : C(X, 𝕜) | localOscillation E f g < r }

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
  metric : ∀ (_x : X) (_r : ℝ), PseudoMetricSpace Θ

export FunctionDistances (Θ coeΘ)

section FunctionDistances
variable [FunctionDistances 𝕜 X]

instance : Coe (Θ X) C(X, 𝕜) := ⟨coeΘ⟩
instance : CoeFun (Θ X) (fun _ ↦ X → 𝕜) := ⟨fun f ↦ coeΘ f⟩

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
notation3 "nndist_{" x " ," r "}" => @nndist (WithFunctionDistance x r) _
notation3 "ball_{" x " ," r "}" => @ball (WithFunctionDistance x r) _ in

/-- A set `Θ` of (continuous) functions is compatible. `A` will usually be `2 ^ a`. -/
class CompatibleFunctions (𝕜 : outParam Type*) (X : Type u) (A : outParam ℝ)
  [RCLike 𝕜] [PseudoMetricSpace X] extends FunctionDistances 𝕜 X where
  eq_zero : ∃ o : X, ∀ f : Θ, f o = 0
  /-- The distance is bounded below by the local oscillation. -/
  localOscillation_le_cdist {x : X} {r : ℝ} {f g : Θ} :
    localOscillation (ball x r) (coeΘ f) (coeΘ g) ≤ dist_{x, r} f g
  /-- The distance is monotone in the ball. -/
  cdist_mono {x₁ x₂ : X} {r₁ r₂ : ℝ} {f g : Θ}
    (h : ball x₁ r₁ ⊆ ball x₂ r₂) : dist_{x₁, r₂} f g ≤ dist_{x₂, r₂} f g
  /-- The distance of a ball with large radius is bounded above. -/
  cdist_le {x₁ x₂ : X} {r : ℝ} {f g : Θ} (h : dist x₁ x₂ < 2 * r) :
    dist_{x₂, 2 * r} f g ≤ A * dist_{x₁, r} f g
  /-- The distance of a ball with large radius is bounded below. -/
  le_cdist {x₁ x₂ : X} {r : ℝ} {f g : Θ} (h1 : ball x₁ r ⊆ ball x₂ (A * r))
    /-(h2 : A * r ≤ Metric.diam (univ : Set X))-/ :
    2 * dist_{x₁, r} f g ≤ dist_{x₂, A * r} f g
  /-- The distance of a ball with large radius is bounded below. -/
  ballsCoverBalls {x : X} {r R : ℝ} :
    BallsCoverBalls (X := WithFunctionDistance x r) (2 * R) R ⌊A⌋₊

export CompatibleFunctions (localOscillation_le_cdist cdist_mono cdist_le le_cdist)

variable (X) in
/-- The point `o` in the blueprint -/
def cancelPt [CompatibleFunctions 𝕜 X A] : X :=
  CompatibleFunctions.eq_zero (𝕜 := 𝕜) |>.choose
lemma cancelPt_eq_zero [CompatibleFunctions 𝕜 X A] {f : Θ X} : f (cancelPt X) = 0 :=
  CompatibleFunctions.eq_zero (𝕜 := 𝕜) |>.choose_spec f

-- not sure if needed
lemma CompatibleFunctions.IsSeparable [CompatibleFunctions 𝕜 X A] :
  IsSeparable (range (coeΘ (X := X))) :=
  sorry

set_option linter.unusedVariables false in
/-- The inhomogeneous Lipschitz norm on a ball. -/
def iLipNorm {𝕜} [NormedField 𝕜] (ϕ : X → 𝕜) (x₀ : X) (R : ℝ) : ℝ :=
  (⨆ x ∈ ball x₀ R, ‖ϕ x‖) + R * ⨆ (x : X) (y : X) (h : x ≠ y), ‖ϕ x - ϕ y‖ / dist x y

variable (X) in
/-- Θ is τ-cancellative. `τ` will usually be `1 / a` -/
class IsCancellative (τ : ℝ) [CompatibleFunctions ℝ X A] : Prop where
  norm_integral_exp_le {x : X} {r : ℝ} {ϕ : X → ℂ} {K : ℝ≥0} (h1 : LipschitzWith K ϕ)
    (h2 : tsupport ϕ ⊆ ball x r) {f g : Θ X} :
    ‖∫ x in ball x r, exp (I * (f x - g x)) * ϕ x‖ ≤
    A * volume.real (ball x r) * iLipNorm ϕ x r * (1 + dist_{x, r} f g) ^ (- τ)

export IsCancellative (norm_integral_exp_le)

/-- The "volume function" `V`. Note that we will need to assume
`IsFiniteMeasureOnCompacts` and `ProperSpace` to actually know that this volume is finite. -/
def Real.vol {X : Type*} [PseudoMetricSpace X] [MeasureSpace X] (x y : X) : ℝ :=
  volume.real (ball x (dist x y))

open Real (vol)
open Function

/-- The constant used twice in the definition of the Calderon-Zygmund kernel. -/
@[simp] def C_K (a : ℝ) : ℝ := 2 ^ a ^ 3

/-- `K` is a one-sided Calderon-Zygmund kernel
In the formalization `K x y` is defined everywhere, even for `x = y`. The assumptions on `K` show
that `K x x = 0`. -/
class IsCZKernel (a : ℝ) (K : X → X → ℂ) : Prop where
  measurable : Measurable (uncurry K)
  norm_le_vol_inv (x y : X) : ‖K x y‖ ≤ C_K a / vol x y
  norm_sub_le {x y y' : X} (h : 2 /-* A-/ * dist y y' ≤ dist x y) :
    ‖K x y - K x y'‖ ≤ (dist y y' / dist x y) ^ a⁻¹ * (C_K a / vol x y)
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

/-- An operator has strong type (p, q) if it is bounded as an operator on L^p → L^q.
We write `HasStrongType T μ ν p p' c` to say that `T` has strong type (p, q) w.r.t. measures `μ`, `ν` and constant `c`.  -/
def HasStrongType {E E' α α' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → E) → (α' → E'))
    (μ : Measure α) (ν : Measure α') (p p' : ℝ≥0∞) (c : ℝ≥0) : Prop :=
  ∀ f : α → E, Memℒp f p μ → AEStronglyMeasurable (T f) ν ∧ snorm (T f) p' ν ≤ c * snorm f p μ

-- todo: define `HasWeakType`

/-- A weaker version of `HasStrongType`, where we add additional assumptions on the function `f`.
Note(F): I'm not sure if this is an equivalent characterization of having weak type (p, q) -/
def HasBoundedStrongType {E E' α α' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → E) → (α' → E'))
    (μ : Measure α) (ν : Measure α') (p p' : ℝ≥0∞) (c : ℝ≥0) : Prop :=
  ∀ f : α → E, Memℒp f p μ → snorm f ∞ μ < ∞ → μ (support f) < ∞ →
  AEStronglyMeasurable (T f) ν ∧ snorm (T f) p' ν ≤ c * snorm f p μ

set_option linter.unusedVariables false in
/-- The associated nontangential Calderon Zygmund operator `T_*` -/
def ANCZOperator (K : X → X → ℂ) (f : X → ℂ) (x : X) : ℝ :=
  ⨆ (R₁ : ℝ) (R₂ : ℝ) (h1 : R₁ < R₂) (x' : X) (h2 : dist x x' ≤ R₁),
  ‖∫ y in {y | dist x' y ∈ Ioo R₁ R₂}, K x' y * f y‖₊ |>.toReal

-- /-- The associated nontangential Calderon Zygmund operator, viewed as a map `L^p → L^p`.
-- Todo: is `T_*f` indeed in L^p if `f` is? Needed at least for `p = 2`. -/
-- def ANCZOperatorLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (K : X → X → ℂ)
--     (f : Lp ℂ p (volume : Measure X)) : Lp ℝ p (volume : Measure X) :=
--   Memℒp.toLp (ANCZOperator K (f : X → ℂ) · |>.toReal) sorry

/-- The generalized Carleson operator `T`, taking values in `ℝ≥0∞`.
Use `ENNReal.toReal` to get the corresponding real number. -/
--TODO: remove the last two suprema?
def CarlesonOperator [FunctionDistances ℝ X] (K : X → X → ℂ) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (Q : Θ X) (R₁ : ℝ) (R₂ : ℝ) (_ : 0 < R₁) (_ : R₁ < R₂),
  ↑‖∫ y in {y | dist x y ∈ Ioo R₁ R₂}, K x y * f y * exp (I * Q y)‖₊


end DoublingMeasure


/-- This is usually the value of the argument `A` in `DoublingMeasure`
and `CompatibleFunctions` -/
@[simp] abbrev defaultA (a : ℝ) : ℝ := 2 ^ a
@[simp] def defaultD (a : ℝ) : ℝ := 2 ^ (100 * a ^ 2)
@[simp] def defaultκ (a : ℝ) : ℝ := 2 ^ (- 10 * a)
@[simp] def defaultZ (a : ℝ) : ℝ := 2 ^ (12 * a)
@[simp] def defaultτ (a : ℝ) : ℝ := a⁻¹


/- A constant used on the boundedness of `T_*`. We generally assume
`HasBoundedStrongType (ANCZOperator K) volume volume 2 2 (C_Ts a)`
throughout this formalization. -/
def C_Ts (a : ℝ) : ℝ≥0 := 2 ^ a ^ 3

/-- Data common through most of chapters 2-9. -/
class PreProofData {X : Type*} (a q : outParam ℝ) (K : outParam (X → X → ℂ))
  (σ₁ σ₂ : outParam (X → ℤ)) (F G : outParam (Set X)) [PseudoMetricSpace X] where
  d : DoublingMeasure X (defaultA a)
  four_le_a : 4 ≤ a
  cf : CompatibleFunctions ℝ X (defaultA a)
  c : IsCancellative X (defaultτ a)
  hasBoundedStrongType_T : HasBoundedStrongType (ANCZOperator K) volume volume 2 2 (C_Ts a)
  measurableSet_F : MeasurableSet F
  measurableSet_G : MeasurableSet G
  measurable_σ₁ : Measurable σ₁
  measurable_σ₂ : Measurable σ₂
  finite_range_σ₁ : Finite (range σ₁)
  finite_range_σ₂ : Finite (range σ₂)
  σ₁_le_σ₂ : σ₁ ≤ σ₂
  Q : SimpleFunc X (Θ X)
  q_mem_Ioc : q ∈ Ioc 1 2


export PreProofData (four_le_a hasBoundedStrongType_T measurableSet_F measurableSet_G
  measurable_σ₁ measurable_σ₂ finite_range_σ₁ finite_range_σ₂ σ₁_le_σ₂ Q q_mem_Ioc)
attribute [instance] PreProofData.d PreProofData.cf PreProofData.c

section ProofData

variable {X : Type*} {a q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [PseudoMetricSpace X] [PreProofData a q K σ₁ σ₂ F G]

variable (X) in
lemma S_spec [PreProofData a q K σ₁ σ₂ F G] : ∃ n : ℕ, ∀ x, -n ≤ σ₁ x ∧ σ₂ x ≤ n := sorry

variable (X) in
open Classical in
def S [PreProofData a q K σ₁ σ₂ F G] : ℤ := Nat.find (S_spec X)

lemma range_σ₁_subset [PreProofData a q K σ₁ σ₂ F G] : range σ₁ ⊆ Icc (- S X) (S X) := sorry

lemma range_σ₂_subset [PreProofData a q K σ₁ σ₂ F G] : range σ₂ ⊆ Icc (- S X) (S X) := sorry

lemma neg_S_mem_or_S_mem [PreProofData a q K σ₁ σ₂ F G] :
    - S X ∈ range σ₁ ∨ S X ∈ range σ₂ := sorry

variable (X) in lemma q_pos : 0 < q := zero_lt_one.trans (q_mem_Ioc X).1
variable (X) in lemma q_nonneg : 0 ≤ q := (q_pos X).le

variable (X) in
/-- `q` as an element of `ℝ≥0`. -/
def nnq : ℝ≥0 := ⟨q, q_nonneg X⟩

end ProofData

class ProofData {X : Type*} (a q : outParam ℝ) (K : outParam (X → X → ℂ))
    (σ₁ σ₂ : outParam (X → ℤ)) (F G : outParam (Set X)) [PseudoMetricSpace X]
    extends PreProofData a q K σ₁ σ₂ F G where
  F_subset : F ⊆ ball (cancelPt X) (defaultD a ^ S X)
  G_subset : G ⊆ ball (cancelPt X) (defaultD a ^ S X)


namespace ShortVariables
-- open this section to get shorter 1-letter names for a bunch of variables

set_option hygiene false
scoped notation "D" => defaultD a
scoped notation "κ" => defaultκ a
scoped notation "Z" => defaultZ a
scoped notation "τ" => defaultτ a
scoped notation "o" => cancelPt X
scoped notation "S" => S X

end ShortVariables

open scoped ShortVariables
variable {X : Type*} {a q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]

/-- the L^∞-normalized τ-Hölder norm. Do we use this for other values of τ? -/
@[nolint unusedArguments]
def hnorm [ProofData a q K σ₁ σ₂ F G] (ϕ : X → ℂ) (x₀ : X) (R : ℝ≥0) : ℝ≥0∞ :=
  ⨆ (x ∈ ball x₀ R), (‖ϕ x‖₊ : ℝ≥0∞) +
  R ^ τ * ⨆ (x ∈ ball x₀ R) (y ∈ ball x₀ R) (_ : x ≠ y), (‖ϕ x - ϕ y‖₊ / (nndist x y) ^ τ : ℝ≥0∞)

/-! Lemma 2.1.1 -/

-- Note: See also/prove card_le_of_le_dist in DoublingMeasure.
lemma mk_le_of_le_dist {x₀ : X} {r R : ℝ} (hr : 0 < r) {f : Θ X} {k : ℕ}
    {𝓩 : Set (Θ X)} (h𝓩 : 𝓩 ⊆ ball_{x₀, R} f (r * 2 ^ k))
    (h2𝓩 : ∀ z z', z ∈ 𝓩 → z' ∈ 𝓩 → z ≠ z' → r ≤ dist_{x₀, R} z z') :
    Cardinal.mk 𝓩 ≤ 2 ^ (k * ⌊a⌋₊) := sorry

-- the following two lemma should follow easily from `mk_le_of_le_dist`.

lemma card_le_of_le_dist' {x₀ : X} {r R : ℝ} (hr : 0 < r) {f : Θ X} {k : ℕ}
    {𝓩 : Set (Θ X)} (h𝓩 : 𝓩 ⊆ ball_{x₀, R} f (r * 2 ^ k))
    (h2𝓩 : ∀ z z', z ∈ 𝓩 → z' ∈ 𝓩 → z ≠ z' → r ≤ dist_{x₀, R} z z') :
    Nat.card 𝓩 ≤ 2 ^ (k * ⌊a⌋₊) := sorry

lemma finite_of_le_dist {x₀ : X} {r R : ℝ} (hr : 0 < r) {f : Θ X} {k : ℕ}
    {𝓩 : Set (Θ X)} (h𝓩 : 𝓩 ⊆ ball_{x₀, R} f (r * 2 ^ k))
    (h2𝓩 : ∀ z z', z ∈ 𝓩 → z' ∈ 𝓩 → z ≠ z' → r ≤ dist_{x₀, R} z z') :
    𝓩.Finite := sorry
