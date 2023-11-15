import Carleson.HomogeneousType

open MeasureTheory Measure NNReal Metric Complex Set
open scoped ENNReal
noncomputable section


/-! Miscellaneous definitions.
We should move them to separate files once we start proving things about them. -/

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

/-- A quasi metric space with regular/`A`-Lipschitz distance. -/
class Metric.IsRegular (X : Type*) (A : outParam ℝ≥0) [fact : Fact (1 ≤ A)]
    [PseudoQuasiMetricSpace X A]
  where abs_dist_sub_dist_le : ∀ x y y' : X, |dist x y - dist x y'| ≤ A * dist y y'

export Metric.IsRegular (abs_dist_sub_dist_le)

variable {X : Type*} {A : ℝ≥0} [fact : Fact (1 ≤ A)] [IsSpaceOfHomogeneousType X A]

section localOscillation

set_option linter.unusedVariables false in
/-- A type synonym of `C(X, ℂ)` that uses the local oscillation w.r.t. `E` as the metric. -/
def withLocalOscillation (E : Set X) : Type _ := C(X, ℂ)

instance withLocalOscillation.toContinuousMapClass (E : Set X) :
    ContinuousMapClass (withLocalOscillation E) X ℂ :=
  ContinuousMap.toContinuousMapClass

/-- The local oscillation of two functions. -/
def localOscillation (E : Set X) (f g : withLocalOscillation E) : ℝ :=
  ⨆ z : E × E, ‖f z.1 - g z.1 - f z.2 + g z.2‖

/-- The local oscillation on a set `E` gives rise to a pseudo-metric-space structure
  on the continuous functions `X → ℂ`. -/
instance homogeneousPseudoMetric (E : Set X) : PseudoQuasiMetricSpace (withLocalOscillation E) A where
  dist := localOscillation E
  dist_self := by simp [localOscillation]
  dist_comm := by sorry
  dist_triangle := by sorry
  edist_dist := fun x y => by exact ENNReal.coe_nnreal_eq _

variable {E : Set X} {f g : C(X, ℂ)}

def localOscillationBall (E : Set X) (f : C(X, ℂ)) (r : ℝ) : Set C(X, ℂ) :=
  { g : C(X, ℂ) | localOscillation E f g < r }

end localOscillation


/- mathlib is missing Hölder spaces.
Todo:
* Define Hölder spaces
* Define the norm in Hölder spaces
* Show that Hölder spaces are homogeneous -/

/-- A set `𝓠` of (continuous) functions is compatible. -/
class IsCompatible (𝓠 : Set C(X, ℂ)) : Prop where
  localOscillation_two_mul_le {x₁ x₂ : X} {r : ℝ} {f g : C(X, ℂ)} (hf : f ∈ 𝓠) (hg : g ∈ 𝓠)
    (h : dist x₁ x₂ < 2 * r) :
    localOscillation (ball x₂ (2 * r)) f g ≤ A * localOscillation (ball x₁ r) f g
  localOscillation_le_of_subset {x₁ x₂ : X} {r : ℝ} {f g : C(X, ℂ)} (hf : f ∈ 𝓠) (hg : g ∈ 𝓠)
    (h1 : ball x₁ r ⊆ ball x₂ (A * r)) (h2 : A * r ≤ Metric.diam (univ : Set X)) :
    2 * localOscillation (ball x₁ r) f g ≤ localOscillation (ball x₂ (A * r)) f g
  ballsCoverBalls {x : X} {r R : ℝ} :
    BallsCoverBalls (withLocalOscillation (ball x r)) (2 * R) R ⌊A⌋₊

export IsCompatible (localOscillation_two_mul_le localOscillation_le_of_subset ballsCoverBalls)

set_option linter.unusedVariables false in
/-- The inhomogeneous Lipschitz norm on a ball (I'm assuming `R` is the radius of the ball?). -/
def iLipNorm (ϕ : X → ℂ) (x₀ : X) (R : ℝ) : ℝ :=
  (⨆ x ∈ ball x₀ R, ‖ϕ x‖) + R * ⨆ (x : X) (y : X) (h : x ≠ y), ‖ϕ x - ϕ y‖ / nndist x y

/-- 𝓠 is τ-cancellative -/
class IsCancellative (τ : ℝ) (𝓠 : Set C(X, ℂ)) : Prop where
  norm_integral_exp_le {x : X} {r : ℝ} {ϕ : X → ℂ} {K : ℝ≥0} (h1 : LipschitzWith K ϕ)
    (h2 : tsupport ϕ ⊆ ball x r) {f g : C(X, ℂ)} (hf : f ∈ 𝓠) (hg : g ∈ 𝓠) :
    ‖∫ x in ball x r, exp (I * (f x - g x)) * ϕ x‖ ≤
    A * (volume (ball x r)).toReal * iLipNorm ϕ x r * (1 + localOscillation (ball x r) f g) ^ (- τ)

export IsCancellative (norm_integral_exp_le)

/-- The "volume function". Note that we will need to assume
`IsFiniteMeasureOnCompacts` and `ProperSpace` to actually know that this volume is finite. -/
def Real.vol {X : Type*} [PseudoQuasiMetricSpace X A] [MeasureSpace X] (x y : X) : ℝ :=
  ENNReal.toReal (volume (ball x (dist x y)))

open Real (vol)
open Function

/-- `K` is a one-sided `τ`-Calderon-Zygmund kernel
In the formalization `K x y` is defined everywhere, even for `x = y`. The assumptions on `K` show
that `K x x = 0`. -/
class IsCZKernel (τ : ℝ) (K : X → X → ℂ) : Prop where
  norm_le_vol_inv (x y : X) : ‖K x y‖ ≤ (vol x y)⁻¹
  norm_sub_le {x y y' : X} (h : 2 * A * dist y y' ≤ dist x y) :
    ‖K x y - K x y'‖ ≤ (dist y y' / dist x y) ^ τ * (vol x y)⁻¹
  measurable_right (y : X) : Measurable (K · y)
  -- either we should assume this or prove from the other conditions
  measurable : Measurable (uncurry K)

-- to show: K is locally bounded and hence integrable outside the diagonal

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
  ‖∫ y in {y | dist x' y ∈ Ioo R₁ R₂}, K x' y * f y‖

/-- The associated nontangential Calderon Zygmund operator, viewed as a map `L^p → L^p`.
Todo: is `T_*f` indeed in L^p if `f` is? -/
def ANCZOperatorLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (K : X → X → ℂ) (f : Lp ℂ p (volume : Measure X)) :
    Lp ℝ p (volume : Measure X) :=
  Memℒp.toLp (ANCZOperator K (f : X → ℂ)) sorry

set_option linter.unusedVariables false in
/-- The (maximally truncated) polynomial Carleson operator `T`. -/
def CarlesonOperator (K : X → X → ℂ) (𝓠 : Set C(X, ℂ)) (f : X → ℂ) (x : X) : ℝ :=
  ⨆ (Q ∈ 𝓠) (R₁ : ℝ) (R₂ : ℝ) (h1 : R₁ < R₂),
  ‖∫ y in {y | dist x y ∈ Ioo R₁ R₂}, K x y * f y * exp (I * Q y)‖

variable (X) in
/-- A grid structure on `X`.
I expect we prefer `𝓓 : ι → Set X` over `𝓓 : Set (Set X)` -/
class GridStructure (D κ : outParam ℝ) (C : outParam ℝ≥0) where
  ι : Type*
  𝓓 : ι → Set X
  s : ι → ℤ
  x : ι → X
  volume_iUnion_preimage : ∀ σ ∈ range s, volume (⋃ i ∈ s ⁻¹' {σ}, 𝓓 i)ᶜ = 0
  volume_inter_eq_zero {i j} (h1 : i ≠ j) (h2 : s i = s j) : volume (𝓓 i ∩ 𝓓 j) = 0
  fundamental_dyadic {i j} : 𝓓 i ⊆ 𝓓 j ∨ 𝓓 j ⊆ 𝓓 i ∨ Disjoint (𝓓 i) (𝓓 j)
  ball_subset_𝓓 {i} : ball (x i) ((2 * A) ^ (-2 : ℤ) * D ^ s i) ⊆ 𝓓 i
  𝓓_subset_ball {i} : 𝓓 i ⊆ ball (x i) ((2 * A) ^ 2 * D ^ s i)
  small_boundary {i} {t : ℝ≥0} (ht : 0 < t) : volume {x ∈ 𝓓 i | infDist x (𝓓 i)ᶜ ≤ t * D ^ s i } ≤
    C * t ^ κ * volume (𝓓 i)
  -- should the following become axioms? I believe they don't follow from previous axioms.
  -- or maybe Î is only defined when it exists?
  -- next : ι → ι
  -- subset_next {i} : 𝓓 i ⊆ 𝓓 (next i)
  -- s_next : s (next i) = s i + 1

export GridStructure (volume_iUnion_preimage volume_inter_eq_zero fundamental_dyadic
  ball_subset_𝓓 𝓓_subset_ball small_boundary)

variable {D κ : ℝ} {C : ℝ≥0}

section GridStructure

variable [GridStructure X D κ C]

variable (X) in
def ι : Type* := GridStructure.ι X A
def s : ι X → ℤ := GridStructure.s
def 𝓓 : ι X → Set X := GridStructure.𝓓
variable (X) in
def x : ι X → X := GridStructure.x

end GridStructure

instance homogeneousMeasurableSpace [Inhabited X] : MeasurableSpace C(X, ℂ) :=
  let m : PseudoQuasiMetricSpace C(X, ℂ) A :=
    homogeneousPseudoMetric (ball default 1) -- an arbitary ball
  let t : TopologicalSpace C(X, ℂ) := m.toUniformSpace.toTopologicalSpace
  @borel C(X, ℂ) t

/-- A tile structure. Note: compose `𝓘` with `𝓓` to get the `𝓘` of the paper. -/
class TileStructure [Inhabited X] (𝓠 : outParam (Set C(X, ℂ)))
    (D κ : outParam ℝ) (C : outParam ℝ≥0) extends GridStructure X κ D C where
  protected 𝔓 : Type*
  protected 𝓘 : 𝔓 → ι
  Ω : 𝔓 → Set C(X, ℂ)
  measurableSet_Ω : ∀ p, MeasurableSet (Ω p)
  Q : 𝔓 → C(X, ℂ)
  Q_mem : ∀ p, Q p ∈ 𝓠
  union_Ω {i} : ⋃ (p) (_h : 𝓓 (𝓘 p) = 𝓓 i), Ω p = 𝓠
  disjoint_Ω {p p'} (h : p ≠ p') (hp : 𝓓 (𝓘 p) = 𝓓 (𝓘 p')) : Disjoint (Ω p) (Ω p')
  relative_fundamental_dyadic {p p'} (h : 𝓓 (𝓘 p) ⊆ 𝓓 (𝓘 p')) : Disjoint (Ω p) (Ω p') ∨ Ω p' ⊆ Ω p
  localOscillationBall_subset {p} : localOscillationBall (𝓓 (𝓘 p)) (Q p) 5⁻¹ ∩ 𝓠 ⊆ Ω p
  subset_localOscillationBall {p} : Ω p ⊆ localOscillationBall (𝓓 (𝓘 p)) (Q p) 1

export TileStructure (Ω measurableSet_Ω Q Q_mem union_Ω disjoint_Ω
  relative_fundamental_dyadic localOscillationBall_subset subset_localOscillationBall)
-- #print homogeneousMeasurableSpace
-- #print TileStructure
variable [Inhabited X] {𝓠 : Set C(X, ℂ)} [TileStructure 𝓠 D κ C]

variable (X) in
def 𝔓 := TileStructure.𝔓 X A
def 𝓘 : 𝔓 X → ι X := TileStructure.𝓘

/- The set `E` defined in Proposition 2.1. -/
def E (Q' : X → C(X, ℂ)) (σ σ' : X → ℤ) (p : 𝔓 X) : Set X :=
  { x ∈ 𝓓 (𝓘 p) | Q' x ∈ Ω p ∧ s (𝓘 p) ∈ Icc (σ x) (σ' x) }

section T

variable (K : X → X → ℂ) (Q' : X → C(X, ℂ)) (σ σ' : X → ℤ) (ψ : ℝ → ℝ) (p : 𝔓 X) (F : Set X)

/- The operator `T` defined in Proposition 2.1, considered on the set `F`.
It is the map `T ∘ (1_F * ·) : f ↦ T (1_F * f)`, also denoted `T1_F`
The operator `T` in Proposition 2.1 is therefore `applied to `(F := Set.univ)`. -/
def T (f : X → ℂ) : X → ℂ :=
  indicator (E Q' σ σ' p)
    fun x ↦ ∫ y, exp (Q' x x - Q' x y) * K x y * ψ (D ^ (- s (𝓘 p)) * dist x y) * F.indicator f y

lemma Memℒp_T {f : X → ℂ} {q : ℝ≥0∞} (hf : Memℒp f q) : Memℒp (T K Q' σ σ' ψ p F f) q :=
  by sorry

/- The operator `T`, defined on `L^2` maps. -/
def T₂ (f : X →₂[volume] ℂ) : X →₂[volume] ℂ :=
  Memℒp.toLp (T K Q' σ σ' ψ p F f) <| Memℒp_T K Q' σ σ' ψ p F <| Lp.memℒp f

/- The operator `T`, defined on `L^2` maps as a continuous linear map. -/
def TL : (X →₂[volume] ℂ) →L[ℂ] (X →₂[volume] ℂ) where
    toFun := T₂ K Q' σ σ' ψ p F
    map_add' := sorry
    map_smul' := sorry
    cont := sorry

end T

variable (X) in
def TileLike : Type _ := Set X × OrderDual (Set (C(X,ℂ)))

def TileLike.fst (x : TileLike X) : Set X := x.1
def TileLike.snd (x : TileLike X) : Set (C(X,ℂ)) := x.2
instance : PartialOrder (TileLike X) := by dsimp [TileLike]; infer_instance
example (x y : TileLike X) : x ≤ y ↔ x.fst ⊆ y.fst ∧ y.snd ⊆ x.snd := by rfl

def toTileLike (p : 𝔓 X) : TileLike X := (𝓓 (𝓘 p), Ω p)

lemma toTileLike_injective : Injective (fun p : 𝔓 X ↦ toTileLike p) := sorry

instance : PartialOrder (𝔓 X) := PartialOrder.lift toTileLike toTileLike_injective
def smul (a : ℝ) (p : 𝔓 X) : TileLike X :=
  (𝓓 (𝓘 p), localOscillationBall (𝓓 (𝓘 p)) (Q p) a)

def TileLike.toTile (t : TileLike X) : Set (X × C(X,ℂ)) :=
  t.fst ×ˢ t.snd

lemma isAntichain_iff_disjoint (𝔄 : Set (𝔓 X)) :
    IsAntichain (·≤·) (toTileLike (X := X) '' 𝔄) ↔
    ∀ p p', p ∈ 𝔄 → p' ∈ 𝔄 → p ≠ p' →
    Disjoint (toTileLike (X := X) p).toTile (toTileLike p').toTile := sorry

def convexShadow (𝔓' : Set (𝔓 X)) : Set (ι X) :=
  { i | ∃ p p' : 𝔓 X, p ∈ 𝔓' ∧ p' ∈ 𝔓' ∧ (𝓓 (𝓘 p) : Set X) ⊆ 𝓓 i ∧ 𝓓 i ⊆ 𝓓 (𝓘 p') }

def EBar (G : Set X) (Q' : X → C(X,ℂ)) (t : TileLike X) : Set X :=
  { x ∈ t.fst ∩ G | Q' x ∈ t.snd }

def density (G : Set X) (Q' : X → C(X,ℂ)) (𝔓' : Set (𝔓 X)) : ℝ≥0∞ :=
  ⨆ (p ∈ 𝔓') (l ≥ (2 : ℝ≥0)), l ^ (-2 * Real.log A) *
  ⨆ (p' : 𝔓 X) (_h : 𝓘 p' ∈ convexShadow 𝔓') (_h2 : smul l p ≤ smul l p'),
  volume (EBar G Q' (smul l p')) / volume (EBar G Q' (toTileLike p))

/-- Hardy-Littlewood maximal function -/
def maximalFunction {E} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : X → E) (x : X) : ℝ≥0∞ :=
  ⨆ (x' : X) (δ : ℝ) (_hx : x ∈ ball x' δ),
  ⨍⁻ y, ‖f y‖₊ ∂volume.restrict (ball x' δ)

def boundedTiles (F : Set X) (t : ℝ≥0) : Set (𝔓 X) :=
  { p : 𝔓 X | ∃ x ∈ 𝓓 (𝓘 p), maximalFunction (Set.indicator F (1 : X → ℝ)) x ≤ t }

set_option linter.unusedVariables false in
variable (X) in
class SmallBoundaryProperty (η : ℝ) : Prop where
  volume_diff_le : ∃ (C : ℝ≥0) (hC : C > 0), ∀ (x : X) r (δ : ℝ≥0), 0 < r → 0 < δ → δ < 1 →
    volume (ball x ((1 + δ) * r) \ ball x ((1 - δ) * r)) ≤ C * δ ^ η * volume (ball x r)

variable (X) in
structure TileStructure.Tree where
  𝔗 : Set (𝔓 X)
  top : 𝔓 X
  le_top {p : 𝔓 X} (hp : p ∈ 𝔗): smul 4 p ≤ toTileLike top
  ordConnected : OrdConnected 𝔗 -- the convexity condition

def Δ (p : 𝔓 X) (Q'' : C(X, ℂ)) : ℝ := localOscillation (𝓓 (𝓘 p)) (Q p) Q'' + 1

open TileStructure
structure TileStructure.Forest (G : Set X) (Q' : X → C(X,ℂ)) (δ : ℝ) (n : ℕ) where
  I : Set (Tree X)
  disjoint_I : ∀ {i j}, i ∈ I → j ∈ I → Disjoint i.𝔗 j.𝔗
  top_finite (x : X) : {i ∈ I | x ∈ 𝓓 (𝓘 i.top)}.Finite
  card_top_le (x : X) : Nat.card {i ∈ I | x ∈ 𝓓 (𝓘 i.top) } ≤ 2 ^ n * Real.log (n + 1)
  density_le {j} (hj : j ∈ I) : density G Q' (j.𝔗) ≤ (2 : ℝ≥0) ^ (-n : ℤ)
  something {j j'} (hj : j ∈ I) (hj' : j' ∈ I) {p : 𝔓 X} (hp : p ∈ j.𝔗)
    (h2p : 𝓓 (𝓘 p) ⊆ 𝓓 (𝓘 j'.top)) : Δ p (Q j.top) > (2 : ℝ) ^ (3 * n / δ)
