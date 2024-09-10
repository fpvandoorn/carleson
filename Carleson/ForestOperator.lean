import Carleson.Forest
import Carleson.HardyLittlewood

open ShortVariables TileStructure
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
  {n : ℕ} {t : Forest X n} {u u₁ u₂ p : 𝔓 X} {x x' : X} {𝔖 : Set (𝔓 X)} {f f₁ f₂ g g₁ g₂ : X → ℂ}
  {I J L : Grid X}
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

noncomputable section

open Set MeasureTheory Metric Function Complex Bornology TileStructure Classical
open scoped NNReal ENNReal ComplexConjugate

namespace TileStructure.Forest

/-! ## Section 7.1 and Lemma 7.1.3 -/

variable (t) in
/-- The definition `σ(u, x)` given in Section 7.1.
We may assume `u ∈ t.𝔘` whenever proving things about this definition. -/
def σ (u : 𝔓 X) (x : X) : Finset ℤ := .image 𝔰 { p | p ∈ t.𝔗 u ∧ x ∈ E p }

/- Maybe we should try to avoid using \overline{σ} and \underline{σ} in Lean:
I don't think the set is always non-empty(?) -/
-- def σMax (u : 𝔓 X) (x : X) : ℤ :=
--  Finset.image 𝔰 { p | p ∈ t.𝔗 u ∧ x ∈ E p } |>.max' sorry

/-- The definition of `𝓙₀(𝔖), defined above Lemma 7.1.2 -/
def 𝓙₀ (𝔖 : Set (𝔓 X)) : Set (Grid X) :=
  { J : Grid X | s J = - S ∨ ∀ p ∈ 𝔖, ¬ (𝓘 p : Set X) ⊆ ball (c J)  (100 * D ^ (s J + 1)) }

/-- The definition of `𝓙(𝔖), defined above Lemma 7.1.2 -/
def 𝓙 (𝔖 : Set (𝔓 X)) : Set (Grid X) :=
  { x | Maximal (· ∈ 𝓙₀ 𝔖) x}

/-- The definition of `𝓛₀(𝔖), defined above Lemma 7.1.2 -/
def 𝓛₀ (𝔖 : Set (𝔓 X)) : Set (Grid X) :=
  { L : Grid X | s L = - S ∨ (∃ p ∈ 𝔖, L ≤ 𝓘 p) ∧ ∀ p ∈ 𝔖, ¬ 𝓘 p ≤ L }

/-- The definition of `𝓛(𝔖), defined above Lemma 7.1.2 -/
def 𝓛 (𝔖 : Set (𝔓 X)) : Set (Grid X) :=
  { x | Maximal (· ∈ 𝓛₀ 𝔖) x}

/-- The projection operator `P_𝓒 f(x)`, given above Lemma 7.1.3.
In lemmas the `c` will be pairwise disjoint on `C`. -/
def approxOnCube (C : Set (Grid X)) (f : X → E') (x : X) : E' :=
  ∑ J ∈ { p | p ∈ C }, (J : Set X).indicator (fun _ ↦ ⨍ y, f y) x

/-- The definition `I_i(x)`, given above Lemma 7.1.3.
The cube of scale `s` that contains `x`. There is at most 1 such cube, if it exists. -/
def cubeOf (i : ℤ) (x : X) : Grid X :=
  Classical.epsilon (fun I ↦ x ∈ I ∧ s I = i)

/-- The definition `T_𝓝^θ f(x)`, given in (7.1.3).
For convenience, the suprema are written a bit differently than in the blueprint
(avoiding `cubeOf`), but this should be equivalent.
This is `0` if `x` doesn't lie in a cube. -/
def nontangentialMaximalFunction (θ : Θ X) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (I : Grid X) (_ : x ∈ I) (x' ∈ I) (s₂ ∈ Ioc (s I) S) (_ : D ^ (s₂ - 1) ≤ upperRadius Q θ x'),
  ‖∑ i ∈ Icc (s I) s₂, ∫ y, Ks i x' y * f y‖₊

variable (t) in
/-- The operator `S_{1,𝔲} f(x)`, given in (7.1.4). -/
def boundaryOperator (u : 𝔓 X) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ∑ I : Grid X, (I : Set X).indicator (x := x) fun _ ↦
  ∑ J ∈ { J | J ∈ 𝓙 (t.𝔗 u) ∧ (J : Set X) ⊆ ball (c I) (16 * D ^ (s I)) ∧ s J ≤ s I },
  D ^ ((s J - s I) / a) / volume (ball (c I) (16 * D ^ (s I))) * ∫⁻ y in J, ‖f y‖₊

/-- The indexing set for the collection of balls 𝓑, defined above Lemma 7.1.3. -/
def 𝓑 : Set (ℕ × Grid X) := Icc 0 (S + 5) ×ˢ univ

/-- The radius function for the collection of balls 𝓑, defined above Lemma 7.1.3. -/
def r𝓑 (z : ℕ × Grid X) : ℝ := 2 ^ z.1 * D ^ s z.2

/-- Lemma 7.1.1, freely translated. -/
lemma convex_scales (hu : u ∈ t.𝔘) : OrdConnected (t.σ u x : Set ℤ) := sorry

/-- Part of Lemma 7.1.2 -/
@[simp]
lemma biUnion_𝓙 : ⋃ J ∈ 𝓙 𝔖, J = ⋃ I : Grid X, (I : Set X) := by
  sorry

/-- Part of Lemma 7.1.2 -/
lemma pairwiseDisjoint_𝓙 : (𝓙 𝔖).PairwiseDisjoint (fun I ↦ (I : Set X)) := by
  sorry

/-- Part of Lemma 7.1.2 -/
@[simp]
lemma biUnion_𝓛 : ⋃ J ∈ 𝓛 𝔖, J = ⋃ I : Grid X, (I : Set X) := by
  sorry

/-- Part of Lemma 7.1.2 -/
lemma pairwiseDisjoint_𝓛 : (𝓛 𝔖).PairwiseDisjoint (fun I ↦ (I : Set X)) := by
  sorry

/-- The constant used in `first_tree_pointwise`.
Has value `10 * 2 ^ (105 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C7_1_4 (a : ℕ) : ℝ≥0 := 10 * 2 ^ (105 * (a : ℝ) ^ 3)

/-- Lemma 7.1.4 -/
lemma first_tree_pointwise (hu : u ∈ t.𝔘) (hL : L ∈ 𝓛 (t.𝔗 u)) (hx : x ∈ L) (hx' : x' ∈ L)
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) :
    ‖∑ i in t.σ u x, ∫ y, (exp (.I * (- 𝒬 u y + Q x y + 𝒬 u x - Q x x)) - 1) * Ks i x y * f y ‖₊ ≤
    C7_1_4 a * MB volume 𝓑 (c ·.2) r𝓑 (approxOnCube (𝓙 (t.𝔗 u)) (‖f ·‖)) x' := by
  sorry

/-- Lemma 7.1.5 -/
lemma second_tree_pointwise (hu : u ∈ t.𝔘) (hL : L ∈ 𝓛 (t.𝔗 u)) (hx : x ∈ L) (hx' : x' ∈ L)
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) :
    ‖∑ i in t.σ u x, ∫ y, Ks i x y * approxOnCube (𝓙 (t.𝔗 u)) f y‖₊ ≤
    nontangentialMaximalFunction (𝒬 u) (approxOnCube (𝓙 (t.𝔗 u)) f) x' := by
  sorry

/-- The constant used in `third_tree_pointwise`.
Has value `2 ^ (151 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C7_1_6 (a : ℕ) : ℝ≥0 := 2 ^ (151 * (a : ℝ) ^ 3)

/-- Lemma 7.1.6 -/
lemma third_tree_pointwise (hu : u ∈ t.𝔘) (hL : L ∈ 𝓛 (t.𝔗 u)) (hx : x ∈ L) (hx' : x' ∈ L)
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) :
    ‖∑ i in t.σ u x, ∫ y, Ks i x y * (f y - approxOnCube (𝓙 (t.𝔗 u)) f y)‖₊ ≤
    C7_1_6 a * t.boundaryOperator u (approxOnCube (𝓙 (t.𝔗 u)) (‖f ·‖)) x' := by
  sorry

/-- The constant used in `pointwise_tree_estimate`.
Has value `2 ^ (151 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C7_1_3 (a : ℕ) : ℝ≥0 := 2 ^ (151 * (a : ℝ) ^ 3)

/-- Lemma 7.1.3. -/
lemma pointwise_tree_estimate (hu : u ∈ t.𝔘) (hL : L ∈ 𝓛 (t.𝔗 u)) (hx : x ∈ L) (hx' : x' ∈ L)
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) :
    ‖carlesonSum (t.𝔗 u) (fun y ↦ exp (.I * - 𝒬 u y) * f y) x‖₊ ≤
    C7_1_3 a * (MB volume 𝓑 (c ·.2) r𝓑 (approxOnCube (𝓙 (t.𝔗 u)) (‖f ·‖)) x' +
    t.boundaryOperator u (approxOnCube (𝓙 (t.𝔗 u)) (‖f ·‖)) x' +
    nontangentialMaximalFunction (𝒬 u) (approxOnCube (𝓙 (t.𝔗 u)) f) x'):= by
  set g := approxOnCube (𝓙 (t.𝔗 u)) (‖f ·‖)
  sorry


/-! ## Section 7.2 and Lemma 7.2.1 -/

/-- The constant used in `nontangential_operator_bound`.
Has value `2 ^ (103 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C7_2_2 (a : ℕ) : ℝ≥0 := 2 ^ (103 * (a : ℝ) ^ 3)

/-- Lemma 7.2.2. -/
lemma nontangential_operator_bound
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) (θ : Θ X) :
    eLpNorm (nontangentialMaximalFunction θ f · |>.toReal) 2 volume ≤ eLpNorm f 2 volume := by
  sorry

/-- Lemma 7.2.4. -/
lemma boundary_overlap (I : Grid X) :
    Finset.card { J | s J = s I ∧ ¬ Disjoint (ball (c I) (4 * D ^ s I)) (ball (c J) (4 * D ^ s J)) }
    ≤ 2 ^ (9 * a) := by
  sorry

/-- Lemma 7.2.3. -/
lemma boundary_operator_bound
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) (hu : u ∈ t.𝔘) :
    eLpNorm (boundaryOperator t u f · |>.toReal) 2 volume ≤ eLpNorm f 2 volume := by
  sorry

/-- The constant used in `nontangential_operator_bound`.
Has value `2 ^ (104 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C7_2_1 (a : ℕ) : ℝ≥0 := 2 ^ (104 * (a : ℝ) ^ 3)

/-- Lemma 7.2.1. -/
lemma tree_projection_estimate
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f)
    (hg : IsBounded (range g)) (h2g : HasCompactSupport g) (hu : u ∈ t.𝔘) :
    ‖∫ x, conj (g x) * carlesonSum (t.𝔗 u) f x‖₊ ≤
    C7_2_1 a * eLpNorm (approxOnCube (𝓙 (t.𝔗 u)) (‖f ·‖)) 2 volume *
    eLpNorm (approxOnCube (𝓛 (t.𝔗 u)) (‖g ·‖)) 2 volume := by
  sorry

/-! ## Section 7.3 and Lemma 7.3.1 -/

/-- The constant used in `local_dens1_tree_bound`.
Has value `2 ^ (101 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C7_3_2 (a : ℕ) : ℝ≥0 := 2 ^ (101 * (a : ℝ) ^ 3)

/-- Lemma 7.3.2. -/
lemma local_dens1_tree_bound (hu : u ∈ t.𝔘) (hL : L ∈ 𝓛 (t.𝔗 u)) :
    volume (L ∩ ⋃ (p ∈ t.𝔗 u), E p) ≤ C7_3_2 a * dens₁ (t.𝔗 u) * volume (L : Set X) := by
  sorry

/-- The constant used in `local_dens2_tree_bound`.
Has value `2 ^ (200 * a ^ 3 + 19)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
-- feel free to modify the constant to something simpler.
def C7_3_3 (a : ℕ) : ℝ≥0 := 2 ^ (201 * (a : ℝ) ^ 3)

/-- Lemma 7.3.3. -/
lemma local_dens2_tree_bound (hJ : J ∈ 𝓙 (t.𝔗 u)) {q : 𝔓 X} (hq : q ∈ t.𝔗 u)
    (hJq : ¬ Disjoint (J : Set X) (𝓘 q)) :
    volume (F ∩ J) ≤ C7_3_3 a * dens₂ (t.𝔗 u) * volume (J : Set X) := by
  sorry

/-- The constant used in `density_tree_bound1`.
Has value `2 ^ (155 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C7_3_1_1 (a : ℕ) : ℝ≥0 := 2 ^ (155 * (a : ℝ) ^ 3)

/-- First part of Lemma 7.3.1. -/
lemma density_tree_bound1
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f)
    (hg : IsBounded (range g)) (h2g : HasCompactSupport g) (hu : u ∈ t.𝔘) :
    ‖∫ x, conj (g x) * carlesonSum (t.𝔗 u) f x‖₊ ≤
    C7_3_1_1 a *  dens₁ (t.𝔗 u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume * eLpNorm g 2 volume := by
  sorry

/-- The constant used in `density_tree_bound2`.
Has value `2 ^ (256 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C7_3_1_2 (a : ℕ) : ℝ≥0 := 2 ^ (256 * (a : ℝ) ^ 3)

/-- Second part of Lemma 7.3.1. -/
lemma density_tree_bound2
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) (h3f : ∀ x, ‖f x‖ ≤ F.indicator 1 x)
    (hg : IsBounded (range g)) (h2g : HasCompactSupport g) (hu : u ∈ t.𝔘) :
    ‖∫ x, conj (g x) * carlesonSum (t.𝔗 u) f x‖₊ ≤
    C7_3_1_2 a * dens₁ (t.𝔗 u) ^ (2 : ℝ)⁻¹ * dens₂ (t.𝔗 u) ^ (2 : ℝ)⁻¹ *
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  sorry

/-! ## Section 7.4 except Lemmas 4-6 -/

/-- The definition of `Tₚ*g(x), defined above Lemma 7.4.1 -/
def adjointCarleson (p : 𝔓 X) (f : X → ℂ) (x : X) : ℂ :=
  ∫ y in E p, conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x)) * f y

/-- The definition of `T_ℭ*g(x), defined at the bottom of Section 7.4 -/
def adjointCarlesonSum (ℭ : Set (𝔓 X)) (f : X → ℂ) (x : X) : ℂ :=
  ∑ p ∈ {p | p ∈ ℭ}, adjointCarleson p f x

variable (t) in
/-- The operator `S_{2,𝔲} f(x)`, given above Lemma 7.4.3. -/
def adjointBoundaryOperator (u : 𝔓 X) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ‖adjointCarlesonSum (t.𝔗 u) f x‖₊ + MB volume (𝓑 (X := X)) (c ·.2) r𝓑 f x + ‖f x‖₊

variable (t u₁ u₂) in
/-- The set `𝔖` defined in the proof of Lemma 7.4.4.
We append a subscript 0 to distinguish it from the section variable. -/
def 𝔖₀ : Set (𝔓 X) := { p ∈ t.𝔗 u₁ ∪ t.𝔗 u₂ | 2 ^ ((Z : ℝ) * n / 2) ≤ dist_(p) (𝒬 u₁) (𝒬 u₂) }

/-- Part 1 of Lemma 7.4.1.
Todo: update blueprint with precise properties needed on the function. -/
lemma adjoint_tile_support1 (hf : IsBounded (range f)) (h2f : HasCompactSupport f) :
    adjointCarleson p f =
    (ball (𝔠 p) (5 * D ^ 𝔰 p)).indicator (adjointCarleson p ((𝓘 p : Set X).indicator f)) := by
  sorry

/-- Part 2 of Lemma 7.4.1.
Todo: update blueprint with precise properties needed on the function. -/
lemma adjoint_tile_support2 (hu : u ∈ t.𝔘) (hp : p ∈ t.𝔗 u)
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) :
    adjointCarleson p f =
    (𝓘 p : Set X).indicator (adjointCarleson p ((𝓘 p : Set X).indicator f)) := by
  sorry

/-- The constant used in `adjoint_tree_estimate`.
Has value `2 ^ (155 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C7_4_2 (a : ℕ) : ℝ≥0 := 2 ^ (155 * (a : ℝ) ^ 3)

/-- Lemma 7.4.2. -/
lemma adjoint_tree_estimate (hf : IsBounded (range f)) (h2f : HasCompactSupport f) :
    eLpNorm (adjointCarlesonSum (t.𝔗 u) f) 2 volume ≤
    C7_4_2 a * dens₁ (t.𝔗 u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
  sorry

/-- The constant used in `adjoint_tree_control`.
Has value `2 ^ (156 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C7_4_3 (a : ℕ) : ℝ≥0 := 2 ^ (155 * (a : ℝ) ^ 3)

/-- Lemma 7.4.3. -/
lemma adjoint_tree_control (hu : u ∈ t.𝔘) (hf : IsBounded (range f)) (h2f : HasCompactSupport f) :
    eLpNorm (adjointBoundaryOperator t u f · |>.toReal) 2 volume ≤
    C7_4_3 a * eLpNorm f 2 volume := by
  sorry

/-- Part 2 of Lemma 7.4.7. -/
lemma 𝔗_subset_𝔖₀ (hu₁ : u₁ ∈ t.𝔘) (hu₂ : u₂ ∈ t.𝔘) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) : t.𝔗 u₁ ⊆ 𝔖₀ t u₁ u₂ := by
  sorry

/-- Part 1 of Lemma 7.4.7. -/
lemma overlap_implies_distance (hu₁ : u₁ ∈ t.𝔘) (hu₂ : u₂ ∈ t.𝔘) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hp : p ∈ t.𝔗 u₁ ∪ t.𝔗 u₂)
    (hpu₁ : ¬ Disjoint (𝓘 p : Set X) (𝓘 u₁)) : p ∈ 𝔖₀ t u₁ u₂ := by
  sorry

/-! ## Section 7.5 -/

variable (t u₁ u₂) in
/-- The definition `𝓙'` at the start of Section 7.5.1.
We use a different notation to distinguish it from the 𝓙' used in Section 7.6 -/
def 𝓙₅ : Set (Grid X) := {J ∈ 𝓙 (𝔖₀ t u₁ u₂) | J ≤ 𝓘 u₁ }

/-! ### Subsection 7.5.1 and Lemma 7.5.2 -/

/-- Part of Lemma 7.5.1. -/
lemma union_𝓙₅ (hu₁ : u₁ ∈ t.𝔘) (hu₂ : u₂ ∈ t.𝔘) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) :
    ⋃ J ∈ 𝓙₅ t u₁ u₂, (J : Set X) = 𝓘 u₁ := by
  sorry

/-- Part of Lemma 7.5.1. -/
lemma pairwiseDisjoint_𝓙₅ (hu₁ : u₁ ∈ t.𝔘) (hu₂ : u₂ ∈ t.𝔘) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) :
    (𝓙₅ t u₁ u₂).PairwiseDisjoint (fun I ↦ (I : Set X)) := by
  sorry


/-! ### Subsection 7.5.2 and Lemma 7.5.4 -/



/-! ### Subsection 7.5.3 and Lemma 7.4.5 -/

/-- The constant used in `correlation_distant_tree_parts`.
Has value `2 ^ (541 * a ^ 3 - Z * n / (4 * a ^ 2 + 2 * a ^ 3))` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C7_4_5 (a n : ℕ) : ℝ≥0 := 2 ^ (541 * (a : ℝ) ^ 3 - Z * n / (4 * a ^ 2 + 2 * a ^ 3))

lemma correlation_distant_tree_parts (hu₁ : u₁ ∈ t.𝔘) (hu₂ : u₂ ∈ t.𝔘) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) :
    ‖∫ x, adjointCarlesonSum (t.𝔗 u₁) g₁ x *
    conj (adjointCarlesonSum (t.𝔗 u₂ ∩ 𝔖₀ t u₁ u₂) g₂ x)‖₊ ≤
    C7_4_5 a n *
    eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₁ g₁) · |>.toReal) 2 volume *
    eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₂ g₂) · |>.toReal) 2 volume := by
  sorry

/-! ## Section 7.6 and Lemma 7.4.6 -/

/-- The constant used in `correlation_near_tree_parts`.
Has value `2 ^ (541 * a ^ 3 - Z * n / (4 * a ^ 2 + 2 * a ^ 3))` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C7_4_6 (a n : ℕ) : ℝ≥0 := 2 ^ (222 * (a : ℝ) ^ 3 - Z * n * 2 ^ (-10 * (a : ℝ)))

lemma correlation_near_tree_parts (hu₁ : u₁ ∈ t.𝔘) (hu₂ : u₂ ∈ t.𝔘) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) :
    ‖∫ x, adjointCarlesonSum (t.𝔗 u₁) g₁ x *
    conj (adjointCarlesonSum (t.𝔗 u₂ \ 𝔖₀ t u₁ u₂) g₂ x)‖₊ ≤
    C7_4_5 a n *
    eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₁ g₁) · |>.toReal) 2 volume *
    eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₂ g₂) · |>.toReal) 2 volume := by
  sorry


/-! ## Lemmas 7.4.4 -/

/-- The constant used in `correlation_separated_trees`.
Has value `2 ^ (550 * a ^ 3 - 3 * n)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C7_4_4 (a n : ℕ) : ℝ≥0 := 2 ^ (550 * (a : ℝ) ^ 3 - 3 * n)

lemma correlation_separated_trees_of_subset (hu₁ : u₁ ∈ t.𝔘) (hu₂ : u₂ ∈ t.𝔘) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) :
    ‖∫ x, adjointCarlesonSum (t.𝔗 u₁) g₁ x * conj (adjointCarlesonSum (t.𝔗 u₂) g₂ x)‖₊ ≤
    C7_4_4 a n *
    eLpNorm
      ((𝓘 u₁ ∩ 𝓘 u₂ : Set X).indicator (adjointBoundaryOperator t u₁ g₁) · |>.toReal) 2 volume *
    eLpNorm
      ((𝓘 u₁ ∩ 𝓘 u₂ : Set X).indicator (adjointBoundaryOperator t u₂ g₂) · |>.toReal) 2 volume := by
  sorry

/-- Lemma 7.4.4. -/
lemma correlation_separated_trees (hu₁ : u₁ ∈ t.𝔘) (hu₂ : u₂ ∈ t.𝔘) (hu : u₁ ≠ u₂)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) :
    ‖∫ x, adjointCarlesonSum (t.𝔗 u₁) g₁ x * conj (adjointCarlesonSum (t.𝔗 u₂) g₂ x)‖₊ ≤
    C7_4_4 a n *
    eLpNorm
      ((𝓘 u₁ ∩ 𝓘 u₂ : Set X).indicator (adjointBoundaryOperator t u₁ g₁) · |>.toReal) 2 volume *
    eLpNorm
      ((𝓘 u₁ ∩ 𝓘 u₂ : Set X).indicator (adjointBoundaryOperator t u₂ g₂) · |>.toReal) 2 volume := by
  sorry


/-! ## Section 7.7 and Proposition 2.0.4 -/

end TileStructure.Forest

/-- The constant used in `forest_operator`.
Has value `2 ^ (432 * a ^ 3 - (q - 1) / q * n)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C2_0_4 (a q : ℝ) (n : ℕ) : ℝ≥0 := 2 ^ (432 * a ^ 3 - (q - 1) / q * n)

theorem forest_operator {n : ℕ} (𝔉 : Forest X n) {f g : X → ℂ}
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hg : Measurable g)
    (h2g : IsBounded (support g)) :
    ‖∫ x, conj (g x) * ∑ u ∈ { p | p ∈ 𝔉.𝔘 }, carlesonSum (𝔉.𝔗 u) f x‖₊ ≤
    C2_0_4 a q n * (dens₂ (X := X) (⋃ u ∈ 𝔉.𝔘, 𝔉.𝔗 u)) ^ (q⁻¹ - 2⁻¹) *
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  sorry
