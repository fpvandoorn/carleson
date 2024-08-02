import Carleson.Forest
import Carleson.HardyLittlewood

open ShortVariables TileStructure
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
  {n : ℕ} {t : Forest X n} {u : 𝔓 X} {x x' : X} {G : Set (𝔓 X)} {f : X → ℂ}
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
def σ (u : 𝔓 X) (x : X) : Finset ℤ := Finset.univ.filter (fun p ↦ p ∈ t.𝔗 u ∧ x ∈ E p) |>.image 𝔰

/- Maybe we should try to avoid using \overline{σ} and \underline{σ} in Lean:
I don't think the set is always non-empty(?) -/
-- def σMax (u : 𝔓 X) (x : X) : ℤ :=
--   Finset.univ.filter (fun p ↦ p ∈ t.𝔗 u ∧ x ∈ E p) |>.image 𝔰 |>.max' sorry

/-- Lemma 7.1.1, freely translated. -/
lemma convex_scales (hu : u ∈ t.𝔘) : OrdConnected (t.σ u x : Set ℤ) := sorry

/-- The definition of `𝓙₀(G), defined above Lemma 7.1.2 -/
def 𝓙₀ (G : Set (𝔓 X)) : Set (Grid X) :=
  {J : Grid X | s J = - S ∨ ∀ p ∈ G, ¬ (𝓘 p : Set X) ⊆ ball (c J)  (100 * D ^ (s J + 1)) }

/-- The definition of `𝓙(G), defined above Lemma 7.1.2 -/
def 𝓙 (G : Set (𝔓 X)) : Set (Grid X) :=
  maximals (·≤·) (𝓙₀ G)

/-- The definition of `𝓛₀(G), defined above Lemma 7.1.2 -/
def 𝓛₀ (G : Set (𝔓 X)) : Set (Grid X) :=
  { L : Grid X | s L = - S ∨ (∃ p ∈ G, L ≤ 𝓘 p) ∧ ∀ p ∈ G, ¬ 𝓘 p ≤ L }

/-- The definition of `𝓛(G), defined above Lemma 7.1.2 -/
def 𝓛 (G : Set (𝔓 X)) : Set (Grid X) :=
  maximals (·≤·) (𝓛₀ G)

/-- Part of Lemma 7.1.2 -/
@[simp]
lemma biUnion_𝓙 : ⋃ J ∈ 𝓙 G, J = ⋃ I : Grid X, (I : Set X) := by
  sorry

/-- Part of Lemma 7.1.2 -/
lemma pairwiseDisjoint_𝓙 : (𝓙 G).PairwiseDisjoint (fun I ↦ (I : Set X)) := by
  sorry

/-- Part of Lemma 7.1.2 -/
@[simp]
lemma biUnion_𝓛 : ⋃ J ∈ 𝓛 G, J = ⋃ I : Grid X, (I : Set X) := by
  sorry

/-- Part of Lemma 7.1.2 -/
lemma pairwiseDisjoint_𝓛 : (𝓛 G).PairwiseDisjoint (fun I ↦ (I : Set X)) := by
  sorry

/-- The projection operator `P_𝓒 f(x)`, given above Lemma 7.1.3.
In lemmas the `c` will be pairwise disjoint on `C`. -/
def approxOnCube (C : Set (Grid X)) (f : X → E') (x : X) : E' :=
  ∑ J ∈ Finset.univ.filter (· ∈ C), (J : Set X).indicator (fun _ ↦ ⨍ y, f y) x

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
def auxiliaryOperator1 (u : 𝔓 X) (f : X → ℝ) (x : X) : ℝ≥0∞ :=
  ∑ I : Grid X, (I : Set X).indicator (x := x) fun _ ↦
  ∑ J ∈ Finset.univ.filter fun J ↦
    J ∈ 𝓙 (t.𝔗 u) ∧ (J : Set X) ⊆ ball (c I) (16 * D ^ (s I)) ∧ s J ≤ s I,
  D ^ ((s J - s I) / a) / volume (ball (c I) (16 * D ^ (s I))) * ∫⁻ y in J, ‖f y‖₊

/-- The indexing set for the collection of balls 𝓑, defined above Lemma 7.1.3. -/
def 𝓑 : Set (ℕ × Grid X) := Icc 0 (S + 5) ×ˢ univ

/-- The radius function for the collection of balls 𝓑, defined above Lemma 7.1.3. -/
def r𝓑 (z : ℕ × Grid X) : ℝ := 2 ^ z.1 * D ^ s z.2

-- def 𝓑 : Set (Set X) := (fun (i, I) ↦ ball (c I) (2 ^ i * D ^ s I)) '' Icc 0 (S + 5) ×ˢ univ

/-- The constant used in `first_tree_pointwise`.
Has value `10 * 2 ^ (105 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C7_1_4 (a : ℝ) : ℝ≥0 := 10 * 2 ^ (105 * a ^ 3)

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
def C7_1_6 (a : ℝ) : ℝ≥0 := 2 ^ (151 * a ^ 3)

/-- Lemma 7.1.6 -/
lemma third_tree_pointwise (hu : u ∈ t.𝔘) (hL : L ∈ 𝓛 (t.𝔗 u)) (hx : x ∈ L) (hx' : x' ∈ L)
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) :
    ‖∑ i in t.σ u x, ∫ y, Ks i x y * (f y - approxOnCube (𝓙 (t.𝔗 u)) f y)‖₊ ≤
    C7_1_6 a * t.auxiliaryOperator1 u (approxOnCube (𝓙 (t.𝔗 u)) (‖f ·‖)) x' := by
  sorry

/-- The constant used in `pointwise_tree_estimate`.
Has value `2 ^ (151 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C7_1_3 (a : ℝ) : ℝ≥0 := 2 ^ (151 * a ^ 3)

/-- Lemma 7.1.3. -/
lemma pointwise_tree_estimate (hu : u ∈ t.𝔘) (hL : L ∈ 𝓛 (t.𝔗 u)) (hx : x ∈ L) (hx' : x' ∈ L)
    (hf : IsBounded (range f)) (h2f : HasCompactSupport f) :
    ‖∑ p ∈ Finset.univ.filter (· ∈ t.𝔗 u), carlesonOn p (fun y ↦ exp (.I * - 𝒬 u y) * f y) x‖₊ ≤
    C7_1_3 a * (MB volume 𝓑 (c ·.2) r𝓑 (approxOnCube (𝓙 (t.𝔗 u)) (‖f ·‖)) x' +
    t.auxiliaryOperator1 u (approxOnCube (𝓙 (t.𝔗 u)) (‖f ·‖)) x' +
    nontangentialMaximalFunction (𝒬 u) (approxOnCube (𝓙 (t.𝔗 u)) f) x'):= by
  set g := approxOnCube (𝓙 (t.𝔗 u)) (‖f ·‖)
  sorry


/-! ## Section 7.2 and Lemma 7.2.1 -/

/- todo: make the argument `a` a natural number to constants everywhere(?) -/

/-! ## Section 7.3 and Lemma 7.3.1 -/



/-! ## Section 7.4 and Lemma 7.4.4 -/


/-! ### Section 7.5 -/
/-! ### Subsection 7.5.1 and Lemma 7.5.2 -/



/-! ### Subsection 7.5.2 and Lemma 7.5.4 -/



/-! ### Subsection 7.5.3 and Lemma 7.4.5 -/



/-! ## Section 7.6 and Lemma 7.4.6 -/



/-! ## Section 7.7 and Proposition 2.0.4 -/

end TileStructure.Forest

/-- The constant used in `forest_operator`.
Has value `2 ^ (432 * a ^ 3 - (q - 1) / q * n)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C2_0_4 (a q : ℝ) (n : ℕ) : ℝ≥0 := 2 ^ (432 * a ^ 3 - (q - 1) / q * n)

theorem forest_operator {n : ℕ} (𝔉 : Forest X n) {f g : X → ℂ}
    (hf : Measurable f) (h2f : ∀ x, ‖f x‖ ≤ F.indicator 1 x) (hg : Measurable g)
    (h2g : IsBounded (support g)) :
    ‖∫ x, conj (g x) * ∑ u ∈ Finset.univ.filter (· ∈ 𝔉.𝔘),
      ∑ p ∈ Finset.univ.filter (· ∈ 𝔉.𝔗 u), T p f x‖₊ ≤
    C2_0_4 a q n * (dens₂ (X := X) (⋃ u ∈ 𝔉.𝔘, 𝔉.𝔗 u)) ^ (q⁻¹ - 2⁻¹) *
    snorm f 2 volume * snorm g 2 volume := by
  sorry
