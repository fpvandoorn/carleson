import Carleson.ForestOperator.AlmostOrthogonality

open ShortVariables TileStructure
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
  {n j j' : ℕ} {t : Forest X n} {u u₁ u₂ p : 𝔓 X} {x x' : X} {𝔖 : Set (𝔓 X)}
  {f f₁ f₂ g g₁ g₂ : X → ℂ} {I J J' L : Grid X}
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

noncomputable section

open Set MeasureTheory Metric Function Complex Bornology TileStructure Classical Filter
open scoped NNReal ENNReal ComplexConjugate

namespace TileStructure.Forest


/-! ## Section 7.6 and Lemma 7.4.6 -/

variable (t u₁) in
/-- The definition `𝓙'` at the start of Section 7.6.
We use a different notation to distinguish it from the 𝓙' used in Section 7.5 -/
def 𝓙₆ : Set (Grid X) := 𝓙 (t u₁) ∩ Iic (𝓘 u₁)

/-- Part of Lemma 7.6.1. -/
lemma union_𝓙₆ (hu₁ : u₁ ∈ t) :
    ⋃ J ∈ 𝓙₆ t u₁, (J : Set X) = 𝓘 u₁ := by
  sorry

/-- Part of Lemma 7.6.1. -/
lemma pairwiseDisjoint_𝓙₆ (hu₁ : u₁ ∈ t) :
    (𝓙₆ t u₁).PairwiseDisjoint (fun I ↦ (I : Set X)) := by
  sorry

/-- The constant used in `thin_scale_impact`. This is denoted `s₁` in the proof of Lemma 7.6.3.
Has value `Z * n / (202 * a ^ 3) - 2` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_6_3 (a n : ℕ) : ℝ := Z * n / (202 * a ^ 3) - 2

-- if needed
lemma C7_6_3_pos [ProofData a q K σ₁ σ₂ F G] (h : 1 ≤ n) : 0 < C7_6_3 a n := by
  sorry

/-- Lemma 7.6.3. -/
lemma thin_scale_impact (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hp : p ∈ t u₂ \ 𝔖₀ t u₁ u₂) (hJ : J ∈ 𝓙₆ t u₁)
    (h : ¬ Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J))) :
    𝔰 p ≤ s J - C7_6_3 a n := by
  sorry

/-- The constant used in `square_function_count`.
Has value `Z * n / (202 * a ^ 3) - 2` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_6_4 (a : ℕ) (s : ℤ) : ℝ≥0 := 2 ^ (104 * (a : ℝ) ^ 2) * (8 * D ^ (- s)) ^ κ

/-- Lemma 7.6.4. -/
lemma square_function_count (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hp : p ∈ t u₂ \ 𝔖₀ t u₁ u₂) (hJ : J ∈ 𝓙₆ t u₁) (s' : ℤ /- ? -/) :
    ⨍⁻ x : X, (∑ I ∈ {I : Grid X | s I = s J - s' ∧ Disjoint (I : Set X) (𝓘 u₁) ∧
    ¬ Disjoint (J : Set X) (ball (c I) (8 * D ^ s I)) },
    (ball (c I) (8 * D ^ s I)).indicator 1 x) ^ 2 ≤ C7_6_4 a s' := by
  sorry

/-- The constant used in `bound_for_tree_projection`.
Has value `2 ^ (118 * a ^ 3 - 100 / (202 * a) * Z * n * κ)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_6_2 (a n : ℕ) : ℝ≥0 := 2 ^ (118 * (a : ℝ) ^ 3 - 100 / (202 * a) * Z * n * κ)

/-- Lemma 7.6.2. Todo: add needed hypothesis to LaTeX -/
lemma bound_for_tree_projection (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hf : IsBounded (range f)) (h2f : HasCompactSupport f)
    (h3f : AEStronglyMeasurable f) :
    eLpNorm (approxOnCube (𝓙₆ t u₁) (‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f ·‖)) 2 volume ≤
    C7_6_2 a n *
    eLpNorm ((𝓘 u₁ : Set X).indicator (MB volume 𝓑 c𝓑 r𝓑 (‖f ·‖) · |>.toReal)) 2 volume := by
  sorry

/-- The constant used in `correlation_near_tree_parts`.
Has value `2 ^ (541 * a ^ 3 - Z * n / (4 * a ^ 2 + 2 * a ^ 3))` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_4_6 (a n : ℕ) : ℝ≥0 := 2 ^ (222 * (a : ℝ) ^ 3 - Z * n * 2 ^ (-10 * (a : ℝ)))

/-- Lemma 7.4.6 -/
lemma correlation_near_tree_parts (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) :
    ‖∫ x, adjointCarlesonSum (t u₁) g₁ x * conj (adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) g₂ x)‖₊ ≤
    C7_4_6 a n *
    eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₁ g₁) · |>.toReal) 2 volume *
    eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₂ g₂) · |>.toReal) 2 volume := by
  sorry

end TileStructure.Forest
