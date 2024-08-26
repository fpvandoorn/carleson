import Carleson.Forest

open ShortVariables TileStructure
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
  {n : ℕ} {f : Forest X n} {u : 𝔓 X} {x : X} {G : Set (𝔓 X)}

noncomputable section

open Set MeasureTheory Metric Function Complex Bornology TileStructure Classical
open scoped NNReal ENNReal ComplexConjugate

namespace TileStructure.Forest

/-! ## Section 7.1 and Lemma 7.1.3 -/

variable (f) in
/-- The definition `σ(u, x)` given in Section 7.1.
We may assume `u ∈ f.𝔘` whenever proving things about this definition. -/
def σ (u : 𝔓 X) (x : X) : Set ℤ := 𝔰 '' { p | p ∈ f.𝔗 u ∧ x ∈ E p }

/- Maybe we should try to avoid using \overline{σ} and \underline{σ} in Lean:
I don't think the set is always non-empty(?) -/
-- def σMax (u : 𝔓 X) (x : X) : ℤ :=
--   Finset.univ.filter (fun p ↦ p ∈ f.𝔗 u ∧ x ∈ E p) |>.image 𝔰 |>.max' sorry

/-- Lemma 7.1.1, freely translated. -/
lemma convex_scales (hu : u ∈ f.𝔘) : OrdConnected (f.σ u x) := sorry

/-- The definition of `𝓙₀(G), defined just below Lemma 7.1.1 -/
def 𝓙₀ (G : Set (𝔓 X)) : Set (Grid X) :=
  {J : Grid X | s J = - S ∨ ∀ p ∈ G, ¬ (𝓘 p : Set X) ⊆ ball (c J)  (100 * D ^ (s J + 1)) }

/-- The definition of `𝓙(G), defined below Lemma 7.1.1 -/
def 𝓙 (G : Set (𝔓 X)) : Set (Grid X) :=
  {x | Maximal (· ∈ 𝓙₀ G) x}

/-- The definition of `𝓛₀(G), defined below Lemma 7.1.1 -/
def 𝓛₀ (G : Set (𝔓 X)) : Set (Grid X) :=
  { L : Grid X | s L = - S ∨ (∃ p ∈ G, L ≤ 𝓘 p) ∧ ∀ p ∈ G, ¬ 𝓘 p ≤ L }

/-- The definition of `𝓛(G), defined below Lemma 7.1.1 -/
def 𝓛 (G : Set (𝔓 X)) : Set (Grid X) :=
  {x | Maximal (· ∈ 𝓛₀ G) x}

@[simp]
lemma biUnion_𝓙 : ⋃ J ∈ 𝓙 G, J = ⋃ I : Grid X, (I : Set X) := by
  sorry

lemma pairwiseDisjoint_𝓙 : (𝓙 G).PairwiseDisjoint (fun I ↦ (I : Set X)) := by
  sorry

@[simp]
lemma biUnion_𝓛 : ⋃ J ∈ 𝓛 G, J = ⋃ I : Grid X, (I : Set X) := by
  sorry

lemma pairwiseDisjoint_𝓛 : (𝓛 G).PairwiseDisjoint (fun I ↦ (I : Set X)) := by
  sorry

/-! ## Section 7.2 and Lemma 7.2.1 -/



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
    eLpNorm f 2 volume * eLpNorm g 2 volume := by
  sorry
