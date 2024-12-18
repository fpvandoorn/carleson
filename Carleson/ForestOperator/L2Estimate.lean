import Carleson.ForestOperator.PointwiseEstimate

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

/-! ## Section 7.2 and Lemma 7.2.1 -/

/-- The constant used in `nontangential_operator_bound`.
Has value `2 ^ (103 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_2_2 (a : ℕ) : ℝ≥0 := 2 ^ (103 * (a : ℝ) ^ 3)

/-- Lemma 7.2.2. -/
lemma nontangential_operator_bound
    (hf : BoundedCompactSupport f)
    (θ : Θ X) :
    eLpNorm (nontangentialMaximalFunction θ f · |>.toReal) 2 volume ≤ eLpNorm f 2 volume := by
  sorry

/-- The set of cubes in Lemma 7.2.4. -/
def kissing (I : Grid X) : Finset (Grid X) :=
  {J | s J = s I ∧ ¬Disjoint (ball (c I) (16 * D ^ s I)) (ball (c J) (16 * D ^ s J))}

lemma subset_of_kissing (h : J ∈ kissing I) :
    ball (c J) (D ^ s J / 4) ⊆ ball (c I) (33 * D ^ s I) := by
  simp_rw [kissing, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨x, xI, xJ⟩ := not_disjoint_iff.mp h.2
  apply ball_subset_ball'
  calc
    _ ≤ D ^ s J / 4 + dist (c J) x + dist x (c I) := by
      rw [add_assoc]; exact add_le_add_left (dist_triangle ..) _
    _ ≤ D ^ s J / 4 + 16 * D ^ s J + 16 * D ^ s I := by
      gcongr
      · exact (mem_ball'.mp xJ).le
      · exact (mem_ball.mp xI).le
    _ ≤ _ := by
      rw [h.1, div_eq_mul_inv, mul_comm _ 4⁻¹, ← distrib_three_right]
      gcongr
      norm_num

lemma volume_le_of_kissing (h : J ∈ kissing I) :
    volume (ball (c I) (33 * D ^ s I)) ≤ 2 ^ (9 * a) * volume (ball (c J) (D ^ s J / 4)) := by
  simp_rw [kissing, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨x, xI, xJ⟩ := not_disjoint_iff.mp h.2
  have : ball (c I) (33 * D ^ s I) ⊆ ball (c J) (128 * D ^ s J) := by
    apply ball_subset_ball'
    calc
      _ ≤ 33 * D ^ s I + dist (c I) x + dist x (c J) := by
        rw [add_assoc]; exact add_le_add_left (dist_triangle ..) _
      _ ≤ 33 * D ^ s I + 16 * D ^ s I + 16 * D ^ s J := by
        gcongr
        · exact (mem_ball'.mp xI).le
        · exact (mem_ball.mp xJ).le
      _ ≤ _ := by
        rw [h.1, ← distrib_three_right]
        gcongr; norm_num
  have double := measure_ball_le_pow_two' (μ := volume) (x := c J) (r := D ^ s J / 4) (n := 9)
  have A9 : (defaultA a : ℝ≥0) ^ 9 = (2 : ℝ≥0∞) ^ (9 * a) := by
    simp only [defaultA]; norm_cast; ring
  rw [show (2 : ℝ) ^ 9 * (D ^ s J / 4) = 128 * D ^ s J by ring, A9] at double
  exact (measure_mono this).trans double

lemma pairwiseDisjoint_of_kissing :
    (kissing I).toSet.PairwiseDisjoint fun i ↦ ball (c i) (D ^ s i / 4) := fun j mj k mk hn ↦ by
  apply disjoint_of_subset ball_subset_Grid ball_subset_Grid
  simp_rw [Finset.mem_coe, kissing, Finset.mem_filter] at mj mk
  exact (eq_or_disjoint (mj.2.1.trans mk.2.1.symm)).resolve_left hn

/-- Lemma 7.2.4. -/
lemma boundary_overlap (I : Grid X) : (kissing I).card ≤ 2 ^ (9 * a) := by
  have key : (kissing I).card * volume (ball (c I) (33 * D ^ s I)) ≤
      2 ^ (9 * a) * volume (ball (c I) (33 * D ^ s I)) := by
    calc
      _ = ∑ _ ∈ kissing I, volume (ball (c I) (33 * D ^ s I)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ J ∈ kissing I, 2 ^ (9 * a) * volume (ball (c J) (D ^ s J / 4)) :=
        Finset.sum_le_sum fun _ ↦ volume_le_of_kissing
      _ = 2 ^ (9 * a) * volume (⋃ J ∈ kissing I, ball (c J) (D ^ s J / 4)) := by
        rw [← Finset.mul_sum]; congr
        exact (measure_biUnion_finset pairwiseDisjoint_of_kissing fun _ _ ↦ measurableSet_ball).symm
      _ ≤ _ := by gcongr; exact iUnion₂_subset fun _ ↦ subset_of_kissing
  have vn0 : volume (ball (c I) (33 * D ^ s I)) ≠ 0 := by
    refine (measure_ball_pos volume _ ?_).ne'; simp only [defaultD]; positivity
  rw [ENNReal.mul_le_mul_right vn0 (measure_ball_ne_top _ _)] at key; norm_cast at key

/-- Lemma 7.2.3. -/
lemma boundary_operator_bound
    (hf : BoundedCompactSupport f) (hu : u ∈ t) :
    eLpNorm (boundaryOperator t u f · |>.toReal) 2 volume ≤ eLpNorm f 2 volume := by
  sorry

/-- The constant used in `nontangential_operator_bound`.
Has value `2 ^ (104 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_2_1 (a : ℕ) : ℝ≥0 := 2 ^ (104 * (a : ℝ) ^ 3)

/-- Lemma 7.2.1. -/
lemma tree_projection_estimate
    (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g) (hu : u ∈ t) :
    ‖∫ x, conj (g x) * carlesonSum (t u) f x‖₊ ≤
    C7_2_1 a * eLpNorm (approxOnCube (𝓙 (t u)) (‖f ·‖)) 2 volume *
    eLpNorm (approxOnCube (𝓛 (t u)) (‖g ·‖)) 2 volume := by
  sorry

end TileStructure.Forest
