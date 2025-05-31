import Carleson.ForestOperator.AlmostOrthogonality

open ShortVariables TileStructure
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
  {n : ℕ} {t : Forest X n} {u₁ u₂ : 𝔓 X} {J J' : Grid X}

open Set Metric

namespace TileStructure.Forest

variable (t u₁ u₂) in
/-- The definition `𝓙'` at the start of Section 7.5.1.
We use a different notation to distinguish it from the 𝓙' used in Section 7.6 -/
def 𝓙₅ : Set (Grid X) := 𝓙 (𝔖₀ t u₁ u₂) ∩ Iic (𝓘 u₁)

lemma 𝓘_subset_iUnion_𝓙_𝔖₀ : (𝓘 u₁ : Set X) ⊆ ⋃ J ∈ 𝓙 (t.𝔖₀ u₁ u₂), (J : Set X) := by
  rw [biUnion_𝓙 (𝔖 := 𝔖₀ t u₁ u₂)]
  apply subset_iUnion_of_subset (𝓘 u₁)
  rfl

lemma bigger_than_𝓙_is_not_in_𝓙₀ {𝔖 : Set (𝔓 X)} {A B : Grid X}
    (le : A ≤ B) (sle : s A < s B) (A_in : A ∈ 𝓙 𝔖) :
    B ∉ 𝓙₀ 𝔖 := by
  apply And.right at A_in
  simp only [Grid.le_def, and_imp] at A_in
  intro contr
  apply Lean.Omega.Int.le_lt_asymm (x := s A) (y := s B)
  · exact (A_in contr le.1 (le_of_lt sle)).2
  · exact sle

/- AUXILIARY LEMMAS:START -/

lemma IF_subset_THEN_distance_between_centers (subset : (J : Set X) ⊆ J') :
    dist (c J) (c J') < 4 * D ^ s J' :=
  Grid_subset_ball (subset Grid.c_mem_Grid)

lemma IF_subset_THEN_not_disjoint {A : Grid X} {B: Grid X} (h : (A : Set X) ⊆ B) :
    ¬ Disjoint (B : Set X) (A : Set X) := by
  rw [disjoint_comm]
  intro disjoint
  have nonempty := Grid.nonempty A
  rw [← Mathlib.Tactic.PushNeg.empty_ne_eq_nonempty] at nonempty
  exact nonempty (Eq.symm ((Set.disjoint_of_subset_iff_left_eq_empty h).mp disjoint))

lemma IF_disjoint_with_ball_THEN_distance_bigger_than_radius {J : X} {r : ℝ} {pSet : Set X} {p : X}
    (belongs : p ∈ pSet) (h : Disjoint (Metric.ball J r) pSet) :
    dist J p ≥ r := by
  rw [disjoint_iff_inter_eq_empty, inter_comm] at h
  by_contra! contr
  apply (Set.mem_empty_iff_false p).mp
  rw [← h]
  apply (Set.mem_inter_iff ..).mpr
  apply mem_ball_comm.mp at contr
  exact ⟨belongs, contr⟩

lemma dist_triangle5 (a b c d e : X) :
    dist a e ≤ dist a b + dist b c + dist c d + dist d e :=
  calc
    dist a e ≤ dist a d + dist d e := dist_triangle a d e
    _ ≤ (dist a c + dist c d) + dist d e := add_le_add_right (dist_triangle a c d) _
    _ ≤ (dist a b + dist b c + dist c d) + dist d e :=
      add_le_add_right (add_le_add_right (dist_triangle a b c) _) _

/- AUXILIARY LEMMAS:END -/

end TileStructure.Forest
