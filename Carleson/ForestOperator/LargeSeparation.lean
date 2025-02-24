import Carleson.ForestOperator.AlmostOrthogonality
import Mathlib.Tactic.Rify
import Carleson.ToMathlib.BoundedCompactSupport
import Carleson.Calculations
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

/-! ## Section 7.5 -/

variable (t u₁ u₂) in
/-- The definition `𝓙'` at the start of Section 7.5.1.
We use a different notation to distinguish it from the 𝓙' used in Section 7.6 -/
def 𝓙₅ : Set (Grid X) := 𝓙 (𝔖₀ t u₁ u₂) ∩ Iic (𝓘 u₁)

/-- The definition of χ-tilde, defined in the proof of Lemma 7.5.2 -/
def χtilde (J : Grid X) (u₁ : 𝔓 X) : X → ℝ≥0 :=
  (𝓘 u₁ : Set X).indicator fun x ↦ (8 - D ^ (- s J) * dist x (c J)).toNNReal

variable (t u₁ u₂) in
/-- The definition of χ, defined in the proof of Lemma 7.5.2 -/
def χ (J : Grid X) (x : X) : ℝ≥0 :=
  χtilde J u₁ x / ∑ J' ∈ { I | I ∈ 𝓙₅ t u₁ u₂ }, χtilde J' u₁ x

-- /-- The definition of `B`, defined in (7.5.1) -/
-- protected def _root_.Grid.ball (I : Grid X) : Set X := ball (c I) (8 * D ^ s I)

variable (t u₁ u₂) in
/-- The definition of h_J, defined in the proof of Section 7.5.2 -/
def holderFunction (f₁ f₂ : X → ℂ)  (J : Grid X) (x : X) : ℂ :=
  χ t u₁ u₂ J x * (exp (.I * 𝒬 u₁ x) * adjointCarlesonSum (t u₁) f₁ x) *
  conj (exp (.I * 𝒬 u₂ x) * adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ x)

/- AUXILIARY LEMMAS:START -/
lemma IF_subset_THEN_distance_between_centers (subset : (J : Set X) ⊆ J') :
    dist (c J) (c J') < 4 * D ^ s J' := by
  apply Grid_subset_ball
  exact (subset (Grid.c_mem_Grid))

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

lemma 𝓘_subset_iUnion_𝓙_𝔖₀ : (𝓘 u₁ : Set X) ⊆ ⋃ J ∈ 𝓙 (t.𝔖₀ u₁ u₂), (J : Set X) := by
  rw [biUnion_𝓙 (𝔖 := 𝔖₀ t u₁ u₂)]
  apply subset_iUnion_of_subset (𝓘 u₁)
  rfl
/- AUXILIARY LEMMAS:END -/

/-! ### Subsection 7.5.1 and Lemma 7.5.2 -/

/-- Part of Lemma 7.5.1. -/
lemma union_𝓙₅ (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) :
    ⋃ J ∈ 𝓙₅ t u₁ u₂, (J : Set X) = 𝓘 u₁ := by
  apply Set.Subset.antisymm
  · intros x hx
    simp only [mem_iUnion] at hx
    rcases hx with ⟨cube, ⟨_, interval⟩, h⟩
    exact Set.mem_of_mem_of_subset h interval.left
  · intros x hx
    have existsCube : x ∈ ⋃ J ∈ 𝓙 (t.𝔖₀ u₁ u₂), (J : Set X) := 𝓘_subset_iUnion_𝓙_𝔖₀ hx
    simp only [mem_iUnion, exists_prop] at existsCube
    rcases existsCube with ⟨cube, cube_in_𝓙, xInCube⟩
    simp only [mem_iUnion, exists_prop]
    have notDisjoint := Set.not_disjoint_iff.mpr ⟨x, xInCube, hx⟩
    have cubeIn𝓙₀ : cube ∈ 𝓙₀ (t.𝔖₀ u₁ u₂) := mem_of_mem_inter_left cube_in_𝓙
    simp only [mem_setOf_eq] at cubeIn𝓙₀
    cases cubeIn𝓙₀ with
    | inl west =>
      refine ⟨cube, ?_, xInCube⟩
      unfold 𝓙₅
      rw [inter_def, mem_setOf_eq]
      refine ⟨cube_in_𝓙, ?_⟩
      simp only [mem_Iic, Grid.le_def]
      have smaller := calc s cube
        _ = -S := west
        _ ≤ s (𝓘 u₁) := (mem_Icc.mp (scale_mem_Icc (i := 𝓘 u₁))).left
      refine ⟨?_, smaller⟩
      cases GridStructure.fundamental_dyadic' smaller with
      | inl subset => exact subset
      | inr disjoint => exact False.elim (notDisjoint disjoint)
    | inr east =>
      obtain ⟨p, belongs⟩ := t.nonempty' hu₁
      by_contra! contr
      have white := calc (𝓘 p : Set X)
        _ ⊆ 𝓘 u₁ := (𝓘_le_𝓘 t hu₁ belongs).1
        _ ⊆ cube := by
          apply subset_of_nmem_Iic_of_not_disjoint cube
          · have notIn : cube ∉ t.𝓙₅ u₁ u₂ := λ a => contr cube a xInCube
            rw [𝓙₅, inter_def, Set.mem_setOf_eq, not_and_or] at notIn
            exact Or.resolve_left notIn (Set.not_not_mem.mpr cube_in_𝓙)
          · exact notDisjoint
        _ ⊆ ball (c cube) (4 * D ^ s cube) := by
          exact Grid_subset_ball (i := cube)
        _ ⊆ ball (c cube) (100 * D ^ (s cube + 1)) := by
          intro y xy
          rw [ball, mem_setOf_eq] at xy ⊢
          exact gt_trans (calculation_16 (X := X) (s := s cube)) xy
      have black : ¬↑(𝓘 p) ⊆ ball (c cube) (100 * D ^ (s cube + 1)) := by
        have in_𝔖₀ := 𝔗_subset_𝔖₀ (hu₁ := hu₁) (hu₂ := hu₂) (hu := hu) (h2u := h2u)
        rw [subset_def] at in_𝔖₀
        exact east p (in_𝔖₀ p belongs)
      contradiction

/-- Part of Lemma 7.5.1. -/
lemma pairwiseDisjoint_𝓙₅ :
    (𝓙₅ t u₁ u₂).PairwiseDisjoint (fun I ↦ (I : Set X)) := by
  have ss : (𝓙 (t.𝔖₀ u₁ u₂) ∩ Iic (𝓘 u₁)) ⊆ 𝓙 (t.𝔖₀ u₁ u₂) := inter_subset_left
  exact PairwiseDisjoint.subset (pairwiseDisjoint_𝓙 (𝔖 := 𝔖₀ t u₁ u₂)) ss

lemma bigger_than_𝓙_is_not_in_𝓙₀ {𝔖 : Set (𝔓 X)} {A B : Grid X}
    (le : A ≤ B) (sle : s A < s B) (A_in : A ∈ 𝓙 𝔖) :
    B ∉ 𝓙₀ 𝔖 := by
  apply And.right at A_in
  simp only [Grid.le_def, and_imp] at A_in
  intro contr
  apply Lean.Omega.Int.le_lt_asymm (x := s A) (y := s B)
  · exact (A_in contr le.1 (le_of_lt sle)).2
  · exact sle

/-- Lemma 7.5.3 (stated somewhat differently). -/
lemma moderate_scale_change (hJ : J ∈ 𝓙₅ t u₁ u₂) (hJ' : J' ∈ 𝓙₅ t u₁ u₂)
    (h : ¬ Disjoint (J : Set X) J') :
    s J - 1 ≤ s J' := by
  by_contra! contr
  have pNotSubset : ∀ p ∈ t.𝔖₀ u₁ u₂, ¬↑(𝓘 p) ⊆ ball (c J) (100 * D^(s J + 1)) := by
    obtain ⟨⟨Jin𝓙₀, _⟩, _⟩ := hJ
    have notMin : s J ≠ -S := by linarith [(scale_mem_Icc (i := J')).left]
    exact Jin𝓙₀.resolve_left notMin
  have ⟨p, pIn, pSubset⟩ : ∃ p ∈ t.𝔖₀ u₁ u₂, (𝓘 p : Set X) ⊆ ball (c J) (100 * D^(s J + 1)) := by
    have ⟨J'', belongs, plusOne⟩ : ∃ J'', J' ≤ J'' ∧ s J'' = s J' + 1 :=
      Grid.exists_scale_succ (by linarith)
    have ⟨r, rIn, rSubset⟩ : ∃ p ∈ t.𝔖₀ u₁ u₂, ↑(𝓘 p) ⊆ ball (c J'') (100 * D^(s J' + 1 + 1)) := by
      have : J'' ∉ 𝓙₀ (t.𝔖₀ u₁ u₂) := bigger_than_𝓙_is_not_in_𝓙₀ belongs (by linarith) hJ'.1
      simp only [𝓙₀, mem_setOf_eq, plusOne] at this
      push_neg at this
      exact this.2
    use r
    use rIn
    calc (𝓘 r : Set X)
    _ ⊆ ball (c J'') (100 * D^(s J' + 1 + 1)) := rSubset
    _ ⊆ ball (c J) (100 * D^(s J + 1)) := by
      intro x
      simp only [ball, mem_setOf_eq]
      intro triangle_1
      have smaller : s J'' < s J := by linarith
      have DisBig := twentyfive_le_realD X
      calc dist x (c J)
      _ ≤ dist x (c J'') + dist (c J'') (c J) := dist_triangle x (c J'') (c J)
      _ ≤ 100 * D^(s J'' + 1) + dist (c J'') (c J) := by
        rw [← plusOne] at triangle_1
        gcongr
      _ ≤ 100 * D^(s J'' + 1) + 4 * D^(s J) := by
        have subset : (J'' : Set X) ⊆ J := by
          cases fundamental_dyadic smaller.le with
          | inl subset => exact subset
          | inr disj =>
            have disjoint := disj.mono_left belongs.1
            rw [disjoint_comm] at disjoint
            contradiction
        linarith [IF_subset_THEN_distance_between_centers subset]
      _ ≤ 100 * D^(s J) + 4 * D^(s J) := by
        gcongr
        · linarith
        · exact smaller
      _ < 100 * D^(s J + 1) := by
        ring_nf
        rw [zpow_one_add₀ (by linarith), mul_comm (D : ℝ), mul_assoc]
        gcongr
        linarith
  exact (pNotSubset p pIn) pSubset

/-- The constant used in `dist_χ_χ_le`.
Has value `2 ^ (226 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_2 (a : ℕ) : ℝ≥0 := 2 ^ (226 * (a : ℝ) ^ 3)

/-- Part of Lemma 7.5.2. -/
lemma sum_χ (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (x : X) :
    ∑ J ∈ { I | I ∈ 𝓙₅ t u₁ u₂ }, χ t u₁ u₂ J x = (𝓘 u₁ : Set X).indicator 1 x := by
  sorry

/-- Part of Lemma 7.5.2. -/
lemma χ_mem_Icc (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hx : x ∈ 𝓘 u₁) :
    χ t u₁ u₂ J x ∈ Icc 0 ((ball (c I) (8 * D ^ s I)).indicator 1 x) := by
  sorry

/-- Part of Lemma 7.5.2. -/
lemma dist_χ_χ_le (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hx : x ∈ 𝓘 u₁) (hx' : x' ∈ 𝓘 u₁) :
    dist (χ t u₁ u₂ J x) (χ t u₁ u₂ J x) ≤ C7_5_2 a * dist x x' / D ^ s J := by
  sorry


/-! ### Subsection 7.5.2 and Lemma 7.5.4 -/

/-- The constant used in `holder_correlation_tile`.
Has value `2 ^ (151 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_5 (a : ℕ) : ℝ≥0 := 2 ^ (151 * (a : ℝ) ^ 3)

/-- Lemma 7.5.5. -/
lemma holder_correlation_tile (hu : u ∈ t) (hp : p ∈ t u)
    (hf : BoundedCompactSupport f) :
    nndist (exp (.I * 𝒬 u x) * adjointCarleson p f x)
      (exp (.I * 𝒬 u x') * adjointCarleson p f x') ≤
    C7_5_5 a / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) *
    (nndist x x' / D ^ (𝔰 p : ℝ)) ^ (a : ℝ)⁻¹ * ∫⁻ x in E p, ‖f x‖₊ := by
  sorry

/-- Part of Lemma 7.5.6. -/
lemma limited_scale_impact__first_estimate (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hp : p ∈ t u₂ \ 𝔖₀ t u₁ u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (h : ¬ Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))) : s J ≤ 𝔰 p := by
  by_contra! contr
  apply Int.not_le.mpr contr
  apply Int.sub_one_lt_iff.mp
  apply Int.sub_lt_of_sub_lt
  rify
  apply lt_of_le_of_lt (hbc := calculation_logD_64 (X := X))
  apply tsub_le_iff_left.mpr
  have DIsOne := one_lt_D (X := X)
  rw [
    ← Real.logb_rpow (b := D) (x := 𝔰 p) (by positivity) (by linarith),
    ← Real.logb_mul (by positivity) (by positivity),
    ← Real.logb_rpow (b := D) (x := s J) (by positivity) (by linarith)
  ]
  apply (Real.logb_le_logb DIsOne (by positivity) (by positivity)).mpr
  have bigger : D ^ (s J) / 8 + 8 * D ^ (𝔰 p) ≥ D ^ s J / (4 : ℝ) := by
    rw [not_disjoint_iff] at h
    rcases h with ⟨middleX, h1, h2⟩
    calc (D ^ s J / (4 : ℝ))
    _ ≤ dist (c J) (𝔠 p) := by
      apply IF_disjoint_with_ball_THEN_distance_bigger_than_radius (p := 𝔠 p) (belongs := Grid.c_mem_Grid)
      have inter_1 : (J : Set X) ∩ ball (c J) (D ^ s J / 4) = ball (c J) (D ^ s J / 4) := inter_eq_self_of_subset_right ball_subset_Grid
      have inter_2 : (𝓘 u₁ : Set X) ∩ J = J := inter_eq_self_of_subset_right hJ.2.1
      rw [← inter_1, ← inter_2]
      apply Disjoint.inter_left
      apply Disjoint.inter_left
      rw [disjoint_comm]
      by_contra notDisjoint
      apply hp.2
      apply overlap_implies_distance hu₁ hu₂ hu h2u (hpu₁ := notDisjoint)
      right
      exact hp.1
    _ ≤ dist (𝔠 p) middleX + dist middleX (c J) := by
      rw [dist_comm]
      exact dist_triangle ..
    _ ≤ 8 * D ^ (𝔰 p) + dist middleX (c J) := by
      gcongr
      rw [mem_ball, dist_comm] at h1
      exact le_of_lt h1
    _ ≤ D ^ (s J) / 8 + 8 * D ^ (𝔰 p) := by
      rw [add_comm]
      gcongr
      rw [mem_ball, ← div_eq_inv_mul] at h2
      exact le_of_lt h2
  apply le_neg_add_iff_le.mp
  have := mul_le_mul_of_nonneg_left (a := 8) (sub_nonneg_of_le bigger) (by positivity)
  ring_nf at this
  norm_cast

/-- Part of Lemma 7.5.6. -/
lemma limited_scale_impact__second_estimate (hp : p ∈ t u₂ \ 𝔖₀ t u₁ u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (h : ¬ Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))) :
    𝔰 p ≤ s J + 3 := by
  by_contra! three
  have ⟨J', belongs, plusOne⟩ : ∃ J', J ≤ J' ∧ s J' = s J + 1 :=
    Grid.exists_scale_succ (by change s J < 𝔰 p; linarith)
  have ⟨p', ⟨_, distance⟩, hundred⟩ : ∃ p' ∈ t.𝔖₀ u₁ u₂, ↑(𝓘 p') ⊆ ball (c J') (100 * D ^ (s J + 2)) := by
    rw [← one_add_one_eq_two, ← add_assoc, ← plusOne]
    have J'Touches𝔖₀ : J' ∉ 𝓙₀ (t.𝔖₀ u₁ u₂) := bigger_than_𝓙_is_not_in_𝓙₀ (le := belongs) (sle := by linarith [plusOne]) (A_in := hJ.1)
    rw [𝓙₀, Set.nmem_setOf_iff] at J'Touches𝔖₀
    push_neg at J'Touches𝔖₀
    exact J'Touches𝔖₀.right
  apply calculation_9 (X := X)
  apply one_le_of_le_mul_right₀ (b := 2 ^ ((Z : ℝ) * n / 2)) (by positivity)
  have DIsPos := defaultD_pos a
  calc 2 ^ ((Z : ℝ) * (n : ℝ) / 2)
    _ ≤ dist_{𝓘 p'} (𝒬 u₁) (𝒬 u₂) := by
      exact distance
    _ ≤ dist_{c J', 100 * D ^ (s J + 2)} (𝒬 u₁) (𝒬 u₂) := by
      apply cdist_mono
      intros x hx
      exact hundred (ball_subset_Grid hx)
    _ ≤ 2 ^ ((-100 : ℝ) * a) * dist_{c J', 100 * D^(s J + 3)} (𝒬 u₁) (𝒬 u₂) := by
      apply calculation_8 (X := X)
      rw [mul_comm, calculation_6 (s J) (X := X), calculation_7 (s J) (X := X)]
      exact_mod_cast le_cdist_iterate (k := 100 * a) (f := 𝒬 u₁) (g := 𝒬 u₂) (hr := by positivity)
    _ ≤ 2 ^ ((-100 : ℝ) * a) * dist_{𝔠 p, 10 * D^(𝔰 p)} (𝒬 u₁) (𝒬 u₂) := by
      gcongr
      apply cdist_mono
      simp only [not_disjoint_iff] at h
      rcases h with ⟨middleX, lt_2, lt_3⟩
      have lt_4 := IF_subset_THEN_distance_between_centers belongs.left
      intros x lt_1
      calc dist x (𝔠 p)
      _ ≤ dist x (c J') + dist (c J') (c J) + dist (c J) middleX + dist middleX (𝔠 p) := by
        exact dist_triangle5 x (c J') (c J) middleX (𝔠 p)
      _ < 10 * D ^ 𝔰 p := by
        simp only [mem_ball] at lt_3
        rw [dist_comm] at lt_3 lt_4
        exact calculation_4 (lt_1 := lt_1) (lt_2 := lt_2) (lt_3 := lt_3) (lt_4 := lt_4) (three := three) (plusOne := plusOne) (X := X)
    _ ≤ 2 ^ ((-94 : ℝ) * a) * dist_{𝓘 p} (𝒬 u₁) (𝒬 u₂) := by
      apply calculation_5
      have bigger : 0 < (D : ℝ) ^ 𝔰 p / 4 := by positivity
      calc dist_{𝔠 p, 10 * D^(𝔰 p)} (𝒬 u₁) (𝒬 u₂)
      _ ≤ dist_{𝔠 p, 2 ^ 6 * (D ^ 𝔰 p / 4)} (𝒬 u₁) (𝒬 u₂) := by
        apply cdist_mono
        apply ball_subset_ball
        ring_nf
        linarith
      _ ≤ (2 ^ (a : ℝ)) ^ (6 : ℝ) * dist_{𝔠 p, (D ^ 𝔰 p / 4)} (𝒬 u₁) (𝒬 u₂) := by
        exact_mod_cast cdist_le_iterate (f := (𝒬 u₁)) (g := (𝒬 u₂)) (r := (D ^ (𝔰 p)) / 4) (k := 6) (x := 𝔠 p) bigger
    _ ≤ 2^((-94 : ℝ) * a) * 2^((Z : ℝ) * n / 2) := by
      rcases hp with ⟨tile, notIn𝔖₀⟩
      unfold 𝔖₀ at notIn𝔖₀
      simp only [mem_setOf_eq, not_or, not_and, sep_union, mem_union] at notIn𝔖₀
      gcongr
      apply le_of_not_ge
      exact notIn𝔖₀.2 tile

/-- Lemma 7.5.6. -/
lemma limited_scale_impact (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hp : p ∈ t u₂ \ 𝔖₀ t u₁ u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (h : ¬ Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))) :
    𝔰 p ∈ Icc (s J) (s J + 3) := by
  constructor
  · exact limited_scale_impact__first_estimate (hu₁ := hu₁) (hu₂ := hu₂) (hu := hu) (h2u := h2u) (hp := hp) (hJ := hJ) (h := h)
  · exact limited_scale_impact__second_estimate (hp := hp) (hJ := hJ) (h := h)

/-- The constant used in `local_tree_control`.
Has value `2 ^ (104 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_7 (a : ℕ) : ℝ≥0 := 2 ^ (104 * (a : ℝ) ^ 3)

/-- Lemma 7.5.7. -/
lemma local_tree_control (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (hf : BoundedCompactSupport f) :
    ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f x‖₊ ≤
    C7_5_7 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f ·‖) x := by
  sorry

/-- Lemma 7.5.8. -/
lemma scales_impacting_interval (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hp : p ∈ t u₁ ∪ (t u₂ ∩ 𝔖₀ t u₁ u₂))
    (h : ¬ Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J))) : s J ≤ 𝔰 p := by
  rcases hJ with ⟨hJLeft, _⟩
  apply 𝓙_subset_𝓙₀ at hJLeft
  apply Set.mem_or_mem_of_mem_union at hp
  have belongs : p ∈ t.𝔖₀ u₁ u₂ := by
    cases hp with
    | inl h1 => exact 𝔗_subset_𝔖₀ hu₁ hu₂ hu h2u h1
    | inr h2 => exact Set.mem_of_mem_inter_right h2
  cases hJLeft with
  | inl scaleVerySmall =>
    exact trans scaleVerySmall (scale_mem_Icc.left)
  | inr noGridInBall =>
    have pGridIsNotInBall := noGridInBall p belongs
    rw [not_subset] at pGridIsNotInBall
    rcases pGridIsNotInBall with ⟨x, ⟨xInTile, xIsNotInBall⟩⟩
    rw [Metric.mem_ball'] at xIsNotInBall
    by_contra! contr
    apply xIsNotInBall
    simp only [not_disjoint_iff] at h
    rcases h with ⟨middleX, xxx, yyy⟩
    calc dist (c J) x
    _ = dist (x) (c J) := by
      apply dist_comm
    _ ≤ dist (x) (𝔠 p) + dist (𝔠 p) (c J) := dist_triangle ..
    _ < dist (x) (𝔠 p) + 16 * D ^ s J := by
      gcongr
      calc dist (𝔠 p) (c J)
        _ ≤ dist middleX (𝔠 p) + dist middleX (c J) := by
          nth_rw 2 [dist_comm]
          apply dist_triangle
        _ < 8 * D ^ 𝔰 p + 8 * D ^ s J := by
          exact add_lt_add xxx yyy
        _ = 8 * D ^ s J + 8 * D ^ 𝔰 p := by
          rw [add_comm]
        _ < 8 * D ^ (s J) + 8 * D ^ (s J) := by
          gcongr
          exact one_lt_D (X := X)
        _ = 16 * D ^ s J := by
          linarith
    _ < 4 * D ^ 𝔰 p + 16 * D ^ s J := by
      gcongr
      rw [dist_comm]
      apply Metric.mem_ball'.mp
      apply Grid_subset_ball (X := X) (i := 𝓘 p)
      exact xInTile
    _ < 100 * D ^ (s J + 1) := by
      apply (div_lt_div_iff_of_pos_right zero_lt_four).mp
      ring_nf
      rewrite (config := {occs := .pos [1]}) [add_comm]
      apply lt_tsub_iff_left.mp
      have DIsPos := one_lt_D (X := X)
      calc (D : ℝ) ^ 𝔰 p
        _ < D ^ (s J) := by gcongr; exact DIsPos
        _ < D ^ (s J) * (25 * D - 4) := by
          rewrite (config := {occs := .pos [1]}) [mul_comm]
          apply lt_mul_left
          · positivity
          · linarith
        _ = (D ^ (s J) * D) * 25 - D ^ (s J) * 4 := by ring
        _ = D ^ ((s J) + 1) * 25 - D ^ (s J) * 4 := by
          rw [zpow_add_one₀ (by positivity)]
        _ = D ^ (1 + (s J)) * 25 - D ^ (s J) * 4 := by ring_nf

/-- The constant used in `global_tree_control1_1`.
Has value `2 ^ (154 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_9_1 (a : ℕ) : ℝ≥0 := 2 ^ (154 * (a : ℝ) ^ 3)

/-- The constant used in `global_tree_control1_2`.
Has value `2 ^ (153 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_9_2 (a : ℕ) : ℝ≥0 := 2 ^ (153 * (a : ℝ) ^ 3)

/-- Part 1 of Lemma 7.5.9 -/
lemma global_tree_control1_1 (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (ℭ : Set (𝔓 X)) (hℭ : ℭ = t u₁ ∨ ℭ = t u₂ ∩ 𝔖₀ t u₁ u₂)
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf : BoundedCompactSupport f) :
    ⨆ x ∈ ball (c J) (8 * D ^ s J), ‖adjointCarlesonSum ℭ f x‖₊ ≤
    (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum ℭ f x‖₊) +
    C7_5_9_1 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f ·‖) x := by
  sorry

/-- Part 2 of Lemma 7.5.9 -/
lemma global_tree_control1_2 (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (ℭ : Set (𝔓 X)) (hℭ : ℭ = t u₁ ∨ ℭ = t u₂ ∩ 𝔖₀ t u₁ u₂)
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf : BoundedCompactSupport f)
    (hx : x ∈ ball (c J) (8 * D ^ s J)) (hx' : x' ∈ ball (c J) (8 * D ^ s J)) :
    nndist (exp (.I * 𝒬 u x) * adjointCarlesonSum ℭ f x)
      (exp (.I * 𝒬 u x') * adjointCarlesonSum ℭ f x') ≤
    C7_5_9_1 a * (nndist x x' / D ^ (𝔰 p : ℝ)) ^ (a : ℝ)⁻¹ *
    ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f ·‖) x := by
  sorry

/-- The constant used in `global_tree_control2`.
Has value `2 ^ (155 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_10 (a : ℕ) : ℝ≥0 := 2 ^ (155 * (a : ℝ) ^ 3)

/-- Lemma 7.5.10 -/
lemma global_tree_control2 (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (hf : BoundedCompactSupport f) :
    ⨆ x ∈ ball (c J) (8 * D ^ s J), ‖adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f x‖₊ ≤
    ⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f x‖₊ +
    C7_5_10 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f ·‖) x := by
  sorry

/-- The constant used in `holder_correlation_tree`.
Has value `2 ^ (535 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_4 (a : ℕ) : ℝ≥0 := 2 ^ (535 * (a : ℝ) ^ 3)

/-- Lemma 7.5.4. -/
lemma holder_correlation_tree (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) :
    HolderOnWith (C7_5_4 a *
    ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₁) f₁ x‖₊) +
    (⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f₁ ·‖) x).toNNReal) *
    ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f₂ x‖₊) +
    (⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 (‖f₂ ·‖) x).toNNReal))
    nnτ (holderFunction t u₁ u₂ f₁ f₂ J) (ball (c J) (8 * D ^ s J)) := by
  sorry


/-! ### Subsection 7.5.3 and Lemma 7.4.5 -/

/-- The constant used in `lower_oscillation_bound`.
Has value `2 ^ (Z * n / 2 - 201 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
def C7_5_11 (a n : ℕ) : ℝ≥0 := 2 ^ (Z * n / 2 - 201 * (a : ℝ) ^ 3)

lemma IF_subset_THEN_not_disjoint {A : Grid X} {B: Grid X} (h : (A : Set X) ⊆ B) : ¬ Disjoint (B : Set X) (A : Set X) := by
  rw [disjoint_comm]
  intro disjoint
  have wow := (Set.disjoint_of_subset_iff_left_eq_empty h).mp disjoint
  have black := Grid.nonempty A
  rw [← Mathlib.Tactic.PushNeg.empty_ne_eq_nonempty] at black
  exact black (Eq.symm wow)

lemma betterHelper (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) : s J < s (𝓘 u₁) := by
  obtain ⟨⟨Jin𝓙₀, _⟩, ⟨jIsSubset : (J : Set X) ⊆ 𝓘 u₁, smaller : s J ≤ s (𝓘 u₁)⟩⟩ := hJ
  obtain ⟨p, belongs⟩ := t.nonempty' hu₁
  apply lt_of_le_of_ne smaller
  by_contra! h
  have uIsSmalling : 𝓘 u₁ ∈  𝓙₀ (t.𝔖₀ u₁ u₂) := by
    have equal := by
      have notDisjoint := IF_subset_THEN_not_disjoint jIsSubset
      rw [disjoint_comm] at notDisjoint
      exact (eq_or_disjoint h).resolve_right notDisjoint
    exact mem_of_eq_of_mem (id (Eq.symm equal)) Jin𝓙₀
  cases uIsSmalling with
  | inl MIN =>
    have sameScale : s (𝓘 p) = s (𝓘 u₁) := by
      linarith [
        (scale_mem_Icc (i := 𝓘 p)).left,
        show s (𝓘 p) ≤ s (𝓘 u₁) by exact (𝓘_le_𝓘 t hu₁ belongs).2
      ]
    suffices s (𝓘 u₁) > s (𝓘 p) by linarith
    have pIsSubset := (𝓘_le_𝓘 t hu₁ belongs).1
    by_contra! smaller
    apply HasSubset.Subset.not_ssubset ((fundamental_dyadic smaller).resolve_right (IF_subset_THEN_not_disjoint pIsSubset))
    apply HasSubset.Subset.ssubset_of_ne pIsSubset
    by_contra! sameSet
    have equal := Grid.inj (Prod.ext sameSet sameScale)
    exact (Forest.𝓘_ne_𝓘 (hu:=hu₁) (hp:=belongs)) equal
  | inr avoidance =>
    have pIsEvil : p ∈ t.𝔖₀ u₁ u₂ := 𝔗_subset_𝔖₀ (hu₁ := hu₁) (hu₂ := hu₂) (hu := hu) (h2u := h2u) belongs
    apply avoidance p pIsEvil
    calc (𝓘 p : Set X)
    _ ⊆ ↑(𝓘 u₁) := by
      exact (𝓘_le_𝓘 t hu₁ belongs).1
    _ ⊆ ball (c (𝓘 u₁)) (4 * ↑D ^ s (𝓘 u₁)) := by
      exact Grid_subset_ball (i:= 𝓘 u₁)
    _ ⊆ ball (c (𝓘 u₁)) (100 * ↑D ^ (s (𝓘 u₁) + 1)) := by
      intro x hx
      exact gt_trans (calculation_16 (X:=X) (s:=s (𝓘 u₁))) hx

/--
Lemma 7.5.11
Blueprint: https://florisvandoorn.com/carleson/blueprint/treesection.html#lower-oscillation-bound
-/
lemma lower_oscillation_bound (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) :
    C7_5_11 a n ≤ dist_{c J, 8 * D ^ s J} (𝒬 u₁) (𝒬 u₂) := by

  have first_sentence : ∃ (J' : Grid X), J ≤ J' ∧ s J' = s J + 1 := by
    apply Grid.exists_scale_succ (W:= 𝓘 u₁)
    exact betterHelper hu₁ hu₂ hu h2u hJ
  rcases first_sentence with ⟨J', JleJ', scaleSmaller⟩

  have notInAvoidant : J' ∉ 𝓙₀ (t.𝔖₀ u₁ u₂) := by
    apply bigger_than_𝓙_is_not_in_𝓙₀ (sle:=by linarith) (le:=JleJ')
    exact mem_of_mem_inter_left hJ

  unfold 𝓙₀ at notInAvoidant
  simp only [mem_setOf_eq, not_or, not_forall, Classical.not_imp, Decidable.not_not] at notInAvoidant
  push_neg at notInAvoidant
  obtain ⟨_, ⟨ p, pIn, pSubset ⟩⟩ := notInAvoidant

  have thus :=
    calc 2 ^ ((Z : ℝ) * n / 2)
    _ ≤ dist_{𝔠 p, D ^ 𝔰 p / 4} (𝒬 u₁) (𝒬 u₂) := pIn.2
    _ ≤ dist_{c J, 128 * D^(s J + 2)} (𝒬 u₁) (𝒬 u₂) := by
      apply cdist_mono (f := 𝒬 u₁) (g := 𝒬 u₂)
      intro point pointIn
      calc dist point (c J)
      _ ≤ dist point (c J') + dist (c J') (c J) := dist_triangle ..
      _ ≤ 100 * D ^ (s J' + 1) + dist (c J') (c J) := by
        rw [ball, Set.subset_def] at pSubset
        have dist_1 := pSubset point (ball_subset_Grid pointIn)
        rw [mem_setOf_eq] at dist_1
        gcongr
      _ ≤ 100 * D ^ (s J' + 1) + 4 * D ^ (s J') := by
        have dist_2 : dist (c J) (c J') < 4 * D ^ (s J') := IF_subset_THEN_distance_between_centers (subset:=JleJ'.1)
        rw [dist_comm] at dist_2
        gcongr
      _ = 100 * D ^ (s J + 2) + 4 * D ^ (s J + 1) := by
        rw [scaleSmaller, add_assoc, show (1 : ℤ) + 1 = 2 by rfl]
      _ < 128 * D^(s J + 2) := by
        exact calculation_11 (s J) (X:=X)
    _ ≤ 2 ^ (200 * (a^3) + 4 * a) * dist_{c J, 8 * D ^ s J} (𝒬 u₁) (𝒬 u₂) := by
      rw [show 128 * (D : ℝ)^(s J + 2) = 2 ^ (200*a^2 + 4) * (8*D^(s J)) by exact_mod_cast calculation_12 (s := (s J : ℝ)) (X:=X)]
      rw [calculation_13]
      apply cdist_le_iterate
      have DIsPos := defaultD_pos a
      positivity

  unfold C7_5_11
  push_cast
  linarith [calculation_14 (X:=X) (n:=n), calculation_15 (X:=X) (h:=thus)]

/-- The constant used in `correlation_distant_tree_parts`.
Has value `2 ^ (541 * a ^ 3 - Z * n / (4 * a ^ 2 + 2 * a ^ 3))` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_4_5 (a n : ℕ) : ℝ≥0 := 2 ^ (541 * (a : ℝ) ^ 3 - Z * n / (4 * a ^ 2 + 2 * a ^ 3))

/-- Lemma 7.4.5 -/
lemma correlation_distant_tree_parts (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hf₁ : IsBounded (range f₁)) (h2f₁ : HasCompactSupport f₁)
    (hf₂ : IsBounded (range f₂)) (h2f₂ : HasCompactSupport f₂) :
    ‖∫ x, adjointCarlesonSum (t u₁) g₁ x * conj (adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) g₂ x)‖₊ ≤
    C7_4_5 a n *
    eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₁ g₁) · |>.toReal) 2 volume *
    eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₂ g₂) · |>.toReal) 2 volume := by
  sorry

end TileStructure.Forest
