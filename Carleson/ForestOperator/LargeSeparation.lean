import Carleson.ForestOperator.AlmostOrthogonality
import Mathlib.Tactic.Rify
import Carleson.ToMathlib.BoundedCompactSupport

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
def χtilde (J : Grid X) (x : X) : ℝ≥0 :=
  8 - D ^ (- s J) * dist x (c J) |>.toNNReal

variable (t u₁ u₂) in
/-- The definition of χ, defined in the proof of Lemma 7.5.2 -/
def χ (J : Grid X) (x : X) : ℝ≥0 :=
  χtilde J x / ∑ J' ∈ { I | I ∈ 𝓙₅ t u₁ u₂ }, χtilde J' x

-- /-- The definition of `B`, defined in (7.5.1) -/
-- protected def _root_.Grid.ball (I : Grid X) : Set X := ball (c I) (8 * D ^ s I)

variable (t u₁ u₂) in
/-- The definition of h_J, defined in the proof of Section 7.5.2 -/
def holderFunction (f₁ f₂ : X → ℂ)  (J : Grid X) (x : X) : ℂ :=
  χ t u₁ u₂ J x * (exp (.I * 𝒬 u₁ x) * adjointCarlesonSum (t u₁) f₁ x) *
  conj (exp (.I * 𝒬 u₂ x) * adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ x)

/-! ### Subsection 7.5.1 and Lemma 7.5.2 -/

-- Auxiliary lemma for Lemma 7.5.1.
lemma 𝓘_subset_iUnion_𝓙_𝔖₀ : (𝓘 u₁ : Set X) ⊆ ⋃ J ∈ 𝓙 (t.𝔖₀ u₁ u₂), (J : Set X) := by
  rw [biUnion_𝓙 (𝔖 := 𝔖₀ t u₁ u₂)]
  apply subset_iUnion_of_subset (𝓘 u₁)
  rfl

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
        _ ⊆ 𝓘 u₁ := if_descendant_then_subset t hu₁ belongs
        _ ⊆ cube := by
          apply subset_of_nmem_Iic_of_not_disjoint cube
          · have notIn : cube ∉ t.𝓙₅ u₁ u₂ := λ a => contr cube a xInCube
            rw [𝓙₅, inter_def, Set.mem_setOf_eq, not_and_or] at notIn
            exact Or.resolve_left notIn (Set.not_not_mem.mpr cube_in_𝓙)
          · exact notDisjoint
        _ ⊆ ball (c cube) (4 * ↑D ^ s cube) := by
          exact Grid_subset_ball (i := cube)
        _ ⊆ ball (c cube) (100 * ↑D ^ (s cube + 1)) := by
          unfold ball
          intro y xy
          rw [mem_setOf_eq] at xy ⊢
          have numbers : 4 * (D : ℝ) ^ s cube < 100 * D ^ (s cube + 1) := by
            gcongr
            linarith
            exact one_lt_D (X := X)
            linarith
          exact gt_trans numbers xy
      have black : ¬↑(𝓘 p) ⊆ ball (c cube) (100 * ↑D ^ (s cube + 1)) := by
        have in_𝔖₀ := 𝔗_subset_𝔖₀ (hu₁ := hu₁) (hu₂ := hu₂) (hu := hu) (h2u := h2u)
        rw [subset_def] at in_𝔖₀
        exact east p (in_𝔖₀ p belongs)
      contradiction

/-- Part of Lemma 7.5.1. -/
lemma pairwiseDisjoint_𝓙₅ :
    (𝓙₅ t u₁ u₂).PairwiseDisjoint (fun I ↦ (I : Set X)) := by
  have ss : (𝓙 (t.𝔖₀ u₁ u₂) ∩ Iic (𝓘 u₁)) ⊆ 𝓙 (t.𝔖₀ u₁ u₂) := inter_subset_left
  exact PairwiseDisjoint.subset (pairwiseDisjoint_𝓙 (𝔖 := 𝔖₀ t u₁ u₂)) ss

/-- Lemma 7.5.3 (stated somewhat differently). -/
lemma moderate_scale_change (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hJ' : J' ∈ 𝓙₅ t u₁ u₂)
  (h : ¬ Disjoint (J : Set X) J') : s J + 1 ≤ s J' := by
  sorry

/-- The constant used in `dist_χ_χ_le`.
Has value `2 ^ (226 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_2 (a : ℕ) : ℝ≥0 := 2 ^ (226 * (a : ℝ) ^ 3)

/-- Part of Lemma 7.5.2. -/
lemma sum_χ (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (x : X) :
    ∑ J ∈ { I | I ∈ 𝓙₅ t u₁ u₂   }, χ t u₁ u₂ J x = (𝓘 u₁ : Set X).indicator 1 x := by
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

theorem size_of_D (h: (100 : ℝ) < D) : ((100 : ℝ) + 4 * D ^ (-2 : ℝ) + 8⁻¹ * D ^ (-3 : ℝ)) * D ^ (-1 : ℝ) < 2 := by
  calc ((100 : ℝ) + 4 * ↑D ^ (-2 : ℝ) + 8⁻¹ * ↑D ^ (-3 : ℝ)) * ↑D ^ (-1 : ℝ)
    _ = (100 : ℝ) * ↑D ^ (-1 : ℝ) + 4 * ↑D ^ (-2 : ℝ) * ↑D ^ (-1 : ℝ) + 8⁻¹ * ↑D ^ (-3 : ℝ) * ↑D ^ (-1 : ℝ) := by
      ring
    _ = (100 : ℝ) * ↑D ^ (-1 : ℝ) + 4 * ↑D ^ (-3 : ℝ) + 8⁻¹ * ↑D ^ (-4 : ℝ) := by
      rw [mul_assoc, mul_assoc, ← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity)]
      congr <;> norm_num
    _ < (1 : ℝ) + 1 / 250 + 1 / 80000 := by
      have h1 : 100 * (D : ℝ) ^ (-1 : ℝ) < 1 := by
        nth_rw 2 [show (1 : ℝ) = 100 * 100 ^ (-1 : ℝ) by norm_num]
        gcongr 100 * ?_
        apply (Real.rpow_lt_rpow_iff_of_neg ..).mpr
        all_goals linarith
      have h2 : 4 * (D : ℝ) ^ (-3 : ℝ) < 1 / 250 := by
        rw [show (1 / 250 : ℝ) = 4 * ((10 : ℝ) ^ (-3 : ℝ)) by norm_num]
        gcongr 4 * ?_
        apply (Real.rpow_lt_rpow_iff_of_neg ..).mpr
        all_goals linarith
      have h3 : 8⁻¹ * (D : ℝ) ^ (-4 : ℝ) < 1 / 80000 := by
        rw [show (1 / 80000 : ℝ) = 8⁻¹ * ((10 : ℝ) ^ (-4 : ℝ)) by norm_num]
        gcongr 8⁻¹ * ?_
        apply (Real.rpow_lt_rpow_iff_of_neg ..).mpr
        all_goals linarith
      gcongr
    _ < 2 := by
      norm_num

theorem disjoint
  {J: X} {d: ℝ} {pSet: Set X} {p: X}
  (belongs: p ∈ pSet) (h: Disjoint (Metric.ball J d) pSet)
  : dist J p ≥ d := by
  rw [disjoint_iff_inter_eq_empty, inter_comm] at h
  by_contra! contr
  have belongsIntersection := (Set.mem_inter_iff ..).mpr ⟨belongs, (mem_ball_comm.mp contr)⟩
  rw [h] at belongsIntersection
  exact (Set.mem_empty_iff_false p).mp belongsIntersection

theorem IF_subset_THEN_distance_between_centers
  (subset : (J : Set X) ⊆ J')
  : dist (c J) (c J') < 4 * D ^ s J' := by
  apply Grid_subset_ball
  exact (subset (Grid.c_mem_Grid))

theorem calculation_1 (aIsBig: a ≥ 4) : Real.logb (2 ^ (100 * a ^ 2)) 64 < 1 := by
  have sixtyFourSmaller : (64 : ℝ) < 2 ^ (100 * a ^ 2) := by
    calc (64 : ℝ)
      _ = 2^6 := by norm_num
      _ < 2 ^ (100 * a ^ 2) := by
        gcongr
        exact one_lt_two
        apply lt_of_lt_of_le (b:=1600) (by norm_num)
        exact Nat.mul_le_mul_left 100 (Nat.pow_le_pow_of_le_left aIsBig 2)
  apply (Real.logb_lt_iff_lt_rpow (b := 2 ^ (100 * a ^ 2)) (x := 64) (y := 1) (by linarith) (by linarith)).mpr
  simp
  exact sixtyFourSmaller

lemma first_estimate (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hp : p ∈ t u₂ \ 𝔖₀ t u₁ u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (h : ¬ Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))) : s J ≤ 𝔰 p := by
  by_contra! contr

  rcases hJ with ⟨hJLeft, hJaaa, hJbbb⟩
  simp at hJaaa hJbbb
  apply 𝓙_subset_𝓙₀ at hJLeft

  cases' hp with hi _

  have disjointness : Disjoint (𝓘 p : Set X) (𝓘 u₁ : Set X) := by
    by_contra notDisjoint
    have well : p ∈ t.𝔖₀ u₁ u₂ := by
      apply overlap_implies_distance hu₁ hu₂ hu h2u (hpu₁ := notDisjoint)
      right
      exact hi
    contradiction

  have onOneHand : dist (c J) (𝔠 p) ≥ (D ^ s J / 4) := by
    rw [disjoint_comm] at disjointness
    have pJDisjoint := Disjoint.inter_left (h := disjointness) (u := ↑(J))
    rw [inter_eq_self_of_subset_right hJaaa] at pJDisjoint
    have inter : (J : Set X) ∩ (ball (c J) (D ^ s J / 4) : Set X) = ball (c J) (D ^ s J / 4) := inter_eq_self_of_subset_right (ball_subset_Grid (X := X) (i := J))
    have pBallDisjoint : Disjoint (↑J ∩ ball (c J) (D ^ s J / 4)) ↑(𝓘 p) := Disjoint.inter_left (h := pJDisjoint) (s := J) (t := 𝓘 p) (u := ball (c J) (D ^ s J / 4))
    rw [inter] at pBallDisjoint
    exact disjoint (h := pBallDisjoint) (p := 𝔠 p) (belongs := Grid.c_mem_Grid)

  have onOtherHand : dist (c J) (𝔠 p) ≤ D ^ (s J) / 8 + 8 * D^(𝔰 p) := by
    simp only [not_disjoint_iff] at h
    rcases h with ⟨middleX, h1, h2⟩

    calc dist (c J) (𝔠 p)
      _ ≤ dist (𝔠 p) middleX + dist middleX (c J) := by
        nth_rw 1 [dist_comm]
        exact dist_triangle (y := middleX) (x := 𝔠 p) (z := c J)
      _ ≤ D ^ (s J) / 8 + 8 * D^(𝔰 p) := by
        have first : dist (𝔠 p) middleX ≤ 8 * D^(𝔰 p) := by
          unfold ball at h1
          rw [Set.mem_setOf_eq] at h1
          rw [dist_comm]
          apply le_of_lt
          exact h1
        have second : dist middleX (c J) ≤ ↑D ^ s J / 8 := by
          unfold ball at h2
          rw [Set.mem_setOf_eq] at h2
          apply le_of_lt
          have equal : 8⁻¹ * (D : ℝ) ^ s J = ↑D ^ s J / 8 := by
            exact Eq.symm (div_eq_inv_mul ..)
          rw [equal] at h2
          exact h2
        nth_rw 2 [add_comm]
        exact add_le_add first second

  apply Int.not_le.mpr contr
  apply Int.sub_one_lt_iff.mp
  apply Int.sub_lt_of_sub_lt
  rify
  apply lt_of_le_of_lt (a:=(s J - 𝔰 p : ℝ)) (b:=Real.logb D 64) (c:=1)

  apply tsub_le_iff_left.mpr

  have DIsOne := one_lt_D (X := X)

  rw [
    ← Real.logb_rpow (b:=D) (x:=𝔰 p) (by positivity) (by linarith),
    ← Real.logb_mul (by positivity) (by positivity),
    ← Real.logb_rpow (b:=D) (x:=s J) (by positivity) (by linarith)
  ]
  apply (Real.logb_le_logb DIsOne (by positivity) (by positivity)).mpr

  have thus : (D : ℝ) ^ 𝔰 p * 64 ≥ ↑D ^ s J := by
    rw [← ge_iff_le] at onOtherHand
    have well := Trans.trans onOtherHand onOneHand
    have white := sub_nonneg_of_le well
    apply le_neg_add_iff_le.mp
    have red := mul_le_mul_of_nonneg_left (a := 8) white (by positivity)
    ring_nf at red
    exact red
  exact_mod_cast thus

  exact_mod_cast calculation_1 (aIsBig := four_le_a X)

lemma sentence_2
  (plusOne: s J' = s J + 1)
  (belongs: (J: Set X) ⊆ (J': Set X))
  (j5right: ∀ ⦃y : Grid X⦄, y ∈ 𝓙₀ (t.𝔖₀ u₁ u₂) → (J : Set X) ⊆ ↑y → s J ≤ s y → (y : Set X) ⊆ J ∧ s y ≤ s J)
  : ∃ p' ∈ t.𝔖₀ u₁ u₂, ↑(𝓘 p') ⊆ ball (c J') (100 * ↑D ^ (s J + 2)) := by
  have J'TouchesChildren : J' ∉ 𝓙₀ (t.𝔖₀ u₁ u₂) := by
    have bigger : s J' > s J := Int.lt.intro (id (Eq.symm plusOne))
    intro hJ'
    have smaller : ¬s J' > s J := by
      push_neg
      exact (j5right hJ' belongs (Int.le.intro 1 (id (Eq.symm plusOne)))).right
    contradiction

  rw [← one_add_one_eq_two, ← add_assoc, ← plusOne]

  unfold 𝓙₀ at J'TouchesChildren
  rw [Set.nmem_setOf_iff] at J'TouchesChildren
  push_neg at J'TouchesChildren
  exact J'TouchesChildren.right

theorem dist_triangle5 (a b c d e : X) :
  dist a e ≤ dist a b + dist b c + dist c d + dist d e :=
  calc
    dist a e ≤ dist a d + dist d e := dist_triangle a d e
    _ ≤ (dist a c + dist c d) + dist d e := add_le_add_right (dist_triangle a c d) _
    _ ≤ (dist a b + dist b c + dist c d) + dist d e :=
      add_le_add_right (add_le_add_right (dist_triangle a b c) _) _

lemma sentence_3
  (belongs : (J : Set X) ⊆ ↑J' ∧ s J ≤ s J')
  (plusOne : s J' = s J + 1)
  (three : s J + 3 < 𝔰 p)
  (h : ¬Disjoint (ball (𝔠 p) (8 * ↑D ^ 𝔰 p)) (ball (c J) (8⁻¹ * ↑D ^ s J)))
  : ball (c J') (100 * D^(s J + 3)) ⊆ ball (𝔠 p) (10 * D^𝔰 p) := by
  simp only [not_disjoint_iff] at h
  rcases h with ⟨middleX, xxx, yyy⟩
  intros x xIn
  simp only [mem_ball] at xxx yyy xIn ⊢
  cases' belongs with subset smaller
  apply IF_subset_THEN_distance_between_centers at subset

  calc dist x (𝔠 p)
    _ ≤ dist x (c J') + dist (c J') (c J) + dist (c J) middleX + dist middleX (𝔠 p) := by
      exact dist_triangle5 x (c J') (c J) middleX (𝔠 p)
    _ ≤ 100 * D ^ (s J + 3) + 4 * D ^ (s J + 1) + 8⁻¹ * D ^ s J + 8 * D ^ 𝔰 p := by
      have step1 : dist x (c J') < 100 * ↑D ^ (s J + 3) := xIn
      have step2 : dist (c J') (c J) < 4 * ↑D ^ (s J + 1) := by
        rw [plusOne] at subset
        rw [dist_comm]
        exact subset
      have step3 : dist (c J) middleX < 8⁻¹ * ↑D ^ s J := by
        rw [dist_comm]
        exact yyy
      calc dist x (c J') + dist (c J') (c J) + dist (c J) middleX + dist middleX (𝔠 p) ≤
        100 * ↑D ^ (s J + 3) + dist (c J') (c J) + dist (c J) middleX + dist middleX (𝔠 p) :=
            by gcongr
      _ ≤ 100 * ↑D ^ (s J + 3) + 4 * ↑D ^ (s J + 1) + dist (c J) middleX + dist middleX (𝔠 p) :=
            by gcongr
      _ ≤ 100 * ↑D ^ (s J + 3) + 4 * ↑D ^ (s J + 1) + 8⁻¹ * ↑D ^ s J + dist middleX (𝔠 p) :=
            by gcongr
      _ ≤ 100 * ↑D ^ (s J + 3) + 4 * ↑D ^ (s J + 1) + 8⁻¹ * ↑D ^ s J + 8 * ↑D ^ 𝔰 p :=
            by gcongr
    _ < 10 * ↑D ^ 𝔰 p := by
      have calc8plus2 : (2 : ℝ) + 8 = 10 := by norm_num
      rw [← calc8plus2, right_distrib]
      clear calc8plus2
      gcongr
      have D_big : (2 : ℝ) ≤ D := by linarith [twentyfive_le_realD X]
      have D_pos : (0 : ℝ) < D := by linarith [twentyfive_le_realD X]
      have second : (4 * D ^ (- 2 : ℝ)) * D ^ (s J + 3) = 4 * (D : ℝ) ^ (s J + 1) := by
        calc 4 * (D : ℝ) ^ (-2 : ℝ) * ↑D ^ (s J + 3)
          _ = 4 * (↑D ^ (-2 : ℝ) * ↑D ^ (s J + 3)) := by ring
          _ = 4 * ↑D ^ (-2 + (s J + 3)) := by
            congr
            have pow_th := Real.rpow_add (x := (D : ℝ)) (y := (-2)) (z:= (s J + 3)) D_pos
            rw_mod_cast [pow_th]
          _ = 4 * ↑D ^ (s J + 1) := by ring_nf

      have third : ((8 : ℝ)⁻¹ * D ^ (- 3 : ℝ)) * D ^ (s J + 3) = 8⁻¹ * ↑D ^ s J := by
        calc (8 : ℝ)⁻¹ * (D : ℝ) ^ (-3 : ℝ) * ↑D ^ (s J + 3)
          _ = (8 : ℝ)⁻¹ * (↑D ^ (-3 : ℝ) * ↑D ^ (s J + 3)) := by ring
          _ = (8 : ℝ)⁻¹ * ↑D ^ (-3 + (s J + 3)) := by
            congr
            have pow_th := Real.rpow_add (x := (D : ℝ)) (y := (-3)) (z:= (s J + 3)) D_pos
            rw_mod_cast [pow_th]
          _ = (8 : ℝ)⁻¹* ↑D ^ (s J) := by
            norm_num

      rw [← second, ← third]
      have sss := distrib_three_right (100 : ℝ) (4 * D ^ (-2 : ℝ)) (8⁻¹ * D ^ (-3 : ℝ) : ℝ) (↑D ^ (s J + 3))
      rw [← sss]
      clear second third sss

      have hi : s J + 3 ≤ 𝔰 p - 1 := by omega
      calc (100 + 4 * (D : ℝ) ^ (-2 : ℝ) + 8⁻¹ * ↑D ^ (-3 : ℝ)) * ↑D ^ (s J + 3)
        _ ≤ (100 + 4 * (D : ℝ) ^ (-2 : ℝ) + 8⁻¹ * ↑D ^ (-3 : ℝ)) * ↑D ^ (𝔰 p - 1) := by
          gcongr
          linarith [D_big]
        _ = (100 + 4 * (D : ℝ) ^ (-2 : ℝ) + 8⁻¹ * ↑D ^ (-3 : ℝ)) * (↑D ^ (𝔰 p) * ↑D ^ (- 1 : ℝ)) := by
          congr
          have well : 𝔰 p - 1 = 𝔰 p + (- 1) := by rfl
          rw [well]
          have pow_th := Real.rpow_add (x := (D : ℝ)) (y := (𝔰 p)) (z:= (- 1)) D_pos
          norm_cast at pow_th
          norm_cast
        _ < 2 * ↑D ^ 𝔰 p := by
          nth_rw 4 [mul_comm]
          have well := mul_assoc (a:= (100 + 4 * (D : ℝ) ^ (-2 : ℝ) + 8⁻¹ * ↑D ^ (-3 : ℝ))) (b:= (D : ℝ) ^ (-1 : ℝ)) (c:= (D : ℝ) ^ 𝔰 p)
          rw [← well]
          gcongr
          exact size_of_D (hundred_lt_realD X)

theorem last_step (hp: p ∈ t.𝔗 u₂ \ t.𝔖₀ u₁ u₂) : 2^((-94 : ℝ) * a) * dist_{𝓘 p} (𝒬 u₁) (𝒬 u₂) ≤ 2^((-94 : ℝ) * a) * 2^((Z : ℝ) * (n : ℝ) / 2) := by
  cases' hp with l evil_children
  unfold 𝔖₀ at evil_children
  beta_reduce at evil_children
  simp only [mem_setOf_eq, not_or, not_and, sep_union, mem_union] at evil_children
  cases' evil_children with unimportant good
  have hi := good l
  push_neg at hi
  gcongr

/-- Lemma 7.5.6. -/
-- BLUEPRINT: https://florisvandoorn.com/carleson/blueprint/treesection.html#limited-scale-impact
lemma limited_scale_impact (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hp : p ∈ t u₂ \ 𝔖₀ t u₁ u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (h : ¬ Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))) :
    𝔰 p ∈ Icc (s J) (s J + 3) := by
  constructor
  exact first_estimate (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hp : p ∈ t u₂ \ 𝔖₀ t u₁ u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (h : ¬ Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J)))

  rcases hJ with ⟨J_is_maximal, J_size, (J_scale : s J ≤ 𝔰 u₁)⟩
  simp at J_size

  cases' J_is_maximal with left j5right
  simp at left j5right

  by_contra! three

  have ⟨J', belongs, plusOne⟩ : ∃ J', J ≤ J' ∧ s J' = s J + 1 := by
    have notMax : ¬IsMax J := by
      rw [Grid.isMax_iff]
      intro top
      have topScale : s J = (S : ℤ) := by
        rw [top]
        exact s_topCube (X := X)
      rw [topScale] at three
      have range := (scale_mem_Icc (i:=𝓘 p)).2
      change 𝔰 p ≤ ↑S at range 
      linarith
    use J.succ
    constructor
    exact Grid.succ_def notMax |>.mp rfl |>.1
    exact Grid.scale_succ notMax

  rw [Grid.le_def] at belongs

  have sentence_2_result : ∃ p' ∈ t.𝔖₀ u₁ u₂, ↑(𝓘 p') ⊆ ball (c J') (100 * ↑D ^ (s J + 2)) := sentence_2 (plusOne := plusOne) (belongs := belongs.left) (j5right := j5right)

  have sentence_3_result : ball (c J') (100 * D^(s J + 3)) ⊆ ball (𝔠 p) (10 * D^(𝔰 p)) := sentence_3 belongs plusOne three h

  rcases sentence_2_result with ⟨ p', evilChildren, hundred ⟩
  rcases evilChildren with ⟨ forest, distance ⟩
  beta_reduce at forest

  have contradiction := calc 2^((Z : ℝ) * (n : ℝ) / 2)
    _ ≤ dist_{𝓘 p'}                   (𝒬 u₁) (𝒬 u₂) := by
      exact distance
    _ = dist_{𝔠 p', D ^ 𝔰 p' / 4}      (𝒬 u₁) (𝒬 u₂) := by
      rfl
    _ ≤ dist_{c J', 100 * D^(s J + 2)} (𝒬 u₁) (𝒬 u₂) := by
      have subset : ball (𝔠 p') (D ^ 𝔰 p' / 4) ⊆ ball (c J') (100 * D^(s J + 2)) := by
        have oneForth_subset_of_p : ball (𝔠 p') (↑D ^ 𝔰 p' / 4) ⊆ ↑(𝓘 p') := ball_subset_Grid (X := X) (i := 𝓘 p')
        exact fun ⦃a_1⦄ a ↦ hundred (oneForth_subset_of_p a)
      exact cdist_mono (h := subset)
    _ ≤ 2^((-100 : ℝ) * a) * dist_{c J', 100 * D^(s J + 3)} (𝒬 u₁) (𝒬 u₂) := by
      have result := le_cdist_iterate (k := 100 * a) (f := 𝒬 u₁) (g := 𝒬 u₂) (x := c J') (r := 100 * D^(s J + 2)) (hr := by positivity)
      rw [neg_mul, Real.rpow_neg (x:=(2 : ℝ)) (y:=(100 * (a : ℝ))) (hx := by positivity)]
      rw [mul_comm (a:=(2 ^ (100 * (a : ℝ)))⁻¹)]
      have well := (le_mul_inv_iff₀ (c:=((2 : ℝ) ^ (100 * (a : ℝ)))) (b:= dist_{c J', 100 * D^(s J + 3)} (𝒬 u₁) (𝒬 u₂)) (a:= dist_{c J', 100 * D^(s J + 2)} (𝒬 u₁) (𝒬 u₂)) (by positivity)).mpr
      apply well
      clear well
      rw [mul_comm]

      have useful : (D : ℝ) ^ (s J + 3) = (D : ℝ) ^ (s J + 2) * (D : ℝ) := by
        rw [zpow_add₀ (by linarith [defaultD_pos a]) (s J) 3, zpow_add₀ (by linarith [defaultD_pos a]) (s J) 2, mul_assoc]
        congr
      rw [useful]
      have equality :
        (defaultA a) ^ (100 * a) * (100 * (D : ℝ) ^ (s J + 2)) =
        100 * (D ^ (s J + 2) * D) := by
        rw [← mul_assoc (a:= 100)]
        rw [mul_comm]
        congr
        simp
        have simple : ((2 : ℝ) ^ a) ^ (100 * a) = (2 : ℝ) ^ (a * (100 * a)) := by
          exact Eq.symm (pow_mul 2 a (100 * a))
        rw [simple, mul_comm (a:=a)]
        simp
        ring
      rw [← equality]
      clear equality
      exact_mod_cast result
    _ ≤ 2^((-100 : ℝ) * a) * dist_{𝔠 p, 10 * D^(𝔰 p)} (𝒬 u₁) (𝒬 u₂) := by
      gcongr
      exact cdist_mono (h := sentence_3_result)
    _ ≤ 2^((-94 : ℝ) * a) * dist_{𝓘 p} (𝒬 u₁) (𝒬 u₂) := by
      have DIsPos := defaultD_pos a
      have bigger : 0 < (D : ℝ) ^ 𝔰 p / 4 := by positivity
      have cdist_theorem := cdist_le_iterate (f := (𝒬 u₁)) (g:= (𝒬 u₂)) (r := (D ^ (𝔰 p)) / 4) (k:= 6) (x:= 𝔠 p) bigger
      unfold defaultA at cdist_theorem

      have aIsBig : a ≥ 4 := four_le_a X
      have h_pos : 0 < (2 : ℝ)^((100 : ℝ) * a) := by positivity
      have := mul_le_mul_left h_pos (c:= 2^((-94 : ℝ) * a) * dist_{𝓘 p} (𝒬 u₁) (𝒬 u₂)) (b:= 2^((-100 : ℝ) * a) * dist_{𝔠 p, 10 * D^(𝔰 p)} (𝒬 u₁) (𝒬 u₂))
      apply this.mp
      clear this
      rw [← mul_assoc]
      simp
      rw [Real.rpow_neg (by positivity), LinearOrderedField.mul_inv_cancel (a:= (2 : ℝ) ^ (100 * (a : ℝ))) (by positivity)]
      simp
      rw [← mul_assoc, ← Real.rpow_add]
      ring_nf
      have easy : 10 * (D : ℝ)^(𝔰 p) ≤ 2 ^ 6 * (↑D ^ 𝔰 p / 4) := by
        ring_nf
        gcongr
        linarith
      have smaller : dist_{𝔠 p, 10 * D^(𝔰 p)} (𝒬 u₁) (𝒬 u₂) ≤ dist_{𝔠 p, 2 ^ 6 * (↑D ^ 𝔰 p / 4)} (𝒬 u₁) (𝒬 u₂) := by
        have bll := ball_subset_ball easy (x:= 𝔠 p)
        exact cdist_mono (h:=bll)
      have yellow := Trans.trans smaller cdist_theorem
      rw [Real.rpow_mul (x:= (2 : ℝ)) (hx:=by positivity) (y:=a) (z:= 6)]
      exact_mod_cast yellow
      positivity
    _ ≤ 2^((-94 : ℝ) * a) * 2^((Z : ℝ) * n / 2) := by
      exact last_step hp

  have zer : (2 : ℝ)^((Z : ℝ) * n / 2) > 0 := by positivity
  have contr : (1 : ℝ) ≤ 2 ^ (-94 * (a : ℝ )) := by
    exact one_le_of_le_mul_right₀ zer contradiction

  have aIsBig : a ≥ 4 := four_le_a X
  have trio : (2 : ℝ)^(0 :ℝ) = 1 := by norm_num
  rw [← trio] at contr
  have tr :  1 < (2 : ℝ) := by linarith
  have ff : (0 : ℝ) ≤ -94 * (a : ℝ) := (Real.rpow_le_rpow_left_iff tr).mp contr
  simp at ff
  have h2 : 94 * (a) ≥ 376 := by
    calc
      94 * a ≥ 94 * 4 := by exact Nat.mul_le_mul_left 94 aIsBig
      _ = 376 := by norm_num
  norm_cast at ff
  linarith


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
    _ < dist (x) (𝔠 p) + 16 * ↑D ^ s J := by
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
    _ < 4 * ↑D ^ 𝔰 p + 16 * ↑D ^ s J := by
      gcongr
      rw [dist_comm]
      apply Metric.mem_ball'.mp
      apply Grid_subset_ball (X := X) (i := 𝓘 p)
      exact xInTile
    _ < 100 * ↑D ^ (s J + 1) := by
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
irreducible_def C7_5_11 (a n : ℕ) : ℝ≥0 := 2 ^ (Z * n / 2 - 201 * (a : ℝ) ^ 3)

/-- Lemma 7.5.11 -/
lemma lower_oscillation_bound (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) :
    C7_5_11 a n ≤ dist_{c J, 8 * D ^ s J} (𝒬 u₁) (𝒬 u₂) := by
  sorry

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
