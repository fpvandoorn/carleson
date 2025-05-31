import Carleson.Calculations
import Carleson.ForestOperator.LargeSeparation.Defs
import Carleson.ToMathlib.Data.NNReal

open ShortVariables TileStructure
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
  {n j j' : ℕ} {t : Forest X n} {u u₁ u₂ p : 𝔓 X} {x x' : X} {𝔖 : Set (𝔓 X)}
  {f f₁ f₂ g g₁ g₂ : X → ℂ} {I J J' L : Grid X}
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

noncomputable section

open Set MeasureTheory Metric Function Complex Bornology TileStructure Filter
open scoped NNReal ENNReal ComplexConjugate

namespace TileStructure.Forest

/-! ## Section 7.5.1 (Lipschitz partition of unity, Lemmas 7.5.1 to 7.5.3 -/

/-- The definition of χ-tilde, defined in the proof of Lemma 7.5.2 -/
def χtilde (J : Grid X) (u₁ : 𝔓 X) : X → ℝ≥0 :=
  (𝓘 u₁ : Set X).indicator fun x ↦ (8 - D ^ (- s J) * dist x (c J)).toNNReal

lemma χtilde_pos_iff : 0 < χtilde J u₁ x ↔ x ∈ 𝓘 u₁ ∧ x ∈ ball (c J) (8 * D ^ s J) := by
  have := @one_le_D a; rw [χtilde]
  by_cases h : x ∈ 𝓘 u₁
  · rw [indicator_of_mem h, Real.toNNReal_pos, sub_pos, zpow_neg, inv_mul_lt_iff₀' (by positivity)]
    simp [h]
  · rw [indicator_of_not_mem h]; simp [h]

lemma χtilde_le_eight : χtilde J u₁ x ≤ 8 := by
  unfold χtilde; apply indicator_le fun _ _ ↦ ?_
  rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_ofNat, sub_le_self_iff]
  positivity

lemma four_lt_χtilde (xJ : x ∈ J) (xu : x ∈ 𝓘 u₁) : 4 < χtilde J u₁ x := by
  have := @one_le_D a
  simp_rw [χtilde, indicator_of_mem xu, Real.ofNat_lt_toNNReal, lt_sub_comm, Nat.cast_ofNat]
  rw [show (8 : ℝ) - 4 = 4 by norm_num, zpow_neg, inv_mul_lt_iff₀' (by positivity)]
  exact mem_ball.mp (Grid_subset_ball xJ)

lemma dist_χtilde_le (mx : x ∈ 𝓘 u₁) (mx' : x' ∈ 𝓘 u₁) :
    dist (χtilde J u₁ x) (χtilde J u₁ x') ≤ dist x x' / D ^ s J :=
  calc
    _ ≤ ‖(8 - D ^ (-s J) * dist x (c J)) - (8 - D ^ (-s J) * dist x' (c J))‖ := by
      rw [χtilde, indicator_of_mem mx, indicator_of_mem mx']
      change ‖(_ - _ : ℝ)‖ ≤ _
      simp_rw [NNReal.val_eq_coe, Real.coe_toNNReal']
      exact norm_sup_sub_sup_le_norm ..
    _ = ‖dist x' (c J) - dist x (c J)‖ / D ^ (s J) := by
      rw [sub_sub_sub_cancel_left, ← mul_sub, zpow_neg, ← div_eq_inv_mul, norm_div]; simp
    _ ≤ _ := by gcongr; rw [Real.norm_eq_abs, dist_comm x x']; exact abs_dist_sub_le ..

variable (t u₁ u₂) in
open scoped Classical in
/-- The definition of χ, defined in the proof of Lemma 7.5.2 -/
def χ (J : Grid X) (x : X) : ℝ≥0 :=
  χtilde J u₁ x / ∑ J' ∈ 𝓙₅ t u₁ u₂, χtilde J' u₁ x

-- /-- The definition of `B`, defined in (7.5.1) -/
-- protected def _root_.Grid.ball (I : Grid X) : Set X := ball (c I) (8 * D ^ s I)

/-! ### Subsection 7.5.1 and Lemma 7.5.2 -/

/-- Part of Lemma 7.5.1. -/
lemma union_𝓙₅ (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂) :
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
          · have notIn : cube ∉ t.𝓙₅ u₁ u₂ := fun a ↦ contr cube a xInCube
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
lemma pairwiseDisjoint_𝓙₅ : (𝓙₅ t u₁ u₂).PairwiseDisjoint (fun I ↦ (I : Set X)) := by
  have ss : (𝓙 (t.𝔖₀ u₁ u₂) ∩ Iic (𝓘 u₁)) ⊆ 𝓙 (t.𝔖₀ u₁ u₂) := inter_subset_left
  exact PairwiseDisjoint.subset (pairwiseDisjoint_𝓙 (𝔖 := 𝔖₀ t u₁ u₂)) ss

open scoped Classical in
lemma four_lt_sum_χtilde
    (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hx : x ∈ 𝓘 u₁) :
    4 < ∑ J' ∈ 𝓙₅ t u₁ u₂, χtilde J' u₁ x := by
  have hx₀ := hx
  rw [Grid.mem_def, ← union_𝓙₅ hu₁ hu₂ hu h2u, mem_iUnion₂] at hx; obtain ⟨J, mJ, mx⟩ := hx
  refine (four_lt_χtilde mx hx₀).trans_le ?_
  apply Finset.single_le_sum (f := fun J ↦ χtilde J u₁ x) (fun _ _ ↦ zero_le _)
  rwa [mem_toFinset]

/-- Lemma 7.5.3 (stated somewhat differently). -/
lemma moderate_scale_change (hJ : J ∈ 𝓙₅ t u₁ u₂) (hJ' : J' ∈ 𝓙₅ t u₁ u₂)
    (hd : ¬Disjoint (ball (c J) (8 * D ^ s J)) (ball (c J') (8 * D ^ s J'))) :
    s J - 1 ≤ s J' := by
  by_contra! hs
  have fa : ∀ p ∈ t.𝔖₀ u₁ u₂, ¬↑(𝓘 p) ⊆ ball (c J) (100 * D ^ (s J + 1)) :=
    hJ.1.1.resolve_left (by linarith [(scale_mem_Icc (i := J')).1])
  apply absurd fa; push_neg
  obtain ⟨J'', sJ'', lJ''⟩ : ∃ J'', s J'' = s J' + 1 ∧ J' ≤ J'' := by
    refine Grid.exists_supercube (s J' + 1) ⟨by omega, ?_⟩
    rw [lt_sub_iff_add_lt] at hs; exact hs.le.trans scale_mem_Icc.2
  obtain ⟨p, mp, sp⟩ : ∃ p ∈ t.𝔖₀ u₁ u₂, ↑(𝓘 p) ⊆ ball (c J'') (100 * D ^ (s J' + 1 + 1)) := by
    have : J'' ∉ 𝓙₀ (t.𝔖₀ u₁ u₂) := bigger_than_𝓙_is_not_in_𝓙₀ lJ'' (by linarith) hJ'.1
    rw [𝓙₀, mem_setOf_eq, sJ''] at this; push_neg at this; exact this.2
  use p, mp, sp.trans (ball_subset_ball' ?_)
  calc
    _ ≤ 100 * D ^ (s J' + 1 + 1) + (dist (c J'') (c J') + dist (c J) (c J')) :=
      add_le_add_left (dist_triangle_right ..) _
    _ ≤ 100 * D ^ (s J' + 1 + 1) + (4 * D ^ s J'' + 8 * D ^ s J + 8 * D ^ s J') := by
      rw [add_assoc (4 * _)]; gcongr
      · exact (mem_ball'.mp (Grid_subset_ball (lJ''.1 Grid.c_mem_Grid))).le
      · exact (dist_lt_of_not_disjoint_ball hd).le
    _ ≤ 100 * D ^ s J + (4 * D ^ s J + 8 * D ^ s J + 8 * D ^ s J) := by
      gcongr; exacts [one_le_D, by omega, one_le_D, by omega, one_le_D, by omega]
    _ ≤ _ := by
      rw [← add_mul, ← add_mul, ← add_mul, zpow_add_one₀ (by simp), mul_comm _ (D : ℝ), ← mul_assoc]
      gcongr; trans 100 * 4
      · norm_num
      · gcongr; exact four_le_realD X

open scoped Classical in
/-- Part of Lemma 7.5.2. -/
lemma sum_χ (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (x : X) :
    ∑ J ∈ 𝓙₅ t u₁ u₂, χ t u₁ u₂ J x = (𝓘 u₁ : Set X).indicator 1 x := by
  simp_rw [χ, ← Finset.sum_div, NNReal.div_self_eq_ite, indicator, Pi.one_apply]
  refine if_congr ?_ rfl rfl
  simp_rw [NNReal.finset_sum_pos_iff, mem_toFinset, χtilde_pos_iff]
  conv_lhs => enter [1, J]; rw [and_rotate]
  rw [exists_and_left, Grid.mem_def, and_iff_left_iff_imp, ← union_𝓙₅ hu₁ hu₂ hu h2u]; intro mx
  rw [mem_iUnion₂] at mx; obtain ⟨J, mJ, hJ⟩ := mx
  refine ⟨J, Grid_subset_ball.trans (ball_subset_ball ?_) hJ, mJ⟩
  change (4 : ℝ) * D ^ s J ≤ _; gcongr; norm_num

/-- Part of Lemma 7.5.2. -/
lemma χ_le_indicator (hJ : J ∈ 𝓙₅ t u₁ u₂) :
    χ t u₁ u₂ J x ≤ (ball (c J) (8 * D ^ s J)).indicator 1 x := by
  classical
  simp_rw [χ, indicator, Pi.one_apply]
  split_ifs with h
  · apply NNReal.div_le_of_le_mul; rw [one_mul]
    apply Finset.single_le_sum (f := fun J ↦ χtilde J u₁ x) (fun _ _ ↦ zero_le _)
    rwa [mem_toFinset]
  · have : χtilde J u₁ x = 0 := by
      contrapose! h; rw [← zero_lt_iff, χtilde_pos_iff] at h; exact h.2
    simp [this]

/-- The constant used in `dist_χ_le`. Has value `2 ^ (226 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_2 (a : ℕ) : ℝ≥0 := 2 ^ (226 * (a : ℝ) ^ 3)

lemma one_le_C7_5_2 : 1 ≤ C7_5_2 a := by
  rw [C7_5_2]; exact_mod_cast Nat.one_le_two_pow

open scoped Classical in
lemma quarter_add_two_mul_D_mul_card_le (hJ : J ∈ 𝓙₅ t u₁ u₂) :
    1 / 4 + 2 * (D : ℝ) * {J' ∈ (𝓙₅ t u₁ u₂).toFinset |
      ¬Disjoint (ball (c J) (8 * D ^ s J)) (ball (c J') (8 * D ^ s J'))}.card ≤ C7_5_2 a := by
  set V := {J' ∈ (𝓙₅ t u₁ u₂).toFinset |
      ¬Disjoint (ball (c J) (8 * D ^ s J)) (ball (c J') (8 * D ^ s J'))}
  suffices V.card ≤ 2 ^ (200 * a ^ 3 + 7 * a) by
    calc
      _ ≤ 1 / 4 + 2 * (D : ℝ) * 2 ^ (200 * a ^ 3 + 7 * a) := by gcongr; norm_cast
      _ ≤ 2 ^ (100 * a ^ 2 + 1 + (200 * a ^ 3 + 7 * a)) +
          2 ^ (100 * a ^ 2 + 1 + (200 * a ^ 3 + 7 * a)) := by
        rw [defaultD, Nat.cast_pow, Nat.cast_ofNat, ← pow_succ', ← pow_add]
        gcongr; trans 1
        · norm_num
        · norm_cast; exact Nat.one_le_two_pow
      _ ≤ _ := by
        rw [← two_mul, ← pow_succ', C7_5_2,
          show 100 * a ^ 2 + 1 + (200 * a ^ 3 + 7 * a) + 1 =
            200 * a ^ 3 + 100 * a ^ 2 + 7 * a + 2 by ring]
        norm_cast; apply pow_le_pow_right' one_le_two
        calc
          _ = 200 * a ^ 3 + 25 * 4 * a ^ 2 + 7 * a + 2 := by norm_num
          _ ≤ 200 * a ^ 3 + 25 * a * a ^ 2 + 7 * a + a := by gcongr <;> linarith [four_le_a X]
          _ = 225 * a ^ 3 + 4 * 2 * a := by ring
          _ ≤ 225 * a ^ 3 + a * a * a := by gcongr <;> linarith [four_le_a X]
          _ = _ := by ring
  have dbl : ∀ J' ∈ V, volume (ball (c J) (9 * D ^ (s J + 1))) ≤
      2 ^ (200 * a ^ 3 + 7 * a) * volume (ball (c J') (D ^ s J' / 4)) := fun J' mJ' ↦ by
    simp_rw [V, Finset.mem_filter, mem_toFinset] at mJ'
    have hs := moderate_scale_change hJ mJ'.1 mJ'.2
    rw [disjoint_comm] at mJ'
    have hs' := moderate_scale_change mJ'.1 hJ mJ'.2
    calc
      _ ≤ 2 ^ (200 * a ^ 3) * volume (ball (c J') (18 * D ^ s J')) := by
        have db : dist (c J') (c J) + 9 * D ^ (s J + 1) ≤ D ^ 2 * (18 * D ^ s J') :=
          calc
            _ ≤ 8 * (D : ℝ) ^ s J' + 8 * D ^ s J + 9 * D ^ (s J + 1) := by
              gcongr; exact (dist_lt_of_not_disjoint_ball mJ'.2).le
            _ ≤ 8 * (D : ℝ) ^ (s J + 1) + D ^ (s J + 1) + 9 * D ^ (s J + 1) := by
              gcongr; exacts [one_le_D, by omega, by
                rw [zpow_add_one₀ (by simp), mul_comm 8]; gcongr; exact eight_le_realD X]
            _ ≤ _ := by
              rw [← add_one_mul, ← add_mul, ← mul_assoc, ← mul_rotate, ← zpow_natCast,
                ← zpow_add₀ (by simp), mul_comm _ 18, show (8 : ℝ) + 1 + 9 = 18 by norm_num]
              gcongr 18 * (D : ℝ) ^ ?_; exacts [one_le_D, by omega]
        convert measure_ball_le_of_dist_le' (μ := volume) (by simp) db
        simp_rw [As, defaultA, defaultD, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, Real.logb_pow,
          Real.logb_self_eq_one one_lt_two, mul_one, Nat.ceil_natCast, ENNReal.coe_pow,
          ENNReal.coe_ofNat]
        ring
      _ ≤ 2 ^ (200 * a ^ 3 + 7 * a) * volume (ball (c J') (18 / 128 * D ^ s J')) := by
        nth_rw 1 [show (18 : ℝ) * D ^ s J' = 2 ^ 7 * (18 / 128 * D ^ s J') by ring]
        rw [pow_add, mul_assoc]; gcongr
        convert measure_ball_two_le_same_iterate (μ := volume) (c J') _ 7 using 2
        unfold defaultA; norm_cast; rw [← pow_mul']
      _ ≤ _ := by rw [div_eq_inv_mul _ 4]; gcongr; norm_num
  replace dbl : V.card * volume (ball (c J) (9 * D ^ (s J + 1))) ≤
      2 ^ (200 * a ^ 3 + 7 * a) * volume (ball (c J) (9 * D ^ (s J + 1))) := by
    calc
      _ ≤ 2 ^ (200 * a ^ 3 + 7 * a) * ∑ J' ∈ V, volume (ball (c J') (D ^ s J' / 4)) := by
        rw [Finset.mul_sum, ← nsmul_eq_mul, ← Finset.sum_const]; exact Finset.sum_le_sum dbl
      _ = 2 ^ (200 * a ^ 3 + 7 * a) * volume (⋃ J' ∈ V, ball (c J') (D ^ s J' / 4)) := by
        congr; refine (measure_biUnion_finset ?_ fun _ _ ↦ measurableSet_ball).symm
        have Vs : V ⊆ (t.𝓙₅ u₁ u₂).toFinset := Finset.filter_subset ..
        rw [subset_toFinset] at Vs
        exact (pairwiseDisjoint_𝓙₅.subset Vs).mono fun _ ↦ ball_subset_Grid
      _ ≤ _ := by
        gcongr; refine iUnion₂_subset fun J' mJ' ↦ ball_subset_ball' ?_
        simp_rw [V, Finset.mem_filter, mem_toFinset] at mJ'
        have hs := moderate_scale_change hJ mJ'.1 mJ'.2
        rw [disjoint_comm] at mJ'
        have hs' := moderate_scale_change mJ'.1 hJ mJ'.2
        calc
          _ ≤ (D : ℝ) ^ s J' / 4 + (8 * D ^ s J' + 8 * D ^ s J) := by
            gcongr; exact (dist_lt_of_not_disjoint_ball mJ'.2).le
          _ ≤ (D : ℝ) ^ (s J + 1) / 4 + (8 * D ^ (s J + 1) + (8 * D / 25) * D ^ s J) := by
            have : (8 : ℝ) ≤ 8 * D / 25 := by
              rw [le_div_iff₀ (by norm_num)]; gcongr; exact twentyfive_le_realD X
            gcongr; exacts [one_le_D, by omega, one_le_D, by omega]
          _ ≤ _ := by
            rw [show 8 * (D : ℝ) / 25 * D ^ s J = 8 / 25 * (D ^ s J * D) by ring,
              ← zpow_add_one₀ (by simp), ← add_mul, div_eq_inv_mul, ← add_mul]
            gcongr; norm_num
  have vpos : 0 < volume (ball (c J) (9 * ↑D ^ (s J + 1))) := by
    apply measure_ball_pos volume; unfold defaultD; positivity
  rw [ENNReal.mul_le_mul_right vpos.ne' measure_ball_lt_top.ne] at dbl
  exact_mod_cast dbl

/-- Part of Lemma 7.5.2. -/
lemma dist_χ_le (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (mx : x ∈ 𝓘 u₁) (mx' : x' ∈ 𝓘 u₁) :
    dist (χ t u₁ u₂ J x) (χ t u₁ u₂ J x') ≤ C7_5_2 a * dist x x' / D ^ s J := by
  classical
  by_cases hxx : x ∉ ball (c J) (8 * D ^ s J) ∧ x' ∉ ball (c J) (8 * D ^ s J)
  · have n₁ := χ_le_indicator hJ (x := x)
    rw [indicator_of_not_mem hxx.1, nonpos_iff_eq_zero] at n₁
    have n₂ := χ_le_indicator hJ (x := x')
    rw [indicator_of_not_mem hxx.2, nonpos_iff_eq_zero] at n₂
    rw [n₁, n₂, dist_self]; positivity
  rw [not_and_or, not_not_mem, not_not_mem] at hxx
  wlog hx : x ∈ ball (c J) (8 * D ^ s J) generalizing x x'
  · rw [or_comm] at hxx; specialize this mx' mx hxx (hxx.resolve_right hx)
    rwa [dist_comm, dist_comm x' x] at this
  clear hxx
  let ctx := χtilde J u₁ x
  let ctx' := χtilde J u₁ x'
  let ax := ∑ J' ∈ 𝓙₅ t u₁ u₂, χtilde J' u₁ x
  let ax' := ∑ J' ∈ 𝓙₅ t u₁ u₂, χtilde J' u₁ x'
  have ax4 : 4 ≤ ax := (four_lt_sum_χtilde hu₁ hu₂ hu h2u mx).le
  have ax'4 : 4 ≤ ax' := (four_lt_sum_χtilde hu₁ hu₂ hu h2u mx').le
  have nax : (ax : ℝ) ≠ 0 := by exact_mod_cast (zero_lt_four.trans_le ax4).ne'
  have nax' : (ax' : ℝ) ≠ 0 := by exact_mod_cast (zero_lt_four.trans_le ax'4).ne'
  have part1 : dist (χ t u₁ u₂ J x) (χ t u₁ u₂ J x') ≤
      (dist x x' / D ^ s J + ctx' * dist ax ax') / 4 := by
    calc
      _ = ‖(ctx - ctx' : ℝ) / ax - ctx' * (ax - ax') / (ax * ax')‖ := by
        rw [mul_sub, sub_div, sub_div, mul_div_mul_right _ _ nax', mul_comm (ax : ℝ) ax',
          mul_div_mul_right _ _ nax, ← sub_add, sub_right_comm, sub_add_cancel]; rfl
      _ ≤ dist ctx ctx' / ax + ctx' * dist ax ax' / (ax * ax') := by
        change _ ≤ ‖(ctx - ctx' : ℝ)‖ / ax + ctx' * ‖(ax - ax' : ℝ)‖ / (ax * ax')
        conv_rhs => enter [1]; rw [← NNReal.norm_eq ax]
        conv_rhs =>
          enter [2]; rw [← NNReal.norm_eq ctx']
          enter [2]; rw [← NNReal.norm_eq ax, ← NNReal.norm_eq ax']
        rw [← norm_mul, ← norm_mul, ← norm_div, ← norm_div]
        exact nnnorm_sub_le ..
      _ ≤ dist ctx ctx' / 4 + ctx' * dist ax ax' / (1 * 4) := by
        gcongr <;> norm_cast; exact le_trans (by norm_num) ax4
      _ ≤ _ := by
        rw [one_mul, ← add_div]; gcongr; exact dist_χtilde_le mx mx'
  apply part1.trans
  by_cases hx' : x' ∉ ball (c J) (8 * D ^ s J)
  · have : ctx' = 0 := by
      simp_rw [ctx', ← not_ne_iff, ← zero_lt_iff, χtilde_pos_iff]; tauto
    rw [this, NNReal.coe_zero, zero_mul, add_zero, div_eq_inv_mul _ 4, mul_div_assoc]; gcongr
    rw [show 4⁻¹ = (2 : ℝ) ^ (-2 : ℝ) by norm_num, C7_5_2, NNReal.coe_rpow, NNReal.coe_ofNat,
      Real.rpow_le_rpow_left_iff one_lt_two]
    norm_cast; omega
  rw [not_not_mem] at hx'
  calc
    _ ≤ (dist x x' / D ^ s J +
        8 * ∑ J' ∈ 𝓙₅ t u₁ u₂, dist (χtilde J' u₁ x) (χtilde J' u₁ x')) / 4 := by
      gcongr
      · exact χtilde_le_eight
      · have := dist_sum_sum_le (𝓙₅ t u₁ u₂).toFinset
          (fun J' ↦ (χtilde J' u₁ x : ℝ)) (fun J' ↦ χtilde J' u₁ x')
        exact_mod_cast this
    _ = (dist x x' / D ^ s J +
        8 * ∑ J' ∈ 𝓙₅ t u₁ u₂ with
          ¬Disjoint (ball (c J) (8 * D ^ s J)) (ball (c J') (8 * D ^ s J')),
            dist (χtilde J' u₁ x) (χtilde J' u₁ x')) / 4 := by
      congr 3; refine (Finset.sum_filter_of_ne fun J' mJ' hd ↦ ?_).symm; contrapose! hd
      have h₁ : χtilde J' u₁ x = 0 := by
        have := disjoint_left.mp hd hx
        rw [← not_ne_iff, ← zero_lt_iff, χtilde_pos_iff]; tauto
      have h₂ : χtilde J' u₁ x' = 0 := by
        have := disjoint_left.mp hd hx'
        rw [← not_ne_iff, ← zero_lt_iff, χtilde_pos_iff]; tauto
      rw [h₁, h₂, dist_self]
    _ ≤ (dist x x' / D ^ s J +
        8 * ∑ J' ∈ 𝓙₅ t u₁ u₂ with
          ¬Disjoint (ball (c J) (8 * D ^ s J)) (ball (c J') (8 * D ^ s J')),
            dist x x' * D ^ (1 - s J)) / 4 := by
      gcongr with J' mJ'; trans dist x x' / D ^ (s J')
      · exact dist_χtilde_le mx mx'
      · rw [div_eq_mul_inv, ← zpow_neg]; gcongr
        · exact one_le_D
        · rw [Finset.mem_filter, mem_toFinset] at mJ'
          rw [neg_le, neg_sub]; exact moderate_scale_change hJ mJ'.1 mJ'.2
    _ = dist x x' / (D : ℝ) ^ s J *
        (1 / 4 + 2 * D * {J' ∈ (𝓙₅ t u₁ u₂).toFinset |
          ¬Disjoint (ball (c J) (8 * D ^ s J)) (ball (c J') (8 * D ^ s J'))}.card) := by
      rw [Finset.sum_const, nsmul_eq_mul, zpow_sub₀ (by simp), zpow_one,
        show 8 * (_ * (dist x x' * (D / D ^ s J))) = dist x x' / D ^ s J * (2 * D * _) * 4 by ring,
        add_div, mul_div_cancel_right₀ _ four_ne_zero, div_eq_mul_one_div, ← mul_add]
    _ ≤ _ := by rw [mul_comm, mul_div_assoc]; gcongr; exact quarter_add_two_mul_D_mul_card_le hJ

end TileStructure.Forest
