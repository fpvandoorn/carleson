import Carleson.Calculations
import Carleson.ForestOperator.AlmostOrthogonality
import Carleson.HolderVanDerCorput
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

/-! ## Section 7.5 -/

variable (t u₁ u₂) in
/-- The definition `𝓙'` at the start of Section 7.5.1.
We use a different notation to distinguish it from the 𝓙' used in Section 7.6 -/
def 𝓙₅ : Set (Grid X) := 𝓙 (𝔖₀ t u₁ u₂) ∩ Iic (𝓘 u₁)

/-- The definition of χ-tilde, defined in the proof of Lemma 7.5.2 -/
def χtilde (J : Grid X) (u₁ : 𝔓 X) : X → ℝ≥0 :=
  (𝓘 u₁ : Set X).indicator fun x ↦ (8 - D ^ (- s J) * dist x (c J)).toNNReal

lemma χtilde_pos_iff : 0 < χtilde J u₁ x ↔ x ∈ 𝓘 u₁ ∧ x ∈ ball (c J) (8 * D ^ s J) := by
  have := @one_le_realD a; rw [χtilde]
  by_cases h : x ∈ 𝓘 u₁
  · rw [indicator_of_mem h, Real.toNNReal_pos, sub_pos, zpow_neg, inv_mul_lt_iff₀' (by positivity)]
    exact iff_and_self.mpr fun a ↦ h
  · rw [indicator_of_notMem h]
    apply Iff.intro
    · simp
    · simp only [lt_self_iff_false, imp_false, not_and]
      intro h1
      exfalso
      exact h h1

lemma χtilde_le_eight : χtilde J u₁ x ≤ 8 := by
  unfold χtilde; apply indicator_le fun _ _ ↦ ?_
  rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_ofNat, sub_le_self_iff]
  positivity

lemma four_lt_χtilde (xJ : x ∈ J) (xu : x ∈ 𝓘 u₁) : 4 < χtilde J u₁ x := by
  have := one_le_realD a
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

lemma stronglyMeasurable_χtilde : StronglyMeasurable (χtilde J u₁) :=
  measurable_id.dist measurable_const |>.const_mul _ |>.const_sub _
    |>.real_toNNReal.indicator coeGrid_measurable |>.stronglyMeasurable

variable (t u₁ u₂) in
open scoped Classical in
/-- The definition of χ, defined in the proof of Lemma 7.5.2 -/
def χ (J : Grid X) (x : X) : ℝ≥0 :=
  χtilde J u₁ x / ∑ J' ∈ 𝓙₅ t u₁ u₂, χtilde J' u₁ x

lemma stronglyMeasurable_χ : StronglyMeasurable (χ t u₁ u₂ J) :=
  stronglyMeasurable_χtilde.measurable.div
    (Finset.measurable_sum _ fun _ _ ↦ stronglyMeasurable_χtilde.measurable) |>.stronglyMeasurable

-- /-- The definition of `B`, defined in (7.5.1) -/

variable (t u₁ u₂) in
/-- The definition of h_J, defined in the proof of Section 7.5.2 -/
def holderFunction (f₁ f₂ : X → ℂ) (J : Grid X) (x : X) : ℂ :=
  χ t u₁ u₂ J x * (exp (.I * 𝒬 u₁ x) * adjointCarlesonSum (t u₁) f₁ x) *
  conj (exp (.I * 𝒬 u₂ x) * adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ x)

/- AUXILIARY LEMMAS:START -/

lemma IF_subset_THEN_not_disjoint {A B : Grid X} (h : (A : Set X) ⊆ B) :
    ¬ Disjoint (B : Set X) (A : Set X) := by
  rw [disjoint_comm, Set.disjoint_of_subset_iff_left_eq_empty h, ← Ne, ← nonempty_iff_ne_empty]
  exact Grid.nonempty A

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
    _ ≤ (dist a c + dist c d) + dist d e := add_le_add_left (dist_triangle a c d) _
    _ ≤ (dist a b + dist b c + dist c d) + dist d e :=
      add_le_add_left (add_le_add_left (dist_triangle a b c) _) _

lemma 𝓘_subset_iUnion_𝓙_𝔖₀ : (𝓘 u₁ : Set X) ⊆ ⋃ J ∈ 𝓙 (t.𝔖₀ u₁ u₂), (J : Set X) := by
  rw [biUnion_𝓙 (𝔖 := 𝔖₀ t u₁ u₂)]
  apply subset_iUnion_of_subset (𝓘 u₁)
  rfl

/- AUXILIARY LEMMAS:END -/

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
          apply subset_of_notMem_Iic_of_not_disjoint cube
          · have notIn : cube ∉ t.𝓙₅ u₁ u₂ := fun a ↦ contr cube a xInCube
            rw [𝓙₅, inter_def, Set.mem_setOf_eq, not_and_or] at notIn
            exact Or.resolve_left notIn (Set.not_notMem.mpr cube_in_𝓙)
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

lemma bigger_than_𝓙_is_not_in_𝓙₀ {𝔖 : Set (𝔓 X)} {A B : Grid X}
    (le : A ≤ B) (sle : s A < s B) (A_in : A ∈ 𝓙 𝔖) :
    B ∉ 𝓙₀ 𝔖 := by
  replace A_in := A_in.2
  simp only [Grid.le_def, and_imp] at A_in
  intro contr
  apply Lean.Omega.Int.le_lt_asymm (x := s A) (y := s B)
  · exact (A_in contr le.1 (le_of_lt sle)).2
  · exact sle

/-- Lemma 7.5.3 (stated somewhat differently). -/
lemma moderate_scale_change (hJ : J ∈ 𝓙₅ t u₁ u₂) (hJ' : J' ∈ 𝓙₅ t u₁ u₂)
    (hd : ¬Disjoint (ball (c J) (8 * D ^ s J)) (ball (c J') (8 * D ^ s J'))) :
    s J - 1 ≤ s J' := by
  by_contra! hs
  have fa : ∀ p ∈ t.𝔖₀ u₁ u₂, ¬↑(𝓘 p) ⊆ ball (c J) (100 * D ^ (s J + 1)) :=
    hJ.1.1.resolve_left (by linarith [(scale_mem_Icc (i := J')).1])
  apply absurd fa; push Not
  obtain ⟨J'', sJ'', lJ''⟩ : ∃ J'', s J'' = s J' + 1 ∧ J' ≤ J'' := by
    refine Grid.exists_supercube (s J' + 1) ⟨by lia, ?_⟩
    rw [lt_sub_iff_add_lt] at hs; exact hs.le.trans scale_mem_Icc.2
  obtain ⟨p, mp, sp⟩ : ∃ p ∈ t.𝔖₀ u₁ u₂, ↑(𝓘 p) ⊆ ball (c J'') (100 * D ^ (s J' + 1 + 1)) := by
    have : J'' ∉ 𝓙₀ (t.𝔖₀ u₁ u₂) := bigger_than_𝓙_is_not_in_𝓙₀ lJ'' (by linarith) hJ'.1
    rw [𝓙₀, mem_setOf_eq, sJ''] at this; push Not at this; exact this.2
  use p, mp, sp.trans (ball_subset_ball' ?_)
  calc
    _ ≤ 100 * D ^ (s J' + 1 + 1) + (dist (c J'') (c J') + dist (c J) (c J')) :=
      add_le_add_right (dist_triangle_right ..) _
    _ ≤ 100 * D ^ (s J' + 1 + 1) + (4 * D ^ s J'' + 8 * D ^ s J + 8 * D ^ s J') := by
      rw [add_assoc (4 * _)]; gcongr
      · exact (mem_ball'.mp (Grid_subset_ball (lJ''.1 Grid.c_mem_Grid))).le
      · exact (dist_lt_of_not_disjoint_ball hd).le
    _ ≤ 100 * D ^ s J + (4 * D ^ s J + 8 * D ^ s J + 8 * D ^ s J) := by
      gcongr; exacts [one_le_realD a, by lia, one_le_realD a, by lia, one_le_realD a, by lia]
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
  simp_rw [Finset.sum_pos_iff, mem_toFinset, χtilde_pos_iff]
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

lemma χ_eq_zero_of_notMem_ball (hJ : J ∈ 𝓙₅ t u₁ u₂) (nx : x ∉ ball (c J) (8 * D ^ s J)) :
    χ t u₁ u₂ J x = 0 := by
  have := χ_le_indicator hJ (x := x)
  rwa [indicator_of_notMem nx, le_zero_iff] at this

lemma boundedCompactSupport_toReal_χ (hJ : J ∈ 𝓙₅ t u₁ u₂) :
    BoundedCompactSupport fun x ↦ (χ t u₁ u₂ J x : ℝ) := by
  apply BoundedCompactSupport.mono_norm (g := fun x ↦ (ball (c J) (8 * D ^ s J)).indicator 1 x)
    ?_ ?_ (fun x ↦ ?_)
  · constructor
    · refine memLp_top_of_bound (by fun_prop (discharger := measurability)) 1 (.of_forall fun x ↦ ?_)
      unfold indicator; split_ifs <;> simp
    · refine HasCompactSupport.intro (isCompact_closedBall (c J) (8 * D ^ s J)) fun x mx ↦ ?_
      apply indicator_of_notMem; contrapose! mx; exact ball_subset_closedBall mx
  · exact stronglyMeasurable_χ.measurable.coe_nnreal_real.aestronglyMeasurable
  · simp_rw [show (1 : X → ℝ) = (↑) ∘ (1 : X → ℝ≥0) by rfl]
    rw [indicator_comp_of_zero (by simp), Function.comp_apply, Real.norm_eq_abs, NNReal.abs_eq,
      NNReal.coe_le_coe]
    exact χ_le_indicator hJ

/-- The constant used in `dist_χ_le`.
Has value `2 ^ (227 * a ^ 3)` in the blueprint. -/
irreducible_def C7_5_2 (a : ℕ) : ℝ≥0 := 2 ^ ((2 * 𝕔 + 2 + 𝕔 / 4) * a ^ 3)

lemma one_le_C7_5_2 : 1 ≤ C7_5_2 a := by
  rw [C7_5_2]; exact_mod_cast Nat.one_le_two_pow

open scoped Classical in
lemma quarter_add_two_mul_D_mul_card_le (hJ : J ∈ 𝓙₅ t u₁ u₂) :
    1 / 4 + 2 * (D : ℝ) * {J' ∈ (𝓙₅ t u₁ u₂).toFinset |
      ¬Disjoint (ball (c J) (8 * D ^ s J)) (ball (c J') (8 * D ^ s J'))}.card ≤ C7_5_2 a := by
  set V := {J' ∈ (𝓙₅ t u₁ u₂).toFinset |
      ¬Disjoint (ball (c J) (8 * D ^ s J)) (ball (c J') (8 * D ^ s J'))}
  suffices V.card ≤ 2 ^ (2 * 𝕔 * a ^ 3 + 7 * a) by
    calc
      _ ≤ 1 / 4 + 2 * (D : ℝ) * 2 ^ (2 * 𝕔 * a ^ 3 + 7 * a) := by gcongr; norm_cast
      _ ≤ 2 ^ (𝕔 * a ^ 2 + 1 + (2 * 𝕔 * a ^ 3 + 7 * a)) +
          2 ^ (𝕔 * a ^ 2 + 1 + (2 * 𝕔 * a ^ 3 + 7 * a)) := by
        rw [defaultD, Nat.cast_pow, Nat.cast_ofNat, ← pow_succ', ← pow_add]
        gcongr; trans 1
        · norm_num
        · norm_cast; exact Nat.one_le_two_pow
      _ ≤ _ := by
        rw [C7_5_2]
        norm_cast
        apply add_le_pow_two le_rfl le_rfl ?_
        have := four_le_a X
        ring_nf
        suffices 𝕔 * a ^ 2 + 7 * a + 2 ≤ a ^ 3 * 2 + a ^ 3 * (𝕔 / 4)  by linarith
        calc
          _ ≤ (4 * (𝕔 / 4) + 3) * a ^ 2 + 7 * a + a := by
            gcongr
            · lia
            · linarith
          _ = (𝕔 / 4) * 4 * a ^ 2 + 3 * a ^ 2 + 2 * 4 * a := by ring
          _ ≤ (𝕔 / 4) * a * a ^ 2 + 3 * a ^ 2 + 2 * a * a := by gcongr
          _ = (𝕔 / 4) * a ^ 3 + 5 * a ^ 2 := by ring
          _ ≤ (𝕔 / 4) * a ^ 3 + 2 * 4 * a ^ 2 := by gcongr; norm_num
          _ ≤ (𝕔 / 4) * a ^ 3 + 2 * a * a ^ 2 := by gcongr
          _ = _ := by ring
  have dbl : ∀ J' ∈ V, volume (ball (c J) (9 * D ^ (s J + 1))) ≤
      2 ^ (2 * 𝕔 * a ^ 3 + 7 * a) * volume (ball (c J') (D ^ s J' / 4)) := fun J' mJ' ↦ by
    simp_rw [V, Finset.mem_filter, mem_toFinset] at mJ'
    have hs := moderate_scale_change hJ mJ'.1 mJ'.2
    rw [disjoint_comm] at mJ'
    have hs' := moderate_scale_change mJ'.1 hJ mJ'.2
    calc
      _ ≤ 2 ^ (2 * 𝕔 * a ^ 3) * volume (ball (c J') (18 * D ^ s J')) := by
        have db : dist (c J') (c J) + 9 * D ^ (s J + 1) ≤ D ^ 2 * (18 * D ^ s J') :=
          calc
            _ ≤ 8 * (D : ℝ) ^ s J' + 8 * D ^ s J + 9 * D ^ (s J + 1) := by
              gcongr; exact (dist_lt_of_not_disjoint_ball mJ'.2).le
            _ ≤ 8 * (D : ℝ) ^ (s J + 1) + D ^ (s J + 1) + 9 * D ^ (s J + 1) := by
              gcongr; exacts [one_le_realD a, by lia, by
                rw [zpow_add_one₀ (by simp), mul_comm 8]; gcongr; exact eight_le_realD X]
            _ ≤ _ := by
              rw [← add_one_mul, ← add_mul, ← mul_assoc, ← mul_rotate, ← zpow_natCast,
                ← zpow_add₀ (by simp), mul_comm _ 18, show (8 : ℝ) + 1 + 9 = 18 by norm_num]
              gcongr 18 * (D : ℝ) ^ ?_; exacts [one_le_realD a, by lia]
        convert measure_ball_le_of_dist_le' (μ := volume) (by simp) db
        simp_rw [As, defaultA, defaultD, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, Real.logb_pow,
          Real.logb_self_eq_one one_lt_two, mul_one, Nat.ceil_natCast, ENNReal.coe_pow,
          ENNReal.coe_ofNat]
        ring
      _ ≤ 2 ^ (2 * 𝕔 * a ^ 3 + 7 * a) * volume (ball (c J') (18 / 128 * D ^ s J')) := by
        nth_rw 1 [show (18 : ℝ) * D ^ s J' = 2 ^ 7 * (18 / 128 * D ^ s J') by ring]
        rw [pow_add, mul_assoc, mul_assoc]; gcongr
        convert measure_ball_two_le_same_iterate (μ := volume) (c J') _ 7 using 2
        unfold defaultA; norm_cast; rw [← pow_mul']
      _ ≤ _ := by rw [div_eq_inv_mul _ 4]; gcongr; norm_num
  replace dbl : V.card * volume (ball (c J) (9 * D ^ (s J + 1))) ≤
      2 ^ (2 * 𝕔 * a ^ 3 + 7 * a) * volume (ball (c J) (9 * D ^ (s J + 1))) := by
    calc
      _ ≤ 2 ^ (2 * 𝕔 * a ^ 3 + 7 * a) * ∑ J' ∈ V, volume (ball (c J') (D ^ s J' / 4)) := by
        rw [Finset.mul_sum, ← nsmul_eq_mul, ← Finset.sum_const]; exact Finset.sum_le_sum dbl
      _ = 2 ^ (2 * 𝕔 * a ^ 3 + 7 * a) * volume (⋃ J' ∈ V, ball (c J') (D ^ s J' / 4)) := by
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
            gcongr; exacts [one_le_realD a, by lia, one_le_realD a, by lia]
          _ ≤ _ := by
            rw [show 8 * (D : ℝ) / 25 * D ^ s J = 8 / 25 * (D ^ s J * D) by ring,
              ← zpow_add_one₀ (by simp), ← add_mul, div_eq_inv_mul, ← add_mul]
            gcongr; norm_num
  have vpos : 0 < volume (ball (c J) (9 * D ^ (s J + 1))) := by
    apply measure_ball_pos volume; unfold defaultD; positivity
  rw [ENNReal.mul_le_mul_iff_left vpos.ne' measure_ball_lt_top.ne] at dbl
  exact_mod_cast dbl

/-- Part of Lemma 7.5.2. -/
lemma dist_χ_le (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (mx : x ∈ 𝓘 u₁) (mx' : x' ∈ 𝓘 u₁) :
    dist (χ t u₁ u₂ J x) (χ t u₁ u₂ J x') ≤ C7_5_2 a * dist x x' / D ^ s J := by
  classical
  by_cases hxx : x ∉ ball (c J) (8 * D ^ s J) ∧ x' ∉ ball (c J) (8 * D ^ s J)
  · have n₁ := χ_le_indicator hJ (x := x)
    rw [indicator_of_notMem hxx.1, nonpos_iff_eq_zero] at n₁
    have n₂ := χ_le_indicator hJ (x := x')
    rw [indicator_of_notMem hxx.2, nonpos_iff_eq_zero] at n₂
    rw [n₁, n₂, dist_self]; positivity
  rw [not_and_or, not_notMem, not_notMem] at hxx
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
    rw [show 4⁻¹ = (2 : ℝ) ^ (-2 : ℝ) by norm_num, C7_5_2, NNReal.coe_pow, NNReal.coe_ofNat,
      ← Real.rpow_natCast, Real.rpow_le_rpow_left_iff one_lt_two]
    apply le_trans ?_ (by positivity)
    linarith
  rw [not_notMem] at hx'
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
        · exact one_le_realD a
        · rw [Finset.mem_filter, mem_toFinset] at mJ'
          rw [neg_le, neg_sub]; exact moderate_scale_change hJ mJ'.1 mJ'.2
    _ = dist x x' / (D : ℝ) ^ s J *
        (1 / 4 + 2 * D * {J' ∈ (𝓙₅ t u₁ u₂).toFinset |
          ¬Disjoint (ball (c J) (8 * D ^ s J)) (ball (c J') (8 * D ^ s J'))}.card) := by
      rw [Finset.sum_const, nsmul_eq_mul, zpow_sub₀ (by simp), zpow_one,
        show 8 * (_ * (dist x x' * (D / D ^ s J))) = dist x x' / D ^ s J * (2 * D * _) * 4 by ring,
        add_div, mul_div_cancel_right₀ _ four_ne_zero, div_eq_mul_one_div, ← mul_add]
    _ ≤ _ := by rw [mul_comm, mul_div_assoc]; gcongr; exact quarter_add_two_mul_D_mul_card_le hJ

/-! ### Subsection 7.5.2 and Lemma 7.5.4 -/

/-- The constant used in `holder_correlation_tile`.
Has value `2 ^ (128 * a ^ 3)` in the blueprint. -/
irreducible_def C7_5_5 (a : ℕ) : ℝ≥0 := 2 ^ ((𝕔 + 3 + 𝕔 / 4) * a ^ 3)

section OneInOneOut

omit [ProofData a q K σ₁ σ₂ F G] in
lemma ψ_le_max [ProofData a q K σ₁ σ₂ F G] {x : ℝ} : ψ x ≤ max 0 ((2 - 4 * x) ^ (a : ℝ)⁻¹) := by
  by_cases! h₁ : x ≤ 1 / 4
  · exact (ψ_le_one ..).trans ((Real.one_le_rpow (by linarith) (by simp)).trans (le_max_right ..))
  by_cases! h₂ : 1 / 2 ≤ x
  · rw [ψ_formula₄ h₂]; exact le_max_left ..
  rw [ψ_formula₃ (one_lt_realD X) ⟨h₁.le, h₂.le⟩]
  refine le_trans ?_ (le_max_right ..)
  set y := 2 - 4 * x; apply Real.self_le_rpow_of_le_one
  · unfold y; linarith
  · unfold y; linarith
  · exact Nat.cast_inv_le_one a

lemma le_of_mem_E {y : X} (hy : y ∈ E p) (hx' : x' ∉ ball (𝔠 p) (5 * D ^ 𝔰 p)) :
    2 - 4 * ((D : ℝ) ^ (-𝔰 p) * dist y x) ≤ dist x x' / D ^ (𝔰 p) * 4 := by
  have := one_le_realD a
  calc
    _ ≤ 2 - 4 * (D : ℝ) ^ (-𝔰 p) * (dist x (𝔠 p) - dist y (𝔠 p)) := by
      rw [mul_assoc]; gcongr; rw [sub_le_iff_le_add]; exact dist_triangle_left ..
    _ ≤ 2 - 4 * (D : ℝ) ^ (-𝔰 p) * dist x (𝔠 p) + 16 := by
      rw [mul_sub, sub_add]; gcongr; rw [mul_rotate, show (16 : ℝ) = 4 * 4 by norm_num]; gcongr
      rw [zpow_neg, inv_mul_le_iff₀' (by positivity)]
      exact (mem_ball.mp ((E_subset_𝓘.trans Grid_subset_ball) hy)).le
    _ = 4 * (D : ℝ) ^ (-𝔰 p) * (5 * D ^ 𝔰 p - dist x (𝔠 p)) - 2 := by
      rw [mul_sub, show 4 * (D : ℝ) ^ (-𝔰 p) * (5 * D ^ 𝔰 p) = 20 * (D ^ 𝔰 p * D ^ (-𝔰 p)) by ring,
        ← zpow_add₀ (by positivity), add_neg_cancel, zpow_zero, mul_one]; ring
    _ ≤ 4 * (D : ℝ) ^ (-𝔰 p) * (dist x' (𝔠 p) - dist x (𝔠 p)) - 2 := by
      gcongr; rwa [mem_ball, not_lt] at hx'
    _ ≤ 4 * (D : ℝ) ^ (-𝔰 p) * dist x x' - 2 := by
      gcongr; rw [sub_le_iff_le_add]; exact dist_triangle_left ..
    _ ≤ _ := by rw [zpow_neg, mul_rotate, inv_mul_eq_div]; norm_num

lemma enorm_ψ_le_edist {y : X} (my : y ∈ E p) (hx' : x' ∉ ball (𝔠 p) (5 * D ^ 𝔰 p)) :
    ‖ψ (D ^ (-𝔰 p) * dist y x)‖ₑ ≤ 4 * (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ := by
  by_cases h : 1 / 2 ≤ D ^ (-𝔰 p) * dist y x
  · rw [ψ_formula₄ h, enorm_zero]; exact zero_le _
  replace h : 0 ≤ 2 - 4 * (D ^ (-𝔰 p) * dist y x) := by linarith
  calc
    _ ≤ ‖max 0 ((2 - 4 * (D ^ (-𝔰 p) * dist y x)) ^ (a : ℝ)⁻¹)‖ₑ :=
      Real.enorm_le_enorm (zero_le_ψ ..) (ψ_le_max (X := X))
    _ = ‖2 - 4 * (D ^ (-𝔰 p) * dist y x)‖ₑ ^ (a : ℝ)⁻¹ := by
      rw [max_eq_right (Real.rpow_nonneg h _), Real.enorm_rpow_of_nonneg h (by positivity)]
    _ ≤ ‖dist x x' / D ^ (𝔰 p) * 4‖ₑ ^ (a : ℝ)⁻¹ := by
      gcongr; exact Real.enorm_le_enorm h (le_of_mem_E my hx')
    _ = (edist x x' / D ^ (𝔰 p) * 4) ^ (a : ℝ)⁻¹ := by
      rw [enorm_mul]; nth_rw 2 [enorm_eq_nnnorm]; rw [Real.nnnorm_ofNat, ENNReal.coe_ofNat]; congr
      rw [enorm_eq_nnnorm, nnnorm_div, nnnorm_zpow]; norm_cast
      rw [ENNReal.coe_div (by simp only [defaultD, Nat.cast_pow, Nat.cast_ofNat, defaultA,
        defaultκ.eq_1, ne_eq]; positivity), ENNReal.coe_zpow (by simp)]; norm_cast; congr
      rw [edist_dist, ← Real.enorm_of_nonneg dist_nonneg, enorm_eq_nnnorm]
    _ ≤ _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), mul_comm]; gcongr
      nth_rw 2 [← ENNReal.rpow_one 4]
      exact ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.cast_inv_le_one a)

lemma holder_correlation_tile_one
    (hf : BoundedCompactSupport f) (hx' : x' ∉ ball (𝔠 p) (5 * D ^ 𝔰 p)) :
    ‖adjointCarleson p f x‖ₑ ≤ C7_5_5 a / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) *
      (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ * ∫⁻ x in E p, ‖f x‖ₑ :=
  calc
    _ ≤ ∫⁻ y in E p, ‖conj (Ks (𝔰 p) y x)‖ₑ * ‖exp (I * (Q y y - Q y x))‖ₑ * ‖f y‖ₑ := by
      simp_rw [← enorm_mul]; exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y in E p, ‖Ks (𝔰 p) y x‖ₑ * ‖f y‖ₑ := by
      congr 1 with y; norm_cast; nth_rw 1 [mul_comm I]
      rw [enorm_exp_ofReal_mul_I, mul_one, RCLike.enorm_conj]
    _ ≤ ∫⁻ y in E p, C2_1_3 a / volume (ball y (D ^ 𝔰 p)) *
        ‖ψ (D ^ (-𝔰 p) * dist y x)‖ₑ * ‖f y‖ₑ := by gcongr; exact enorm_Ks_le'
    _ ≤ ∫⁻ y in E p, C2_1_3 a / (volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) / 2 ^ (3 * a)) *
        (4 * (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹) * ‖f y‖ₑ := by
      refine setLIntegral_mono_ae (hf.restrict.aestronglyMeasurable.enorm.const_mul _)
        (.of_forall fun y my ↦ ?_)
      gcongr with y
      · exact volume_xDsp_bound (E_subset_𝓘 my)
      · exact enorm_ψ_le_edist my hx'
    _ = C2_1_3 a * 2 ^ (3 * a) * 4 / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) *
        (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ * ∫⁻ y in E p, ‖f y‖ₑ := by
      rw [lintegral_const_mul'' _ hf.restrict.aestronglyMeasurable.enorm, ← mul_assoc]; congr 2
      rw [ENNReal.div_eq_inv_mul, ENNReal.inv_div (by simp) (by simp), mul_assoc,
        ENNReal.mul_comm_div, ← mul_div_assoc, ← mul_assoc, mul_comm (2 ^ (3 * a))]
    _ ≤ _ := by
      gcongr; rw [C2_1_3, C7_5_5]; norm_cast
      simp_rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]
      apply pow_le_pow_right' one_le_two
      calc
        _ ≤ (𝕔 + 2) * a ^ 3 + 3 * a + a := by gcongr; linarith [four_le_a X]
        _ = (𝕔 + 2) * a ^ 3 + 4 * 1 * a := by ring
        _ ≤ (𝕔 + 2) * a ^ 3 + a * a * a := by gcongr <;> linarith [four_le_a X]
        _ = (𝕔 + 3 + 0) * a ^ 3 := by ring
        _ ≤ (𝕔 + 3 + 𝕔 / 4) * a ^ 3 := by gcongr; positivity

end OneInOneOut

section BothIn

lemma integrable_adjointCarleson_interior (hf : BoundedCompactSupport f) :
    Integrable (fun y ↦ exp (.I * 𝒬 u x) * (conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x)) * f y))
      (volume.restrict (E p)) := by
  have h2f := hf.memLp_top.ae_norm_le
  set B := eLpNorm f ∞ volume |>.toReal
  refine Integrable.const_mul ?_ _; simp_rw [mul_rotate]
  refine Integrable.bdd_mul (c := B) ?_ ?_ ?_
  · have bep : IsBounded (E p) := by
      rw [isBounded_iff_subset_ball (𝔠 p)]; use 4 * D ^ 𝔰 p
      exact E_subset_𝓘.trans Grid_subset_ball
    obtain ⟨C, nnC, hC⟩ := IsBounded.exists_bound_of_norm_Ks bep (𝔰 p)
    apply Measure.integrableOn_of_bounded (M := C) volume_E_lt_top.ne ?_ ?_
    · exact continuous_conj.comp_aestronglyMeasurable
        (measurable_Ks.comp measurable_prodMk_right).aestronglyMeasurable
    · simp only [RCLike.norm_conj]
      exact ae_restrict_of_forall_mem measurableSet_E fun y my ↦ hC y x my
  · refine (AEMeasurable.const_mul ?_ I).cexp.mul
      hf.restrict.aestronglyMeasurable.aemeasurable |>.aestronglyMeasurable
    refine (measurable_ofReal.comp ?_).sub (measurable_ofReal.comp ?_) |>.aemeasurable
    · have pair : Measurable fun y : X ↦ (y, y) := by fun_prop
      exact measurable_Q₂.comp pair
    · exact measurable_Q₂.comp measurable_prodMk_right
  · filter_upwards [ae_restrict_of_ae h2f] with x hB
    rw [norm_mul, ← one_mul B]
    refine mul_le_mul ?_ hB (norm_nonneg _) zero_le_one
    rw_mod_cast [mul_comm, norm_exp_ofReal_mul_I]

attribute [fun_prop] continuous_conj Continuous.comp_aestronglyMeasurable

/-- Sub-equations (7.5.10) and (7.5.11) in Lemma 7.5.5. -/
lemma holder_correlation_rearrange (hf : BoundedCompactSupport f) :
    edist (exp (.I * 𝒬 u x) * adjointCarleson p f x) (exp (.I * 𝒬 u x') * adjointCarleson p f x') ≤
    (∫⁻ y in E p, ‖f y‖ₑ * ‖Ks (𝔰 p) y x‖ₑ * ‖- Q y x + Q y x' + 𝒬 u x - 𝒬 u x'‖ₑ) +
      ∫⁻ y in E p, ‖f y‖ₑ * ‖Ks (𝔰 p) y x - Ks (𝔰 p) y x'‖ₑ :=
  calc
    _ = ‖∫ y in E p,
        exp (.I * 𝒬 u x) * (conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x)) * f y) -
        exp (.I * 𝒬 u x') * (conj (Ks (𝔰 p) y x') * exp (.I * (Q y y - Q y x')) * f y)‖ₑ := by
      erw [edist_eq_enorm_sub, adjointCarleson, adjointCarleson, ← integral_const_mul, ← integral_const_mul, ← integral_sub (integrable_adjointCarleson_interior hf) (integrable_adjointCarleson_interior hf)]
    _ = ‖∫ y in E p, f y *
          (conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x + 𝒬 u x)) -
          conj (Ks (𝔰 p) y x') * exp (.I * (Q y y - Q y x' + 𝒬 u x')))‖ₑ := by
      congr! 3 with y
      rw [← mul_assoc _ _ (f y), ← mul_assoc _ _ (f y), ← sub_mul, mul_comm (f y)]
      congr 1
      rw [mul_comm _ (_ * _), mul_comm _ (_ * _), mul_assoc, mul_assoc, ← exp_add, ← exp_add,
        mul_add, mul_add]
    _ = ‖∫ y in E p, f y *
          exp (.I * (Q y y - Q y x' + 𝒬 u x')) * exp (-(.I * (Q y y - Q y x' + 𝒬 u x'))) *
          (conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x + 𝒬 u x)) -
          conj (Ks (𝔰 p) y x') * exp (.I * (Q y y - Q y x' + 𝒬 u x')))‖ₑ := by
      congr! 3 with y
      rw [mul_assoc _ (exp _) (exp _), ← exp_add, add_neg_cancel, exp_zero, mul_one]
    _ ≤ ∫⁻ y in E p, ‖f y‖ₑ *
          ‖exp (.I * (Q y y - Q y x' + 𝒬 u x'))‖ₑ * ‖exp (-(.I * (Q y y - Q y x' + 𝒬 u x'))) *
          (conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x + 𝒬 u x)) -
          conj (Ks (𝔰 p) y x') * exp (.I * (Q y y - Q y x' + 𝒬 u x')))‖ₑ := by
      simp_rw [← enorm_mul, ← mul_assoc]; exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y in E p, ‖f y‖ₑ *
          ‖conj (Ks (𝔰 p) y x) * exp (.I * (- Q y x + Q y x' + 𝒬 u x - 𝒬 u x' : ℝ)) -
          conj (Ks (𝔰 p) y x')‖ₑ := by
      congr 1 with y; norm_cast; nth_rw 1 [mul_comm I]; nth_rw 2 [← enorm_norm]
      rw [norm_exp_ofReal_mul_I, enorm_one, mul_one]; congr 2
      rw [mul_sub, ← mul_assoc, mul_rotate, mul_assoc, ← exp_add, ← sub_eq_add_neg, ← mul_sub,
        ← mul_assoc, mul_rotate, mul_assoc, ← exp_add, add_neg_cancel, exp_zero, mul_one]
      congr; norm_cast; ring
    _ ≤ ∫⁻ y in E p, ‖f y‖ₑ *
          (‖conj (Ks (𝔰 p) y x) * (exp (.I * (- Q y x + Q y x' + 𝒬 u x - 𝒬 u x' : ℝ)) - 1)‖ₑ +
          ‖conj (Ks (𝔰 p) y x) - conj (Ks (𝔰 p) y x')‖ₑ) := by
      gcongr with y
      rw [← sub_add_cancel (conj (Ks (𝔰 p) y x) * _) (conj (Ks (𝔰 p) y x)), ← mul_sub_one,
        add_sub_assoc]
      exact _root_.enorm_add_le _ _
    _ = (∫⁻ y in E p, ‖f y‖ₑ *
          ‖conj (Ks (𝔰 p) y x) * (exp (.I * (- Q y x + Q y x' + 𝒬 u x - 𝒬 u x' : ℝ)) - 1)‖ₑ) +
        ∫⁻ y in E p, ‖f y‖ₑ * ‖conj (Ks (𝔰 p) y x) - conj (Ks (𝔰 p) y x')‖ₑ := by
      simp_rw [mul_add]; apply lintegral_add_right'
      apply hf.restrict.aestronglyMeasurable.enorm.mul (AEMeasurable.enorm (AEMeasurable.sub ?_ ?_)) <;>
        exact continuous_conj.comp_aestronglyMeasurable
          (measurable_Ks.comp measurable_prodMk_right).aestronglyMeasurable |>.aemeasurable
    _ ≤ (∫⁻ y in E p, ‖f y‖ₑ * ‖conj (Ks (𝔰 p) y x)‖ₑ * ‖- Q y x + Q y x' + 𝒬 u x - 𝒬 u x'‖ₑ) +
        ∫⁻ y in E p, ‖f y‖ₑ * ‖conj (Ks (𝔰 p) y x) - conj (Ks (𝔰 p) y x')‖ₑ := by
      simp_rw [mul_assoc]; gcongr with y; rw [enorm_mul]; gcongr
      exact Real.enorm_exp_I_mul_ofReal_sub_one_le
    _ = _ := by
      congr! 4
      · congr 1; rw [RCLike.enorm_conj]
      · rw [← map_sub, RCLike.enorm_conj]

/-- Multiplicative factor for the bound on `‖- Q y x + Q y x' + 𝒬 u x - 𝒬 u x'‖ₑ`. -/
irreducible_def Q7_5_5 (a : ℕ) : ℝ≥0 := 10 * 2 ^ (6 * a)

lemma QQQQ_bound_real {y : X} (my : y ∈ E p) (hu : u ∈ t) (hp : p ∈ t u)
    (hx : x ∈ ball (𝔠 p) (5 * D ^ 𝔰 p)) (hx' : x' ∈ ball (𝔠 p) (5 * D ^ 𝔰 p)) :
    ‖-Q y x + Q y x' + 𝒬 u x - 𝒬 u x'‖ ≤ Q7_5_5 a * (dist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ := by
  rcases eq_or_ne x x' with rfl | hd
  · have : (a : ℝ)⁻¹ ≠ 0 := by rw [ne_eq, inv_eq_zero, Nat.cast_eq_zero]; linarith [four_le_a X]
    simp [this]
  replace hd : 0 < dist x x' := dist_pos.mpr hd
  have Dsppos : (0 : ℝ) < D ^ 𝔰 p := by simp only [defaultD]; positivity
  have dxx' : dist x x' < 10 * D ^ 𝔰 p :=
    calc
      _ ≤ dist x (𝔠 p) + dist x' (𝔠 p) := dist_triangle_right ..
      _ < 5 * D ^ 𝔰 p + 5 * D ^ 𝔰 p := by rw [mem_ball] at hx hx'; gcongr
      _ = _ := by rw [← add_mul]; norm_num
  let k : ℤ := ⌊Real.logb 2 (10 * D ^ 𝔰 p / dist x x') / a⌋
  have knn : 0 ≤ k := by
    calc
      _ ≥ ⌊Real.logb 2 1 / a⌋ := by
        simp_rw [k]; gcongr
        · exact one_lt_two
        · rw [one_le_div hd]; exact dxx'.le
      _ = _ := by simp
  calc
    _ ≤ dist_{x, 16 / 10 * dist x x'} (Q y) (𝒬 u) := by
      rw [show -Q y x + Q y x' + 𝒬 u x - 𝒬 u x' = Q y x' - 𝒬 u x' - Q y x + 𝒬 u x by ring]
      apply oscillation_le_cdist <;> rw [mem_ball]
      · rw [← one_mul (dist x' x), dist_comm]; exact mul_lt_mul_of_pos_right (by norm_num) hd
      · simp [hd]
    _ ≤ 2 ^ (-k) * dist_{x, (defaultA a) ^ k * (16 / 10 * dist x x')} (Q y) (𝒬 u) := by
      rw [← div_le_iff₀' (by positivity), zpow_neg, div_inv_eq_mul, mul_comm]
      have : ∀ r : ℝ, r ^ k = r ^ k.toNat := fun r ↦ by
        rw [← zpow_natCast]; congr; exact (Int.toNat_of_nonneg knn).symm
      rw [this, this]; exact le_cdist_iterate (by positivity) ..
    _ ≤ 2 ^ (-k) * dist_{x, 16 * D ^ 𝔰 p} (Q y) (𝒬 u) := by
      refine mul_le_mul_of_nonneg_left (cdist_mono (ball_subset_ball ?_)) (by positivity)
      calc
        _ ≤ ((2 : ℝ) ^ a) ^ (Real.logb 2 (10 * D ^ 𝔰 p / dist x x') / a) *
            (16 / 10 * dist x x') := by
          simp_rw [defaultA]; rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_intCast]; gcongr
          · norm_cast; exact Nat.one_le_two_pow
          · exact Int.floor_le _
        _ = _ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two,
            mul_div_cancel₀ _ (by norm_cast; linarith [four_le_a X]),
            Real.rpow_logb zero_lt_two one_lt_two.ne' (by positivity), div_mul_comm,
            mul_div_cancel_right₀ _ hd.ne', ← mul_assoc]
          norm_num
    _ ≤ 2 ^ (-k) * defaultA a * dist_{𝔠 p, 8 * D ^ 𝔰 p} (Q y) (𝒬 u) := by
      rw [show (16 : ℝ) = 2 * 8 by norm_num, mul_assoc, mul_assoc]; gcongr; apply cdist_le
      exact (mem_ball'.mp hx).trans_le (by rw [← mul_assoc]; gcongr; norm_num)
    _ ≤ 2 ^ (-k) * defaultA a * (defaultA a ^ 5 * dist_(p) (Q y) (𝒬 u)) := by
      gcongr; rw [show 8 * (D : ℝ) ^ 𝔰 p = 2 ^ 5 * (D ^ 𝔰 p / 4) by ring]
      exact cdist_le_iterate (by positivity) ..
    _ = 2 ^ (6 * a) * 2 ^ (-k) * dist_(p) (Q y) (𝒬 u) := by
      simp_rw [defaultA, Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc, mul_assoc _ _ (_ ^ 5)]
      rw [← pow_succ', ← pow_mul', mul_comm (2 ^ _)]
    _ ≤ 5 * 2 ^ (6 * a) * 2 ^ (-k) := by
      rw [mul_rotate 5]; gcongr
      calc
        _ ≤ dist_(p) (Q y) (𝒬 p) + dist_(p) (𝒬 p) (𝒬 u) := dist_triangle ..
        _ ≤ 1 + 4 := by
          gcongr <;> apply le_of_lt
          · rw [← mem_ball]; exact subset_cball my.2.1
          · rw [← mem_ball']; convert (t.smul_four_le hu hp).2 (mem_ball_self zero_lt_one)
        _ = _ := by norm_num
    _ ≤ 2 * 5 * 2 ^ (6 * a) * (dist x x' / (10 * D ^ 𝔰 p)) ^ (a : ℝ)⁻¹ := by
      rw [mul_rotate 2, mul_assoc _ 2]; gcongr
      calc
        _ ≤ (2 : ℝ) ^ (1 - Real.logb 2 (10 * D ^ 𝔰 p / dist x x') / a) := by
          rw [← Real.rpow_intCast]; apply Real.rpow_le_rpow_of_exponent_le one_le_two
          simp_rw [Int.cast_neg, k, neg_le_sub_iff_le_add']
          exact (Int.lt_floor_add_one _).le
        _ = _ := by
          rw [sub_eq_add_neg, Real.rpow_add zero_lt_two, Real.rpow_one, div_eq_mul_inv, ← neg_mul,
            Real.rpow_mul zero_le_two, ← Real.logb_inv, inv_div,
            Real.rpow_logb zero_lt_two one_lt_two.ne' (by positivity)]
    _ ≤ _ := by
      rw [show (2 : ℝ) * 5 = 10 by norm_num, Q7_5_5, NNReal.coe_mul, NNReal.coe_pow,
        NNReal.coe_ofNat, NNReal.coe_ofNat]; gcongr
      nth_rw 1 [← one_mul (_ ^ _)]; gcongr; norm_num

lemma QQQQ_bound {y : X} (my : y ∈ E p) (hu : u ∈ t) (hp : p ∈ t u)
    (hx : x ∈ ball (𝔠 p) (5 * D ^ 𝔰 p)) (hx' : x' ∈ ball (𝔠 p) (5 * D ^ 𝔰 p)) :
    ‖-Q y x + Q y x' + 𝒬 u x - 𝒬 u x'‖ₑ ≤ Q7_5_5 a * (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ := by
  calc
    _ ≤ ‖Q7_5_5 a * (dist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹‖ₑ := by
      rw [← enorm_norm]
      exact Real.enorm_le_enorm (norm_nonneg _) (QQQQ_bound_real my hu hp hx hx')
    _ = _ := by
      rw [enorm_mul, Real.enorm_rpow_of_nonneg (by positivity) (by norm_cast; positivity),
        NNReal.enorm_eq, div_eq_mul_inv, enorm_mul, enorm_inv (by unfold defaultD; positivity),
        ← div_eq_mul_inv]; congr
      · rw [Real.enorm_eq_ofReal dist_nonneg, dist_edist, ENNReal.ofReal_toReal]
        exact edist_ne_top x x'
      · rw [Real.enorm_eq_ofReal (by positivity), ← Real.rpow_intCast,
          ← ENNReal.ofReal_rpow_of_pos (by simp), ENNReal.rpow_intCast]; norm_cast

lemma holder_correlation_tile_two (hu : u ∈ t) (hp : p ∈ t u) (hf : BoundedCompactSupport f)
    (hx : x ∈ ball (𝔠 p) (5 * D ^ 𝔰 p)) (hx' : x' ∈ ball (𝔠 p) (5 * D ^ 𝔰 p)) :
    edist (exp (.I * 𝒬 u x) * adjointCarleson p f x) (exp (.I * 𝒬 u x') * adjointCarleson p f x') ≤
    C7_5_5 a / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) *
      (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ * ∫⁻ x in E p, ‖f x‖ₑ := by
  calc
    _ ≤ (∫⁻ y in E p, ‖f y‖ₑ * ‖Ks (𝔰 p) y x‖ₑ * ‖- Q y x + Q y x' + 𝒬 u x - 𝒬 u x'‖ₑ) +
        ∫⁻ y in E p, ‖f y‖ₑ * ‖Ks (𝔰 p) y x - Ks (𝔰 p) y x'‖ₑ := holder_correlation_rearrange hf
    _ ≤ (∫⁻ y in E p, ‖f y‖ₑ *
          (C2_1_3 a / volume (ball y (D ^ 𝔰 p))) * (Q7_5_5 a * (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹)) +
        ∫⁻ y in E p, ‖f y‖ₑ *
          (D2_1_3 a / volume (ball y (D ^ 𝔰 p)) * (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹) := by
      refine add_le_add (setLIntegral_mono' measurableSet_E fun y my ↦ ?_)
        (lintegral_mono fun _ ↦ ?_)
      · exact mul_le_mul' (mul_le_mul_right enorm_Ks_le _) (QQQQ_bound my hu hp hx hx')
      · gcongr; exact enorm_Ks_sub_Ks_le
    _ = (C2_1_3 a * Q7_5_5 a + D2_1_3 a) * (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ *
        ∫⁻ y in E p, ‖f y‖ₑ / volume (ball y (D ^ 𝔰 p)) := by
      conv_lhs =>
        enter [1, 2, y]
        rw [← mul_div_assoc, mul_comm ‖f y‖ₑ, mul_div_assoc, ← mul_rotate]
      have nt₀ : (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ < ⊤ := by
        apply ENNReal.rpow_lt_top_of_nonneg (by positivity); rw [← lt_top_iff_ne_top]
        exact ENNReal.div_lt_top (edist_ne_top _ _) (ENNReal.zpow_pos (by simp) (by simp) _).ne'
      have nt₁ : Q7_5_5 a * (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ * C2_1_3 a ≠ ⊤ := by finiteness
      rw [lintegral_const_mul' _ _ nt₁]
      conv_lhs =>
        enter [2, 2, y]
        rw [← mul_assoc, ← mul_div_assoc, mul_comm ‖f y‖ₑ, mul_div_assoc, ← mul_rotate]
      have nt₂ : (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ * D2_1_3 a ≠ ⊤ := by finiteness
      rw [lintegral_const_mul' _ _ nt₂, ← add_mul]; congr 1
      rw [← mul_rotate, mul_comm _ (D2_1_3 a : ℝ≥0∞), ← add_mul]
    _ ≤ (C2_1_3 a * Q7_5_5 a + D2_1_3 a) * (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ *
        ∫⁻ y in E p, ‖f y‖ₑ / (volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) / 2 ^ (3 * a)) := by
      refine mul_le_mul_right (setLIntegral_mono' measurableSet_E fun y my ↦ ?_) _
      exact ENNReal.div_le_div_left (volume_xDsp_bound (E_subset_𝓘 my)) _
    _ = 2 ^ (3 * a) * (C2_1_3 a * Q7_5_5 a + D2_1_3 a) / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) *
        (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ * ∫⁻ y in E p, ‖f y‖ₑ := by
      conv_lhs =>
        enter [2, 2, y]
        rw [ENNReal.div_eq_inv_mul]
      rw [lintegral_const_mul'' _ hf.restrict.aestronglyMeasurable.enorm, ← mul_assoc]; congr 1
      rw [ENNReal.inv_div (by simp) (by simp), ← mul_rotate, ENNReal.mul_div_right_comm]
    _ ≤ _ := by
      gcongr; rw [C2_1_3, D2_1_3, C7_5_5, Q7_5_5]; norm_cast
      calc
        _ ≤ 2 ^ (3 * a) * (2 ^ ((𝕔 + 2) * a ^ 3) * (2 ^ 4 * 2 ^ (6 * a))
              + 2 ^ ((𝕔 + 2 + 𝕔 / 4) * a ^ 3)) := by gcongr; norm_num
        _ ≤ 2 ^ (3 * a) * (2 ^ ((𝕔 + 2 + 𝕔 / 4) * a ^ 3) + 2 ^ ((𝕔 + 2 + 𝕔 / 4) * a ^ 3)) := by
          gcongr; rw [← pow_add, ← pow_add]; apply pow_le_pow_right' one_le_two
          calc
            _ = (𝕔 + 2) * a ^ 3 + 2 * 1 * 2 + 2 * 3 * a := by ring
            _ ≤ (𝕔 + 2) * a ^ 3 + 2 * a * a + 2 * a * a := by gcongr <;> linarith [four_le_a X]
            _ = (𝕔 + 2) * a ^ 3 + 1 * 4 * a ^ 2 := by ring
            _ ≤ (𝕔 + 2) * a ^ 3 + (𝕔 / 4) * a * a ^ 2 := by
              gcongr
              · have := seven_le_c; lia
              · exact four_le_a X
            _ = _ := by ring
        _ = 2 ^ ((𝕔 + 2 + 𝕔 / 4) * a ^ 3 + (3 * a + 1)) := by
          rw [← two_mul, ← pow_succ', ← pow_add]; ring
        _ ≤ _ := by
          apply pow_le_pow_right' one_le_two
          rw [show (𝕔 + 3 + 𝕔 / 4) * a ^ 3 = (𝕔 + 2 + 𝕔 / 4) * a ^ 3 + a ^ 3 by ring]; gcongr
          calc
            _ = 3 * a * 1 + 1 * 1 * 1 := by ring
            _ ≤ 3 * a * a + 1 * a * a := by gcongr <;> linarith [four_le_a X]
            _ = 4 * a * a := by ring
            _ ≤ _ := by rw [pow_succ, sq]; gcongr; exact four_le_a X

end BothIn

/-- Lemma 7.5.5. -/
lemma holder_correlation_tile (hu : u ∈ t) (hp : p ∈ t u) (hf : BoundedCompactSupport f) :
    edist (exp (.I * 𝒬 u x) * adjointCarleson p f x) (exp (.I * 𝒬 u x') * adjointCarleson p f x') ≤
    C7_5_5 a / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) *
      (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ * ∫⁻ x in E p, ‖f x‖ₑ := by
  by_cases hxx : x ∉ ball (𝔠 p) (5 * D ^ 𝔰 p) ∧ x' ∉ ball (𝔠 p) (5 * D ^ 𝔰 p)
  · rw [adjoint_tile_support1, indicator_of_notMem hxx.1, indicator_of_notMem hxx.2]; simp
  rw [not_and_or, not_notMem, not_notMem] at hxx
  wlog hx : x ∈ ball (𝔠 p) (5 * D ^ 𝔰 p) generalizing x x'
  · rw [or_comm] at hxx; specialize this hxx (hxx.resolve_right hx)
    rwa [edist_comm, edist_comm x' x] at this
  clear hxx
  by_cases! hx' : x' ∉ ball (𝔠 p) (5 * D ^ 𝔰 p)
  · nth_rw 2 [adjoint_tile_support1]
    rw [indicator_of_notMem hx', mul_zero, edist_zero_right, enorm_mul, mul_comm I, ← enorm_norm,
      norm_exp_ofReal_mul_I, enorm_one, one_mul]
    exact holder_correlation_tile_one hf hx'
  exact holder_correlation_tile_two hu hp hf hx hx'

/-- Part of Lemma 7.5.6. -/
lemma limited_scale_impact_first_estimate (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hp : p ∈ t u₂ \ 𝔖₀ t u₁ u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (h : ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))) : s J ≤ 𝔰 p := by
  by_contra! contr
  apply Int.not_le.mpr contr
  apply Int.sub_one_lt_iff.mp
  apply Int.sub_lt_of_sub_lt
  rify
  apply lt_of_le_of_lt (hbc := calculation_logD_64 (X := X))
  apply tsub_le_iff_left.mpr
  have DIsOne := one_lt_realD X
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
lemma limited_scale_impact_second_estimate (hp : p ∈ t u₂ \ 𝔖₀ t u₁ u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂)
    (h : ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))) :
    𝔰 p ≤ s J + 3 := by
  by_contra! three
  have ⟨J', belongs, plusOne⟩ : ∃ J', J ≤ J' ∧ s J' = s J + 1 :=
    Grid.exists_scale_succ (by change s J < 𝔰 p; linarith)
  have ⟨p', ⟨_, distance⟩, hundred⟩ :
      ∃ p' ∈ t.𝔖₀ u₁ u₂, ↑(𝓘 p') ⊆ ball (c J') (100 * D ^ (s J + 2)) := by
    rw [← one_add_one_eq_two, ← add_assoc, ← plusOne]
    have J'Touches𝔖₀ : J' ∉ 𝓙₀ (t.𝔖₀ u₁ u₂) := bigger_than_𝓙_is_not_in_𝓙₀ (le := belongs)
      (sle := by linarith [plusOne]) (A_in := hJ.1)
    rw [𝓙₀, Set.notMem_setOf_iff] at J'Touches𝔖₀
    push Not at J'Touches𝔖₀
    exact J'Touches𝔖₀.right
  apply calculation_9 (X := X)
  apply one_le_of_le_mul_right₀ (b := 2 ^ ((Z : ℝ) * n / 2)) (by positivity)
  have DIsPos := realD_pos a
  calc 2 ^ ((Z : ℝ) * (n : ℝ) / 2)
    _ ≤ dist_{𝓘 p'} (𝒬 u₁) (𝒬 u₂) := by
      exact distance
    _ ≤ dist_{c J', 100 * D ^ (s J + 2)} (𝒬 u₁) (𝒬 u₂) := by
      apply cdist_mono
      intros x hx
      exact hundred (ball_subset_Grid hx)
    _ ≤ 2 ^ ((-𝕔 : ℝ) * a) * dist_{c J', 100 * D^(s J + 3)} (𝒬 u₁) (𝒬 u₂) := by
      apply calculation_8
      rw [mul_comm, calculation_6 a (s J), calculation_7 a (s J)]
      exact_mod_cast le_cdist_iterate (k := 𝕔 * a) (f := 𝒬 u₁) (g := 𝒬 u₂) (hr := by positivity)
    _ ≤ 2 ^ ((-𝕔 : ℝ) * a) * dist_{𝔠 p, 10 * D^(𝔰 p)} (𝒬 u₁) (𝒬 u₂) := by
      gcongr
      apply cdist_mono
      simp only [not_disjoint_iff] at h
      rcases h with ⟨middleX, lt_2, lt_3⟩
      have lt_4 := Grid.dist_c_le_of_subset belongs.left
      intros x lt_1
      calc dist x (𝔠 p)
      _ ≤ dist x (c J') + dist (c J') (c J) + dist (c J) middleX + dist middleX (𝔠 p) := by
        exact dist_triangle5 x (c J') (c J) middleX (𝔠 p)
      _ < 10 * D ^ 𝔰 p := by
        simp only [mem_ball] at lt_3
        rw [dist_comm] at lt_3 lt_4
        exact calculation_4 (lt_1 := lt_1) (lt_2 := lt_2) (lt_3 := lt_3) (lt_4 := lt_4)
          (three := three) (plusOne := plusOne) (X := X)
    _ ≤ 2 ^ ((-(𝕔 - 6) : ℝ) * a) * dist_{𝓘 p} (𝒬 u₁) (𝒬 u₂) := by
      apply calculation_5
      have bigger : 0 < (D : ℝ) ^ 𝔰 p / 4 := by positivity
      calc dist_{𝔠 p, 10 * D^(𝔰 p)} (𝒬 u₁) (𝒬 u₂)
      _ ≤ dist_{𝔠 p, 2 ^ 6 * (D ^ 𝔰 p / 4)} (𝒬 u₁) (𝒬 u₂) := by
        apply cdist_mono
        apply ball_subset_ball
        ring_nf
        linarith
      _ ≤ (2 ^ (a : ℝ)) ^ (6 : ℝ) * dist_{𝔠 p, (D ^ 𝔰 p / 4)} (𝒬 u₁) (𝒬 u₂) :=
        mod_cast cdist_le_iterate (f := (𝒬 u₁)) (g := (𝒬 u₂)) (r := (D ^ (𝔰 p)) / 4)
          (k := 6) (x := 𝔠 p) bigger
    _ ≤ 2 ^ ((-(𝕔 - 6) : ℝ) * a) * 2 ^ ((Z : ℝ) * n / 2) := by
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
    𝔰 p ∈ Icc (s J) (s J + 3) :=
  ⟨limited_scale_impact_first_estimate hu₁ hu₂ hu h2u hp hJ h,
    limited_scale_impact_second_estimate hp hJ h⟩

open scoped Classical in
lemma local_tree_control_sumsumsup (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) :
    ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f x‖ₑ ≤
    ∑ k ∈ Finset.Icc (s J) (s J + 3),
    ∑ p with 𝔰 p = k ∧ ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J)),
      ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarleson p f x‖ₑ :=
  calc
    _ ≤ ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J),
        ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset, ‖adjointCarleson p f x‖ₑ := by
      apply iSup₂_mono fun x mx ↦ ?_
      simp_rw [enorm_eq_nnnorm, ← ENNReal.coe_finset_sum, ENNReal.coe_le_coe, adjointCarlesonSum,
        filter_mem_univ_eq_toFinset]
      exact nnnorm_sum_le ..
    _ = ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J),
        ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset,
          (ball (𝔠 p) (5 * D ^ 𝔰 p)).indicator (fun y ↦ ‖adjointCarleson p f y‖ₑ) x := by
      congr! 5 with x mx p mp
      nth_rw 1 [adjoint_tile_support1, ← adjoint_eq_adjoint_indicator E_subset_𝓘,
        enorm_indicator_eq_indicator_enorm]
    _ ≤ ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J),
        ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset.filter
          (fun p ↦ ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))),
            ‖adjointCarleson p f x‖ₑ := by
      apply iSup₂_mono fun x mx ↦ ?_
      rw [Finset.sum_indicator_eq_sum_filter]
      apply Finset.sum_le_sum_of_subset fun p mp ↦ ?_
      rw [Finset.mem_filter] at mp ⊢
      exact ⟨mp.1, not_disjoint_iff.mpr ⟨_, (ball_subset_ball (by gcongr; norm_num)) mp.2, mx⟩⟩
    _ ≤ ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset.filter
          (fun p ↦ ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))),
        ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarleson p f x‖ₑ :=
      ENNReal.biSup_finsetSum_le_finsetSum_biSup
    _ = ∑ k ∈ Finset.Icc (s J) (s J + 3), ∑ p ∈ (t u₂ \ 𝔖₀ t u₁ u₂).toFinset.filter
          (fun p ↦ 𝔰 p = k ∧ ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))),
            ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarleson p f x‖ₑ := by
      conv_rhs => enter [2, p, 1]; rw [← Finset.filter_filter, Finset.filter_comm]
      refine (Finset.sum_fiberwise_of_maps_to (fun p mp ↦ ?_) _).symm
      rw [Finset.mem_filter, mem_toFinset] at mp
      simpa only [Finset.mem_Icc] using limited_scale_impact hu₁ hu₂ hu h2u mp.1 hJ mp.2
    _ ≤ _ := by gcongr; exact Finset.subset_univ _

lemma local_tree_control_sup_bound {k : ℤ} (mk : k ∈ Finset.Icc (s J) (s J + 3))
    (mp : 𝔰 p = k ∧ ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J)))
    (nfm : AEMeasurable fun x ↦ ‖f x‖ₑ) :
    ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarleson p f x‖ₑ ≤
    2 ^ ((𝕔 + 3) * a ^ 3) * (volume (ball (c J) (16 * D ^ k)))⁻¹ * ∫⁻ x in E p, ‖f x‖ₑ :=
  calc
    _ ≤ ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J),
        ∫⁻ y in E p, ‖conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x)) * f y‖ₑ :=
      iSup₂_mono fun x mx ↦ enorm_integral_le_lintegral_enorm _
    _ = ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ∫⁻ y in E p, ‖Ks (𝔰 p) y x‖ₑ * ‖f y‖ₑ := by
      congr! with x mx y
      rw [enorm_mul, enorm_mul, RCLike.enorm_conj, ← ofReal_sub, enorm_exp_I_mul_ofReal, mul_one]
    _ ≤ ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ∫⁻ y in E p,
        C2_1_3 a / volume (ball y (D ^ 𝔰 p)) * ‖f y‖ₑ := by gcongr; exact enorm_Ks_le
    _ = ∫⁻ x in E p, C2_1_3 a / volume (ball x (D ^ 𝔰 p)) * ‖f x‖ₑ := by
      have := one_le_realD a
      exact biSup_const (nonempty_ball.mpr (by positivity))
    _ ≤ ∫⁻ x in E p,
        C2_1_3 a / (volume (ball (c J) (16 * D ^ 𝔰 p)) / 2 ^ (5 * a)) * ‖f x‖ₑ := by
      apply setLIntegral_mono_ae (nfm.restrict.const_mul _) (.of_forall fun x mx ↦ ?_)
      gcongr
      have dpJ : dist (c J) (𝔠 p) < (8⁻¹ + 8) * D ^ 𝔰 p := by
        obtain ⟨y, my₁, my₂⟩ := not_disjoint_iff.mp mp.2
        rw [mem_ball] at my₁ my₂
        calc
          _ ≤ dist y (c J) + dist y (𝔠 p) := dist_triangle_left ..
          _ < 8⁻¹ * D ^ s J + 8 * D ^ 𝔰 p := by gcongr
          _ ≤ _ := by
            rw [Finset.mem_Icc, ← mp.1] at mk; rw [add_mul]; gcongr; exacts [one_le_realD a, mk.1]
      have inc : ball (c J) (16 * D ^ 𝔰 p) ⊆ ball x (32 * D ^ 𝔰 p) := fun y my ↦ by
        rw [mem_ball] at my ⊢
        calc
          _ ≤ dist y (c J) + dist (c J) (𝔠 p) + dist (𝔠 p) x := dist_triangle4 ..
          _ < 16 * D ^ (𝔰 p) + (8⁻¹ + 8) * D ^ (𝔰 p) + 4 * D ^ (𝔰 p) := by
            gcongr; rw [dist_comm, ← mem_ball]; exact Grid_subset_ball mx.1
          _ ≤ _ := by rw [← add_mul, ← add_mul]; gcongr; norm_num
      have dbl := measure_ball_two_le_same_iterate (μ := volume) x (D ^ 𝔰 p) 5
      simp_rw [show (2 : ℝ) ^ 5 = 32 by norm_num, defaultA, ← ENNReal.coe_pow,
        Nat.cast_pow, Nat.cast_ofNat, ← pow_mul', ENNReal.coe_pow, ENNReal.coe_ofNat] at dbl
      exact ENNReal.div_le_of_le_mul' ((measure_mono inc).trans dbl)
    _ ≤ _ := by
      rw [lintegral_const_mul'' _ nfm.restrict]; gcongr
      rw [ENNReal.div_eq_inv_mul, ENNReal.inv_div (by left; norm_num) (by left; positivity),
        ← ENNReal.mul_div_right_comm, mp.1, ENNReal.div_eq_inv_mul, mul_comm]
      gcongr; unfold C2_1_3; norm_cast
      simp_rw [← pow_add]
      refine pow_le_pow_right' one_le_two ?_
      rw [show (𝕔 + 3) * a ^ 3 = a * a * a + (𝕔 + 2) * a ^ 3 by ring]
      gcongr
      nlinarith [four_le_a X]

/-- The constant used in `local_tree_control`.
Has value `2 ^ (104 * a ^ 3)` in the blueprint. -/
irreducible_def C7_5_7 (a : ℕ) : ℝ≥0 := 2 ^ ((𝕔 + 4) * a ^ 3)

/-- Lemma 7.5.7. -/
lemma local_tree_control (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf : BoundedCompactSupport f) :
    ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f x‖ₑ ≤
    C7_5_7 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x := by
  classical
  calc
    _ ≤ ∑ k ∈ Finset.Icc (s J) (s J + 3),
        ∑ p with 𝔰 p = k ∧ ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J)),
          ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarleson p f x‖ₑ :=
      local_tree_control_sumsumsup hu₁ hu₂ hu h2u hJ
    _ ≤ ∑ k ∈ Finset.Icc (s J) (s J + 3),
        ∑ p ∈ {p | 𝔰 p = k ∧ ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))},
          2 ^ ((𝕔 + 3) * a ^ 3) * (volume (ball (c J) (16 * D ^ k)))⁻¹ * ∫⁻ x in E p, ‖f x‖ₑ := by
      gcongr with k mk p mp
      simp_rw [Finset.mem_filter, Finset.mem_univ, true_and] at mp
      exact local_tree_control_sup_bound mk mp hf.aestronglyMeasurable.enorm
    _ = 2 ^ ((𝕔 + 3) * a ^ 3) * ∑ k ∈ Finset.Icc (s J) (s J + 3),
        (volume (ball (c J) (16 * D ^ k)))⁻¹ *
          ∑ p with 𝔰 p = k ∧ ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J)),
            ∫⁻ x in E p, ‖f x‖ₑ := by
      simp_rw [Finset.mul_sum, mul_assoc]
    _ = 2 ^ ((𝕔 + 3) * a ^ 3) * ∑ k ∈ Finset.Icc (s J) (s J + 3),
        (volume (ball (c J) (16 * D ^ k)))⁻¹ * ∫⁻ x in ⋃ p ∈ Finset.univ.filter (fun p ↦ 𝔰 p = k ∧
          ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))), E p, ‖f x‖ₑ := by
      congr! with k mk
      refine (lintegral_biUnion_finset ?_ (fun _ _ ↦ measurableSet_E) _).symm
      intro p mp q mq hn
      by_cases hi : 𝓘 p = 𝓘 q
      · by_contra h; rw [not_disjoint_iff] at h; obtain ⟨x, mx₁ : x ∈ E p, mx₂ : x ∈ E q⟩ := h
        apply absurd (disjoint_Ω hn hi); rw [not_disjoint_iff]; use Q x, mx₁.2.1, mx₂.2.1
      · apply disjoint_of_subset E_subset_𝓘 E_subset_𝓘
        simp_rw [Finset.coe_filter, Finset.mem_univ, true_and, mem_setOf_eq] at mp mq
        have := eq_or_disjoint (mq.1 ▸ mp.1)
        exact this.resolve_left hi
    _ ≤ 2 ^ ((𝕔 + 3) * a ^ 3) * ∑ k ∈ Finset.Icc (s J) (s J + 3),
        (volume (ball (c J) (16 * D ^ k)))⁻¹ * ∫⁻ x in ball (c J) (16 * D ^ k), ‖f x‖ₑ := by
      gcongr with k mk; refine iUnion₂_subset fun p mp ↦ ?_
      rw [Finset.mem_filter_univ] at mp
      refine (E_subset_𝓘.trans Grid_subset_ball).trans (ball_subset_ball' ?_)
      obtain ⟨y, my₁, my₂⟩ := not_disjoint_iff.mp mp.2
      rw [mem_ball] at my₁ my₂; change 4 * D ^ 𝔰 p + dist (𝔠 p) (c J) ≤ _
      calc
        _ ≤ 4 * D ^ 𝔰 p + (dist y (𝔠 p) + dist y (c J)) := by gcongr; exact dist_triangle_left ..
        _ ≤ 4 * D ^ 𝔰 p + 8 * D ^ 𝔰 p + 8⁻¹ * D ^ s J := by rw [add_assoc]; gcongr
        _ ≤ (4 + 8 + 8⁻¹) * D ^ k := by
          rw [Finset.mem_Icc] at mk; simp_rw [add_mul, mp.1]; gcongr; exacts [one_le_realD a, mk.1]
        _ ≤ _ := by gcongr; norm_num
    _ = 2 ^ ((𝕔 + 3) * a ^ 3) *
        ∑ k ∈ Finset.Icc (s J) (s J + 3), ⨍⁻ x in ball (c J) (16 * D ^ k), ‖f x‖ₑ ∂volume := by
      simp_rw [setLAverage_eq, ENNReal.div_eq_inv_mul]
    _ ≤ 2 ^ ((𝕔 + 3) * a ^ 3) *
        ∑ k ∈ Finset.Icc (s J) (s J + 3), ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x := by
      gcongr with k mk; rw [Finset.mem_Icc] at mk
      apply laverage_le_biInf_MB
      · gcongr; exacts [by norm_num, one_le_realD a, mk.1]
      · use ⟨4, (k - s J).toNat, J⟩
        simp only [𝓑, c𝓑, r𝓑, mem_prod, mem_Iic, mem_univ, le_add_iff_nonneg_left, zero_le,
          and_true, true_and]
        rw [show s J + (k - s J).toNat = k by lia, Int.toNat_le, Nat.cast_add, Nat.cast_mul,
          Nat.cast_ofNat]
        refine ⟨by omega, by norm_num⟩
    _ = 2 ^ ((𝕔 + 3) * a ^ 3) * 2 ^ 2 * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x := by
      rw [Finset.sum_const, Int.card_Icc, show s J + 3 + 1 - s J = 4 by lia, nsmul_eq_mul,
        show (Int.toNat 4 : ℝ≥0∞) = 2 ^ 2 by simp; norm_num, mul_assoc]
    _ ≤ _ := by
      gcongr; rw [C7_5_7, ← pow_add]; norm_cast
      refine pow_le_pow_right' one_le_two ?_
      rw [show (𝕔 + 4) * a ^ 3 = (𝕔 + 3) * a ^ 3 + a * a * a by ring]
      gcongr
      nlinarith [four_le_a X]

/-- Lemma 7.5.8. -/
lemma scales_impacting_interval (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hp : p ∈ t u₁ ∪ (t u₂ ∩ 𝔖₀ t u₁ u₂))
    (h : ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (16 * D ^ s J))) : s J ≤ 𝔰 p := by
  obtain ⟨hJLeft, -⟩ := hJ
  apply 𝓙_subset_𝓙₀ at hJLeft
  rw [mem_union] at hp
  have belongs : p ∈ 𝔖₀ t u₁ u₂ := by
    cases hp with
    | inl h1 => exact 𝔗_subset_𝔖₀ hu₁ hu₂ hu h2u h1
    | inr h2 => exact h2.2
  cases hJLeft with
  | inl scaleVerySmall => exact scaleVerySmall ▸ scale_mem_Icc.1
  | inr noGridInBall =>
    have pGridIsNotInBall := noGridInBall p belongs
    rw [not_subset] at pGridIsNotInBall
    obtain ⟨x, ⟨xInTile, xIsNotInBall⟩⟩ := pGridIsNotInBall
    rw [mem_ball'] at xIsNotInBall; contrapose! xIsNotInBall; rw [dist_comm]
    calc
      _ ≤ dist x (𝔠 p) + dist (𝔠 p) (c J) := dist_triangle ..
      _ < 4 * D ^ 𝔰 p + 8 * D ^ 𝔰 p + 16 * D ^ s J := by
        rw [add_assoc]; gcongr
        · exact mem_ball.mp (Grid_subset_ball xInTile)
        · exact dist_lt_of_not_disjoint_ball h
      _ ≤ 4 * D ^ s J + 8 * D ^ s J + 16 * D ^ s J := by gcongr <;> exact one_le_realD a
      _ ≤ _ := by
        rw [← add_mul, ← add_mul, zpow_add_one₀ (realD_pos a).ne', mul_comm _ (D : ℝ),
          ← mul_assoc]; gcongr
        calc
          _ ≤ 100 * (1 : ℝ) := by norm_num
          _ ≤ _ := by gcongr; exact one_le_realD a

lemma volume_cpDsp_bound {J : Grid X}
    (hd : ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (16 * D ^ s J))) (hs : s J ≤ 𝔰 p) :
    volume (ball (c J) (32 * D ^ 𝔰 p)) / 2 ^ (4 * a) ≤ volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) := by
  apply ENNReal.div_le_of_le_mul'
  have h : dist (𝔠 p) (c J) + 32 * D ^ 𝔰 p ≤ 16 * (4 * D ^ 𝔰 p) := by
    calc
      _ ≤ 8 * (D : ℝ) ^ 𝔰 p + 16 * D ^ s J + 32 * D ^ 𝔰 p := by
        gcongr; exact (dist_lt_of_not_disjoint_ball hd).le
      _ ≤ 8 * (D : ℝ) ^ 𝔰 p + 16 * D ^ 𝔰 p + 32 * D ^ 𝔰 p := by
        gcongr; exact one_le_realD a
      _ ≤ _ := by rw [← add_mul, ← add_mul, ← mul_assoc]; gcongr; norm_num
  convert measure_ball_le_of_dist_le' (μ := volume) (by norm_num) h
  unfold As defaultA; norm_cast
  rw [← pow_mul', show (16 : ℕ) = 2 ^ 4 by norm_num, Nat.clog_pow _ _ one_lt_two]

open scoped Classical in
lemma gtc_integral_bound {k : ℤ} {ℭ : Set (𝔓 X)}
    (hs : ∀ p ∈ ℭ, ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (16 * D ^ s J)) → s J ≤ 𝔰 p) :
    ∑ p ∈ ℭ with ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (16 * D ^ s J)) ∧ 𝔰 p = k,
      ∫⁻ x in E p, ‖f x‖ₑ ≤
    ∫⁻ x in ball (c J) (32 * D ^ k), ‖f x‖ₑ := by
  set V := ℭ.toFinset.filter
      (fun p ↦ ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (16 * D ^ s J)) ∧ 𝔰 p = k)
  calc
    _ = ∫⁻ x in ⋃ p ∈ V, E p, ‖f x‖ₑ := by
      refine (lintegral_biUnion_finset (fun p₁ mp₁ p₂ mp₂ hn ↦ ?_)
        (fun _ _ ↦ measurableSet_E) _).symm
      contrapose! hn; obtain ⟨x, mx₁ : x ∈ E p₁, mx₂ : x ∈ E p₂⟩ := not_disjoint_iff.mp hn
      rw [E, mem_setOf] at mx₁ mx₂
      simp_rw [Finset.mem_coe, V, Finset.mem_filter, mem_toFinset] at mp₁ mp₂
      have i_eq := mp₂.2.2 ▸ mp₁.2.2
      replace i_eq : 𝓘 p₁ = 𝓘 p₂ :=
        (eq_or_disjoint i_eq).resolve_right (not_disjoint_iff.mpr ⟨x, mx₁.1, mx₂.1⟩)
      by_contra! h
      exact absurd (disjoint_Ω h i_eq) (not_disjoint_iff.mpr ⟨Q x, mx₁.2.1, mx₂.2.1⟩)
    _ ≤ _ := by
      refine lintegral_mono_set (iUnion₂_subset fun p mp ↦ ?_)
      simp_rw [V, Finset.mem_filter, mem_toFinset] at mp; specialize hs p mp.1 mp.2.1
      refine (E_subset_𝓘.trans Grid_subset_ball).trans (ball_subset_ball' ?_)
      rw [← mp.2.2]; change (4 : ℝ) * D ^ 𝔰 p + dist (𝔠 p) (c J) ≤ _
      calc
        _ ≤ (4 : ℝ) * D ^ 𝔰 p + 8 * D ^ 𝔰 p + 16 * D ^ s J := by
          rw [add_assoc]; gcongr; exact (dist_lt_of_not_disjoint_ball mp.2.1).le
        _ ≤ (4 : ℝ) * D ^ 𝔰 p + 8 * D ^ 𝔰 p + 16 * D ^ 𝔰 p := by gcongr; exact one_le_realD a
        _ ≤ _ := by rw [← add_mul, ← add_mul]; gcongr; norm_num

/-- Part 1 of equation (7.5.18) of Lemma 7.5.9. -/
lemma global_tree_control1_edist_part1
    (hu : u ∈ t) {ℭ : Set (𝔓 X)} (hℭ : ℭ ⊆ t u) (hf : BoundedCompactSupport f)
    (hs : ∀ p ∈ ℭ, ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (16 * D ^ s J)) → s J ≤ 𝔰 p)
    (hx : x ∈ ball (c J) (16 * D ^ s J)) (hx' : x' ∈ ball (c J) (16 * D ^ s J)) :
    edist (exp (.I * 𝒬 u x) * adjointCarlesonSum ℭ f x)
      (exp (.I * 𝒬 u x') * adjointCarlesonSum ℭ f x') ≤
    C7_5_5 a * 2 ^ (4 * a) * edist x x' ^ (a : ℝ)⁻¹ * ∑ k ∈ Finset.Icc (s J) S,
        D ^ (-k / (a : ℝ)) * ⨍⁻ x in ball (c J) (32 * D ^ k), ‖f x‖ₑ ∂volume := by
  classical calc
    _ ≤ ∑ p ∈ ℭ, edist (exp (.I * 𝒬 u x) * adjointCarleson p f x)
        (exp (.I * 𝒬 u x') * adjointCarleson p f x') := by
      simp_rw [adjointCarlesonSum, Finset.mul_sum]
      have heq : Finset.univ.filter (· ∈ ℭ) = ℭ.toFinset := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
      rw [heq]
      exact ENNReal.edist_sum_le_sum_edist
    _ = ∑ p ∈ ℭ with ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (16 * D ^ s J)),
        edist (exp (.I * 𝒬 u x) * adjointCarleson p f x)
          (exp (.I * 𝒬 u x') * adjointCarleson p f x') := by
      refine (Finset.sum_filter_of_ne fun p mp hp ↦ ?_).symm; contrapose! hp
      replace hp : Disjoint (ball (𝔠 p) (5 * D ^ 𝔰 p)) (ball (c J) (16 * D ^ s J)) :=
        hp.mono_left (ball_subset_ball (by gcongr; norm_num))
      rw [adjoint_tile_support1, indicator_of_notMem (disjoint_right.mp hp hx), mul_zero,
        indicator_of_notMem (disjoint_right.mp hp hx'), mul_zero, edist_self]
    _ ≤ ∑ p ∈ ℭ with ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (16 * D ^ s J)),
        C7_5_5 a / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) *
          (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ * ∫⁻ x in E p, ‖f x‖ₑ := by
      gcongr with p mp; rw [Finset.mem_filter, mem_toFinset] at mp
      exact holder_correlation_tile hu (hℭ mp.1) hf
    _ = C7_5_5 a * edist x x' ^ (a : ℝ)⁻¹ *
        ∑ p ∈ ℭ with ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (16 * D ^ s J)),
          D ^ (-𝔰 p / (a : ℝ)) / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) * ∫⁻ x in E p, ‖f x‖ₑ := by
      rw [Finset.mul_sum]; congr! 1 with p mp
      rw [← mul_assoc, ← mul_div_assoc, mul_assoc _ _ ((D : ℝ≥0∞) ^ _), mul_comm _ (_ * _),
        mul_div_assoc, mul_comm (_ ^ _ * _)]; congr
      rw [div_eq_mul_inv, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
        ← ENNReal.zpow_neg, ← ENNReal.rpow_intCast, ← ENNReal.rpow_mul,
        ← div_eq_mul_inv, Int.cast_neg]
    _ = C7_5_5 a * edist x x' ^ (a : ℝ)⁻¹ * ∑ k ∈ Finset.Icc (s J) S,
        ∑ p ∈ ℭ with ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (16 * D ^ s J)) ∧ 𝔰 p = k,
          D ^ (-𝔰 p / (a : ℝ)) / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) * ∫⁻ x in E p, ‖f x‖ₑ := by
      congr 1; simp_rw [← Finset.filter_filter]
      refine (Finset.sum_fiberwise_of_maps_to (fun p mp ↦ ?_) _).symm
      rw [Finset.mem_Icc]; rw [Finset.mem_filter, mem_toFinset] at mp
      exact ⟨hs p mp.1 mp.2, scale_mem_Icc.2⟩
    _ = C7_5_5 a * edist x x' ^ (a : ℝ)⁻¹ * ∑ k ∈ Finset.Icc (s J) S, D ^ (-k / (a : ℝ)) *
        ∑ p ∈ ℭ with ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (16 * D ^ s J)) ∧ 𝔰 p = k,
          (∫⁻ x in E p, ‖f x‖ₑ) / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) := by
      congr! 2 with k mk; rw [Finset.mul_sum]; congr! 1 with p mp
      rw [mul_comm, ← mul_div_assoc, ← mul_div_assoc, mul_comm]; congr
      rw [Finset.mem_filter] at mp; exact mp.2.2
    _ ≤ C7_5_5 a * edist x x' ^ (a : ℝ)⁻¹ * ∑ k ∈ Finset.Icc (s J) S, D ^ (-k / (a : ℝ)) *
        ∑ p ∈ ℭ with ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (16 * D ^ s J)) ∧ 𝔰 p = k,
          (∫⁻ x in E p, ‖f x‖ₑ) / (volume (ball (c J) (32 * D ^ k)) / 2 ^ (4 * a)) := by
      gcongr with k mk p mp; rw [Finset.mem_filter, mem_toFinset] at mp
      rw [← mp.2.2]; exact volume_cpDsp_bound mp.2.1 (hs p mp.1 mp.2.1)
    _ = C7_5_5 a * 2 ^ (4 * a) * edist x x' ^ (a : ℝ)⁻¹ * ∑ k ∈ Finset.Icc (s J) S,
        D ^ (-k / (a : ℝ)) * (volume (ball (c J) (32 * D ^ k)))⁻¹ *
        ∑ p ∈ ℭ with ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (16 * D ^ s J)) ∧ 𝔰 p = k,
          ∫⁻ x in E p, ‖f x‖ₑ := by
      rw [← mul_rotate _ _ (2 ^ (4 * a)), mul_comm (_ ^ _), mul_assoc (_ * _),
        Finset.mul_sum (a := 2 ^ (4 * a))]; congr! 2 with k mk
      rw [← mul_assoc _ (_ * _), mul_rotate', ← ENNReal.div_eq_inv_mul, mul_assoc,
        Finset.mul_sum (a := _ / _)]; congr! 2 with p mp
      rw [← ENNReal.inv_div (b := 2 ^ (4 * a)) (by left; simp) (by left; simp),
        ENNReal.div_eq_inv_mul]
    _ ≤ C7_5_5 a * 2 ^ (4 * a) * edist x x' ^ (a : ℝ)⁻¹ * ∑ k ∈ Finset.Icc (s J) S,
        D ^ (-k / (a : ℝ)) * (volume (ball (c J) (32 * D ^ k)))⁻¹ *
        ∫⁻ x in ball (c J) (32 * D ^ k), ‖f x‖ₑ := by
      gcongr with k mk; exact gtc_integral_bound hs
    _ = _ := by congr! 2 with k mk; rw [mul_assoc, setLAverage_eq, ENNReal.div_eq_inv_mul]

lemma gtc_sum_Icc_le_two : ∑ k ∈ Finset.Icc (s J) S, (D : ℝ≥0∞) ^ ((s J - k) / (a : ℝ)) ≤ 2 := by
  calc
    _ = ∑ k ∈ Finset.Icc (s J) S, ((D : ℝ≥0∞) ^ (a : ℝ)⁻¹) ^ (s J - k) := by
      congr with k; rw [← ENNReal.rpow_intCast, ← ENNReal.rpow_mul]; congr 1
      rw [← div_eq_inv_mul, Int.cast_sub]
    _ ≤ ∑ k ∈ Finset.Icc (s J) S, 2 ^ (s J - k) := by
      gcongr with k mk; rw [← ENNReal.rpow_intCast, ← ENNReal.rpow_intCast]
      apply ENNReal.rpow_le_rpow_of_nonpos (by simp_all)
      rw [defaultD, Nat.cast_pow, Nat.cast_ofNat, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      nth_rw 1 [← ENNReal.rpow_one 2]; apply ENNReal.rpow_le_rpow_of_exponent_le one_le_two
      rw [Nat.cast_mul, Nat.cast_pow, sq, mul_assoc, mul_self_mul_inv]
      norm_cast
      nlinarith [seven_le_c, four_le_a X]
    _ = ∑ k ∈ Finset.Icc 0 (S - s J).toNat, 2 ^ (-k : ℤ) := by
      have : s J ≤ S := scale_mem_Icc.2
      apply Finset.sum_nbij' (fun (k : ℤ) ↦ (k - s J).toNat) (· + s J) <;> intro k hk
      pick_goal -1
      · rw [Finset.mem_Icc] at hk
        rw [Int.toNat_of_nonneg (by lia), neg_sub]
      all_goals simp only [Finset.mem_Icc] at hk ⊢; omega
    _ ≤ ∑' k : ℕ, 2 ^ (-k : ℤ) := ENNReal.sum_le_tsum _
    _ = _ := ENNReal.sum_geometric_two_pow_neg_one

/-- The constant used in `global_tree_control1_edist`.
Has value `2 ^ (128 * a ^ 3 + 4 * a + 1)` in the blueprint. -/
irreducible_def C7_5_9d (a : ℕ) : ℝ≥0 := C7_5_5 a * 2 ^ (4 * a + 1)

/-- Part 2 of equation (7.5.18) of Lemma 7.5.9. -/
lemma global_tree_control1_edist_part2
    (hu : u ∈ t) {ℭ : Set (𝔓 X)} (hℭ : ℭ ⊆ t u) (hf : BoundedCompactSupport f)
    (hs : ∀ p ∈ ℭ, ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (16 * D ^ s J)) → s J ≤ 𝔰 p)
    (hx : x ∈ ball (c J) (16 * D ^ s J)) (hx' : x' ∈ ball (c J) (16 * D ^ s J)) :
    edist (exp (.I * 𝒬 u x) * adjointCarlesonSum ℭ f x)
      (exp (.I * 𝒬 u x') * adjointCarlesonSum ℭ f x') ≤
    C7_5_9d a * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x := by
  calc
    _ ≤ C7_5_5 a * 2 ^ (4 * a) * edist x x' ^ (a : ℝ)⁻¹ * ∑ k ∈ Finset.Icc (s J) S,
        D ^ (-k / (a : ℝ)) * ⨍⁻ x in ball (c J) (32 * D ^ k), ‖f x‖ₑ ∂volume :=
      global_tree_control1_edist_part1 hu hℭ hf hs hx hx'
    _ ≤ C7_5_5 a * 2 ^ (4 * a) * edist x x' ^ (a : ℝ)⁻¹ * ∑ k ∈ Finset.Icc (s J) S,
        D ^ (-k / (a : ℝ)) * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x := by
      gcongr with k mk; rw [Finset.mem_Icc] at mk
      apply laverage_le_biInf_MB
      · gcongr; exacts [by norm_num, one_le_realD a, mk.1]
      · use ⟨5, (k - s J).toNat, J⟩
        simp only [𝓑, c𝓑, r𝓑, mem_prod, mem_Iic, mem_univ, le_add_iff_nonneg_left, zero_le,
          and_true, true_and]
        rw [show s J + (k - s J).toNat = k by lia, Int.toNat_le, Nat.cast_add, Nat.cast_mul,
          Nat.cast_ofNat]
        have : -S ≤ s J := scale_mem_Icc.1
        exact ⟨by omega, by norm_num⟩
    _ = C7_5_5 a * 2 ^ (4 * a) * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ *
        (∑ k ∈ Finset.Icc (s J) S, (D : ℝ≥0∞) ^ ((s J - k) / (a : ℝ))) *
        ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x := by
      have fla := four_le_a X
      have dpos : 0 < (D : ℝ≥0∞) ^ s J := ENNReal.zpow_pos (by simp) (by simp) _
      have dlt : (D : ℝ≥0∞) ^ s J < ⊤ := ENNReal.zpow_lt_top (by simp) (by simp) _
      have bpos : ((D : ℝ≥0∞) ^ s J) ^ (a : ℝ)⁻¹ ≠ 0 := (ENNReal.rpow_pos dpos dlt.ne).ne'
      have bnt : ((D : ℝ≥0∞) ^ s J) ^ (a : ℝ)⁻¹ ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by positivity) dlt.ne
      rw [← ENNReal.inv_mul_cancel_right (a := (_ ^ (a : ℝ)⁻¹)) bpos bnt, mul_comm _ _⁻¹,
        ← ENNReal.div_eq_inv_mul, ← ENNReal.div_rpow_of_nonneg _ _ (by positivity), ← mul_assoc,
        mul_assoc _ _ (∑ k ∈ _, _), Finset.mul_sum]
      conv_lhs => enter [2, 2, k]; rw [← mul_assoc]
      rw [← Finset.sum_mul, ← mul_assoc]; congr! with k mk
      rw [← ENNReal.rpow_intCast, ← ENNReal.rpow_mul, ← div_eq_mul_inv,
        ← ENNReal.rpow_add _ _ (by simp) (by simp), neg_div, ← sub_eq_add_neg, sub_div]
    _ ≤ C7_5_5 a * 2 ^ (4 * a + 1) * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ *
        ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x := by
      rw [pow_succ, ← mul_assoc, mul_assoc _ 2, mul_comm 2, ← mul_assoc]; gcongr
      exact gtc_sum_Icc_le_two
    _ = _ := by congr; rw [C7_5_9d, C7_5_5]; norm_cast

/-- Equation (7.5.18) of Lemma 7.5.9 for `ℭ = t u₁`. -/
lemma global_tree_control1_edist_left (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf : BoundedCompactSupport f)
    (hx : x ∈ ball (c J) (16 * D ^ s J)) (hx' : x' ∈ ball (c J) (16 * D ^ s J)) :
    edist (exp (.I * 𝒬 u₁ x) * adjointCarlesonSum (t u₁) f x)
      (exp (.I * 𝒬 u₁ x') * adjointCarlesonSum (t u₁) f x') ≤
    C7_5_9d a * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x :=
  global_tree_control1_edist_part2 hu₁ subset_rfl hf
    (fun _ mp dp ↦ scales_impacting_interval hu₁ hu₂ hu h2u hJ (mem_union_left _ mp) dp) hx hx'

/-- Equation (7.5.18) of Lemma 7.5.9 for `ℭ = t u₂ ∩ 𝔖₀ t u₁ u₂`. -/
lemma global_tree_control1_edist_right (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf : BoundedCompactSupport f)
    (hx : x ∈ ball (c J) (16 * D ^ s J)) (hx' : x' ∈ ball (c J) (16 * D ^ s J)) :
    edist (exp (.I * 𝒬 u₂ x) * adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f x)
      (exp (.I * 𝒬 u₂ x') * adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f x') ≤
    C7_5_9d a * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x :=
  global_tree_control1_edist_part2 hu₂ inter_subset_left hf
    (fun _ mp dp ↦ scales_impacting_interval hu₁ hu₂ hu h2u hJ (mem_union_right _ mp) dp) hx hx'

/-- The constant used in `global_tree_control1_supbound`.
Has value `2 ^ (128 * a ^ 3 + 4 * a + 3)` in the blueprint. -/
irreducible_def C7_5_9s (a : ℕ) : ℝ≥0 := C7_5_5 a * 2 ^ (4 * a + 3)

lemma one_le_C7_5_9s : 1 ≤ C7_5_9s a := by
  simp only [C7_5_9s, C7_5_5]; norm_cast
  rw [← pow_add]; exact Nat.one_le_two_pow

lemma C7_5_9d_le_C7_5_9s : C7_5_9d a ≤ C7_5_9s a := by
  simp only [C7_5_9d, C7_5_9s]
  exact mul_le_mul_right (pow_le_pow_right' one_le_two (add_le_add_right NeZero.one_le _)) _

/-- Equation (7.5.17) of Lemma 7.5.9. -/
lemma global_tree_control1_supbound (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (ℭ : Set (𝔓 X)) (hℭ : ℭ = t u₁ ∨ ℭ = t u₂ ∩ 𝔖₀ t u₁ u₂)
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf : BoundedCompactSupport f) :
    ⨆ x ∈ ball (c J) (16 * D ^ s J), ‖adjointCarlesonSum ℭ f x‖ₑ ≤
    (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum ℭ f x‖ₑ) +
    C7_5_9s a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x := by
  rw [← tsub_le_iff_left]; refine ENNReal.le_of_forall_pos_le_add fun ε εpos blt ↦ ?_
  obtain ⟨x, hx, ex⟩ : ∃ x₀ ∈ ball (c J) (16 * D ^ s J),
      ⨆ x ∈ ball (c J) (16 * D ^ s J), ‖adjointCarlesonSum ℭ f x‖ₑ ≤
      ‖adjointCarlesonSum ℭ f x₀‖ₑ + (ε / 2 : ℝ≥0) := by
    apply ENNReal.exists_biSup_le_enorm_add_eps (by positivity)
      ⟨c J, mem_ball_self (by unfold defaultD; positivity)⟩
    rw [isBounded_image_iff_bddAbove_norm']
    exact hf.bddAbove_norm_adjointCarlesonSum |>.mono (image_subset_range ..)
  obtain ⟨x', hx', ex'⟩ : ∃ x₀ ∈ ball (c J) (8⁻¹ * D ^ s J),
      ‖adjointCarlesonSum ℭ f x₀‖ₑ - (ε / 2 : ℝ≥0) ≤
      ⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum ℭ f x‖ₑ :=
    ENNReal.exists_enorm_sub_eps_le_biInf (by positivity)
      ⟨c J, mem_ball_self (by unfold defaultD; positivity)⟩
  calc
    _ ≤ (‖adjointCarlesonSum ℭ f x‖ₑ + (ε / 2 : ℝ≥0)) -
        (‖adjointCarlesonSum ℭ f x'‖ₑ - (ε / 2 : ℝ≥0)) := tsub_le_tsub ex ex'
    _ ≤ (ε / 2 : ℝ≥0) + ‖adjointCarlesonSum ℭ f x‖ₑ -
        ‖adjointCarlesonSum ℭ f x'‖ₑ + (ε / 2 : ℝ≥0) := by
      rw [add_comm]; exact tsub_tsub_le_tsub_add
    _ ≤ (ε / 2 : ℝ≥0) + (‖adjointCarlesonSum ℭ f x‖ₑ - ‖adjointCarlesonSum ℭ f x'‖ₑ) +
        (ε / 2 : ℝ≥0) := add_le_add_left add_tsub_le_assoc _
    _ = ‖‖adjointCarlesonSum ℭ f x‖ₑ - ‖adjointCarlesonSum ℭ f x'‖ₑ‖ₑ + ε := by
      rw [add_rotate, add_assoc]; simp
    _ ≤ (C7_5_9d a * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x) + ε := by
      refine add_le_add_left ?_ _
      replace hx' : x' ∈ ball (c J) (16 * D ^ s J) := by
        exact (ball_subset_ball (by gcongr; norm_num)) hx'
      rcases hℭ with rfl | rfl
      · nth_rw 2 [← one_mul ‖_‖ₑ]; rw [← enorm_exp_I_mul_ofReal (𝒬 u₁ x), ← enorm_mul]
        nth_rw 3 [← one_mul ‖_‖ₑ]; rw [← enorm_exp_I_mul_ofReal (𝒬 u₁ x'), ← enorm_mul]
        apply ENNReal.enorm_enorm_sub_enorm_le.trans
        rw [← edist_eq_enorm_sub]
        exact global_tree_control1_edist_left hu₁ hu₂ hu h2u hJ hf hx hx'
      · nth_rw 2 [← one_mul ‖_‖ₑ]; rw [← enorm_exp_I_mul_ofReal (𝒬 u₂ x), ← enorm_mul]
        nth_rw 3 [← one_mul ‖_‖ₑ]; rw [← enorm_exp_I_mul_ofReal (𝒬 u₂ x'), ← enorm_mul]
        apply ENNReal.enorm_enorm_sub_enorm_le.trans
        rw [← edist_eq_enorm_sub]
        exact global_tree_control1_edist_right hu₁ hu₂ hu h2u hJ hf hx hx'
    _ ≤ (C7_5_9d a * 2 ^ ((2 : ℕ) : ℝ) * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x) + ε := by
      gcongr; rw [mem_ball] at hx hx'; rw [edist_dist]
      calc
        _ ≤ (ENNReal.ofReal ((16 + 8⁻¹) * D ^ s J) / D ^ s J) ^ (a : ℝ)⁻¹ := by
          gcongr; rw [add_mul]; exact ((dist_triangle_right ..).trans_lt (add_lt_add hx hx')).le
        _ ≤ (2 ^ (8 : ℝ)) ^ (a : ℝ)⁻¹ := by
          have Dpos : 0 < (D : ℝ≥0∞) ^ s J := ENNReal.zpow_pos (by simp) (by simp) _
          have Dlt : (D : ℝ≥0∞) ^ s J < ⊤ := ENNReal.zpow_lt_top (by simp) (by simp) _
          rw [ENNReal.ofReal_mul (by norm_num), ← Real.rpow_intCast,
            ← ENNReal.ofReal_rpow_of_pos (by unfold defaultD; positivity),
            show ENNReal.ofReal D = D by norm_cast, ENNReal.rpow_intCast,
            ENNReal.mul_div_cancel_right Dpos.ne' Dlt.ne]
          exact ENNReal.rpow_le_rpow (by norm_num) (by positivity)
        _ ≤ (2 ^ (8 : ℝ)) ^ (4 : ℝ)⁻¹ := by
          gcongr; exacts [by norm_num, by norm_cast; linarith [four_le_a X]]
        _ = _ := by rw [← ENNReal.rpow_mul]; norm_num
    _ = _ := by
      congr
      rw [C7_5_9d, C7_5_9s, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat, mul_assoc,
        ENNReal.rpow_natCast, ← pow_add]; rfl

/-- The constant used in `global_tree_control2`.
Has value `2 ^ (129 * a ^ 3)` in the blueprint. -/
irreducible_def C7_5_10 (a : ℕ) : ℝ≥0 := 2 ^ ((𝕔 + 4 + 𝕔 / 4) * a ^ 3)

lemma le_C7_5_10 (ha : 4 ≤ a) : C7_5_7 a + C7_5_9s a ≤ C7_5_10 a := by
  simp only [C7_5_7, C7_5_9s, C7_5_5, ← pow_add, C7_5_10]
  apply add_le_pow_two ?_ le_rfl ?_
  · suffices 1 * a ^ 3 ≤ (𝕔 / 4) * a ^ 3 by linarith
    gcongr
    have := seven_le_c
    lia
  · have : 4 * (4 * a) ≤ a ^ 3 := by rw [pow_three]; gcongr
    linarith

lemma C7_5_9s_le_C7_5_10 (ha : 4 ≤ a) : C7_5_9s a ≤ C7_5_10 a :=
  le_trans le_add_self (le_C7_5_10 ha)

lemma one_le_C7_5_10 (ha : 4 ≤ a) : 1 ≤ C7_5_10 a :=
  one_le_C7_5_9s.trans (C7_5_9s_le_C7_5_10 ha)

/-- Lemma 7.5.10 -/
lemma global_tree_control2 (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf : BoundedCompactSupport f) :
    ⨆ x ∈ ball (c J) (16 * D ^ s J), ‖adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f x‖ₑ ≤
    (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f x‖ₑ) +
    C7_5_10 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x :=
  calc
    _ ≤ _ := global_tree_control1_supbound hu₁ hu₂ hu h2u _ (.inr rfl) hJ hf
    _ = (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J),
        ‖adjointCarlesonSum (t u₂) f x - adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f x‖ₑ) +
        C7_5_9s a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x := by
      congr! with x mx; exact adjointCarlesonSum_inter
    _ ≤ (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f x‖ₑ) +
        (⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f x‖ₑ) +
        C7_5_9s a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x := by
      gcongr; exact ENNReal.biInf_enorm_sub_le
    _ ≤ (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f x‖ₑ) +
        (C7_5_7 a + C7_5_9s a) * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x := by
      rw [add_mul, add_assoc]
      gcongr
      exact local_tree_control hu₁ hu₂ hu h2u hJ hf
    _ ≤ _ := by
      gcongr
      norm_cast
      apply le_C7_5_10 (four_le_a X)

/-- The product on the right-hand side of Lemma 7.5.4. -/
def P7_5_4 (t : Forest X n) (u₁ u₂ : 𝔓 X) (f₁ f₂ : X → ℂ) (J : Grid X) : ℝ≥0∞ :=
  ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₁) f₁ x‖ₑ) +
    ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₁ x) *
  ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f₂ x‖ₑ) +
    ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₂ x)

lemma P7_5_4_le_adjointBoundaryOperator_mul (mx : x ∈ ball (c J) (8⁻¹ * D ^ s J)) :
    P7_5_4 t u₁ u₂ f₁ f₂ J ≤
    adjointBoundaryOperator t u₁ f₁ x * adjointBoundaryOperator t u₂ f₂ x := by
  have mx' : x ∈ J := by
    refine ((ball_subset_ball ?_).trans ball_subset_Grid) mx
    change _ ≤ (D : ℝ) ^ s J / 4; rw [div_eq_inv_mul]; gcongr; norm_num
  unfold P7_5_4 adjointBoundaryOperator
  conv_lhs => enter [1]; rw [← add_zero (_ + _)]
  conv_lhs => enter [2]; rw [← add_zero (_ + _)]
  gcongr
  exacts [biInf_le _ mx, biInf_le _ mx', zero_le _, biInf_le _ mx, biInf_le _ mx', zero_le _]

/-- The support of `holderFunction` is in `𝓘 u₁`. -/
lemma support_holderFunction_subset (u₂ : 𝔓 X) (f₁ f₂ : X → ℂ) (J : Grid X) (hu₁ : u₁ ∈ t) :
    support (holderFunction t u₁ u₂ f₁ f₂ J) ⊆ 𝓘 u₁ := by
  rw [support_subset_iff']; intro x nx
  have : adjointCarlesonSum (t u₁) f₁ x = 0 := by
    refine Finset.sum_eq_zero fun p mp ↦ ?_
    simp_rw [Finset.mem_filter_univ] at mp
    rw [adjoint_tile_support2 hu₁ mp]
    exact indicator_of_notMem nx _
  rw [holderFunction, this, mul_zero, mul_zero, zero_mul]

lemma enorm_holderFunction_le (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf₁ : BoundedCompactSupport f₁) (hf₂ : BoundedCompactSupport f₂)
    (mx : x ∈ ball (c J) (16 * D ^ s J)) :
    ‖holderFunction t u₁ u₂ f₁ f₂ J x‖ₑ ≤ C7_5_9s a * C7_5_10 a * P7_5_4 t u₁ u₂ f₁ f₂ J := by
  simp_rw [holderFunction, enorm_mul, RCLike.enorm_conj, enorm_mul, enorm_exp_I_mul_ofReal, one_mul,
    Complex.enorm_real, NNReal.enorm_eq]
  calc
    _ ≤ 1 * (⨆ z ∈ ball (c J) (16 * D ^ s J), ‖adjointCarlesonSum (t u₁) f₁ z‖ₑ) *
        ⨆ z ∈ ball (c J) (16 * D ^ s J), ‖adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ z‖ₑ := by
      gcongr
      · rw [ENNReal.coe_le_one_iff]
        exact (χ_le_indicator hJ).trans ((indicator_le fun _ _ ↦ le_refl _) _)
      · apply le_biSup _ mx
      · apply le_biSup _ mx
    _ ≤ ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₁) f₁ x‖ₑ) +
          C7_5_9s a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₁ x) *
        ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f₂ x‖ₑ) +
          C7_5_10 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₂ x) := by
      rw [one_mul]; gcongr
      · exact global_tree_control1_supbound hu₁ hu₂ hu h2u _ (.inl rfl) hJ hf₁
      · exact global_tree_control2 hu₁ hu₂ hu h2u hJ hf₂
    _ ≤ _ := by
      rw [P7_5_4, mul_mul_mul_comm]
      conv_rhs => rw [mul_add, mul_add]
      gcongr <;> (nth_rw 1 [← one_mul (⨅ x ∈ _, _)]; gcongr; rw [ENNReal.one_le_coe_iff])
      · exact one_le_C7_5_9s
      · exact one_le_C7_5_10 (four_le_a X)

lemma holder_correlation_tree_1 (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf₁ : BoundedCompactSupport f₁) (hf₂ : BoundedCompactSupport f₂)
    (mx : x ∈ ball (c J) (16 * D ^ s J)) (mx' : x' ∈ 𝓘 u₁) :
    edist (χ t u₁ u₂ J x) (χ t u₁ u₂ J x') *
    ‖exp (.I * 𝒬 u₁ x) * adjointCarlesonSum (t u₁) f₁ x‖ₑ *
    ‖exp (.I * 𝒬 u₂ x) * adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ x‖ₑ ≤
    C7_5_2 a * C7_5_9s a * C7_5_10 a * P7_5_4 t u₁ u₂ f₁ f₂ J * (edist x x' / D ^ s J) := by
  simp_rw [enorm_mul, enorm_exp_I_mul_ofReal, one_mul]
  by_cases mu₁ : x ∉ 𝓘 u₁
  · have : adjointCarlesonSum (t u₁) f₁ x = 0 := by
      refine Finset.sum_eq_zero fun p mp ↦ ?_
      simp_rw [Finset.mem_filter_univ] at mp
      rw [adjoint_tile_support2 hu₁ mp]
      exact indicator_of_notMem mu₁ _
    rw [this, enorm_zero, mul_zero, zero_mul]; exact zero_le _
  rw [not_not] at mu₁; rw [edist_dist]
  calc
    _ ≤ ENNReal.ofReal (C7_5_2 a * dist x x' / D ^ s J) *
        ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₁) f₁ x‖ₑ) +
          C7_5_9s a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₁ x) *
        ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f₂ x‖ₑ) +
          C7_5_10 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₂ x) := by
      gcongr
      · exact dist_χ_le hu₁ hu₂ hu h2u hJ mu₁ mx'
      · exact (le_biSup _ mx).trans <|
          global_tree_control1_supbound hu₁ hu₂ hu h2u _ (.inl rfl) hJ hf₁
      · exact (le_biSup _ mx).trans <| global_tree_control2 hu₁ hu₂ hu h2u hJ hf₂
    _ ≤ ENNReal.ofReal (C7_5_2 a * dist x x' / D ^ s J) *
        (C7_5_9s a * C7_5_10 a * P7_5_4 t u₁ u₂ f₁ f₂ J) := by
      rw [mul_assoc (ENNReal.ofReal _)]; gcongr _ * ?_
      rw [P7_5_4, mul_mul_mul_comm]
      conv_rhs => rw [mul_add, mul_add]
      gcongr <;> (nth_rw 1 [← one_mul (⨅ x ∈ _, _)]; gcongr; rw [ENNReal.one_le_coe_iff])
      · exact one_le_C7_5_9s
      · exact one_le_C7_5_10 (four_le_a X)
    _ = _ := by
      rw [mul_div_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_div_of_pos (by unfold defaultD; positivity), ← edist_dist x x',
        ← Real.rpow_intCast, ← ENNReal.ofReal_rpow_of_pos (realD_pos a), ENNReal.rpow_intCast,
        ENNReal.ofReal_natCast]
      ring

lemma holder_correlation_tree_2 (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf₁ : BoundedCompactSupport f₁) (hf₂ : BoundedCompactSupport f₂)
    (mx : x ∈ ball (c J) (16 * D ^ s J)) (mx' : x' ∈ ball (c J) (16 * D ^ s J)) :
    χ t u₁ u₂ J x' * edist (exp (.I * 𝒬 u₁ x) * adjointCarlesonSum (t u₁) f₁ x)
      (exp (.I * 𝒬 u₁ x') * adjointCarlesonSum (t u₁) f₁ x') *
    ‖exp (.I * 𝒬 u₂ x) * adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ x‖ₑ ≤
    C7_5_9d a * C7_5_10 a * P7_5_4 t u₁ u₂ f₁ f₂ J * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ :=
  calc
    _ ≤ 1 * (C7_5_9d a * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₁ x) *
        ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f₂ x‖ₑ) +
          C7_5_10 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₂ x) := by
      gcongr
      · rw [ENNReal.coe_le_one_iff]
        exact (χ_le_indicator hJ).trans ((indicator_le fun _ _ ↦ le_refl _) _)
      · exact global_tree_control1_edist_left hu₁ hu₂ hu h2u hJ hf₁ mx mx'
      · rw [enorm_mul, enorm_exp_I_mul_ofReal, one_mul]
        exact (le_biSup _ mx).trans <| global_tree_control2 hu₁ hu₂ hu h2u hJ hf₂
    _ = (C7_5_9d a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₁ x) *
        ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f₂ x‖ₑ) +
          C7_5_10 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₂ x) * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ := by
      ring
    _ ≤ (C7_5_9d a * (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₁) f₁ x‖ₑ) +
          C7_5_9d a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₁ x) *
        (C7_5_10 a * (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f₂ x‖ₑ) +
          C7_5_10 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₂ x) * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ := by
      gcongr
      · exact le_add_self
      · nth_rw 1 [← one_mul (⨅ x ∈ _, _)]; gcongr; rw [ENNReal.one_le_coe_iff]
        exact one_le_C7_5_10 (four_le_a X)
    _ = _ := by rw [← mul_add, ← mul_add, mul_mul_mul_comm, P7_5_4]

lemma holder_correlation_tree_3 (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf₁ : BoundedCompactSupport f₁) (hf₂ : BoundedCompactSupport f₂)
    (mx : x ∈ ball (c J) (16 * D ^ s J)) (mx' : x' ∈ ball (c J) (16 * D ^ s J)) :
    χ t u₁ u₂ J x' * ‖exp (.I * 𝒬 u₁ x') * adjointCarlesonSum (t u₁) f₁ x'‖ₑ *
    edist (exp (.I * 𝒬 u₂ x) * adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ x)
      (exp (.I * 𝒬 u₂ x') * adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ x') ≤
    C7_5_9s a * C7_5_9d a * P7_5_4 t u₁ u₂ f₁ f₂ J * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ :=
  calc
    _ ≤ 1 * ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₁) f₁ x‖ₑ) +
          C7_5_9s a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₁ x) *
        (C7_5_9d a * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₂ x) := by
      gcongr
      · rw [ENNReal.coe_le_one_iff]
        exact (χ_le_indicator hJ).trans ((indicator_le fun _ _ ↦ le_refl _) _)
      · rw [enorm_mul, enorm_exp_I_mul_ofReal, one_mul]
        exact (le_biSup _ mx').trans <|
          global_tree_control1_supbound hu₁ hu₂ hu h2u _ (.inl rfl) hJ hf₁
      · exact global_tree_control1_edist_right hu₁ hu₂ hu h2u hJ hf₂ mx mx'
    _ = ((⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₁) f₁ x‖ₑ) +
          C7_5_9s a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₁ x) *
        (C7_5_9d a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₂ x) * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ := by
      ring
    _ ≤ (C7_5_9s a * (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₁) f₁ x‖ₑ) +
          C7_5_9s a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₁ x) *
        (C7_5_9d a * (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂) f₂ x‖ₑ) +
          C7_5_9d a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f₂ x) * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ := by
      gcongr
      · nth_rw 1 [← one_mul (⨅ x ∈ _, _)]; gcongr; rw [ENNReal.one_le_coe_iff]
        exact one_le_C7_5_9s
      · exact le_add_self
    _ = _ := by rw [← mul_add, ← mul_add, mul_mul_mul_comm, P7_5_4]

/-- An intermediate constant in Lemma 7.5.4. -/
def I7_5_4 (a : ℕ) : ℝ≥0 := 2 ^ ((4 * 𝕔 + 9 + 3 * (𝕔 / 4)) * a ^ 3 + 12 * a)

lemma le_I7_5_4 (ha : 4 ≤ a) :
    32 * C7_5_2 a * C7_5_9s a * C7_5_10 a + C7_5_9d a * C7_5_10 a + C7_5_9s a * C7_5_9d a
    ≤ I7_5_4 a := by
  have C : (32 : ℝ≥0) = 2 ^ 5 := by norm_num
  simp only [C7_5_2, C7_5_9s, C7_5_10, C7_5_9d, C7_5_5, C, ← pow_add, I7_5_4]
  apply add_le_pow_two₃ (s := 11 * a + (4 * 𝕔 + 9 + 3 * (𝕔 / 4)) * a ^ 3) ?_ ?_ ?_ ?_
  · ring_nf
    linarith
  · ring_nf
    lia
  · ring_nf
    lia
  · linarith [sixteen_times_le_cube ha]

lemma edist_holderFunction_le (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf₁ : BoundedCompactSupport f₁) (hf₂ : BoundedCompactSupport f₂)
    (mx : x ∈ ball (c J) (16 * D ^ s J)) (mx' : x' ∈ ball (c J) (16 * D ^ s J)) :
    edist (holderFunction t u₁ u₂ f₁ f₂ J x) (holderFunction t u₁ u₂ f₁ f₂ J x') ≤
    I7_5_4 a * P7_5_4 t u₁ u₂ f₁ f₂ J * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ := by
  by_cases mu₁ : x ∉ 𝓘 u₁ ∧ x' ∉ 𝓘 u₁
  · have h0 := support_subset_iff'.mp (support_holderFunction_subset u₂ f₁ f₂ J hu₁)
    rw [h0 _ mu₁.1, h0 _ mu₁.2, edist_self]; exact zero_le _
  rw [not_and_or, not_not, not_not] at mu₁
  wlog mu₁' : x' ∈ 𝓘 u₁ generalizing x x'
  · specialize this mx' mx mu₁.symm (mu₁.resolve_right mu₁')
    rwa [edist_comm, edist_comm x'] at this
  let CH := χ t u₁ u₂ J
  let T₁ := fun z ↦ exp (.I * 𝒬 u₁ z) * adjointCarlesonSum (t u₁) f₁ z
  let T₂ := fun z ↦ exp (.I * 𝒬 u₂ z) * adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ z
  rw [edist_eq_enorm_sub]
  change ‖CH x * T₁ x * conj (T₂ x) - CH x' * T₁ x' * conj (T₂ x')‖ₑ ≤ _
  calc
    _ ≤ edist (CH x * T₁ x * conj (T₂ x)) (CH x' * T₁ x * conj (T₂ x)) +
        edist (CH x' * T₁ x * conj (T₂ x)) (CH x' * T₁ x' * conj (T₂ x)) +
        edist (CH x' * T₁ x' * conj (T₂ x)) (CH x' * T₁ x' * conj (T₂ x')) := by
      rw [← edist_eq_enorm_sub]
      exact edist_triangle4 ..
    _ = edist (CH x) (CH x') * ‖T₁ x‖ₑ * ‖T₂ x‖ₑ + CH x' * edist (T₁ x) (T₁ x') * ‖T₂ x‖ₑ +
        CH x' * ‖T₁ x'‖ₑ * edist (T₂ x) (T₂ x') := by
      simp_rw [edist_eq_enorm_sub, ← sub_mul, ← mul_sub, ← map_sub (starRingEnd ℂ), enorm_mul, RCLike.enorm_conj]
      rw [Complex.enorm_real, NNReal.enorm_eq, edist_dist, NNReal.dist_eq, ← Complex.ofReal_sub, Complex.enorm_real, Real.enorm_eq_ofReal_abs]
    _ ≤ C7_5_2 a * C7_5_9s a * C7_5_10 a * P7_5_4 t u₁ u₂ f₁ f₂ J * (edist x x' / D ^ s J) +
        C7_5_9d a * C7_5_10 a * P7_5_4 t u₁ u₂ f₁ f₂ J * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ +
        C7_5_9s a * C7_5_9d a * P7_5_4 t u₁ u₂ f₁ f₂ J * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ := by
      gcongr ?_ + ?_ + ?_
      · exact holder_correlation_tree_1 hu₁ hu₂ hu h2u hJ hf₁ hf₂ mx mu₁'
      · exact holder_correlation_tree_2 hu₁ hu₂ hu h2u hJ hf₁ hf₂ mx mx'
      · exact holder_correlation_tree_3 hu₁ hu₂ hu h2u hJ hf₁ hf₂ mx mx'
    _ ≤ C7_5_2 a * C7_5_9s a * C7_5_10 a * P7_5_4 t u₁ u₂ f₁ f₂ J *
          (32 * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹) +
        C7_5_9d a * C7_5_10 a * P7_5_4 t u₁ u₂ f₁ f₂ J * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ +
        C7_5_9s a * C7_5_9d a * P7_5_4 t u₁ u₂ f₁ f₂ J * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ := by
      gcongr
      rcases le_or_gt (edist x x' / D ^ s J) 1 with h | h
      · nth_rw 1 [← one_mul (_ / _), ← ENNReal.rpow_one (_ / _)]
        refine mul_le_mul' (by norm_num) (ENNReal.rpow_le_rpow_of_exponent_ge h ?_)
        rw [inv_le_one_iff₀]; right; exact_mod_cast a_pos X
      · nth_rw 1 [← mul_one (_ / _), ← ENNReal.one_rpow (a : ℝ)⁻¹]
        refine mul_le_mul' (ENNReal.div_le_of_le_mul ?_) (ENNReal.rpow_le_rpow h.le (by positivity))
        have hc : 32 * (D : ℝ≥0∞) ^ s J = ENNReal.ofReal (32 * D ^ s J) := by
          rw [ENNReal.ofReal_mul (by norm_num), ← Real.rpow_intCast,
            ← ENNReal.ofReal_rpow_of_pos (realD_pos a), ENNReal.rpow_intCast,
            ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
        rw [edist_dist, hc]; apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ dist x (c J) + dist x' (c J) := dist_triangle_right ..
          _ ≤ 16 * D ^ s J + 16 * D ^ s J := add_le_add (mem_ball.mp mx).le (mem_ball.mp mx').le
          _ = _ := by ring
    _ = (32 * C7_5_2 a * C7_5_9s a * C7_5_10 a + C7_5_9d a * C7_5_10 a + C7_5_9s a * C7_5_9d a)
          * P7_5_4 t u₁ u₂ f₁ f₂ J * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ := by ring
    _ ≤ _ := by
      gcongr
      norm_cast
      apply le_I7_5_4 (four_le_a X)

/-- The constant used in `holder_correlation_tree`.
Has value `2 ^ (485 * a ^ 3)` in the blueprint. -/
irreducible_def C7_5_4 (a : ℕ) : ℝ≥0 := 2 ^ ((4 * 𝕔 + 10 + 3 * (𝕔 / 4)) * a ^ 3)

lemma le_C7_5_4 (ha : 4 ≤ a) :
    C7_5_9s a * C7_5_10 a + 16 ^ τ * I7_5_4 a ≤ C7_5_4 a := by
  have : (16 : ℝ≥0) ^ τ ≤ 2 ^ 1 := by
    rw [defaultτ, show (16 : ℝ≥0) = 2 ^ (4 : ℝ) by norm_num, ← NNReal.rpow_mul, ← div_eq_mul_inv,
      pow_one]
    nth_rw 2 [← NNReal.rpow_one 2]
    apply NNReal.rpow_le_rpow_of_exponent_le one_le_two
    rw [div_le_one_iff]
    norm_cast
    lia
  grw [this]
  simp only [C7_5_9s, C7_5_5, C7_5_10, I7_5_4, C7_5_4, ← pow_add]
  apply add_le_pow_two ?_ le_rfl ?_
  · ring_nf
    suffices 2 + a * 4 ≤ a ^ 3 by lia
    linarith [sixteen_times_le_cube ha]
  · ring_nf
    linarith [sixteen_times_le_cube ha]

/-- Lemma 7.5.4. -/
lemma holder_correlation_tree (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂)
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf₁ : BoundedCompactSupport f₁) (hf₂ : BoundedCompactSupport f₂) :
    iHolENorm (holderFunction t u₁ u₂ f₁ f₂ J) (c J) (16 * D ^ s J) τ ≤
    C7_5_4 a * P7_5_4 t u₁ u₂ f₁ f₂ J := by
  unfold iHolENorm
  calc
    _ ≤ C7_5_9s a * C7_5_10 a * P7_5_4 t u₁ u₂ f₁ f₂ J +
        ENNReal.ofReal (16 * D ^ s J) ^ τ *
        ⨆ x ∈ ball (c J) (16 * D ^ s J), ⨆ y ∈ ball (c J) (16 * D ^ s J), ⨆ (_ : x ≠ y),
          (I7_5_4 a * P7_5_4 t u₁ u₂ f₁ f₂ J * ((D : ℝ≥0∞) ^ s J)⁻¹ ^ (a : ℝ)⁻¹) := by
      gcongr with x mx x' mx' hn
      · exact iSup₂_le_iff.mpr fun x mx ↦ enorm_holderFunction_le hu₁ hu₂ hu h2u hJ hf₁ hf₂ mx
      · calc
          _ ≤ I7_5_4 a * P7_5_4 t u₁ u₂ f₁ f₂ J *
              (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ / edist x x' ^ τ := by
              rw [← edist_eq_enorm_sub]
              have h := edist_holderFunction_le hu₁ hu₂ hu h2u hJ hf₁ hf₂ mx mx'
              exact ENNReal.div_le_div_right h (edist x x' ^ τ)
          _ = _ := by
            rw [mul_div_assoc, defaultτ, ← ENNReal.div_rpow_of_nonneg _ _ (by positivity),
              div_eq_mul_inv, div_eq_mul_inv, ← mul_rotate _ (edist x x'),
              ENNReal.inv_mul_cancel (by positivity [edist_pos.mpr hn]) (edist_ne_top x x'), one_mul]
    _ ≤ C7_5_9s a * C7_5_10 a * P7_5_4 t u₁ u₂ f₁ f₂ J +
        ENNReal.ofReal (16 * D ^ s J) ^ τ *
        (I7_5_4 a * P7_5_4 t u₁ u₂ f₁ f₂ J * ((D : ℝ≥0∞) ^ s J)⁻¹ ^ (a : ℝ)⁻¹) := by
      gcongr; exact iSup₂_le fun _ _ ↦ iSup₂_le fun _ _ ↦ iSup_le fun _ ↦ le_rfl
    _ = (C7_5_9s a * C7_5_10 a + 16 ^ τ * I7_5_4 a) * P7_5_4 t u₁ u₂ f₁ f₂ J := by
      have dn0 : ((D : ℝ≥0∞) ^ s J) ^ (a : ℝ)⁻¹ ≠ 0 := by
        rw [← pos_iff_ne_zero]; refine ENNReal.rpow_pos_of_nonneg ?_ (by positivity)
        exact ENNReal.zpow_pos (by unfold defaultD; positivity) (ENNReal.natCast_ne_top _) _
      have dnt : ((D : ℝ≥0∞) ^ s J) ^ (a : ℝ)⁻¹ ≠ ⊤ := by
        apply ENNReal.rpow_ne_top_of_nonneg (τ_nonneg X)
        rw [← lt_top_iff_ne_top]
        exact ENNReal.zpow_lt_top (by unfold defaultD; positivity) (ENNReal.natCast_ne_top _) _
      rw [add_mul, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
        ENNReal.mul_rpow_of_nonneg _ _ (τ_nonneg X), ← Real.rpow_intCast,
        ← ENNReal.ofReal_rpow_of_pos (realD_pos a), ENNReal.rpow_intCast, ENNReal.ofReal_natCast,
        ← mul_assoc, ← mul_rotate _ (_ ^ _), mul_assoc _ (_ ^ τ), defaultτ, ENNReal.inv_rpow,
        ENNReal.mul_inv_cancel dn0 dnt, mul_one, mul_rotate (_ ^ _)]
    _ ≤ _ := by
      gcongr
      rw [show (16 : ℝ≥0∞) = (16 : ℝ≥0) by rfl, ← ENNReal.coe_rpow_of_nonneg _ (τ_nonneg X),
        ← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_add, ENNReal.coe_le_coe]
      exact le_C7_5_4 (four_le_a X)

/-! ### Subsection 7.5.3 and Lemma 7.4.5 -/

/-- The constant used in `lower_oscillation_bound`.
Has value `2 ^ (Z * n / 2 - 201 * a ^ 3)` in the blueprint. -/
irreducible_def C7_5_11 (a n : ℕ) : ℝ≥0 := 2 ^ (Z * n / 2 - (2 * 𝕔 + 1) * (a : ℝ) ^ 3)

/-- A binomial bound used in Lemma 7.4.5. -/
lemma C7_5_11_binomial_bound (a4 : 4 ≤ a) :
    (1 + C7_5_11 a n : ℝ≥0∞) ^ (-(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) ≤
    2 ^ ((𝕔 / 4) * a ^ 3 + 7) * 2 ^ (-(Z * n : ℝ) / (4 * a ^ 2 + 2 * a ^ 3)) :=
  calc
    _ ≤ (2 : ℝ≥0∞) ^ ((Z * n / 2 - (2 * 𝕔 + 1) * a ^ 3) * -(2 * a ^ 2 + a ^ 3 : ℝ)⁻¹) := by
      rw [ENNReal.rpow_mul]
      apply ENNReal.rpow_le_rpow_of_nonpos (by rw [Left.neg_nonpos_iff]; positivity)
      rw [C7_5_11, ENNReal.coe_rpow_of_ne_zero two_ne_zero]
      exact le_add_self
    _ = 2 ^ ((2 * 𝕔 + 1) * (a : ℝ) / (2 + a)) * 2 ^ (-(Z * n : ℝ) / (4 * a ^ 2 + 2 * a ^ 3)) := by
      rw [← neg_mul_comm, neg_sub, ← div_eq_mul_inv, sub_div, sub_eq_add_neg,
        ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
      congr 2
      · rw [pow_succ' _ 2, ← add_mul, ← mul_assoc, mul_div_mul_right _ _ (by positivity)]
      · rw [div_div, ← neg_div]; congr; ring
    _ ≤ 2 ^ (2 * 𝕔 + 1) * 2 ^ (-(Z * n : ℝ) / (4 * a ^ 2 + 2 * a ^ 3)) := by
      rw [← ENNReal.rpow_natCast]; gcongr
      · exact one_le_two
      · rw [div_le_iff₀ (by positivity)]
        gcongr
        · simp
        · linarith
    _ ≤ _ := by
      gcongr 2 ^ ?_ * _
      · exact one_le_two
      · calc
          _ ≤ 2 * (4 * (𝕔 / 4) + 3) + 1 := by lia
          _ = 2 * 4 * 1 * (𝕔 / 4) + 7 := by ring
          _ ≤ a * a * a * (𝕔 / 4) + 7 := by gcongr <;> linarith
          _ = (𝕔 / 4) * a ^ 3 + 7 := by ring

/-- Lemma 7.5.11 -/
lemma lower_oscillation_bound (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) :
    C7_5_11 a n ≤ dist_{c J, 8 * D ^ s J} (𝒬 u₁) (𝒬 u₂) := by
  have existsBiggerThanJ : ∃ (J' : Grid X), J ≤ J' ∧ s J' = s J + 1 := by
    apply Grid.exists_scale_succ
    obtain ⟨⟨Jin𝓙₀, _⟩, ⟨jIsSubset : (J : Set X) ⊆ 𝓘 u₁, smaller : s J ≤ s (𝓘 u₁)⟩⟩ := hJ
    obtain ⟨p, belongs⟩ := t.nonempty' hu₁
    apply lt_of_le_of_ne smaller
    by_contra! h
    have u₁In𝓙₀ : 𝓘 u₁ ∈ 𝓙₀ (t.𝔖₀ u₁ u₂) := by
      apply mem_of_eq_of_mem (h := Jin𝓙₀)
      rw [eq_comm]
      apply (eq_or_disjoint h).resolve_right
      have notDisjoint := IF_subset_THEN_not_disjoint jIsSubset
      rw [disjoint_comm] at notDisjoint
      exact notDisjoint
    cases u₁In𝓙₀ with
    | inl min =>
      have sameScale : s (𝓘 p) = s (𝓘 u₁) := by
        linarith [
          (scale_mem_Icc (i := 𝓘 p)).left,
          show s (𝓘 p) ≤ s (𝓘 u₁) by exact (𝓘_le_𝓘 t hu₁ belongs).2
        ]
      suffices s (𝓘 u₁) > s (𝓘 p) by linarith
      by_contra! smaller
      have pIsSubset := (𝓘_le_𝓘 t hu₁ belongs).1
      apply HasSubset.Subset.not_ssubset
        ((fundamental_dyadic smaller).resolve_right (IF_subset_THEN_not_disjoint pIsSubset))
      apply HasSubset.Subset.ssubset_of_ne pIsSubset
      by_contra! sameSet
      apply Forest.𝓘_ne_𝓘 (hu := hu₁) (hp := belongs)
      exact Grid.inj (Prod.ext sameSet sameScale)
    | inr avoidance =>
      have pIn𝔖₀ : p ∈ t.𝔖₀ u₁ u₂ :=
        𝔗_subset_𝔖₀ (hu₁ := hu₁) (hu₂ := hu₂) (hu := hu) (h2u := h2u) belongs
      apply avoidance p pIn𝔖₀
      calc (𝓘 p : Set X)
      _ ⊆ 𝓘 u₁ := (𝓘_le_𝓘 t hu₁ belongs).1
      _ ⊆ ball (c (𝓘 u₁)) (4 * D ^ s (𝓘 u₁)) := by
        exact Grid_subset_ball
      _ ⊆ ball (c (𝓘 u₁)) (100 * D ^ (s (𝓘 u₁) + 1)) := by
        intro x hx
        exact gt_trans (calculation_16 (X := X) (s := s (𝓘 u₁))) hx
  rcases existsBiggerThanJ with ⟨J', JleJ', scaleSmaller⟩
  have notIn𝓙₀ : J' ∉ 𝓙₀ (t.𝔖₀ u₁ u₂) := by
    apply bigger_than_𝓙_is_not_in_𝓙₀ (sle := by linarith) (le := JleJ')
    exact mem_of_mem_inter_left hJ
  unfold 𝓙₀ at notIn𝓙₀
  simp only [mem_setOf_eq, not_or, not_forall] at notIn𝓙₀
  push Not at notIn𝓙₀
  obtain ⟨_, ⟨ p, pIn, pSubset ⟩⟩ := notIn𝓙₀
  have thus :=
    calc 2 ^ ((Z : ℝ) * n / 2)
    _ ≤ dist_{𝔠 p, D ^ 𝔰 p / 4} (𝒬 u₁) (𝒬 u₂) := pIn.2
    _ ≤ dist_{c J, 128 * D^(s J + 2)} (𝒬 u₁) (𝒬 u₂) := by
      apply cdist_mono
      intro point pointIn
      calc dist point (c J)
      _ ≤ dist point (c J') + dist (c J') (c J) := dist_triangle ..
      _ ≤ 100 * D ^ (s J' + 1) + dist (c J') (c J) := by
        rw [ball, Set.subset_def] at pSubset
        have := pSubset point (ball_subset_Grid pointIn)
        rw [mem_setOf_eq] at this
        gcongr
      _ ≤ 100 * D ^ (s J' + 1) + 4 * D ^ (s J') := by
        have : dist (c J) (c J') < 4 * D ^ (s J') :=
          Grid.dist_c_le_of_subset (subset := JleJ'.1)
        rw [dist_comm] at this
        gcongr
      _ = 100 * D ^ (s J + 2) + 4 * D ^ (s J + 1) := by
        rw [scaleSmaller, add_assoc, show (1 : ℤ) + 1 = 2 by rfl]
      _ < 128 * D^(s J + 2) := by
        exact calculation_11 (s J) (X := X)
    _ ≤ 2 ^ (2 * 𝕔 * (a^3) + 4 * a) * dist_{c J, 8 * D ^ s J} (𝒬 u₁) (𝒬 u₂) := by
      rw [show 128 * (D : ℝ)^(s J + 2) = 2 ^ (2 * 𝕔 * a ^ 2 + 4) * (8*D^(s J))
        by exact_mod_cast calculation_12 (s := s J)]
      rw [calculation_13]
      apply cdist_le_iterate
      have := realD_pos a
      positivity
  rw [C7_5_11]
  push_cast
  linarith [calculation_14 (X := X) (n := n), calculation_15 thus]

open Classical in
lemma cdtp_le_iHolENorm (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hf₁ : BoundedCompactSupport f₁) (hf₂ : BoundedCompactSupport f₂) :
    ‖∫ x, adjointCarlesonSum (t u₁) f₁ x * conj (adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ x)‖ₑ ≤
    ∑ J ∈ 𝓙₅ t u₁ u₂, C2_0_5 a * volume (ball (c J) (8 * D ^ s J)) *
      iHolENorm (holderFunction t u₁ u₂ f₁ f₂ J) (c J) (2 * (8 * D ^ s J)) τ *
      (1 + edist_{c J, 8 * D ^ s J} (𝒬 u₂) (𝒬 u₁)) ^ (-(2 * a^2 + a^3 : ℝ)⁻¹) := by
  classical
  have rearr : ∀ J x, t.χ u₁ u₂ J x *
      (adjointCarlesonSum (t u₁) f₁ x * conj (adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ x)) =
      exp (I * (𝒬 u₂ x - 𝒬 u₁ x)) * holderFunction t u₁ u₂ f₁ f₂ J x := fun J x ↦ by
    unfold holderFunction
    simp_rw [map_mul, ← mul_assoc]; congr 1
    rw [← mul_rotate _ _ (adjointCarlesonSum _ _ _)]; congr 1
    rw [← exp_conj, map_mul, conj_I, conj_ofReal, ← mul_assoc, ← mul_assoc, ← Complex.exp_add,
      neg_mul, ← sub_eq_neg_add, ← mul_sub, sub_sub_cancel_left, ← mul_rotate, ← Complex.exp_add,
      ← mul_add, add_neg_cancel, mul_zero, exp_zero, one_mul]
  calc
    _ = ‖∫ x in 𝓘 u₁, adjointCarlesonSum (t u₁) f₁ x *
        conj (adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ x)‖ₑ := by
      congr 1; refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x nx ↦ ?_).symm
      rw [adjoint_tile_support2_sum hu₁, indicator_of_notMem nx, zero_mul]
    _ = ‖∑ J ∈ 𝓙₅ t u₁ u₂, ∫ x, χ t u₁ u₂ J x * (adjointCarlesonSum (t u₁) f₁ x *
        conj (adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ x))‖ₑ := by
      rw [← integral_indicator coeGrid_measurable]
      conv_lhs =>
        enter [1, 2, x]
        rw [indicator_eq_indicator_one_mul, show (1 : X → ℂ) = (↑) ∘ (1 : X → ℝ≥0) by rfl,
          indicator_comp_of_zero (by simp), Function.comp_apply, ← sum_χ hu₁ hu₂ hu h2u x,
          NNReal.coe_sum, ofReal_sum, Finset.sum_mul]
      congr 1
      refine integral_finset_sum _ fun J mJ ↦ ((BoundedCompactSupport.toComplex ?_).mul
        (hf₁.adjointCarlesonSum.mul hf₂.adjointCarlesonSum.conj)).integrable
      rw [mem_toFinset] at mJ; exact boundedCompactSupport_toReal_χ mJ
    _ ≤ ∑ J ∈ 𝓙₅ t u₁ u₂, ‖∫ x, χ t u₁ u₂ J x * (adjointCarlesonSum (t u₁) f₁ x *
        conj (adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ x))‖ₑ := enorm_sum_le _ _
    _ = ∑ J ∈ 𝓙₅ t u₁ u₂,
        ‖∫ x, exp (.I * (𝒬 u₂ x - 𝒬 u₁ x)) * holderFunction t u₁ u₂ f₁ f₂ J x‖ₑ := by
      congr! 4 with J mJ x; exact rearr ..
    _ ≤ _ := by
      gcongr with J mJ; apply holder_van_der_corput (X := X); rw [support_subset_iff']; intro x nx
      rw [mem_toFinset] at mJ
      rw [holderFunction, χ_eq_zero_of_notMem_ball mJ nx, NNReal.coe_zero, ofReal_zero, zero_mul,
        zero_mul]

/-- The constant used in `correlation_distant_tree_parts`.
Has value `2 ^ (511 * a ^ 3) * 2 ^ (-(Z n) / (4a^2 + 2a^3))` in the blueprint. -/
irreducible_def C7_4_5 (a n : ℕ) : ℝ≥0 :=
  2 ^ ((4 * 𝕔 + 11 + 4 * (𝕔 / 4)) * a ^ 3) * 2 ^ (-(Z * n : ℝ) / (4 * a ^ 2 + 2 * a ^ 3))

lemma le_C7_4_5 (a4 : 4 ≤ a) :
    C2_0_5 a * C7_5_4 a * 2 ^ ((𝕔 / 4) * a ^ 3 + 7 + 6 * a)
      * 2 ^ (-(Z * n : ℝ) / (4 * a ^ 2 + 2 * a ^ 3)) ≤ C7_4_5 a n := by
  rw [C2_0_5, C7_5_4, C7_4_5]
  conv_lhs => enter [1, 1, 1, 2]; norm_cast
  conv_lhs => enter [1, 1, 2, 2]; norm_cast
  simp_rw [NNReal.rpow_natCast, ← pow_add]; gcongr
  · exact one_le_two
  · linarith [sixteen_times_le_cube a4]

/-- Lemma 7.4.5 -/
lemma correlation_distant_tree_parts (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hf₁ : BoundedCompactSupport f₁) (hf₂ : BoundedCompactSupport f₂) :
    ‖∫ x, adjointCarlesonSum (t u₁) f₁ x * conj (adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f₂ x)‖ₑ ≤
    C7_4_5 a n *
    eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₁ f₁) ·) 2 volume *
    eLpNorm ((𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₂ f₂) ·) 2 volume := by
  classical
  calc
    _ ≤ _ := cdtp_le_iHolENorm hu₁ hu₂ hu h2u hf₁ hf₂
    _ ≤ ∑ J ∈ 𝓙₅ t u₁ u₂, C2_0_5 a * volume (ball (c J) (8 * D ^ s J)) *
        (C7_5_4 a * P7_5_4 t u₁ u₂ f₁ f₂ J) * (1 + C7_5_11 a n) ^ (-(2 * a^2 + a^3 : ℝ)⁻¹) := by
      gcongr ∑ _ ∈ _, _ * ?_ * ?_ with J mJ <;> rw [mem_toFinset] at mJ
      · rw [← mul_assoc, show (2 : ℝ) * 8 = 16 by norm_num]
        exact holder_correlation_tree hu₁ hu₂ hu h2u mJ hf₁ hf₂
      · apply ENNReal.rpow_le_rpow_of_nonpos (by rw [Left.neg_nonpos_iff]; positivity)
        gcongr; rw [edist_comm, edist_nndist, ENNReal.coe_le_coe]
        exact lower_oscillation_bound hu₁ hu₂ hu h2u mJ
    _ = C2_0_5 a * C7_5_4 a * (1 + C7_5_11 a n) ^ (-(2 * a^2 + a^3 : ℝ)⁻¹) *
        ∑ J ∈ 𝓙₅ t u₁ u₂, volume (ball (c J) (8 * D ^ s J)) * P7_5_4 t u₁ u₂ f₁ f₂ J := by
      rw [Finset.mul_sum]; congr! 1 with J mJ; ring
    _ ≤ C2_0_5 a * C7_5_4 a *
        (2 ^ ((𝕔 / 4) * a ^ 3 + 7) * 2 ^ (-(Z * n : ℝ) / (4 * a ^ 2 + 2 * a ^ 3))) *
        ∑ J ∈ 𝓙₅ t u₁ u₂,
          2 ^ (6 * a) * volume (ball (c J) (8⁻¹ * D ^ s J)) * P7_5_4 t u₁ u₂ f₁ f₂ J := by
      gcongr with J mJ
      · exact C7_5_11_binomial_bound (four_le_a X)
      · convert measure_ball_two_le_same_iterate (μ := volume) (c J) (8⁻¹ * D ^ s J) 6 using 2
        · rw [← mul_assoc, show (2 : ℝ) ^ 6 * 8⁻¹ = 8 by norm_num]
        · unfold defaultA; norm_cast; rw [← pow_mul, mul_comm]
    _ = C2_0_5 a * C7_5_4 a * 2 ^ ((𝕔 / 4) * a ^ 3 + 7 + 6 * a) *
        2 ^ (-(Z * n : ℝ) / (4 * a ^ 2 + 2 * a ^ 3)) *
        ∑ J ∈ 𝓙₅ t u₁ u₂, ∫⁻ x in ball (c J) (8⁻¹ * D ^ s J), P7_5_4 t u₁ u₂ f₁ f₂ J := by
      simp_rw [mul_assoc (_ ^ (6 * a)), ← Finset.mul_sum, ← mul_assoc]; congr 1
      · ring
      · congr! with J mJ; rw [setLIntegral_const, mul_comm]
    _ ≤ C7_4_5 a n * ∑ J ∈ 𝓙₅ t u₁ u₂, ∫⁻ x in ball (c J) (8⁻¹ * D ^ s J),
        adjointBoundaryOperator t u₁ f₁ x * adjointBoundaryOperator t u₂ f₂ x := by
      gcongr ?_ * ∑ _ ∈ _, ?_ with J mJ
      · rw [show (2 : ℝ≥0∞) = (2 : ℝ≥0) by rfl]
        simp_rw [← ENNReal.coe_rpow_of_ne_zero two_ne_zero, ← ENNReal.coe_pow, ← ENNReal.coe_mul,
          ENNReal.coe_le_coe]
        exact le_C7_4_5 (four_le_a X)
      · exact setLIntegral_mono' measurableSet_ball fun x mx ↦
          P7_5_4_le_adjointBoundaryOperator_mul mx
    _ ≤ C7_4_5 a n * ∑ J ∈ 𝓙₅ t u₁ u₂, ∫⁻ x in J,
        adjointBoundaryOperator t u₁ f₁ x * adjointBoundaryOperator t u₂ f₂ x := by
      gcongr with J mJ; refine (ball_subset_ball ?_).trans ball_subset_Grid
      change _ ≤ (D : ℝ) ^ s J / 4; rw [div_eq_inv_mul]; gcongr; norm_num
    _ = C7_4_5 a n * ∫⁻ x in 𝓘 u₁,
        adjointBoundaryOperator t u₁ f₁ x * adjointBoundaryOperator t u₂ f₂ x := by
      simp_rw [← union_𝓙₅ hu₁ hu₂ hu h2u, ← mem_toFinset]
      congr 1; refine (lintegral_biUnion_finset ?_ (fun _ _ ↦ coeGrid_measurable) _).symm
      rw [coe_toFinset]; exact pairwiseDisjoint_𝓙₅
    _ = C7_4_5 a n * ∫⁻ x,
        (𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₁ f₁) x *
        (𝓘 u₁ : Set X).indicator (adjointBoundaryOperator t u₂ f₂) x := by
      conv_rhs => enter [2, 2, x]; rw [← inter_indicator_mul _ _ x, inter_self]
      rw [lintegral_indicator coeGrid_measurable]
    _ ≤ _ := by
      rw [mul_assoc]; gcongr
      apply ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm inferInstance <;>
        refine AEMeasurable.indicator ?_ coeGrid_measurable
      · have af₁ := hf₁.aestronglyMeasurable
        refine (af₁.adjointCarlesonSum.enorm.add ?_).add af₁.enorm
        exact (AEStronglyMeasurable.maximalFunction 𝓑.to_countable).aemeasurable
      · have af₂ := hf₂.aestronglyMeasurable
        refine (af₂.adjointCarlesonSum.enorm.add ?_).add af₂.enorm
        exact (AEStronglyMeasurable.maximalFunction 𝓑.to_countable).aemeasurable

end TileStructure.Forest
