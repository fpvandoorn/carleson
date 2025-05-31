import Carleson.Calculations
import Carleson.ForestOperator.LargeSeparation.HolderCorrelationTile
import Carleson.ForestOperator.LargeSeparation.Defs
import Mathlib.Tactic.Rify

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

/-! ## Lemmas 7.5.6 to 7.5.10 -/

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
      apply calculation_8
      rw [mul_comm, calculation_6 a (s J), calculation_7 a (s J)]
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
        exact calculation_4 (lt_1 := lt_1) (lt_2 := lt_2) (lt_3 := lt_3) (lt_4 := lt_4)
          (three := three) (plusOne := plusOne) (X := X)
    _ ≤ 2 ^ ((-94 : ℝ) * a) * dist_{𝓘 p} (𝒬 u₁) (𝒬 u₂) := by
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
    _ ≤ 2 ^ ((-94 : ℝ) * a) * 2 ^ ((Z : ℝ) * n / 2) := by
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
    ∑ p ∈ {p | 𝔰 p = k ∧ ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))},
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
    (mp : 𝔰 p = k ∧ ¬Disjoint (ball (𝔠 p) (8 * ↑D ^ 𝔰 p)) (ball (c J) (8⁻¹ * ↑D ^ s J)))
    (nfm : AEMeasurable fun x ↦ ‖f x‖ₑ) :
    ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarleson p f x‖ₑ ≤
    2 ^ (103 * a ^ 3) * (volume (ball (c J) (16 * D ^ k)))⁻¹ * ∫⁻ x in E p, ‖f x‖ₑ :=
  calc
    _ ≤ ⨆ x ∈ ball (c J) (8⁻¹ * ↑D ^ s J),
        ∫⁻ y in E p, ‖conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x)) * f y‖ₑ :=
      iSup₂_mono fun x mx ↦ enorm_integral_le_lintegral_enorm _
    _ = ⨆ x ∈ ball (c J) (8⁻¹ * ↑D ^ s J), ∫⁻ y in E p, ‖Ks (𝔰 p) y x‖ₑ * ‖f y‖ₑ := by
      congr! with x mx y
      rw [enorm_mul, enorm_mul, enorm_eq_nnnorm, RCLike.nnnorm_conj]
      nth_rw 1 [← enorm_norm, norm_exp_I_mul_sub_ofReal, enorm_one, mul_one, ← enorm_eq_nnnorm]
    _ ≤ ⨆ x ∈ ball (c J) (8⁻¹ * ↑D ^ s J), ∫⁻ y in E p,
        C2_1_3 a / volume (ball y (D ^ 𝔰 p)) * ‖f y‖ₑ := by gcongr; exact enorm_Ks_le
    _ = ∫⁻ x in E p, C2_1_3 a / volume (ball x (D ^ 𝔰 p)) * ‖f x‖ₑ := by
      have := one_le_D (a := a)
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
            rw [Finset.mem_Icc, ← mp.1] at mk; rw [add_mul]; gcongr; exacts [one_le_D, mk.1]
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
      simp_rw [NNReal.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
      refine pow_le_pow_right' one_le_two ?_
      rw [show 103 * a ^ 3 = a * a * a + 102 * a ^ 3 by ring]; gcongr; nlinarith [four_le_a X]

/-- The constant used in `local_tree_control`.
Has value `2 ^ (104 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_7 (a : ℕ) : ℝ≥0 := 2 ^ (104 * (a : ℝ) ^ 3)

/-- Lemma 7.5.7. -/
lemma local_tree_control (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf : BoundedCompactSupport f) :
    ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum (t u₂ \ 𝔖₀ t u₁ u₂) f x‖ₑ ≤
    C7_5_7 a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x := by
  classical
  calc
    _ ≤ ∑ k ∈ Finset.Icc (s J) (s J + 3),
        ∑ p ∈ {p | 𝔰 p = k ∧ ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))},
          ⨆ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarleson p f x‖ₑ :=
      local_tree_control_sumsumsup hu₁ hu₂ hu h2u hJ
    _ ≤ ∑ k ∈ Finset.Icc (s J) (s J + 3),
        ∑ p ∈ {p | 𝔰 p = k ∧ ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))},
          2 ^ (103 * a ^ 3) * (volume (ball (c J) (16 * D ^ k)))⁻¹ * ∫⁻ x in E p, ‖f x‖ₑ := by
      gcongr with k mk p mp
      simp_rw [Finset.mem_filter, Finset.mem_univ, true_and] at mp
      exact local_tree_control_sup_bound mk mp hf.aestronglyMeasurable.enorm
    _ = 2 ^ (103 * a ^ 3) * ∑ k ∈ Finset.Icc (s J) (s J + 3),
        (volume (ball (c J) (16 * D ^ k)))⁻¹ *
          ∑ p ∈ {p | 𝔰 p = k ∧ ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))},
            ∫⁻ x in E p, ‖f x‖ₑ := by
      simp_rw [Finset.mul_sum, mul_assoc]
    _ = 2 ^ (103 * a ^ 3) * ∑ k ∈ Finset.Icc (s J) (s J + 3),
        (volume (ball (c J) (16 * D ^ k)))⁻¹ * ∫⁻ x in ⋃ p ∈ Finset.univ.filter (fun p ↦ 𝔰 p = k ∧
          ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8⁻¹ * D ^ s J))), E p, ‖f x‖₊ := by
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
    _ ≤ 2 ^ (103 * a ^ 3) * ∑ k ∈ Finset.Icc (s J) (s J + 3),
        (volume (ball (c J) (16 * D ^ k)))⁻¹ * ∫⁻ x in ball (c J) (16 * D ^ k), ‖f x‖ₑ := by
      gcongr with k mk; refine lintegral_mono_set (iUnion₂_subset fun p mp ↦ ?_)
      simp_rw [Finset.mem_filter, Finset.mem_univ, true_and] at mp
      refine (E_subset_𝓘.trans Grid_subset_ball).trans (ball_subset_ball' ?_)
      obtain ⟨y, my₁, my₂⟩ := not_disjoint_iff.mp mp.2
      rw [mem_ball] at my₁ my₂; change 4 * D ^ 𝔰 p + dist (𝔠 p) (c J) ≤ _
      calc
        _ ≤ 4 * D ^ 𝔰 p + (dist y (𝔠 p) + dist y (c J)) := by gcongr; exact dist_triangle_left ..
        _ ≤ 4 * D ^ 𝔰 p + 8 * D ^ 𝔰 p + 8⁻¹ * D ^ s J := by rw [add_assoc]; gcongr
        _ ≤ (4 + 8 + 8⁻¹) * D ^ k := by
          rw [Finset.mem_Icc] at mk; simp_rw [add_mul, mp.1]; gcongr; exacts [one_le_D, mk.1]
        _ ≤ _ := by gcongr; norm_num
    _ = 2 ^ (103 * a ^ 3) *
        ∑ k ∈ Finset.Icc (s J) (s J + 3), ⨍⁻ x in ball (c J) (16 * D ^ k), ‖f x‖ₑ ∂volume := by
      simp_rw [setLAverage_eq, ENNReal.div_eq_inv_mul]
    _ ≤ 2 ^ (103 * a ^ 3) *
        ∑ k ∈ Finset.Icc (s J) (s J + 3), ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x := by
      gcongr with k mk; rw [Finset.mem_Icc] at mk
      apply laverage_le_biInf_MB
      · gcongr; exacts [by norm_num, one_le_D, mk.1]
      · use ⟨4, (k - s J).toNat, J⟩
        simp only [𝓑, c𝓑, r𝓑, mem_prod, mem_Iic, mem_univ, le_add_iff_nonneg_left, zero_le,
          and_true, true_and]
        rw [show s J + (k - s J).toNat = k by omega, Int.toNat_le, Nat.cast_add, Nat.cast_mul,
          Nat.cast_ofNat]
        exact ⟨by omega, by norm_num⟩
    _ = 2 ^ (103 * a ^ 3) * 2 ^ 2 * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x := by
      rw [Finset.sum_const, Int.card_Icc, show s J + 3 + 1 - s J = 4 by omega, nsmul_eq_mul,
        show (Int.toNat 4 : ℝ≥0∞) = 2 ^ 2 by simp; norm_num, mul_assoc]
    _ ≤ _ := by
      gcongr; rw [C7_5_7, ← pow_add]; norm_cast
      refine pow_le_pow_right' one_le_two ?_
      rw [show 104 * a ^ 3 = 103 * a ^ 3 + a * a * a by ring]; gcongr; nlinarith [four_le_a X]

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

lemma volume_cpDsp_bound {J : Grid X}
    (hd : ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J))) (hs : s J ≤ 𝔰 p) :
    volume (ball (c J) (32 * D ^ 𝔰 p)) / 2 ^ (4 * a) ≤ volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) := by
  apply ENNReal.div_le_of_le_mul'
  have h : dist (𝔠 p) (c J) + 32 * D ^ 𝔰 p ≤ 16 * (4 * D ^ 𝔰 p) := by
    calc
      _ ≤ 8 * (D : ℝ) ^ 𝔰 p + 8 * D ^ s J + 32 * ↑D ^ 𝔰 p := by
        gcongr; exact (dist_lt_of_not_disjoint_ball hd).le
      _ ≤ 8 * (D : ℝ) ^ 𝔰 p + 8 * D ^ 𝔰 p + 32 * ↑D ^ 𝔰 p := by
        gcongr; exact one_le_D
      _ ≤ _ := by rw [← add_mul, ← add_mul, ← mul_assoc]; gcongr; norm_num
  convert measure_ball_le_of_dist_le' (μ := volume) (by norm_num) h
  unfold As defaultA; norm_cast; rw [← pow_mul']; congr 2
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num, Nat.clog_pow _ _ one_lt_two]

open scoped Classical in
lemma gtc_integral_bound {k : ℤ} {ℭ : Set (𝔓 X)}
    (hs : ∀ p ∈ ℭ, ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J)) → s J ≤ 𝔰 p) :
    ∑ p ∈ ℭ with ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J)) ∧ 𝔰 p = k,
      ∫⁻ x in E p, ‖f x‖ₑ ≤
    ∫⁻ x in ball (c J) (32 * D ^ k), ‖f x‖ₑ := by
  set V := ℭ.toFinset.filter
      (fun p ↦ ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J)) ∧ 𝔰 p = k)
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
        _ ≤ (4 : ℝ) * D ^ 𝔰 p + 8 * D ^ 𝔰 p + 8 * D ^ s J := by
          rw [add_assoc]; gcongr; exact (dist_lt_of_not_disjoint_ball mp.2.1).le
        _ ≤ (4 : ℝ) * D ^ 𝔰 p + 8 * D ^ 𝔰 p + 8 * D ^ 𝔰 p := by gcongr; exact one_le_D
        _ ≤ _ := by rw [← add_mul, ← add_mul]; gcongr; norm_num

/-- Part 1 of equation (7.5.18) of Lemma 7.5.9. -/
lemma global_tree_control1_edist_part1
    (hu : u ∈ t) {ℭ : Set (𝔓 X)} (hℭ : ℭ ⊆ t u) (hf : BoundedCompactSupport f)
    (hs : ∀ p ∈ ℭ, ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J)) → s J ≤ 𝔰 p)
    (hx : x ∈ ball (c J) (8 * D ^ s J)) (hx' : x' ∈ ball (c J) (8 * D ^ s J)) :
    edist (exp (.I * 𝒬 u x) * adjointCarlesonSum ℭ f x)
      (exp (.I * 𝒬 u x') * adjointCarlesonSum ℭ f x') ≤
    C7_5_5 a * 2 ^ (4 * a) * edist x x' ^ (a : ℝ)⁻¹ * ∑ k ∈ Finset.Icc (s J) S,
        D ^ (-k / (a : ℝ)) * ⨍⁻ x in ball (c J) (32 * D ^ k), ‖f x‖ₑ ∂volume := by
  classical calc
    _ ≤ ∑ p ∈ ℭ, edist (exp (.I * 𝒬 u x) * adjointCarleson p f x)
        (exp (.I * 𝒬 u x') * adjointCarleson p f x') := by
      simp_rw [adjointCarlesonSum, Finset.mul_sum, toFinset_ofFinset]
      exact ENNReal.edist_sum_le_sum_edist
    _ = ∑ p ∈ ℭ with ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J)),
        edist (exp (.I * 𝒬 u x) * adjointCarleson p f x)
          (exp (.I * 𝒬 u x') * adjointCarleson p f x') := by
      refine (Finset.sum_filter_of_ne fun p mp hp ↦ ?_).symm; contrapose! hp
      replace hp : Disjoint (ball (𝔠 p) (5 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J)) :=
        hp.mono_left (ball_subset_ball (by gcongr; norm_num))
      rw [adjoint_tile_support1, indicator_of_not_mem (disjoint_right.mp hp hx), mul_zero,
        indicator_of_not_mem (disjoint_right.mp hp hx'), mul_zero, edist_self]
    _ ≤ ∑ p ∈ ℭ with ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J)),
        C7_5_5 a / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) *
          (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ * ∫⁻ x in E p, ‖f x‖ₑ := by
      gcongr with p mp; rw [Finset.mem_filter, mem_toFinset] at mp
      exact holder_correlation_tile hu (hℭ mp.1) hf
    _ = C7_5_5 a * edist x x' ^ (a : ℝ)⁻¹ *
        ∑ p ∈ ℭ with ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J)),
          D ^ (-𝔰 p / (a : ℝ)) / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) * ∫⁻ x in E p, ‖f x‖ₑ := by
      rw [Finset.mul_sum]; congr! 1 with p mp
      rw [← mul_assoc, ← mul_div_assoc, mul_assoc _ _ ((D : ℝ≥0∞) ^ _), mul_comm _ (_ * _),
        mul_div_assoc, mul_comm (_ ^ _ * _)]; congr
      rw [div_eq_mul_inv, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
        ← ENNReal.zpow_neg (by simp) (by simp), ← ENNReal.rpow_intCast, ← ENNReal.rpow_mul,
        ← div_eq_mul_inv, Int.cast_neg]
    _ = C7_5_5 a * edist x x' ^ (a : ℝ)⁻¹ * ∑ k ∈ Finset.Icc (s J) S,
        ∑ p ∈ ℭ with ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J)) ∧ 𝔰 p = k,
          D ^ (-𝔰 p / (a : ℝ)) / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) * ∫⁻ x in E p, ‖f x‖ₑ := by
      congr 1; simp_rw [← Finset.filter_filter]
      refine (Finset.sum_fiberwise_of_maps_to (fun p mp ↦ ?_) _).symm
      rw [Finset.mem_Icc]; rw [Finset.mem_filter, mem_toFinset] at mp
      exact ⟨hs p mp.1 mp.2, scale_mem_Icc.2⟩
    _ = C7_5_5 a * edist x x' ^ (a : ℝ)⁻¹ * ∑ k ∈ Finset.Icc (s J) S, D ^ (-k / (a : ℝ)) *
        ∑ p ∈ ℭ with ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J)) ∧ 𝔰 p = k,
          (∫⁻ x in E p, ‖f x‖ₑ) / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) := by
      congr! 2 with k mk; rw [Finset.mul_sum]; congr! 1 with p mp
      rw [mul_comm, ← mul_div_assoc, ← mul_div_assoc, mul_comm]; congr
      rw [Finset.mem_filter] at mp; exact mp.2.2
    _ ≤ C7_5_5 a * edist x x' ^ (a : ℝ)⁻¹ * ∑ k ∈ Finset.Icc (s J) S, D ^ (-k / (a : ℝ)) *
        ∑ p ∈ ℭ with ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J)) ∧ 𝔰 p = k,
          (∫⁻ x in E p, ‖f x‖ₑ) / (volume (ball (c J) (32 * D ^ k)) / 2 ^ (4 * a)) := by
      gcongr with k mk p mp; rw [Finset.mem_filter, mem_toFinset] at mp
      rw [← mp.2.2]; exact volume_cpDsp_bound mp.2.1 (hs p mp.1 mp.2.1)
    _ = C7_5_5 a * 2 ^ (4 * a) * edist x x' ^ (a : ℝ)⁻¹ * ∑ k ∈ Finset.Icc (s J) S,
        D ^ (-k / (a : ℝ)) * (volume (ball (c J) (32 * D ^ k)))⁻¹ *
        ∑ p ∈ ℭ with ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J)) ∧ 𝔰 p = k,
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
      rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, sq, mul_assoc, mul_self_mul_inv]
      norm_cast; linarith [four_le_a X]
    _ = ∑ k ∈ Finset.Icc 0 (S - s J).toNat, 2 ^ (-k : ℤ) := by
      have : s J ≤ S := scale_mem_Icc.2
      apply Finset.sum_nbij' (fun (k : ℤ) ↦ (k - s J).toNat) (· + s J) <;> intro k hk
      pick_goal -1
      · rw [Finset.mem_Icc] at hk
        rw [Int.toNat_of_nonneg (by omega), neg_sub]
      all_goals simp at hk ⊢; try omega
    _ ≤ ∑' k : ℕ, 2 ^ (-k : ℤ) := ENNReal.sum_le_tsum _
    _ = _ := ENNReal.sum_geometric_two_pow_neg_one

/-- The constant used in `global_tree_control1_edist`. -/
irreducible_def C7_5_9d (a : ℕ) : ℝ≥0 := C7_5_5 a * 2 ^ (4 * a + 1)

/-- Part 2 of equation (7.5.18) of Lemma 7.5.9. -/
lemma global_tree_control1_edist_part2
    (hu : u ∈ t) {ℭ : Set (𝔓 X)} (hℭ : ℭ ⊆ t u) (hf : BoundedCompactSupport f)
    (hs : ∀ p ∈ ℭ, ¬Disjoint (ball (𝔠 p) (8 * D ^ 𝔰 p)) (ball (c J) (8 * D ^ s J)) → s J ≤ 𝔰 p)
    (hx : x ∈ ball (c J) (8 * D ^ s J)) (hx' : x' ∈ ball (c J) (8 * D ^ s J)) :
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
      · gcongr; exacts [by norm_num, one_le_D, mk.1]
      · use ⟨5, (k - s J).toNat, J⟩
        simp only [𝓑, c𝓑, r𝓑, mem_prod, mem_Iic, mem_univ, le_add_iff_nonneg_left, zero_le,
          and_true, true_and]
        rw [show s J + (k - s J).toNat = k by omega, Int.toNat_le, Nat.cast_add, Nat.cast_mul,
          Nat.cast_ofNat]
        have : -S ≤ s J := scale_mem_Icc.1
        exact ⟨by omega, by norm_num⟩
    _ = C7_5_5 a * 2 ^ (4 * a) * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ *
        (∑ k ∈ Finset.Icc (s J) S, (D : ℝ≥0∞) ^ ((s J - k) / (a : ℝ))) *
        ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x := by
      have fla := four_le_a X
      have dpos : 0 < (D : ℝ≥0∞) ^ s J := by apply ENNReal.zpow_pos (by simp) (by simp)
      have dlt : (D : ℝ≥0∞) ^ s J < ⊤ := by apply ENNReal.zpow_lt_top (by simp) (by simp)
      have bpos : ((D : ℝ≥0∞) ^ s J) ^ (a : ℝ)⁻¹ ≠ 0 := (ENNReal.rpow_pos dpos dlt.ne).ne'
      have bnt : ((D : ℝ≥0∞) ^ s J) ^ (a : ℝ)⁻¹ ≠ ⊤ := by
        exact ENNReal.rpow_ne_top_of_nonneg (by positivity) dlt.ne
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
    (hx : x ∈ ball (c J) (8 * D ^ s J)) (hx' : x' ∈ ball (c J) (8 * D ^ s J)) :
    edist (exp (.I * 𝒬 u₁ x) * adjointCarlesonSum (t u₁) f x)
      (exp (.I * 𝒬 u₁ x') * adjointCarlesonSum (t u₁) f x') ≤
    C7_5_9d a * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x :=
  global_tree_control1_edist_part2 hu₁ subset_rfl hf
    (fun _ mp dp ↦ scales_impacting_interval hu₁ hu₂ hu h2u hJ (mem_union_left _ mp) dp) hx hx'

/-- Equation (7.5.18) of Lemma 7.5.9 for `ℭ = t u₂ ∩ 𝔖₀ t u₁ u₂`. -/
lemma global_tree_control1_edist_right (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf : BoundedCompactSupport f)
    (hx : x ∈ ball (c J) (8 * D ^ s J)) (hx' : x' ∈ ball (c J) (8 * D ^ s J)) :
    edist (exp (.I * 𝒬 u₂ x) * adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f x)
      (exp (.I * 𝒬 u₂ x') * adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f x') ≤
    C7_5_9d a * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x :=
  global_tree_control1_edist_part2 hu₂ inter_subset_left hf
    (fun _ mp dp ↦ scales_impacting_interval hu₁ hu₂ hu h2u hJ (mem_union_right _ mp) dp) hx hx'

/-- The constant used in `global_tree_control1_supbound`. -/
irreducible_def C7_5_9s (a : ℕ) : ℝ≥0 := C7_5_5 a * 2 ^ (4 * a + 2)

lemma one_le_C7_5_9s : 1 ≤ C7_5_9s a := by
  simp only [C7_5_9s, C7_5_5]; norm_cast
  rw [← pow_add]; exact Nat.one_le_two_pow

lemma C7_5_9d_le_C7_5_9s : C7_5_9d a ≤ C7_5_9s a := by
  simp only [C7_5_9d, C7_5_9s]
  exact mul_le_mul_left' (pow_le_pow_right' one_le_two (add_le_add_left one_le_two _)) _

/-- Equation (7.5.17) of Lemma 7.5.9. -/
lemma global_tree_control1_supbound (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (ℭ : Set (𝔓 X)) (hℭ : ℭ = t u₁ ∨ ℭ = t u₂ ∩ 𝔖₀ t u₁ u₂)
    (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf : BoundedCompactSupport f) :
    ⨆ x ∈ ball (c J) (8 * D ^ s J), ‖adjointCarlesonSum ℭ f x‖ₑ ≤
    (⨅ x ∈ ball (c J) (8⁻¹ * D ^ s J), ‖adjointCarlesonSum ℭ f x‖ₑ) +
    C7_5_9s a * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x := by
  rw [← tsub_le_iff_left]; refine ENNReal.le_of_forall_pos_le_add fun ε εpos blt ↦ ?_
  obtain ⟨x, hx, ex⟩ : ∃ x₀ ∈ ball (c J) (8 * D ^ s J),
      ⨆ x ∈ ball (c J) (8 * D ^ s J), ‖adjointCarlesonSum ℭ f x‖ₑ ≤
      ‖adjointCarlesonSum ℭ f x₀‖ₑ + (ε / 2 : ℝ≥0) := by
    apply ENNReal.exists_biSup_le_enorm_add_eps (by positivity)
      ⟨c J, mem_ball_self (by unfold defaultD; positivity)⟩
    rw [isBounded_image_iff_bddAbove_norm]
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
        (ε / 2 : ℝ≥0) := add_le_add_right add_tsub_le_assoc _
    _ = ‖‖adjointCarlesonSum ℭ f x‖ₑ - ‖adjointCarlesonSum ℭ f x'‖ₑ‖ₑ + ε := by
      rw [add_rotate, add_assoc]; simp
    _ ≤ (C7_5_9d a * (edist x x' / D ^ s J) ^ (a : ℝ)⁻¹ * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x) + ε := by
      refine add_le_add_right ?_ _
      replace hx' : x' ∈ ball (c J) (8 * D ^ s J) := by
        exact (ball_subset_ball (by gcongr; norm_num)) hx'
      rcases hℭ with rfl | rfl
      · nth_rw 2 [← one_mul ‖_‖ₑ]; rw [← enorm_exp_I_mul_ofReal (𝒬 u₁ x), ← enorm_mul]
        nth_rw 3 [← one_mul ‖_‖ₑ]; rw [← enorm_exp_I_mul_ofReal (𝒬 u₁ x'), ← enorm_mul]
        exact ENNReal.enorm_enorm_sub_enorm_le.trans
          (global_tree_control1_edist_left hu₁ hu₂ hu h2u hJ hf hx hx')
      · nth_rw 2 [← one_mul ‖_‖ₑ]; rw [← enorm_exp_I_mul_ofReal (𝒬 u₂ x), ← enorm_mul]
        nth_rw 3 [← one_mul ‖_‖ₑ]; rw [← enorm_exp_I_mul_ofReal (𝒬 u₂ x'), ← enorm_mul]
        exact ENNReal.enorm_enorm_sub_enorm_le.trans
          (global_tree_control1_edist_right hu₁ hu₂ hu h2u hJ hf hx hx')
    _ ≤ (C7_5_9d a * 2 * ⨅ x ∈ J, MB volume 𝓑 c𝓑 r𝓑 f x) + ε := by
      gcongr; rw [mem_ball] at hx hx'; rw [edist_dist]
      calc
        _ ≤ (ENNReal.ofReal ((8 + 8⁻¹) * D ^ s J) / ↑D ^ s J) ^ (a : ℝ)⁻¹ := by
          gcongr; rw [add_mul]; exact ((dist_triangle_right ..).trans_lt (add_lt_add hx hx')).le
        _ ≤ 16 ^ (a : ℝ)⁻¹ := by
          have Dpos : 0 < (D : ℝ≥0∞) ^ s J := ENNReal.zpow_pos (by simp) (by simp) _
          have Dlt : (D : ℝ≥0∞) ^ s J < ⊤ := ENNReal.zpow_lt_top (by simp) (by simp) _
          rw [ENNReal.ofReal_mul (by norm_num), ← Real.rpow_intCast,
            ← ENNReal.ofReal_rpow_of_pos (by unfold defaultD; positivity),
            show ENNReal.ofReal D = D by norm_cast, ENNReal.rpow_intCast,
            ENNReal.mul_div_cancel_right Dpos.ne' Dlt.ne]
          exact ENNReal.rpow_le_rpow (by norm_num) (by positivity)
        _ ≤ 16 ^ (4 : ℝ)⁻¹ := by
          gcongr; exacts [by norm_num, by norm_cast; linarith [four_le_a X]]
        _ = _ := by
          rw [show (16 : ℝ≥0∞) = 2 ^ (4 : ℝ) by norm_num, ← ENNReal.rpow_mul,
            show (4 : ℝ) * 4⁻¹ = 1 by norm_num, ENNReal.rpow_one]
    _ = _ := by
      congr; rw [C7_5_9d, C7_5_9s, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat, mul_assoc,
        ← pow_succ, add_assoc]; rfl

/-- The constant used in `global_tree_control2`. -/
irreducible_def C7_5_10 (a : ℕ) : ℝ≥0 := C7_5_7 a + C7_5_9s a

lemma C7_5_9s_le_C7_5_10 : C7_5_9s a ≤ C7_5_10 a := by
  simp only [C7_5_10, C7_5_9s]; exact le_add_self

lemma one_le_C7_5_10 : 1 ≤ C7_5_10 a := one_le_C7_5_9s.trans C7_5_9s_le_C7_5_10

/-- Lemma 7.5.10 -/
lemma global_tree_control2 (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hJ : J ∈ 𝓙₅ t u₁ u₂) (hf : BoundedCompactSupport f) :
    ⨆ x ∈ ball (c J) (8 * D ^ s J), ‖adjointCarlesonSum (t u₂ ∩ 𝔖₀ t u₁ u₂) f x‖ₑ ≤
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
    _ ≤ _ := by
      rw [C7_5_10, ENNReal.coe_add, add_mul, add_assoc]
      gcongr; exact local_tree_control hu₁ hu₂ hu h2u hJ hf

end TileStructure.Forest
