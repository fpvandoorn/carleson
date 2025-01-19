import Carleson.ForestOperator.PointwiseEstimate
import Carleson.ToMathlib.Misc

open ShortVariables TileStructure
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
  {n j j' : ℕ} {t : Forest X n} {u u₁ u₂ p : 𝔓 X} {x x' : X} {𝔖 : Set (𝔓 X)}
  {f f₁ f₂ g g₁ g₂ : X → ℂ} {I J J' L : Grid X}
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

noncomputable section

open Set MeasureTheory Metric Function Complex Bornology TileStructure Classical Filter
open scoped NNReal ENNReal ComplexConjugate

lemma CMB_defaultA_two_eq {a : ℕ} : CMB (defaultA a) 2 = 2 ^ (a + (3 / 2 : ℝ)) := by
  suffices (2 : ℝ≥0) * 2 ^ (2 : ℝ)⁻¹ * (ENNReal.ofReal |2 - 1|⁻¹).toNNReal ^ (2 : ℝ)⁻¹ *
      ((2 ^ a) ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ = 2 ^ (a + 3 / (2 : ℝ)) by
    simpa [CMB, C_realInterpolation, C_realInterpolation_ENNReal]
  rw [← NNReal.rpow_mul, show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by norm_num]
  repeat rw [NNReal.rpow_add two_ne_zero]
  norm_num
  ring

namespace TileStructure.Forest

lemma eLpNorm_MB_le {𝕜 : Type*} [RCLike 𝕜] {f : X → 𝕜} (hf : BoundedCompactSupport f) :
    eLpNorm (MB volume 𝓑 c𝓑 r𝓑 f ·) 2 volume ≤ (CMB (defaultA a) 2) * eLpNorm f 2 volume := by
  have : HasStrongType (fun (u : X → 𝕜) ↦ (MB volume 𝓑 c𝓑 r𝓑 u · |>.toReal)) 2 2 _ _ _ :=
    hasStrongType_MB_finite 𝓑_finite one_lt_two
  convert this f (hf.memℒp 2) |>.2 using 1
  congr
  ext
  rw [ENNReal.nnorm_toReal]
  refine ENNReal.coe_toNNReal (ne_of_lt ?_) |>.symm
  exact lt_of_le_of_lt MB_le_eLpNormEssSup (hf.memℒp ⊤).2

/-! ## Section 7.2 and Lemma 7.2.1 -/

/-- The constant used in `nontangential_operator_bound`.
Has value `2 ^ (103 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_2_2 (a : ℕ) : ℝ≥0 := 2 ^ (103 * (a : ℝ) ^ 3)

omit [TileStructure Q D κ S o] in
lemma _root_.integrableOn_K_mul_f (hf : BoundedCompactSupport f) (r : ℝ) (hr : r > 0) :
    IntegrableOn (fun y ↦ K x' y * f y) {y | dist x' y ∈ Ici r} volume := by
  by_cases supp_f : (support f).Nonempty; swap
  · simp [Function.support_eq_empty_iff.mp <| Set.not_nonempty_iff_eq_empty.mp supp_f]
  have ⟨x'', hx''⟩ := supp_f
  have ⟨C, hC⟩ := Metric.isBounded_iff.mp hf.isBoundedSupport
  specialize hC hx''
  have : support (fun y ↦ f y * K x' y) ⊆ closedBall x' (dist x' x'' + C) := by
    intro y hy
    rw [mem_closedBall']
    have : y ∈ support f := by contrapose! hy; simp [hy]
    exact (dist_triangle x' x'' y).trans <| add_le_add_left (hC this) _
  simp_rw [mul_comm (K x' _)]
  unfold IntegrableOn
  rw [← integrableOn_iff_integrable_of_support_subset this]
  unfold IntegrableOn
  rw [Measure.restrict_restrict]
  · apply hf.integrable_mul
    have := integrableOn_K_Icc (K := K) x' r (dist x' x'' + C) hr
    unfold IntegrableOn at this
    convert this using 2
    ext y
    simp [inter_comm (closedBall _ _), dist_comm y]
  · exact measurableSet_closedBall

omit [TileStructure Q D κ S o] in
lemma _root_.integrableOn_K_mul_f_ennreal (hf : BoundedCompactSupport f) (r : ℝ≥0∞) (hr₀ : r > 0)
    (hr₁ : r ≠ ⊤) : IntegrableOn (fun y ↦ K x' y * f y)
    {y | ENNReal.ofReal (dist x' y) ∈ Ici r} volume := by
  convert integrableOn_K_mul_f hf (ENNReal.toReal r) <| ENNReal.toReal_pos hr₀.ne.symm hr₁
  exact ENNReal.le_ofReal_iff_toReal_le hr₁ dist_nonneg

private def annulus_oo (x : X) (R₁ R₂ : ℝ≥0∞) := {y | ENNReal.ofReal (dist x y) ∈ Ioo R₁ R₂}
--private def annulus_oc (x : X) (R₁ R₂ : ℝ≥0∞) := {y | ENNReal.ofReal (dist x y) ∈ Ioc R₁ R₂}

private lemma annulus_oo_eq_of_lt_top (x : X) {r R : ℝ≥0∞} (hr : r < ⊤) (hR : R < ⊤) :
    annulus_oo x r R = ball x (ENNReal.toReal R) ∩ (closedBall x (ENNReal.toReal r))ᶜ := by
  ext y
  simp [annulus_oo, dist_comm, and_comm, ENNReal.lt_ofReal_iff_toReal_lt hr.ne (b := dist x y),
    ENNReal.ofReal_lt_iff_lt_toReal dist_nonneg hR.ne]

private lemma annulus_oo_eq_of_top (x : X) {r : ℝ≥0∞} (hr : r < ⊤) :
    annulus_oo x r ⊤ = (closedBall x (ENNReal.toReal r))ᶜ := by
  ext y
  simpa [annulus_oo, dist_comm] using ENNReal.lt_ofReal_iff_toReal_lt hr.ne

private lemma annulus_oo_empty (x : X) (R : ℝ≥0∞) : annulus_oo x ⊤ R = ∅ := by simp [annulus_oo]

omit [TileStructure Q D κ S o] in
private lemma measurableSet_annulus_oo (x : X) (r R : ℝ≥0∞) : MeasurableSet (annulus_oo x r R) := by
  by_cases hr : r = ⊤
  · simp [hr, annulus_oo_empty x R]
  replace hr : r < ⊤ := Ne.lt_top' fun h ↦ hr h.symm
  by_cases hR : R = ⊤
  · simp [hR, annulus_oo_eq_of_top x hr, measurableSet_closedBall]
  rw [annulus_oo_eq_of_lt_top x hr (Ne.lt_top' fun h ↦ hR h.symm)]
  measurability

-- Bound for (7.2.3) in the proof of `nontangential_pointwise_bound`
private lemma nontangential_integral_bound₁ (hf : BoundedCompactSupport f) (θ : Θ X) (x x' : X)
    (I : Grid X) (hx : x ∈ I) (hx' : x' ∈ I) (s₂ : ℤ) (hs : s I ≤ s₂)
    (hs₂ : (D : ℝ≥0∞) ^ (s₂ - 1) ≤ upperRadius Q θ x') :
    ‖∫ y in {y | ENNReal.ofReal (dist x' y) ∈ Ioc (8 * (D : ℝ≥0∞) ^ s I) (D ^ (s₂ - 1) / 4)},
      K x' y * f y‖ₑ ≤ 2 * linearizedNontangentialOperator Q θ K f x := by
    by_cases R₁_le_R₂ : 8 * (D : ℝ≥0∞) ^ (s I) ≤ (D : ℝ≥0∞) ^ (s₂ - 1) / 4; swap
    · simp [-defaultD, Set.Ioc_eq_empty (fun h ↦ R₁_le_R₂ h.le)]
    have int_Kf : IntegrableOn (fun y ↦ K x' y * f y)
        {y | ENNReal.ofReal (dist x' y) ∈ Ici (8 * (D : ℝ≥0∞) ^ s I)} volume := by
      apply integrableOn_K_mul_f_ennreal hf (8 * (D : ℝ≥0∞) ^ s I)
      · apply ENNReal.mul_pos (by norm_num)
        refine (ENNReal.zpow_pos (by norm_num) (ENNReal.natCast_ne_top D) (s I)).ne.symm
      · apply ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        exact (ENNReal.zpow_lt_top (by norm_num) (ENNReal.natCast_ne_top D) (s I)).ne
    have D0 : (D : ℝ≥0∞) ≠ 0 := by norm_num
    have R₂_lt_upperRadius : (D : ℝ≥0∞) ^ (s₂ - 1) / 4 < upperRadius Q θ x' := by
      refine lt_of_lt_of_le (ENNReal.div_lt_of_lt_mul' ?_) hs₂
      nth_rewrite 1 [← one_mul ((D : ℝ≥0∞) ^ _), mul_comm 1, mul_comm 4]
      have : (D : ℝ≥0∞) ^ (s₂ - 1) > 0 := ENNReal.zpow_pos D0 (ENNReal.natCast_ne_top D) (s₂ - 1)
      apply ENNReal.mul_left_strictMono this.ne.symm ?_ (by norm_num)
      exact (ENNReal.zpow_lt_top D0 (ENNReal.natCast_ne_top D) _).ne
    have dist_le : dist x x' ≤ 8 * (D : ℝ) ^ s I := by
      apply le_trans (dist_triangle x (c I) x')
      have h1 := mem_ball.mp (Grid_subset_ball hx)
      have h2 := mem_ball'.mp (Grid_subset_ball hx')
      convert (add_lt_add h1 h2).le using 1
      unfold s
      ring
    calc
      _ = ‖(∫ y in annulus_oo x' (8 * D ^ s I) (upperRadius Q θ x'), K x' y * f y) -
            ∫ y in annulus_oo x' (D ^ (s₂ - 1) / 4) (upperRadius Q θ x'), K x' y * f y‖ₑ := by
        congr
        apply eq_sub_of_add_eq
        rw [← setIntegral_union]
        · congr
          ext y
          rw [annulus_oo, annulus_oo, mem_union, mem_setOf_eq, mem_setOf_eq, mem_setOf_eq]
          rw [← mem_union, Set.Ioc_union_Ioo_eq_Ioo R₁_le_R₂ R₂_lt_upperRadius]
        · rw [Set.disjoint_iff]
          intro y ⟨⟨_, hy₁⟩, ⟨hy₂, _⟩⟩
          exact (lt_self_iff_false _).mp (lt_of_lt_of_le hy₂ hy₁)
        · apply measurableSet_annulus_oo
        · apply int_Kf.mono_set
          intro y hy
          simp only [mem_Ioc, mem_setOf_eq, mem_Ici] at hy ⊢
          exact hy.1.le
        · apply int_Kf.mono_set
          intro y hy
          simp only [mem_Ioo, mem_setOf_eq, mem_Ici] at hy ⊢
          exact R₁_le_R₂.trans hy.1.le
      _ ≤ ‖∫ y in annulus_oo x' (8 * D ^ s I) (upperRadius Q θ x'), K x' y * f y‖ₑ +
            ‖∫ y in annulus_oo x' (D ^ (s₂ - 1) / 4) (upperRadius Q θ x'), K x' y * f y‖ₑ := by
        rw [enorm_eq_nnnorm, enorm_eq_nnnorm, enorm_eq_nnnorm, ← ENNReal.coe_add]
        exact ENNReal.coe_mono (nnnorm_sub_le _ _)
      _ ≤ 2 * linearizedNontangentialOperator Q θ K f x := by
        rw [two_mul, annulus_oo, annulus_oo]
        unfold linearizedNontangentialOperator
        gcongr
        · refine le_trans ?_ <| le_iSup _ (8 * (D : ℝ) ^ s I)
          refine le_trans ?_ <| le_iSup _ x'
          simp only [dist_le, iSup_pos, enorm_eq_nnnorm]
          suffices ENNReal.ofReal (8 * ↑D ^ s I) = 8 * (D : ℝ≥0∞) ^ s I by rw [this]
          rw [ENNReal.ofReal_mul (by norm_num)]
          rw [← ENNReal.ofReal_natCast D, ENNReal.ofReal_zpow (defaultD_pos a) (s I)]
          norm_num
        ·
          refine le_trans ?_ <| le_iSup _ (8 * (D : ℝ) ^ s I)
          sorry

-- Pointwise bound needed for Lemma 7.2.2
private lemma nontangential_pointwise_bound (hf : BoundedCompactSupport f) (θ : Θ X) (x : X) :
    nontangentialMaximalFunction θ f x ≤ nontangentialOperator K f x +
      2 ^ (102 * (a : ℝ) ^ 3) * MB volume 𝓑 c𝓑 r𝓑 f x := by

  sorry
#exit
/-- Lemma 7.2.2. -/
lemma nontangential_operator_bound
    (hf : BoundedCompactSupport f)
    (θ : Θ X) :
    eLpNorm (nontangentialMaximalFunction θ f ·) 2 volume ≤ (C7_2_2 a) * eLpNorm f 2 volume := by
  have ha : 4 ≤ (a : ℝ) := by exact_mod_cast four_le_a X
  have aemeas_MB : AEMeasurable (MB volume 𝓑 c𝓑 r𝓑 f ·) :=
    (AEStronglyMeasurable.maximalFunction (to_countable 𝓑)).aemeasurable
  have ⟨hT₁, hT₂⟩ := hasBoundedStrongType_Tstar f (hf.memℒp 2) hf.memℒp_top.eLpNorm_lt_top
    hf.isBoundedSupport.measure_lt_top
  calc eLpNorm (nontangentialMaximalFunction θ f) 2 volume
    _ ≤ eLpNorm (fun x ↦ nontangentialOperator K f x +
          2 ^ (102 * (a : ℝ) ^ 3) * MB volume 𝓑 c𝓑 r𝓑 f x) 2 volume := by
      simp only [eLpNorm, OfNat.ofNat_ne_zero, reduceIte, ENNReal.ofNat_ne_top, eLpNorm']
      gcongr
      exact nontangential_pointwise_bound hf θ _
    _ ≤ eLpNorm (nontangentialOperator K f) 2 volume +
          eLpNorm ((2 : ℝ≥0∞) ^ (102 * (a : ℝ) ^ 3) * MB volume 𝓑 c𝓑 r𝓑 f ·) 2 volume := by
      simp only [eLpNorm, OfNat.ofNat_ne_zero, reduceIte, ENNReal.ofNat_ne_top, eLpNorm',
        enorm_eq_self, ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
      simpa using ENNReal.lintegral_Lp_add_le hT₁.aemeasurable (aemeas_MB.const_mul _) one_le_two
    _ = eLpNorm (nontangentialOperator K f) 2 volume +
          2 ^ (102 * (a : ℝ) ^ 3) * eLpNorm (MB volume 𝓑 c𝓑 r𝓑 f ·) 2 volume := by
      congr
      simp only [eLpNorm, eLpNorm', OfNat.ofNat_ne_zero, reduceIte, ENNReal.ofNat_ne_top]
      convert ENNReal.lintegral_Lp_smul aemeas_MB two_pos ((2 : ℝ≥0) ^ (102 * (a : ℝ) ^ 3))
      · congr; norm_cast
      · ext; rw [ENNReal.smul_def, smul_eq_mul]; norm_cast
    _ ≤ ((C_Ts a) + 2 ^ (102 * (a : ℝ) ^ 3) * (CMB (defaultA a) 2)) * eLpNorm f 2 volume := by
      rw [add_mul, mul_assoc]
      gcongr
      exact eLpNorm_MB_le hf
    _ ≤ ((2 ^ a ^ 3) + 2 ^ (102 * a ^ 3) * (2 ^ (2 * a))) * eLpNorm f 2 volume := by
      rw [C_Ts, CMB_defaultA_two_eq]
      gcongr
      · norm_cast
      · norm_cast
      · norm_cast
        simp only [Nat.cast_pow, Nat.cast_ofNat, ← NNReal.rpow_natCast]
        apply NNReal.rpow_le_rpow_of_exponent_le one_le_two
        rw [Nat.cast_mul]
        linarith
    _ ≤ (C7_2_2 a) * eLpNorm f 2 volume := by
      rw [← ENNReal.rpow_natCast, Nat.cast_pow]
      exact mul_right_mono <| calc
        _ ≤ (2 : ℝ≥0∞) ^ ((102.5 : ℝ) * a ^ 3) + (2 : ℝ≥0∞) ^ ((102.5 : ℝ) * a ^ 3) := by
          gcongr
          · exact one_le_two
          · linarith [show (101.5 : ℝ) * (a : ℝ) ^ 3 ≥ 0 by positivity]
          · simp_rw [← pow_add, ← ENNReal.rpow_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
            apply ENNReal.rpow_le_rpow_of_exponent_le one_le_two
            linarith [show 2 * a ≤ (0.5 : ℝ) * a ^ 2 * a by nlinarith]
        _ ≤ C7_2_2 a := calc
            _ = (2 : ℝ≥0∞) ^ (102.5 * (a : ℝ) ^ 3 + 1) := by
              rw [← mul_two, ENNReal.rpow_add _ _ two_ne_zero ENNReal.two_ne_top, ENNReal.rpow_one]
            _ ≤ C7_2_2 a := by
              have := ENNReal.coe_rpow_def 2 (103 * a ^ 3)
              simp only [ENNReal.coe_ofNat, OfNat.ofNat_ne_zero, false_and, reduceIte] at this
              rw [C7_2_2, ← this]
              apply ENNReal.rpow_le_rpow_of_exponent_le one_le_two
              linarith [show 0.5 * 4 ^ 3 ≤ (0.5 : ℝ) * a ^ 3 by gcongr]

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

irreducible_def C7_2_3 (a : ℕ) : ℝ≥0 := 2 ^ (12 * (a : ℝ))

/-- Lemma 7.2.3. -/
lemma boundary_operator_bound
    (hf : BoundedCompactSupport f) (hu : u ∈ t) :
    eLpNorm (boundaryOperator t u f) 2 volume ≤ (C7_2_3 a) * eLpNorm f 2 volume := by
  sorry

/-- The constant used in `tree_projection_estimate`.
Originally had value `2 ^ (104 * a ^ 3)` in the blueprint, but that seems to be a mistake. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_2_1 (a : ℕ) : ℝ≥0 := 2 ^ (152 * (a : ℝ) ^ 3)

-- Auxiliary function used in the proof of Lemma 7.2.1
private def eI𝒬u_mul (u : 𝔓 X) (f : X → ℂ) : X → ℂ := fun y ↦ exp (.I * 𝒬 u y) * f y

private lemma boundedCompactSupport_eI𝒬u_mul (u : 𝔓 X) {f : X → ℂ} (hf : BoundedCompactSupport f) :
    BoundedCompactSupport (eI𝒬u_mul u f) := by
  apply hf.mul_bdd_left
  · refine isBounded_iff_forall_norm_le.mpr ⟨1, fun _ h ↦ ?_⟩
    obtain ⟨_, rfl⟩ := mem_range.mp h
    rw [mul_comm, norm_exp_ofReal_mul_I]
  · apply measurable_exp.stronglyMeasurable.comp_measurable
    exact (measurable_ofReal.comp' (map_continuous (𝒬 u)).measurable).const_mul I

private lemma norm_eI𝒬u_mul_eq (u : 𝔓 X) (f : X → ℂ) (x : X) : ‖eI𝒬u_mul u f x‖ = ‖f x‖ := by
  simp [eI𝒬u_mul, mul_comm I]

-- The bound for `carlesonSum` from `pointwise_tree_estimate` (Lemma 7.1.3)
variable (t) (u) (f) in
private def cS_bound (x' : X) :=
    C7_1_3 a * (MB volume 𝓑 c𝓑 r𝓑 (approxOnCube (𝓙 (t u)) (‖f ·‖)) x' +
    t.boundaryOperator u (approxOnCube (𝓙 (t u)) (‖f ·‖)) x') +
    nontangentialMaximalFunction (𝒬 u) (approxOnCube (𝓙 (t u)) (eI𝒬u_mul u f)) x'

private lemma aeMeasurable_cS_bound : AEMeasurable (cS_bound t u f) := by
  refine AEMeasurable.add ?_ MeasureTheory.Measurable.nontangentialMaximalFunction.aemeasurable
  apply ((AEStronglyMeasurable.maximalFunction (to_countable 𝓑)).aemeasurable.add ?_).const_mul
  exact MeasureTheory.Measurable.boundaryOperator.aemeasurable

-- The natural constant for Lemma 7.2.1 is ≤ the simpler constant `C7_2_1` we use instead.
private lemma le_C7_2_1 {a : ℕ} (ha : 4 ≤ a) :
    C7_1_3 a * CMB (defaultA a) 2 + C7_1_3 a * C7_2_3 a + C7_2_2 a ≤ (C7_2_1 a : ℝ≥0∞) := calc
  _ ≤ (3 : ℕ) • (2 : ℝ≥0∞) ^ (151 * (a : ℝ) ^ 3 + 12 * a) := by
    rw [three'_nsmul]
    gcongr
    · rw [C7_1_3_eq_C7_1_6 ha, C7_1_6_def, CMB_defaultA_two_eq, ← ENNReal.coe_mul,
        ← NNReal.rpow_add two_ne_zero, ENNReal.coe_rpow_of_ne_zero two_ne_zero, ENNReal.coe_ofNat]
      apply ENNReal.rpow_le_rpow_of_exponent_le one_le_two ?_
      linarith [show 4 ≤ (a : ℝ) by exact_mod_cast ha]
    · rw [C7_1_3_eq_C7_1_6 ha, C7_2_3_def, C7_1_6_def]
      norm_cast
      exact le_of_eq (pow_add _ _ _).symm
    · rw [C7_2_2_def]
      norm_cast
      exact pow_right_mono₀ one_le_two <| (Nat.mul_le_mul_right _ (by norm_num)).trans le_self_add
  _ = 3 * 2 ^ (12 * (a : ℝ)) * (2 : ℝ≥0∞) ^ (151 * (a : ℝ) ^ 3) := by
    rw [add_comm, ENNReal.rpow_add _ _ two_ne_zero ENNReal.two_ne_top]; ring
  _ ≤ (2 : ℝ≥0∞) ^ ((a : ℝ) ^ 3) * (2 : ℝ≥0∞) ^ (151 * (a : ℝ) ^ 3) := by
    apply mul_right_mono
    norm_cast
    calc
      3 * 2 ^ (12 * a) ≤ 2 ^ 2 * 2 ^ (12 * a) := by gcongr; norm_num
      _                = 2 ^ (2 + 12 * a)     := by rw [pow_add]
      _                ≤ 2 ^ (a ^ 3)          := pow_le_pow_right₀ one_le_two <| calc
                          2 + 12 * a ≤ a + 12 * a  := by apply add_le_add_right; linarith
                          _          = 13 * a      := by ring
                          _          ≤ a ^ 2 * a   := by rw [mul_le_mul_right] <;> nlinarith
                          _          = a ^ 3       := rfl
  _ = _ := by
    rw [C7_2_1_def, ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.two_ne_top]
    norm_cast
    ring

-- Main estimate used in the proof of `tree_projection_estimate`
private lemma eLpNorm_two_cS_bound_le (hu : u ∈ t) : eLpNorm (cS_bound t u f) 2 volume ≤
    C7_2_1 a * eLpNorm (approxOnCube (𝓙 (t u)) (‖f ·‖)) 2 volume := by
  let μ := volume (α := X)
  let aOC := (approxOnCube (𝓙 (t u)) (‖f ·‖))
  let g₁ := MB μ 𝓑 c𝓑 r𝓑 aOC
  let g₂ := t.boundaryOperator u (approxOnCube (𝓙 (t u)) (‖f ·‖))
  let g₃ := nontangentialMaximalFunction (𝒬 u) (approxOnCube (𝓙 (t u)) (eI𝒬u_mul u f))
  have m₁ : AEMeasurable g₁ :=
    (MeasureTheory.AEStronglyMeasurable.maximalFunction (to_countable 𝓑)).aemeasurable
  have m₂ : AEMeasurable g₂ := MeasureTheory.Measurable.boundaryOperator.aemeasurable
  calc eLpNorm (cS_bound t u f) 2 μ
    _ = eLpNorm (C7_1_3 a • (g₁ + g₂) + g₃) 2 μ := rfl
    _ ≤ eLpNorm (C7_1_3 a • (g₁ + g₂)) 2 μ + eLpNorm g₃ 2 μ := by
      simpa [eLpNorm, eLpNorm'] using
        ENNReal.lintegral_Lp_add_le ((m₁.add m₂).const_smul (C7_1_3 a)) (hp1 := one_le_two)
          MeasureTheory.Measurable.nontangentialMaximalFunction.aemeasurable
    _ = C7_1_3 a • eLpNorm (g₁ + g₂) 2 μ + eLpNorm g₃ 2 μ := by
      congr
      simpa [eLpNorm, eLpNorm'] using ENNReal.lintegral_Lp_smul (m₁.add m₂) two_pos (C7_1_3 a)
    _ ≤ C7_1_3 a • (eLpNorm g₁ 2 μ + eLpNorm g₂ 2 μ) + eLpNorm g₃ 2 μ := by
      gcongr
      simpa [eLpNorm, eLpNorm'] using ENNReal.lintegral_Lp_add_le m₁ m₂ one_le_two
    _ ≤ C7_1_3 a • ((CMB (defaultA a) 2) * eLpNorm aOC 2 μ + (C7_2_3 a) * eLpNorm aOC 2 μ) +
          (C7_2_2 a) * eLpNorm aOC 2 μ := by
      gcongr
      · exact eLpNorm_MB_le boundedCompactSupport_approxOnCube
      · apply le_of_le_of_eq <| boundary_operator_bound boundedCompactSupport_approxOnCube hu
        simp [eLpNorm, eLpNorm', aOC, approxOnCube_ofReal, enorm_eq_nnnorm, μ]
      · apply le_trans <| nontangential_operator_bound boundedCompactSupport_approxOnCube (𝒬 u)
        refine mul_le_mul_left' (eLpNorm_mono (fun x ↦ ?_)) _
        apply le_of_le_of_eq norm_approxOnCube_le_approxOnCube_norm
        rw [Real.norm_of_nonneg <| approxOnCube_nonneg (fun _ ↦ norm_nonneg _)]
        simp_rw [norm_eI𝒬u_mul_eq]
    _ = (C7_1_3 a * CMB (defaultA a) 2 + C7_1_3 a * C7_2_3 a + C7_2_2 a) * eLpNorm aOC 2 μ := by
      rw [ENNReal.smul_def, smul_eq_mul]; ring
    _ ≤ _ := mul_le_mul_right' (le_C7_2_1 (four_le_a X)) _

/-- Lemma 7.2.1. -/
lemma tree_projection_estimate
    (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g) (hu : u ∈ t) :
    ‖∫ x, conj (g x) * carlesonSum (t u) f x‖₊ ≤
    C7_2_1 a * eLpNorm (approxOnCube (𝓙 (t u)) (‖f ·‖)) 2 volume *
    eLpNorm (approxOnCube (𝓛 (t u)) (‖g ·‖)) 2 volume := by
  set aOC := approxOnCube (𝓛 (t u)) (‖g ·‖)
  let eaOC (x : X) := ENNReal.ofReal (aOC x)
  have aOC_nonneg {x : X} : 0 ≤ aOC x := approxOnCube_nonneg (fun _ ↦ norm_nonneg _)
  calc ENNReal.ofNNReal ‖∫ x, conj (g x) * carlesonSum (t u) f x‖₊
    _ ≤ ∫⁻ x, ‖conj (g x) * carlesonSum (t u) f x‖ₑ := ennnorm_integral_le_lintegral_ennnorm _
    _ = ∫⁻ x in (⋃ p ∈ t u, 𝓘 p), ‖g x‖ₑ * ‖carlesonSum (t u) f x‖ₑ := by
      rw [← lintegral_indicator]; swap
      · exact MeasurableSet.biUnion (t u).to_countable (fun _ _ ↦ coeGrid_measurable)
      simp_rw [enorm_eq_nnnorm, nnnorm_mul, ENNReal.coe_mul, RCLike.nnnorm_conj]
      refine lintegral_congr (fun x ↦ ?_)
      by_cases hx : x ∈ ⋃ p ∈ t u, 𝓘 p
      · rw [indicator_of_mem hx]
      · simp [indicator_of_not_mem hx, nmem_support.mp (hx <| support_carlesonSum_subset ·)]
    _ ≤ ∫⁻ x in (⋃ L ∈ 𝓛 (t u), (L : Set X)), ‖g x‖ₑ * ‖carlesonSum (t u) f x‖ₑ := by
      rw [biUnion_𝓛]
      refine lintegral_mono_set (fun x hx ↦ ?_)
      have ⟨p, hp⟩ : ∃ p ∈ t u, x ∈ 𝓘 p := by simpa using hx
      apply mem_iUnion.mpr ⟨𝓘 p, hp.2⟩
    _ = ∑ L in 𝓛 (t u), ∫⁻ x in L, ‖g x‖ₑ * ‖carlesonSum (t u) f x‖ₑ := by
      simp only [← mem_toFinset]
      refine lintegral_biUnion_finset ?_ (fun _ _ ↦ coeGrid_measurable) _
      rw [coe_toFinset]
      exact pairwiseDisjoint_𝓛
    _ ≤ ∑ L in 𝓛 (t u), ∫⁻ x in L, ‖g x‖ₑ * (⨅ x' ∈ L, ‖cS_bound t u f x'‖ₑ) := by
      gcongr ∑ L in 𝓛 (t u), ?_ with L hL
      refine setLIntegral_mono (Measurable.mul ?_ measurable_const) (fun x hx ↦ ?_)
      · exact measurable_coe_nnreal_ennreal_iff.mpr hg.stronglyMeasurable.measurable.nnnorm
      · gcongr
        refine le_iInf₂ (fun x' hx' ↦ ?_)
        simp only [mem_toFinset] at hL
        convert pointwise_tree_estimate hu hL hx hx' (boundedCompactSupport_eI𝒬u_mul u hf) using 1
        · congr
          simp_rw [mul_neg, eI𝒬u_mul, ← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]
        · simp only [cS_bound, enorm_eq_self, norm_eI𝒬u_mul_eq u f]
    _ = ∑ L in 𝓛 (t u), ∫⁻ x in L, eaOC x * (⨅ x' ∈ L, ‖cS_bound t u f x'‖ₑ) := by
      refine Finset.sum_congr rfl (fun L hL ↦ ?_)
      rw [lintegral_mul_const, lintegral_mul_const]; rotate_left
      · exact ENNReal.measurable_ofReal.comp (stronglyMeasurable_approxOnCube _ _).measurable
      · exact hg.stronglyMeasurable.measurable.ennnorm
      simp_rw [eaOC, enorm_eq_nnnorm]
      simp_rw [lintegral_coe_eq_integral (‖g ·‖₊) hg.integrable.norm.restrict, coe_nnnorm]
      rw [integral_eq_lintegral_approxOnCube pairwiseDisjoint_𝓛 (mem_toFinset.mp hL) hg]
      simp_rw [← Real.ennnorm_eq_ofReal aOC_nonneg, approxOnCube_ofReal, nnnorm_real, aOC]
    _ ≤ ∑ L in 𝓛 (t u), ∫⁻ x in L, eaOC x * ‖cS_bound t u f x‖ₑ :=
      Finset.sum_le_sum fun L hL ↦
        setLIntegral_mono' coeGrid_measurable (fun x hx ↦ mul_left_mono (biInf_le _ hx))
    _ = ∫⁻ x in (⋃ L ∈ 𝓛 (t u), (L : Set X)), eaOC x * ‖cS_bound t u f x‖ₑ := by
      rw [← lintegral_biUnion_finset (hm := fun _ _ ↦ coeGrid_measurable)]
      · simp only [mem_toFinset]
      · simpa only [coe_toFinset] using pairwiseDisjoint_𝓛 (𝔖 := t u)
    _ ≤ ∫⁻ (x : X), eaOC x * ‖cS_bound t u f x‖ₑ := by
      nth_rewrite 2 [← setLIntegral_univ]
      exact lintegral_mono_set (fun _ _ ↦ trivial)
    _ ≤ eLpNorm eaOC 2 volume * eLpNorm (cS_bound t u f) 2 volume := by
      have isConj : Real.IsConjExponent 2 2 := by constructor <;> norm_num
      have : AEMeasurable eaOC := (stronglyMeasurable_approxOnCube _ _).aemeasurable.ennreal_ofReal
      convert ENNReal.lintegral_mul_le_Lp_mul_Lq volume isConj this aeMeasurable_cS_bound <;>
        simp [eLpNorm, eLpNorm']
    _ = eLpNorm (cS_bound t u f) 2 volume * eLpNorm aOC 2 volume := by
      rw [mul_comm]; congr; ext; exact (Real.ennnorm_eq_ofReal aOC_nonneg).symm
    _ ≤ _ := mul_right_mono (eLpNorm_two_cS_bound_le hu)

end TileStructure.Forest
