import Carleson.ForestOperator.PointwiseEstimate
import Carleson.ToMathlib.Misc
import Carleson.ToMathlib.ENorm
import Carleson.ToMathlib.Annulus
import Carleson.ToMathlib.MeasureTheory.Integral.MeanInequalities

noncomputable section

open Set MeasureTheory Metric Function Complex Bornology TileStructure Filter
open scoped NNReal ENNReal ComplexConjugate

open ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] {f : X → ℂ}

lemma integrableOn_K_mul_f (x' : X) (hf : BoundedCompactSupport f volume) (r : ℝ≥0∞) (hr : 0 < r) :
    IntegrableOn (fun y ↦ K x' y * f y) (EAnnulus.ci x' r) := by
  by_cases supp_f : (support f).Nonempty; swap
  · simp [Function.support_eq_empty_iff.mp <| Set.not_nonempty_iff_eq_empty.mp supp_f]
  by_cases r_top : r = ⊤
  · simp [r_top]
  have ⟨x'', hx''⟩ := supp_f
  have ⟨C, hC⟩ := Metric.isBounded_iff.mp hf.isBoundedSupport
  have : support (fun y ↦ f y * K x' y) ⊆ closedBall x' (dist x' x'' + C) := by
    intro y hy
    have : y ∈ support f := by contrapose! hy; simp [hy]
    exact mem_closedBall'.mp <| (dist_triangle x' x'' y).trans <| add_le_add_left (hC hx'' this) _
  simp_rw [mul_comm (K x' _), IntegrableOn, ← integrableOn_iff_integrable_of_support_subset this]
  apply hf.restrict.restrict.integrable_mul
  rw [Measure.restrict_restrict measurableSet_closedBall, inter_comm, ← IntegrableOn]
  convert integrableOn_K_Icc (K := K) (R := dist x' x'' + C) (r.toReal_pos hr.ne.symm r_top) using 1
  ext y
  simp [edist_dist, dist_comm y, EAnnulus.ci, ENNReal.le_ofReal_iff_toReal_le r_top dist_nonneg]


-- Truncated version of `K` used in proof of `nontangential_pointwise_bound`
private def K' (b : ℤ) (c : ℤ) (x y : X) := ∑ i ∈ (Icc b c).toFinset, Ks i x y

namespace K'

private lemma eq_K (b : ℤ) (c : ℤ) (x y : X)
    (h : dist x y ∈ Icc ((D : ℝ) ^ (b - 1) / 2) (D ^ c / 4)) : K' b c x y = K x y := by
  have hxy : dist x y > 0 := lt_of_lt_of_le (div_pos (defaultD_pow_pos a (b - 1)) two_pos) h.1
  simp_rw [K', Ks, ← Finset.mul_sum, ← Complex.ofReal_sum]
  rw [← finsum_eq_sum_of_support_subset, finsum_ψ (one_lt_D (X := X)) hxy, ofReal_one, mul_one]
  rw [toFinset_Icc, Finset.coe_Icc]
  exact support_ψS_subset_Icc (one_lt_D (X := X)) h

private lemma integrableOn_mul_f (x' : X) (hf : BoundedCompactSupport f) (r : ℝ≥0∞) (hr : 0 < r)
    (s₁ s₂ : ℤ) : IntegrableOn (fun y ↦ K' s₁ s₂ x' y * f y) (EAnnulus.ci x' r) := by
  simp_rw [K', Ks, mul_comm (K x' _) (ψ _), ← Finset.sum_mul, mul_assoc]
  apply Integrable.bdd_mul (integrableOn_K_mul_f x' hf r hr)
  · refine (Finset.aestronglyMeasurable_sum _ (fun i hi ↦ ?_)).restrict
    apply continuous_ofReal.comp_aestronglyMeasurable ∘ continuous_ψ.comp_aestronglyMeasurable
    exact (continuous_const.dist continuous_id').aestronglyMeasurable.const_mul _
  · refine ⟨(s₂ + 1 - s₁).toNat, fun _ ↦ le_trans (norm_sum_le ..) ?_⟩
    simp_rw [norm_real]
    exact le_of_le_of_eq (Finset.sum_le_sum fun _ _ ↦ abs_ψ_le_one _ _) (by simp)

private lemma support_subset (b : ℤ) (c : ℤ) (x : X) :
    support (K' b c x) ⊆ Annulus.cc x (D ^ (b - 1) / 4) (D ^ c / 2) := by
  refine subset_trans ?_ (Annulus.oo_subset_cc (le_refl _) (le_refl _))
  intro y hy
  rw [mem_support] at hy
  simp only [Annulus.oo, mem_Ioo, mem_setOf_eq]
  contrapose! hy
  refine Finset.sum_eq_zero (fun s hs ↦ ?_)
  rw [toFinset_Icc] at hs
  suffices ((D : ℝ) ^ s)⁻¹ * dist x y ∉ support ψ by simp [Ks, nmem_support.mp this, -defaultD]
  rw [support_ψ (one_lt_D (X := X)), mem_Ioo, not_and_or]
  by_cases h : (D : ℝ) ^ (b - 1) / 4 < dist x y
  · exact Or.inr <| not_lt_of_ge <| calc
      _ ≥ ((D : ℝ) ^ c)⁻¹ * (D ^ c / 2) := by
        gcongr
        · exact defaultD_pow_pos a s
        · exact one_le_D
        · exact (Finset.mem_Icc.mp hs).2
        · exact hy h
      _ = 2⁻¹ := by field_simp
  · push_neg at h
    exact Or.inl <| not_lt_of_ge <| calc
      ((D : ℝ) ^ s)⁻¹ * dist x y ≤ ((D : ℝ) ^ b)⁻¹ * (D ^ (b - 1) / 4) := by
                                 refine mul_le_mul ?_ h dist_nonneg ?_
                                 · apply inv_anti₀ (defaultD_pow_pos a b)
                                   exact zpow_right_mono₀ one_le_D (Finset.mem_Icc.mp hs).1
                                 · exact inv_nonneg.mpr (defaultD_pow_pos a b).le
      _                          = (4 * (D : ℝ))⁻¹ := by
                                 rw [zpow_sub₀ (defaultD_pos a).ne.symm]; field_simp; apply mul_comm

private lemma enorm_le_enorm_K (a : ℤ) (b : ℤ) (x y : X) : ‖K' a b x y‖ₑ ≤ ‖K x y‖ₑ := by
  unfold K' Ks
  by_cases hxy : 0 = dist x y
  · simp [← hxy, psi_zero]
  rw [← mul_one ‖K x y‖ₑ, ← Finset.mul_sum, enorm_mul]
  apply mul_le_mul_left'
  rw [enorm_eq_nnnorm]
  norm_cast
  apply le_trans <| nnnorm_sum_le _ _
  simp_rw [← norm_toNNReal, Real.norm_eq_abs, ← Real.toNNReal_sum_of_nonneg fun _ _ ↦ abs_nonneg _,
    Real.toNNReal_le_one, abs_eq_self.mpr <| zero_le_ψ _ _]
  exact sum_ψ_le (one_lt_D (X := X)) _ <| lt_of_le_of_ne dist_nonneg hxy

end K'

-- Bound needed for proof of `nontangential_pointwise_bound`, splitting the annulus between radii
-- `r₁` and `r₄` into annuli between `r₁` and `r₂`, between `r₂` and `r₃`, and between `r₃` and
-- `r₄`. Note that we assume only `r₁ ≤ r₂` and `r₃ ≤ r₄`.
private lemma annulus_integral_bound (x : X) (g : X → ℂ) {r₁ r₂ r₃ r₄ : ℝ} (h₁₂ : r₁ ≤ r₂)
    (h₃₄ : r₃ ≤ r₄) (hg : IntegrableOn g (Annulus.cc x r₁ r₄)) :
    ‖∫ y in Annulus.cc x r₁ r₄, g y‖ₑ ≤ ‖∫ y in Annulus.oo x r₂ r₃, g y‖ₑ +
    ((∫⁻ y in Annulus.cc x r₁ r₂, ‖g y‖ₑ) + ∫⁻ y in Annulus.cc x r₃ r₄, ‖g y‖ₑ) := calc
  _ = ‖(∫ y in Annulus.cc x r₁ r₄ ∩ Annulus.oo x r₂ r₃, g y) +
        ∫ y in Annulus.cc x r₁ r₄ ∩ (Annulus.oo x r₂ r₃)ᶜ, g y‖ₑ := by
    apply congrArg (‖·‖ₑ)
    rw [← setIntegral_union (Set.disjoint_left.mpr (fun _ h₁ h₂ ↦ h₂.2 h₁.2)) (by measurability),
        inter_union_compl] <;>
      exact hg.mono_set inter_subset_left
  _ ≤ ‖∫ y in Annulus.cc x r₁ r₄ ∩ Annulus.oo x r₂ r₃, g y‖ₑ +
        ‖∫ y in Annulus.cc x r₁ r₄ ∩ (Annulus.oo x r₂ r₃)ᶜ, g y‖ₑ := by apply ENormedAddMonoid.enorm_add_le
  _ ≤ _ := by
    gcongr
    · rw [inter_eq_self_of_subset_right <| Annulus.oo_subset_cc h₁₂ h₃₄]
    · calc
        _ ≤ _ := enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ y in Annulus.cc x r₁ r₂ ∪ Annulus.cc x r₃ r₄, ‖g y‖ₑ := by
          refine lintegral_mono_set (fun y ↦ ?_)
          simp only [Annulus.oo, Annulus.cc, edist_dist, mem_Ioo, mem_Icc, mem_inter_iff,
            mem_setOf_eq, mem_compl_iff, not_and, not_le, mem_union, and_imp]
          intro hr₁ hr₄ hr₂₃
          by_cases hr₂ : r₂ < dist x y
          · exact Or.inr ⟨le_of_not_gt (hr₂₃ hr₂), hr₄⟩
          · exact Or.inl ⟨hr₁, le_of_not_gt hr₂⟩
        _ ≤ _ := lintegral_union_le _ _ _

lemma CMB_defaultA_two_eq {a : ℕ} : CMB (defaultA a) 2 = 2 ^ (a + (3 / 2 : ℝ)) := by
  suffices (2 : ℝ≥0) * 2 ^ (2 : ℝ)⁻¹ * (ENNReal.ofReal |2 - 1|⁻¹).toNNReal ^ (2 : ℝ)⁻¹ *
      ((2 ^ a) ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ = 2 ^ (a + 3 / (2 : ℝ)) by
    simpa [CMB, C_realInterpolation, C_realInterpolation_ENNReal]
  rw [← NNReal.rpow_mul, show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by norm_num]
  repeat rw [NNReal.rpow_add two_ne_zero]
  norm_num
  ring

open ShortVariables TileStructure
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
  {n j j' : ℕ} {t : Forest X n} {u u₁ u₂ p : 𝔓 X} {x x' : X} {𝔖 : Set (𝔓 X)}
  {f f₁ f₂ g g₁ g₂ : X → ℂ} {I J J' L : Grid X}
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

namespace TileStructure.Forest

lemma eLpNorm_MB_le {𝕜 : Type*} [RCLike 𝕜] {f : X → 𝕜} (hf : BoundedCompactSupport f) :
    eLpNorm (MB volume 𝓑 c𝓑 r𝓑 f ·) 2 volume ≤ CMB (defaultA a : ℝ≥0) 2 * eLpNorm f 2 volume :=
  hasStrongType_MB_finite 𝓑_finite one_lt_two f (hf.memLp 2) |>.2

/-! ## Section 7.2 and Lemma 7.2.1 -/

/-- The constant used in `nontangential_operator_bound`.
Previously had value `2 ^ (103 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_2_2 (a : ℕ) : ℝ≥0 := 2 ^ (102 * (a : ℝ) ^ 3)

-- Bound for (7.2.3) in the proof of `nontangential_pointwise_bound`
omit [TileStructure Q D κ S o] in
private lemma nontangential_integral_bound₁ {x x' : X} {r : ℝ} (R : ℝ) (hr : dist x x' < r) :
    ‖∫ y in Annulus.oo x' r R, K x' y * f y‖ₑ ≤ nontangentialOperator K f x := by
  by_cases r_lt_R : r < R; swap
  · simp [-defaultD, Annulus.oo_eq_empty (le_of_not_gt r_lt_R)]
  refine le_trans ?_ <| le_iSup _ r
  refine le_trans ?_ <| le_iSup _ R
  rw [iSup_pos r_lt_R]
  refine le_of_eq_of_le ?_ <| le_iSup _ x'
  rw [iSup_pos hr, Annulus.oo, enorm_eq_nnnorm]

-- Bound for (7.2.4) and (7.2.5) in the proof of `nontangential_pointwise_bound`
private lemma nontangential_integral_bound₂ (hf : BoundedCompactSupport f) {x x' : X}
    {I : Grid X} (hx : x ∈ I) (hx' : x' ∈ I) {R : ℝ} (h : R ≤ 8 * D ^ s I) :
    ∫⁻ y in Annulus.cc x' ((D : ℝ) ^ (s I - 1) / 4) R, ‖K x' y * f y‖ₑ ≤
    2 ^ (7 * (a : ℝ) + 101 * a ^ 3) * MB volume 𝓑 c𝓑 r𝓑 f x := by
  apply (lintegral_mono_set (Annulus.cc_subset_cc (le_refl _) h)).trans
  have ineq : ∀ y ∈ Annulus.cc x' ((D : ℝ) ^ (s I - 1) / 4) (8 * D ^ s I), ‖K x' y * f y‖ₑ ≤
      2 ^ (7 * (a : ℝ) + 101 * a ^ 3) / volume (ball (c I) (16 * D ^ s I)) * ‖f y‖ₑ := by
    intro y hy
    rw [Annulus.cc] at hy
    rw [enorm_mul]
    refine mul_le_mul_right' ((enorm_K_le 5 hy.1).trans ?_) ‖f y‖ₑ
    gcongr
    · norm_num
    · norm_num
    · suffices dist (c I) x' < 16 * D ^ s I from ball_subset_ball' (by linarith)
      rw [← mem_ball', s]
      refine ball_subset_ball ?_ (Grid_subset_ball hx')
      linarith [defaultD_pow_pos a (GridStructure.s I)]
  apply le_trans <| setLIntegral_mono_ae (hf.aestronglyMeasurable.enorm.const_mul _).restrict
    (.of_forall ineq)
  simp_rw [ENNReal.mul_comm_div, div_eq_mul_inv]
  have := hf.aestronglyMeasurable.enorm
  rw [lintegral_const_mul'' _ (this.mul_const _).restrict, lintegral_mul_const'' _ this.restrict,
    ← div_eq_mul_inv]
  apply mul_left_mono
  calc
    _ ≤ (∫⁻ y in ball (c I) (16 * D ^ s I), ‖f y‖ₑ) / volume (ball (c I) (16 * D ^ s I)) := by
      gcongr
      refine lintegral_mono' (Measure.le_iff.mpr (fun T hT ↦  ?_)) (le_refl _)
      rw [Measure.restrict_apply hT, Measure.restrict_apply hT]
      refine measure_mono (inter_subset_inter_right T (fun y ↦ ?_))
      simp only [Annulus.cc, mem_Icc, mem_setOf_eq, mem_ball, and_imp, dist_comm x']
      intro _ h
      calc dist y (c I)
        _ ≤ dist y x' + dist x' (c I) := dist_triangle y x' (c I)
        _ ≤ 8 * (D : ℝ) ^ s I + 4 * (D : ℝ) ^ s I :=
          add_le_add h (mem_ball.mp (Grid_subset_ball hx')).le
        _ < 16 * (D : ℝ) ^ s I := by linarith [defaultD_pow_pos a (s I)]
    _ = ⨍⁻ y in ball (c I) (16 * D ^ s I), ‖f y‖ₑ ∂volume := by rw [setLAverage_eq]
    _ ≤ MB volume 𝓑 c𝓑 r𝓑 f x := by
      rw [MB, maximalFunction, inv_one, ENNReal.rpow_one]
      have : (4, 0, I) ∈ 𝓑 := by simp [𝓑]
      refine le_of_eq_of_le ?_ (le_biSup _ this)
      have : x ∈ ball (c I) (2 ^ 4 * (D : ℝ) ^ s I) := by
        refine (ball_subset_ball ?_) (Grid_subset_ball hx)
        unfold s
        linarith [defaultD_pow_pos a (GridStructure.s I)]
      simp_rw [c𝓑, r𝓑, ENNReal.rpow_one, Nat.cast_zero, add_zero, indicator_of_mem this,
        enorm_eq_nnnorm]
      norm_num

-- Pointwise bound needed for Lemma 7.2.2
private lemma nontangential_pointwise_bound (hf : BoundedCompactSupport f) (θ : Θ X) (x : X) :
    nontangentialMaximalFunction θ f x ≤ nontangentialOperator K f x +
      2 ^ (1 + 7 * (a : ℝ) + 101 * a ^ 3) * MB volume 𝓑 c𝓑 r𝓑 f x := by
  refine iSup₂_le fun I hI ↦ iSup₂_le fun x' hx' ↦ iSup₂_le fun s₂ hs₂ ↦ iSup_le fun _ ↦ ?_
  rw [← enorm_eq_nnnorm, ← integral_finset_sum]; swap
  · intro i hi
    simp_rw [mul_comm]
    exact hf.integrable_mul (integrable_Ks_x <| one_lt_D (X := X))
  simp_rw [← Finset.sum_mul]
  have ineq {n : ℕ} (hn : n > 0) : (D : ℝ) ^ (s I - 1) / n < 8 * D ^ s I := by
    rw [zpow_sub₀ (defaultD_pos a).ne.symm, div_div, zpow_one]
    calc (D : ℝ) ^ s I / ((D : ℝ) * n)
      _ ≤ D ^ s I / 1 := by gcongr; exact_mod_cast (mul_pos (defaultD_pos' a) hn)
      _ < 8 * D ^ s I := by linarith [defaultD_pow_pos a (s I)]
  calc
    _ = ‖∫ y in Annulus.cc x' (D ^ (s I - 1) / 4) (D ^ s₂ / 2), K' (s I) s₂ x' y * f y‖ₑ := by
      rw [← integral_indicator Annulus.measurableSet_cc]
      congr
      ext y
      by_cases hy : y ∈ Annulus.cc x' (D ^ (s I - 1) / 4) (D ^ s₂ / 2)
      · simp only [K', hy, indicator_of_mem]
      · have K'_eq_zero := nmem_support.mp <| not_mem_subset (K'.support_subset (s I) s₂ x') hy
        rw [← K', K'_eq_zero, zero_mul, indicator_of_not_mem hy]
    _ ≤ ‖∫ y in Annulus.oo x' (8 * D ^ s I) (D ^ (s₂ - 1) / 4), K' (s I) s₂ x' y * f y‖ₑ +
          ((∫⁻ y in Annulus.cc x' (D ^ (s I - 1) / 4) (8 * D ^ s I), ‖K' (s I) s₂ x' y * f y‖ₑ) +
          ∫⁻ y in Annulus.cc x' (D ^ (s₂ - 1) / 4) (D ^ s₂ / 2), ‖K' (s I) s₂ x' y * f y‖ₑ) := by
      apply annulus_integral_bound
      · exact (ineq four_pos).le
      · gcongr
        · exact one_lt_D (X := X) |>.le
        · exact sub_one_lt s₂ |>.le
        · norm_num
      · refine K'.integrableOn_mul_f x' hf (ENNReal.ofReal (D ^ (s I - 1) / 4)) ?_ (s I) s₂
          |>.mono_set ?_
        · exact ENNReal.ofReal_pos.mpr <| div_pos (defaultD_pow_pos a (s I - 1)) four_pos
        · rw [EAnnulus.ci_eq_annulus]
          exact Annulus.cc_subset_ci (le_refl _)
    _ ≤ ‖∫ y in Annulus.oo x' (8 * D ^ s I) (D ^ (s₂ - 1) / 4), K x' y * f y‖ₑ +
          ((∫⁻ y in Annulus.cc x' (D ^ (s I - 1) / 4) (8 * D ^ s I), ‖K x' y * f y‖ₑ) +
          ∫⁻ y in Annulus.cc x' (D ^ (s₂ - 1) / 4) (D ^ s₂ / 2), ‖K x' y * f y‖ₑ) := by
      have norm_K'_f_le : ∀ (y : X), ‖K' (s I) s₂ x' y * f y‖ₑ ≤ ‖K x' y * f y‖ₑ := by
        simp_rw [enorm_mul]
        exact fun y ↦ mul_le_mul_of_nonneg_right (K'.enorm_le_enorm_K _ _ _ _) (zero_le _)
      gcongr
      · refine (congrArg (‖·‖ₑ) <| setIntegral_congr_fun Annulus.measurableSet_oo fun y hy ↦ ?_).le
        apply mul_eq_mul_right_iff.mpr ∘ Or.inl ∘ K'.eq_K (s I) s₂ x' y
        simp only [Annulus.oo, mem_Ioo, mem_setOf_eq] at hy
        have i1 := hy.1
        have i2 := hy.2.le
        refine mem_Icc.mpr ⟨(lt_trans (ineq two_pos) i1).le, i2.trans ?_⟩
        rw [zpow_sub₀ (defaultD_pos a).ne.symm, div_div, zpow_one]
        have : (D : ℝ) * 4 > 0 := mul_pos (defaultD_pos a) four_pos
        apply (div_le_div_iff_of_pos_left (defaultD_pow_pos a s₂) this four_pos).mpr
        norm_cast
        linarith [defaultD_pos' a]
      · exact norm_K'_f_le _
      · exact norm_K'_f_le _
    _ ≤ nontangentialOperator K f x + (2 ^ (7 * (a : ℝ) + 101 * a ^ 3) * MB volume 𝓑 c𝓑 r𝓑 f x +
          2 ^ (7 * (a : ℝ) + 101 * a ^ 3) * MB volume 𝓑 c𝓑 r𝓑 f x) := by
      gcongr
      · apply nontangential_integral_bound₁ (D ^ (s₂ - 1) / 4)
        apply lt_of_le_of_lt (dist_triangle x (c I) x')
        replace hI := mem_ball.mp (Grid_subset_ball hI)
        replace hx' := mem_ball'.mp (Grid_subset_ball hx')
        apply lt_of_lt_of_eq (add_lt_add hI hx')
        unfold s
        ring
      · exact nontangential_integral_bound₂ hf hI hx' (le_refl _)
      · let I₂ := cubeOf s₂ x
        have hs₂' : s₂ ∈ Icc (-(S : ℤ)) (S : ℤ) :=
          Icc_subset_Icc (Set.range_subset_iff.mp range_s_subset I |>.1) (le_refl (S : ℤ)) hs₂
        have ⟨xI₂, hI₂⟩ := cubeOf_spec hs₂' I hI
        rw [← hI₂]
        have : s I ≤ s I₂ := by rw [hI₂]; exact hs₂.1
        have := (fundamental_dyadic this).resolve_right (Set.not_disjoint_iff.mpr ⟨x, ⟨hI, xI₂⟩⟩)
        apply nontangential_integral_bound₂ hf xI₂ (this hx')
        linarith [defaultD_pow_pos a (s (cubeOf s₂ x))]
    _ = _ := by
      rw [← two_mul, ← mul_assoc, add_assoc, ENNReal.rpow_add 1 _ two_ne_zero ENNReal.ofNat_ne_top,
        ENNReal.rpow_one]

/-- Lemma 7.2.2. -/
lemma nontangential_operator_bound
    (hf : BoundedCompactSupport f)
    (θ : Θ X) :
    eLpNorm (nontangentialMaximalFunction θ f ·) 2 volume ≤ (C7_2_2 a) * eLpNorm f 2 volume := by
  have ha : 4 ≤ (a : ℝ) := by exact_mod_cast four_le_a X
  have aemeas_MB : AEMeasurable (MB volume 𝓑 c𝓑 r𝓑 f ·) :=
    (AEStronglyMeasurable.maximalFunction (to_countable 𝓑)).aemeasurable
  have ⟨hT₁, hT₂⟩ := hasBoundedStrongType_Tstar f (hf.memLp 2) hf.memLp_top.eLpNorm_lt_top
    hf.isBoundedSupport.measure_lt_top
  calc eLpNorm (nontangentialMaximalFunction θ f) 2 volume
    _ ≤ eLpNorm (fun x ↦ nontangentialOperator K f x +
          2 ^ (1 + 7 * (a : ℝ) + 101 * a ^ 3) * MB volume 𝓑 c𝓑 r𝓑 f x) 2 volume := by
      simp only [eLpNorm, OfNat.ofNat_ne_zero, reduceIte, ENNReal.ofNat_ne_top, eLpNorm']
      gcongr
      exact nontangential_pointwise_bound hf θ _
    _ ≤ eLpNorm (nontangentialOperator K f) 2 volume +
          eLpNorm ((2 : ℝ≥0∞) ^ (1 + 7 * (a : ℝ) + 101 * a ^ 3) *
          MB volume 𝓑 c𝓑 r𝓑 f ·) 2 volume := by
      simpa [eLpNorm, eLpNorm'] using
        ENNReal.lintegral_Lp_add_le hT₁.aemeasurable (aemeas_MB.const_mul _) one_le_two
    _ = eLpNorm (nontangentialOperator K f) 2 volume +
          2 ^ (1 + 7 * (a : ℝ) + 101 * a ^ 3) * eLpNorm (MB volume 𝓑 c𝓑 r𝓑 f ·) 2 volume := by
      congr
      simp only [eLpNorm, eLpNorm', OfNat.ofNat_ne_zero, reduceIte, ENNReal.ofNat_ne_top]
      convert ENNReal.lintegral_Lp_smul aemeas_MB two_pos ((2 : ℝ≥0) ^ (1 + 7 * a + 101 * a ^ 3))
      · congr; norm_cast
      · ext; rw [ENNReal.smul_def]; norm_cast
    _ ≤ (C_Ts a + 2 ^ (1 + 7 * a + 101 * a ^ 3 : ℝ) * CMB (defaultA a) 2) * eLpNorm f 2 volume := by
      rw [add_mul, mul_assoc]; gcongr; exact eLpNorm_MB_le hf
    _ ≤ ((2 ^ a ^ 3) + 2 ^ (1 + 7 * a + 101 * a ^ 3) * (2 ^ (2 * a))) * eLpNorm f 2 volume := by
      rw [C_Ts, CMB_defaultA_two_eq]
      gcongr <;> norm_cast
      simp only [Nat.cast_pow, Nat.cast_ofNat, ← NNReal.rpow_natCast]
      apply NNReal.rpow_le_rpow_of_exponent_le one_le_two
      rw [Nat.cast_mul]
      linarith
    _ ≤ (C7_2_2 a) * eLpNorm f 2 volume := by
      rw [← ENNReal.rpow_natCast, Nat.cast_pow]
      exact mul_right_mono <| calc 2 ^ (a : ℝ) ^ 3 + 2 ^ (1 + 7 * a + 101 * a ^ 3) * 2 ^ (2 * a)
        _ ≤ (2 : ℝ≥0∞) ^ ((101.6 : ℝ) * a ^ 3) + (2 : ℝ≥0∞) ^ ((101.6 : ℝ) * a ^ 3) := by
          gcongr
          · exact one_le_two
          · linarith [pow_pos (cast_a_pos X) 3]
          · simp_rw [← pow_add, ← ENNReal.rpow_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
            apply ENNReal.rpow_le_rpow_of_exponent_le one_le_two
            linarith [show 4 ^ 2 * (a : ℝ) ≤ a ^ 2 * a by gcongr]
        _ = (2 : ℝ≥0∞) ^ (101.6 * (a : ℝ) ^ 3 + 1) := by
          rw [← mul_two, ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top, ENNReal.rpow_one]
        _ ≤ C7_2_2 a := by
          have := ENNReal.coe_rpow_def 2 (102 * a ^ 3)
          simp only [ENNReal.coe_ofNat, OfNat.ofNat_ne_zero, false_and, reduceIte] at this
          rw [C7_2_2, ← this]
          apply ENNReal.rpow_le_rpow_of_exponent_le one_le_two
          linarith [show 0.4 * 4 ^ 3 ≤ (0.4 : ℝ) * a ^ 3 by gcongr]

open scoped Classical in
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
  have double := @measure_ball_two_le_same_iterate X _ _ _ volume _ (c J) (D ^ s J / 4) 9
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

lemma e728_push_toReal (hf : BoundedCompactSupport f) :
    (t.boundaryOperator u f x).toReal = ∑ I : Grid X,
      (I : Set X).indicator (fun _ ↦ ∑ J ∈ 𝓙' t u (c I) (s I), (ijIntegral f I J).toReal) x := by
  rw [boundaryOperator, ENNReal.toReal_sum]
  · congr! with I -
    unfold indicator; split_ifs
    · exact ENNReal.toReal_sum fun _ _ ↦ (ijIntegral_lt_top hf).ne
    · rfl
  · have bof := fun x ↦ boundaryOperator_lt_top hf (t := t) (u := u) (x := x)
    unfold boundaryOperator at bof
    simp_rw [ENNReal.sum_lt_top] at bof
    exact fun I mI ↦ (bof x I mI).ne

lemma e728_rearrange (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g) :
    ∫ x, conj (g x) * (t.boundaryOperator u f x).toReal =
    ∑ I : Grid X, ((volume (ball (c I) (16 * D ^ s I)))⁻¹.toReal * ∫ x in I, conj (g x)) *
      ∑ J ∈ 𝓙' t u (c I) (s I), (D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ).toReal :=
  calc
    _ = ∫ x, conj (g x) * ∑ I : Grid X,
        (I : Set X).indicator (fun _ ↦ ∑ J ∈ 𝓙' t u (c I) (s I), (ijIntegral f I J).toReal) x := by
      congr with x
      rw [e728_push_toReal hf]
    _ = ∫ x, ∑ I : Grid X, (I : Set X).indicator
        (fun _ ↦ conj (g x) * ∑ J ∈ 𝓙' t u (c I) (s I), (ijIntegral f I J).toReal) x := by
      congr with x; rw [ofReal_sum, Finset.mul_sum]
      congr with I; rw [indicator_const_mul]; congr
      unfold indicator; split_ifs <;> simp
    _ = ∑ I : Grid X, ∫ x, (I : Set X).indicator
        (fun _ ↦ conj (g x) * ∑ J ∈ 𝓙' t u (c I) (s I), (ijIntegral f I J).toReal) x := by
      refine integral_finset_sum _ fun I _ ↦ ?_
      change Integrable ((I : Set X).indicator _)
      rw [integrable_indicator_iff coeGrid_measurable]
      dsimp only
      suffices ∃ M, ∀ᵐ x, ‖conj (g x) * ∑ J ∈ 𝓙' t u (c I) (s I), (ijIntegral f I J).toReal‖ ≤ M by
        obtain ⟨M, hM⟩ := this
        exact Measure.integrableOn_of_bounded (by finiteness)
          ((continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable).mul_const _)
          (ae_restrict_of_ae hM)
      have gb := hg.memLp_top.ae_norm_le
      set L := eLpNorm g ∞ volume |>.toReal
      use L * ‖ofReal (∑ J ∈ 𝓙' t u (c I) (s I), (ijIntegral f I J).toReal)‖;
      filter_upwards [gb] with x hL
      rw [norm_mul, RCLike.norm_conj]; gcongr
    _ = ∑ I : Grid X, ∫ x in I,
        conj (g x) * ∑ J ∈ 𝓙' t u (c I) (s I), (ijIntegral f I J).toReal := by
      congr with I; exact integral_indicator coeGrid_measurable
    _ = ∑ I : Grid X, ∫ x in I, conj (g x) * ∑ J ∈ 𝓙' t u (c I) (s I),
        (D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ).toReal *
          (volume (ball (c I) (16 * D ^ s I)))⁻¹.toReal := by
      congr! with I - x J hJ
      rw [← ENNReal.toReal_mul, ijIntegral]; congr 1
      rw [mul_assoc, mul_comm _ _⁻¹, ← mul_assoc]; rfl
    _ = ∑ I : Grid X, (volume (ball (c I) (16 * D ^ s I)))⁻¹.toReal *
        ∫ x in I, (conj (g x) * ∑ J ∈ 𝓙' t u (c I) (s I),
          (D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ).toReal) := by
      congr with I; rw [← integral_const_mul]
      congr with x; rw [← mul_assoc, mul_comm _ (conj _), mul_assoc]
      congr 1; rw [ofReal_sum, ofReal_sum, Finset.mul_sum]
      congr with J; rw [mul_comm, ofReal_mul]
    _ = _ := by simp_rw [integral_mul_const, mul_assoc]

open scoped Classical in
/-- Equation (7.2.8) in the proof of Lemma 7.2.3. -/
lemma e728 (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g) :
    ‖∫ x, conj (g x) * (t.boundaryOperator u f x).toReal‖ₑ ≤
    ∑ J ∈ 𝓙 (t u), ∫⁻ y in J, ‖f y‖ₑ * MB volume 𝓑 c𝓑 r𝓑 g y *
      ∑ I : Grid X, if (J : Set X) ⊆ ball (c I) (16 * D ^ s I) ∧ s J ≤ s I then
        (D : ℝ≥0∞) ^ ((s J - s I) / (a : ℝ)) else 0 := by
  have nfs := hf.aestronglyMeasurable.enorm
  calc
    _ = ‖∑ I : Grid X, ((volume (ball (c I) (16 * D ^ s I)))⁻¹.toReal * ∫ x in I, conj (g x)) *
        ∑ J ∈ 𝓙' t u (c I) (s I), (D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ).toReal‖ₑ := by
      rw [e728_rearrange hf hg]
    _ ≤ ∑ I : Grid X, ‖((volume (ball (c I) (16 * D ^ s I)))⁻¹.toReal * ∫ x in I, conj (g x)) *
        ∑ J ∈ 𝓙' t u (c I) (s I), (D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ).toReal‖ₑ := by
      simp_rw [enorm_eq_nnnorm, ← ENNReal.coe_finset_sum, ENNReal.coe_le_coe]
      apply nnnorm_sum_le
    _ ≤ ∑ I : Grid X, (volume (ball (c I) (16 * D ^ s I)))⁻¹ * ‖∫ x in I, conj (g x)‖ₑ *
        ∑ J ∈ 𝓙' t u (c I) (s I), ‖(D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ).toReal‖ₑ := by
      simp_rw [enorm_mul]; gcongr <;> rw [← ofReal_norm, norm_real, ofReal_norm]
      · exact enorm_toReal_le
      · simp_rw [enorm_eq_nnnorm, ← ENNReal.coe_finset_sum, ENNReal.coe_le_coe]
        apply nnnorm_sum_le
    _ ≤ ∑ I : Grid X, ((volume (ball (c I) (16 * D ^ s I)))⁻¹ * ∫⁻ x in I, ‖g x‖ₑ) *
        ∑ J ∈ 𝓙' t u (c I) (s I), D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ := by
      gcongr with I
      · calc
          _ ≤ _ := enorm_integral_le_lintegral_enorm _
          _ = _ := by congr! 2 with x; exact RCLike.enorm_conj _
      · exact enorm_toReal_le
    _ ≤ ∑ I : Grid X,
        ((volume (ball (c I) (16 * D ^ s I)))⁻¹ * ∫⁻ x in ball (c I) (16 * D ^ s I), ‖g x‖ₑ) *
        ∑ J ∈ 𝓙' t u (c I) (s I), D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ := by
      gcongr with I; refine lintegral_mono_set (Grid_subset_ball.trans <| ball_subset_ball ?_)
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = ∑ I : Grid X, (⨍⁻ x in ball (c I) (16 * D ^ s I), ‖g x‖ₑ ∂volume) *
        ∑ J ∈ 𝓙' t u (c I) (s I), D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ := by
      congr!; rw [laverage_eq, Measure.restrict_apply .univ, univ_inter, ENNReal.div_eq_inv_mul]
    _ = ∑ J ∈ 𝓙 (t u), ∑ I : Grid X, if (J : Set X) ⊆ ball (c I) (16 * D ^ s I) ∧ s J ≤ s I then
        (⨍⁻ x in ball (c I) (16 * D ^ s I), ‖g x‖ₑ ∂volume) *
          D ^ ((s J - s I) / (a : ℝ)) * ∫⁻ y in J, ‖f y‖ₑ else 0 := by
      rw [Finset.sum_comm]; congr with I
      simp_rw [Finset.mul_sum, mul_assoc, ← Finset.sum_filter]
      exact Finset.sum_congr (by ext; simp [𝓙']) fun _ _ ↦ rfl
    _ = ∑ J ∈ 𝓙 (t u), ∑ I : Grid X, ∫⁻ y in J,
        if (J : Set X) ⊆ ball (c I) (16 * D ^ s I) ∧ s J ≤ s I then
          (⨍⁻ x in ball (c I) (16 * D ^ s I), ‖g x‖ₑ ∂volume) *
            D ^ ((s J - s I) / (a : ℝ)) * ‖f y‖ₑ else 0 := by
      congr!; split_ifs
      · rw [lintegral_const_mul'' _ nfs.restrict]
      · simp
    _ = ∑ J ∈ 𝓙 (t u), ∫⁻ y in J, ∑ I : Grid X,
        if (J : Set X) ⊆ ball (c I) (16 * D ^ s I) ∧ s J ≤ s I then
          (⨍⁻ x in ball (c I) (16 * D ^ s I), ‖g x‖ₑ ∂volume) *
            D ^ ((s J - s I) / (a : ℝ)) * ‖f y‖ₑ else 0 := by
      congr with J; refine (lintegral_finset_sum' _ fun I _ ↦ ?_).symm
      exact (nfs.restrict.const_mul _).ite (.const _) aemeasurable_const
    _ ≤ ∑ J ∈ 𝓙 (t u), ∫⁻ y in J, ∑ I : Grid X,
        if (J : Set X) ⊆ ball (c I) (16 * D ^ s I) ∧ s J ≤ s I then
          MB volume 𝓑 c𝓑 r𝓑 g y * D ^ ((s J - s I) / (a : ℝ)) * ‖f y‖ₑ else 0 := by
      refine Finset.sum_le_sum fun J mJ ↦ setLIntegral_mono_ae ?_ ?_
      · refine (Finset.aemeasurable_sum _ fun I _ ↦ ?_).restrict; split_ifs; swap; · simp
        refine (AEMeasurable.mul_const ?_ _).mul nfs
        exact (AEStronglyMeasurable.maximalFunction 𝓑.to_countable).aemeasurable
      · refine Eventually.of_forall fun y my ↦ Finset.sum_le_sum fun I _ ↦ ?_
        split_ifs with hIJ; swap; · rfl
        refine mul_le_mul_right' (mul_le_mul_right' ?_ _) _
        obtain ⟨b, mb, eb⟩ : ∃ i ∈ 𝓑, ball (c𝓑 i) (r𝓑 i) = ball (c I) (16 * D ^ s I) := by
          use (4, 0, I); norm_num [𝓑, c𝓑, r𝓑]
        rw [MB, maximalFunction]; simp_rw [inv_one, ENNReal.rpow_one]
        exact le_iSup₂_of_le b mb (by rw [indicator_of_mem (eb ▸ hIJ.1 my), eb])
    _ = _ := by
      congr! with J - y -; rw [Finset.mul_sum]
      congr with I; rw [mul_ite, mul_zero, ← mul_rotate]

open scoped Classical in
/-- Bound for the inner sum in Equation (7.2.8). -/
lemma boundary_geometric_series :
    (∑ I : Grid X, if (J : Set X) ⊆ ball (c I) (16 * D ^ s I) ∧ s J ≤ s I then
      (D : ℝ≥0∞) ^ ((s J - s I) / (a : ℝ)) else 0) ≤ 2 ^ (9 * a + 1) :=
  calc
    _ = ∑ k ∈ Icc (s J) S, ∑ I : Grid X,
        if (J : Set X) ⊆ ball (c I) (16 * D ^ s I) ∧ k = s I then
          (D : ℝ≥0∞) ^ ((s J - s I) / (a : ℝ)) else 0 := by
      rw [Finset.sum_comm]; congr with I
      by_cases h : (J : Set X) ⊆ ball (c I) (16 * D ^ s I)
      · simp_rw [h, true_and, ← Finset.sum_filter]; split_ifs with hs
        · have : (Finset.Icc (s J) S).filter (· = s I) = {s I} := by
            ext k
            rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, and_iff_right_iff_imp]
            intro h'; subst h'; exact ⟨hs, scale_mem_Icc.2⟩
          simp [this]
        · have : (Finset.Icc (s J) S).filter (· = s I) = ∅ := by
            ext k
            simp_rw [Finset.mem_filter, Finset.mem_Icc, Finset.not_mem_empty, iff_false, not_and]
            intro; omega
          simp [this]
      · simp_rw [h, false_and, ite_false, Finset.sum_const_zero]
    _ = ∑ kh : Icc (s J) S, ∑ I : Grid X,
        if (J : Set X) ⊆ ball (c I) (16 * D ^ s I) ∧ kh.1 = s I then
          (D : ℝ≥0∞) ^ ((s J - s I) / (a : ℝ)) else 0 := Finset.sum_subtype _ (fun _ ↦ by simp) _
    _ ≤ ∑ kh : Icc (s J) S, ∑ I : Grid X,
        if I ∈ kissing (Grid.exists_supercube kh.1 kh.2).choose then
          (D : ℝ≥0∞) ^ ((s J - kh.1) / (a : ℝ)) else 0 := by
      gcongr with kh _ I
      obtain ⟨k, h⟩ := kh
      set J' := (Grid.exists_supercube k h).choose
      have pJ' : s J' = k ∧ J ≤ J' := (Grid.exists_supercube k h).choose_spec
      by_cases hs : k = s I; swap; · simp [hs]
      suffices (J : Set X) ⊆ ball (c I) (16 * D ^ s I) → I ∈ kissing J' by
        split_ifs; exacts [by simp_all, by tauto, by positivity, by rfl]
      intro mJ; simp_rw [kissing, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨pJ'.1 ▸ hs.symm, not_disjoint_iff.mpr ⟨c J, ?_, mJ Grid.c_mem_Grid⟩⟩
      refine (pJ'.2.1.trans Grid_subset_ball |>.trans (ball_subset_ball ?_)) Grid.c_mem_Grid
      change (4 : ℝ) * D ^ s J' ≤ 16 * D ^ s J'; gcongr; norm_num
    _ = ∑ kh : Icc (s J) S, (D : ℝ≥0∞) ^ ((s J - kh.1) / (a : ℝ)) *
        (kissing (Grid.exists_supercube kh.1 kh.2).choose).card := by
      simp_rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm (Nat.cast _),
        Finset.filter_univ_mem]
    _ ≤ 2 ^ (9 * a) * ∑ kh : Icc (s J) S, (D : ℝ≥0∞) ^ ((s J - kh.1) / (a : ℝ)) := by
      conv_rhs => rw [Finset.mul_sum]; enter [2, kh]; rw [mul_comm]
      gcongr
      calc
        _ ≤ ((2 ^ (9 * a) : ℕ) : ℝ≥0∞) := by rw [Nat.cast_le]; apply boundary_overlap
        _ = _ := by norm_cast
    _ = 2 ^ (9 * a) * ∑ k : Icc 0 (S - s J).toNat, ((D : ℝ≥0∞) ^ (1 / (a : ℝ))) ^ (-k.1 : ℤ) := by
      congr 1
      have sjs : s J ≤ S := scale_mem_Icc.2
      have ssj : (S - s J).toNat = S - s J := Int.toNat_sub_of_le sjs
      let f : Icc (s J) S → Icc 0 (S - s J).toNat := fun ⟨k, bk⟩ ↦
        ⟨(k - s J).toNat, by rw [mem_Icc] at bk; simp [bk]⟩
      have bijf : Bijective f := by
        rw [Fintype.bijective_iff_surjective_and_card]; constructor
        · rintro ⟨k', bk'⟩; use ⟨k' + s J, by rw [mem_Icc] at bk' ⊢; omega⟩; simp [f]
        · simp only [Fintype.card_ofFinset, Int.card_Icc, Nat.card_Icc, tsub_zero]; omega
      refine Fintype.sum_bijective f bijf _ _ fun ⟨k, bk⟩ ↦ ?_
      simp only [f, Int.toNat_sub_of_le bk.1, neg_sub, ← Int.cast_sub]
      rw [← ENNReal.rpow_intCast, ← ENNReal.rpow_mul, div_mul_comm, mul_one]
    _ = 2 ^ (9 * a) * ∑ k ∈ Icc 0 (S - s J).toNat, ((D : ℝ≥0∞) ^ (1 / (a : ℝ))) ^ (-k : ℤ) := by
      congr 1; symm; exact Finset.sum_subtype _ (fun _ ↦ by simp) _
    _ ≤ 2 ^ (9 * a) * ∑ k ∈ Icc 0 (S - s J).toNat, 2 ^ (-k : ℤ) := by
      gcongr with k
      rw [defaultD, Nat.cast_pow, Nat.cast_ofNat, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_intCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_intCast]
      refine ENNReal.rpow_le_rpow_of_exponent_le one_le_two ?_
      rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Int.cast_neg, Int.cast_natCast, mul_neg,
        neg_le_neg_iff, sq, ← mul_div_assoc, mul_one, mul_div_assoc, mul_div_cancel_of_imp id]
      norm_cast; nth_rw 1 [← one_mul k]; exact mul_le_mul_right' (by linarith [four_le_a X]) _
    _ ≤ 2 ^ (9 * a) * ∑' k : ℕ, 2 ^ (-k : ℤ) := mul_le_mul_left' (ENNReal.sum_le_tsum _) _
    _ ≤ 2 ^ (9 * a) * 2 := by rw [ENNReal.sum_geometric_two_pow_neg_one]
    _ = _ := by rw [← pow_succ]

/-- can be improved to `2 ^ (10 * a + 5 / 2)` -/
irreducible_def C7_2_3 (a : ℕ) : ℝ≥0 := 2 ^ (12 * (a : ℝ))

lemma boundary_operator_bound_aux (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g) :
    ‖∫ x, conj (g x) * (t.boundaryOperator u f x).toReal‖ₑ ≤
      C7_2_3 a * eLpNorm f 2 volume * eLpNorm g 2 volume := by
  classical
  calc
    _ ≤ ∑ J ∈ 𝓙 (t u), ∫⁻ y in J, ‖f y‖ₑ * MB volume 𝓑 c𝓑 r𝓑 g y *
        ∑ I : Grid X, if (J : Set X) ⊆ ball (c I) (16 * D ^ s I) ∧ s J ≤ s I then
          (D : ℝ≥0∞) ^ ((s J - s I) / (a : ℝ)) else 0 := e728 hf hg
    _ ≤ ∑ J ∈ 𝓙 (t u), ∫⁻ y in J, ‖f y‖ₑ * MB volume 𝓑 c𝓑 r𝓑 g y * 2 ^ (9 * a + 1) := by
      gcongr; exact boundary_geometric_series
    _ = 2 ^ (9 * a + 1) * ∑ J ∈ 𝓙 (t u), ∫⁻ y in J, ‖f y‖ₑ * MB volume 𝓑 c𝓑 r𝓑 g y := by
      rw [Finset.mul_sum]; congr! with J mJ
      rw [← lintegral_const_mul' _ _ (by tauto)]; congr with y; rw [mul_comm]
    _ = 2 ^ (9 * a + 1) * ∫⁻ y in ⋃ I : Grid X, I, ‖f y‖ₑ * MB volume 𝓑 c𝓑 r𝓑 g y := by
      rw [← lintegral_biUnion_finset] <;> simp only [mem_toFinset, coe_toFinset, biUnion_𝓙]
      · exact pairwiseDisjoint_𝓙
      · exact fun _ _ ↦ coeGrid_measurable
    _ ≤ 2 ^ (9 * a + 1) * ∫⁻ y, ‖f y‖ₑ * MB volume 𝓑 c𝓑 r𝓑 g y := by
      gcongr; exact setLIntegral_le_lintegral _ _
    _ ≤ 2 ^ (9 * a + 1) * eLpNorm f 2 volume * eLpNorm (MB volume 𝓑 c𝓑 r𝓑 g) 2 volume := by
      rw [mul_assoc]; gcongr
      exact ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm ⟨by simpa using ENNReal.inv_two_add_inv_two⟩
        hf.aestronglyMeasurable.aemeasurable.enorm
        (AEStronglyMeasurable.maximalFunction 𝓑.to_countable).aemeasurable
    _ ≤ 2 ^ (9 * a + 1) * eLpNorm f 2 volume * (2 ^ (a + (3 / 2 : ℝ)) * eLpNorm g 2 volume) := by
      have ST : HasStrongType (α := X) (α' := X) (ε₁ := ℂ) (MB volume 𝓑 c𝓑 r𝓑) 2 2 volume volume
          (CMB (defaultA a) 2) := by
        refine hasStrongType_MB 𝓑.to_countable (R := 2 ^ (S + 5) * D ^ (3 * S + 3))
          (fun ⟨bs, bi⟩ mb ↦ ?_) (by norm_num)
        simp_rw [𝓑, mem_prod, mem_Iic, mem_univ, and_true] at mb
        obtain ⟨mb1, mb2⟩ := mb
        simp_rw [r𝓑, ← zpow_natCast (n := 3 * S + 3), Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
          show 3 * (S : ℤ) + 3 = S + (2 * S + 3) by ring]
        gcongr
        · exact one_le_two
        · exact one_le_D
        · exact scale_mem_Icc.2
        · exact_mod_cast mb2
      specialize ST g (hg.memLp 2)
      rw [CMB_defaultA_two_eq, ENNReal.coe_rpow_of_ne_zero two_ne_zero, ENNReal.coe_ofNat] at ST
      exact mul_le_mul_left' ST.2 _
    _ = 2 ^ (9 * a + 1) * 2 ^ (a + (3 / 2 : ℝ)) * eLpNorm f 2 volume * eLpNorm g 2 volume := by ring
    _ ≤ _ := by
      refine mul_le_mul_right' (mul_le_mul_right' ?_ _) _
      rw [C7_2_3, ENNReal.coe_rpow_of_ne_zero two_ne_zero, ENNReal.coe_ofNat,
        ← ENNReal.rpow_natCast, ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
      refine ENNReal.rpow_le_rpow_of_exponent_le one_le_two ?_
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
        show 9 * (a : ℝ) + 1 + (a + 3 / 2) = 10 * (a : ℝ) + 5 / 2 by ring]
      have : 4 ≤ (a : ℝ) := by norm_cast; exact four_le_a X
      linarith

/-- Lemma 7.2.3. -/
lemma boundary_operator_bound (hf : BoundedCompactSupport f) :
    eLpNorm (t.boundaryOperator u f) 2 volume ≤ C7_2_3 a * eLpNorm f 2 volume := by
  have bcs : BoundedCompactSupport fun x ↦ (t.boundaryOperator u f x).toReal := by
    simp_rw [e728_push_toReal hf]
    refine BoundedCompactSupport.finset_sum fun I _ ↦ ?_
    refine BoundedCompactSupport.indicator_of_isCompact_closure (memLp_top_const _)
      (Metric.isBounded_ball.subset Grid_subset_ball).isCompact_closure coeGrid_measurable
  have elpn_eq : eLpNorm (fun x ↦ (t.boundaryOperator u f x).toReal) 2 volume =
      eLpNorm (t.boundaryOperator u f) 2 volume :=
    eLpNorm_toReal_eq (Eventually.of_forall fun _ ↦ (boundaryOperator_lt_top hf).ne)
  by_cases hv : eLpNorm (t.boundaryOperator u f) 2 volume = 0; · simp [hv]
  have hv' : eLpNorm (t.boundaryOperator u f) 2 volume < ⊤ := elpn_eq ▸ (bcs.memLp 2).2
  rw [← ENNReal.mul_le_mul_right hv hv'.ne, ← sq, ← ENNReal.rpow_natCast]
  nth_rw 1 [show ((2 : ℕ) : ℝ) = (2 : ℝ≥0) by rfl, show (2 : ℝ≥0∞) = (2 : ℝ≥0) by rfl,
    eLpNorm_nnreal_pow_eq_lintegral two_ne_zero]
  convert boundary_operator_bound_aux (t := t) (u := u) hf bcs.toComplex using 2
  · simp_rw [RCLike.conj_mul]; norm_cast
    simp_rw [← norm_pow, integral_norm_eq_lintegral_enorm
      (bcs.aestronglyMeasurable.aemeasurable.pow_const 2).aestronglyMeasurable, enorm_pow,
      enorm_toReal (boundaryOperator_lt_top hf).ne, enorm_eq_self]
    simp_rw [enorm_eq_nnnorm, coe_algebraMap, nnnorm_real, ← enorm_eq_nnnorm,
      ← ENNReal.rpow_natCast, Nat.cast_ofNat]
    refine (enorm_toReal ?_).symm
    replace hv' := ENNReal.pow_lt_top (n := 2) hv'
    rw [← ENNReal.rpow_natCast, show ((2 : ℕ) : ℝ) = (2 : ℝ≥0) by rfl,
      show (2 : ℝ≥0∞) = (2 : ℝ≥0) by rfl, eLpNorm_nnreal_pow_eq_lintegral two_ne_zero,
      show ((2 : ℝ≥0) : ℝ) = (2 : ℕ) by rfl] at hv'
    simp_rw [enorm_eq_self] at hv'; exact hv'.ne
  · rw [← elpn_eq, show (2 : ℝ≥0∞) = (2 : ℝ≥0) by rfl]
    simp_rw [eLpNorm_nnreal_eq_lintegral two_ne_zero]; congr!
    simp [enorm_eq_nnnorm, nnnorm_real]

/-- The constant used in `tree_projection_estimate`.
Originally had value `2 ^ (104 * a ^ 3)` in the blueprint, but that seems to be a mistake. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_2_1 (a : ℕ) : ℝ≥0 := 2 ^ (152 * (a : ℝ) ^ 3)

-- Auxiliary function used in the proof of Lemma 7.2.1
private def eI𝒬u_mul (u : 𝔓 X) (f : X → ℂ) : X → ℂ := fun y ↦ exp (.I * 𝒬 u y) * f y

private lemma boundedCompactSupport_eI𝒬u_mul (u : 𝔓 X) {f : X → ℂ} (hf : BoundedCompactSupport f) :
    BoundedCompactSupport (eI𝒬u_mul u f) := by
  apply hf.mul_bdd_left
  apply memLp_top_of_bound (by fun_prop) 1 (.of_forall fun _ ↦ ?_)
  rw [mul_comm, norm_exp_ofReal_mul_I]

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
  exact measurable_boundaryOperator.aemeasurable

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
    rw [add_comm, ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]; ring
  _ ≤ (2 : ℝ≥0∞) ^ ((a : ℝ) ^ 3) * (2 : ℝ≥0∞) ^ (151 * (a : ℝ) ^ 3) := by
    apply mul_right_mono
    norm_cast
    calc 3 * 2 ^ (12 * a)
      _ ≤ 2 ^ 2 * 2 ^ (12 * a) := by gcongr; norm_num
      _ = 2 ^ (2 + 12 * a)     := by rw [pow_add]
      _ ≤ 2 ^ (a ^ 3)          := pow_le_pow_right₀ one_le_two <| calc 2 + 12 * a
        _ ≤ a + 12 * a := by apply add_le_add_right; linarith
        _ = 13 * a     := by ring
        _ ≤ a ^ 2 * a  := by rw [mul_le_mul_right] <;> nlinarith
        _ = a ^ 3      := rfl
  _ = _ := by
    rw [C7_2_1_def, ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
    norm_cast
    ring

-- Main estimate used in the proof of `tree_projection_estimate`
private lemma eLpNorm_two_cS_bound_le : eLpNorm (cS_bound t u f) 2 volume ≤
    C7_2_1 a * eLpNorm (approxOnCube (𝓙 (t u)) (‖f ·‖)) 2 volume := by
  let μ := volume (α := X)
  let aOC := (approxOnCube (𝓙 (t u)) (‖f ·‖))
  let g₁ := MB μ 𝓑 c𝓑 r𝓑 aOC
  let g₂ := t.boundaryOperator u (approxOnCube (𝓙 (t u)) (‖f ·‖))
  let g₃ := nontangentialMaximalFunction (𝒬 u) (approxOnCube (𝓙 (t u)) (eI𝒬u_mul u f))
  have m₁ : AEMeasurable g₁ :=
    (MeasureTheory.AEStronglyMeasurable.maximalFunction (to_countable 𝓑)).aemeasurable
  have m₂ : AEMeasurable g₂ := measurable_boundaryOperator.aemeasurable
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
      · apply le_of_le_of_eq <| boundary_operator_bound boundedCompactSupport_approxOnCube
        simp [eLpNorm, eLpNorm', aOC, approxOnCube_ofReal, enorm_eq_nnnorm, μ]
      · apply le_trans <| nontangential_operator_bound boundedCompactSupport_approxOnCube (𝒬 u)
        refine mul_le_mul_left' (eLpNorm_mono (fun x ↦ ?_)) _
        apply le_of_le_of_eq norm_approxOnCube_le_approxOnCube_norm
        rw [Real.norm_of_nonneg <| approxOnCube_nonneg (fun _ ↦ norm_nonneg _)]
        simp_rw [norm_eI𝒬u_mul_eq]
    _ = (C7_1_3 a * CMB (defaultA a) 2 + C7_1_3 a * C7_2_3 a + C7_2_2 a) * eLpNorm aOC 2 μ := by
      rw [ENNReal.smul_def, smul_eq_mul]; ring
    _ ≤ _ := mul_le_mul_right' (le_C7_2_1 (four_le_a X)) _

/- TODO: PR next to `Complex.norm_real` -/
@[simp 1100, norm_cast]
 protected lemma Complex.enorm_real (x : ℝ) : ‖(x : ℂ)‖ₑ = ‖x‖ₑ := by simp [enorm]

/-- Lemma 7.2.1. -/
lemma tree_projection_estimate
    (hf : BoundedCompactSupport f) (hg : BoundedCompactSupport g) (hu : u ∈ t) :
    ‖∫ x, conj (g x) * carlesonSum (t u) f x‖ₑ ≤
    C7_2_1 a * eLpNorm (approxOnCube (𝓙 (t u)) (‖f ·‖)) 2 volume *
    eLpNorm (approxOnCube (𝓛 (t u)) (‖g ·‖)) 2 volume := by
  classical
  set aOC := approxOnCube (𝓛 (t u)) (‖g ·‖)
  let eaOC (x : X) := ENNReal.ofReal (aOC x)
  have aOC_nonneg {x : X} : 0 ≤ aOC x := approxOnCube_nonneg (fun _ ↦ norm_nonneg _)
  calc ‖∫ x, conj (g x) * carlesonSum (t u) f x‖ₑ
    _ ≤ ∫⁻ x, ‖conj (g x) * carlesonSum (t u) f x‖ₑ := enorm_integral_le_lintegral_enorm _
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
    _ = ∑ L ∈ 𝓛 (t u), ∫⁻ x in L, ‖g x‖ₑ * ‖carlesonSum (t u) f x‖ₑ := by
      simp only [← mem_toFinset]
      refine lintegral_biUnion_finset ?_ (fun _ _ ↦ coeGrid_measurable) _
      rw [coe_toFinset]
      exact pairwiseDisjoint_𝓛
    _ ≤ ∑ L ∈ 𝓛 (t u), ∫⁻ x in L, ‖g x‖ₑ * (⨅ x' ∈ L, ‖cS_bound t u f x'‖ₑ) := by
      gcongr ∑ L ∈ 𝓛 (t u), ?_ with L hL
      refine setLIntegral_mono_ae (AEMeasurable.mul ?_ aemeasurable_const)
        (.of_forall fun x hx ↦ ?_)
      · exact aemeasurable_coe_nnreal_ennreal_iff.mpr
          hg.restrict.aestronglyMeasurable.aemeasurable.nnnorm
      · gcongr
        refine le_iInf₂ (fun x' hx' ↦ ?_)
        simp only [mem_toFinset] at hL
        convert pointwise_tree_estimate hu hL hx hx' (boundedCompactSupport_eI𝒬u_mul u hf) using 1
        · congr
          simp_rw [mul_neg, eI𝒬u_mul, ← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]
        · simp only [cS_bound, enorm_eq_self, norm_eI𝒬u_mul_eq u f]
    _ = ∑ L ∈ 𝓛 (t u), ∫⁻ x in L, eaOC x * (⨅ x' ∈ L, ‖cS_bound t u f x'‖ₑ) := by
      refine Finset.sum_congr rfl (fun L hL ↦ ?_)
      rw [lintegral_mul_const'', lintegral_mul_const]; rotate_left
      · exact ENNReal.measurable_ofReal.comp (stronglyMeasurable_approxOnCube _ _).measurable
      · exact hg.restrict.aestronglyMeasurable.enorm
      simp_rw [eaOC, enorm_eq_nnnorm]
      simp_rw [lintegral_coe_eq_integral (‖g ·‖₊) hg.integrable.norm.restrict, coe_nnnorm]
      rw [integral_eq_lintegral_approxOnCube pairwiseDisjoint_𝓛 (mem_toFinset.mp hL) hg]
      simp_rw [← Real.enorm_eq_ofReal aOC_nonneg, approxOnCube_ofReal, aOC, Complex.enorm_real]
    _ ≤ ∑ L ∈ 𝓛 (t u), ∫⁻ x in L, eaOC x * ‖cS_bound t u f x‖ₑ :=
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
      have isConj : Real.HolderConjugate 2 2 := by constructor <;> norm_num
      have : AEMeasurable eaOC := (stronglyMeasurable_approxOnCube _ _).aemeasurable.ennreal_ofReal
      convert ENNReal.lintegral_mul_le_Lp_mul_Lq volume isConj this aeMeasurable_cS_bound <;>
        simp [eLpNorm, eLpNorm']
    _ = eLpNorm (cS_bound t u f) 2 volume * eLpNorm aOC 2 volume := by
      rw [mul_comm]; congr; ext; exact (Real.enorm_eq_ofReal aOC_nonneg).symm
    _ ≤ _ := mul_right_mono eLpNorm_two_cS_bound_le

end TileStructure.Forest
