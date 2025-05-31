import Carleson.ForestOperator.AlmostOrthogonality

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

/-! ## Lemma 7.5.5 -/

/-- The constant used in `holder_correlation_tile`.
Has value `2 ^ (151 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_5_5 (a : ℕ) : ℝ≥0 := 2 ^ (151 * (a : ℝ) ^ 3)

section OneInOneOut

omit [ProofData a q K σ₁ σ₂ F G] in
lemma ψ_le_max [ProofData a q K σ₁ σ₂ F G] {x : ℝ} : ψ x ≤ max 0 ((2 - 4 * x) ^ (a : ℝ)⁻¹) := by
  by_cases h₁ : x ≤ 1 / 4
  · exact (ψ_le_one ..).trans ((Real.one_le_rpow (by linarith) (by simp)).trans (le_max_right ..))
  by_cases h₂ : 1 / 2 ≤ x
  · rw [ψ_formula₄ h₂]; exact le_max_left ..
  push_neg at h₁ h₂; rw [ψ_formula₃ (one_lt_D (X := X)) ⟨h₁.le, h₂.le⟩]
  refine le_trans ?_ (le_max_right ..)
  set y := 2 - 4 * x; apply Real.self_le_rpow_of_le_one
  · unfold y; linarith
  · unfold y; linarith
  · exact Nat.cast_inv_le_one a

lemma le_of_mem_E {y : X} (hy : y ∈ E p) (hx' : x' ∉ ball (𝔠 p) (5 * D ^ 𝔰 p)) :
    2 - 4 * ((D : ℝ) ^ (-𝔰 p) * dist y x) ≤ dist x x' / D ^ (𝔰 p) * 4 := by
  have := one_le_D (a := a)
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
      congr 1 with y; norm_cast; nth_rw 1 [mul_comm I]; nth_rw 2 [← enorm_norm]
      rw [norm_exp_ofReal_mul_I, enorm_one, mul_one, ← enorm_norm, RCLike.norm_conj, enorm_norm]
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
      simp_rw [Nat.cast_pow, NNReal.rpow_natCast, Nat.cast_ofNat,
        show (4 : ℝ≥0) = 2 ^ 2 by norm_num, ← pow_add]
      apply pow_le_pow_right' one_le_two
      calc
        _ = 102 * a ^ 3 + 3 * a * 1 * 1 + 2 * 1 * 1 * 1 := by norm_num
        _ ≤ 102 * a ^ 3 + 3 * a * a * a + 2 * a * a * a := by gcongr <;> linarith [four_le_a X]
        _ = 107 * a ^ 3 := by ring
        _ ≤ _ := by gcongr; norm_num

end OneInOneOut

section BothIn

lemma integrable_adjointCarleson_interior (hf : BoundedCompactSupport f) :
    Integrable (fun y ↦ exp (.I * 𝒬 u x) * (conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x)) * f y))
      (volume.restrict (E p)) := by
  have h2f := hf.memLp_top.ae_norm_le
  set B := eLpNorm f ∞ volume |>.toReal
  refine Integrable.const_mul ?_ _; simp_rw [mul_rotate]
  refine Integrable.bdd_mul' (c := B) ?_ ?_ ?_
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
      rw [edist_eq_enorm_sub, adjointCarleson, adjointCarleson, ← integral_const_mul,
        ← integral_const_mul, ← integral_sub] <;> exact integrable_adjointCarleson_interior hf
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
      exact enorm_exp_I_mul_ofReal_sub_one_le
    _ = _ := by
      congr! 4
      · congr 1; rw [← enorm_norm, RCLike.norm_conj, enorm_norm]
      · rw [← map_sub, ← enorm_norm, RCLike.norm_conj, enorm_norm]

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
    ‖-Q y x + Q y x' + 𝒬 u x - 𝒬 u x'‖ₑ ≤ Q7_5_5 a * (nndist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ := by
  calc
    _ ≤ ‖Q7_5_5 a * (dist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹‖ₑ := by
      rw [← enorm_norm]
      apply Real.enorm_le_enorm (norm_nonneg _) (QQQQ_bound_real my hu hp hx hx')
    _ = _ := by
      rw [enorm_mul, Real.enorm_rpow_of_nonneg (by positivity) (by norm_cast; positivity),
        NNReal.enorm_eq, div_eq_mul_inv, enorm_mul, enorm_inv (by unfold defaultD; positivity),
        ← div_eq_mul_inv]; congr
      · rw [Real.enorm_eq_ofReal dist_nonneg, dist_nndist]; exact ENNReal.ofReal_coe_nnreal
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
          (C2_1_3 a / volume (ball y (D ^ 𝔰 p))) *
            (Q7_5_5 a * (nndist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹)) +
        ∫⁻ y in E p, ‖f y‖ₑ *
          (D2_1_3 a / volume (ball y (D ^ 𝔰 p)) * (nndist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹) := by
      refine add_le_add (setLIntegral_mono' measurableSet_E fun y my ↦ ?_)
        (lintegral_mono fun _ ↦ ?_)
      · exact mul_le_mul' (mul_le_mul_left' enorm_Ks_le _) (QQQQ_bound my hu hp hx hx')
      · gcongr; exact nnnorm_Ks_sub_Ks_le
    _ = (C2_1_3 a * Q7_5_5 a + D2_1_3 a) * (nndist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ *
        ∫⁻ y in E p, ‖f y‖ₑ / volume (ball y (D ^ 𝔰 p)) := by
      conv_lhs =>
        enter [1, 2, y]
        rw [← mul_div_assoc, mul_comm ‖f y‖ₑ, mul_div_assoc, ← mul_rotate]
      have nt₀ : (nndist x x' / (D : ℝ≥0∞) ^ 𝔰 p) ^ (a : ℝ)⁻¹ < ⊤ := by
        apply ENNReal.rpow_lt_top_of_nonneg (by positivity); rw [← lt_top_iff_ne_top]
        exact ENNReal.div_lt_top ENNReal.coe_ne_top (ENNReal.zpow_pos (by simp) (by simp) _).ne'
      have nt₁ : Q7_5_5 a * (nndist x x' / (D : ℝ≥0∞) ^ 𝔰 p) ^ (a : ℝ)⁻¹ * C2_1_3 a ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) nt₀.ne) (by simp)
      rw [lintegral_const_mul' _ _ nt₁]
      conv_lhs =>
        enter [2, 2, y]
        rw [← mul_assoc, ← mul_div_assoc, mul_comm ‖f y‖ₑ, mul_div_assoc, ← mul_rotate]
      have nt₂ : (nndist x x' / (D : ℝ≥0∞) ^ 𝔰 p) ^ (a : ℝ)⁻¹ * D2_1_3 a ≠ ⊤ :=
        ENNReal.mul_ne_top nt₀.ne (by simp)
      rw [lintegral_const_mul' _ _ nt₂, ← add_mul]; congr 1
      rw [← mul_rotate, mul_comm _ (D2_1_3 a : ℝ≥0∞), ← add_mul]
    _ ≤ (C2_1_3 a * Q7_5_5 a + D2_1_3 a) * (nndist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ *
        ∫⁻ y in E p, ‖f y‖ₑ / (volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) / 2 ^ (3 * a)) := by
      refine mul_le_mul_left' (setLIntegral_mono' measurableSet_E fun y my ↦ ?_) _
      exact ENNReal.div_le_div_left (volume_xDsp_bound (E_subset_𝓘 my)) _
    _ = 2 ^ (3 * a) * (C2_1_3 a * Q7_5_5 a + D2_1_3 a) / volume (ball (𝔠 p) (4 * D ^ 𝔰 p)) *
        (edist x x' / D ^ 𝔰 p) ^ (a : ℝ)⁻¹ * ∫⁻ y in E p, ‖f y‖ₑ := by
      conv_lhs =>
        enter [2, 2, y]
        rw [ENNReal.div_eq_inv_mul]
      rw [lintegral_const_mul'' _ hf.restrict.aestronglyMeasurable.enorm, ← mul_assoc]; congr 1
      rw [ENNReal.inv_div (by simp) (by simp), ← mul_rotate, ENNReal.mul_div_right_comm]; congr
      exact coe_nnreal_ennreal_nndist ..
    _ ≤ _ := by
      gcongr; rw [C2_1_3, D2_1_3, C7_5_5, Q7_5_5]; norm_cast
      simp_rw [NNReal.rpow_natCast, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      calc
        _ ≤ (2 : ℝ≥0) ^ (3 * a) *
            (2 ^ (102 * a ^ 3) * (2 ^ 4 * 2 ^ (6 * a)) + 2 ^ (150 * a ^ 3)) := by gcongr; norm_num
        _ ≤ (2 : ℝ≥0) ^ (3 * a) * (2 ^ (150 * a ^ 3) + 2 ^ (150 * a ^ 3)) := by
          gcongr; rw [← pow_add, ← pow_add]; apply pow_le_pow_right' one_le_two
          calc
            _ = 102 * a ^ 3 + 4 * 1 * 1 * 1 + 6 * a * 1 * 1 := by ring
            _ ≤ 102 * a ^ 3 + 4 * a * a * a + 6 * a * a * a := by gcongr <;> linarith [four_le_a X]
            _ = 112 * a ^ 3 := by ring
            _ ≤ _ := by gcongr; norm_num
        _ = (2 : ℝ≥0) ^ (150 * a ^ 3 + (3 * a + 1)) := by
          rw [← two_mul, ← pow_succ', ← pow_add]; ring
        _ ≤ _ := by
          apply pow_le_pow_right' one_le_two
          rw [show 151 * a ^ 3 = 150 * a ^ 3 + a ^ 3 by ring]; gcongr
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
  · rw [adjoint_tile_support1, indicator_of_not_mem hxx.1, indicator_of_not_mem hxx.2]; simp
  rw [not_and_or, not_not_mem, not_not_mem] at hxx
  wlog hx : x ∈ ball (𝔠 p) (5 * D ^ 𝔰 p) generalizing x x'
  · rw [or_comm] at hxx; specialize this hxx (hxx.resolve_right hx)
    rwa [edist_comm, edist_comm x' x] at this
  clear hxx
  by_cases hx' : x' ∉ ball (𝔠 p) (5 * D ^ 𝔰 p)
  · nth_rw 2 [adjoint_tile_support1]
    rw [indicator_of_not_mem hx', mul_zero, edist_zero_right, enorm_mul, mul_comm I, ← enorm_norm,
      norm_exp_ofReal_mul_I, enorm_one, one_mul]
    exact holder_correlation_tile_one hf hx'
  push_neg at hx'
  exact holder_correlation_tile_two hu hp hf hx hx'

end TileStructure.Forest
